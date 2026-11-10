"""The pinned Lean/Mathlib workspace used for verification.

Resolution order for the default project:

1. ``project=`` argument (path or :class:`LeanProject`)
2. ``PYLEANX_PROJECT`` environment variable
3. a ``lean-project/`` directory in the current directory or any parent
4. ``~/.pyleanx/lean-project`` (created by ``pyleanx init``)
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from dataclasses import dataclass, field, replace
from pathlib import Path

from .backend.audit import DEFAULT_POLICY, AxiomPolicy
from .errors import ProjectError

TEMPLATE_DIR = Path(__file__).parent / "_lean_template"
TEMPLATE_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
USER_PROJECT = Path.home() / ".pyleanx" / "lean-project"


@dataclass(frozen=True)
class LeanProject:
    path: Path
    # Seconds per Lean run, including loading the imported Mathlib modules: a cold load of
    # e.g. the trigonometry modules takes several minutes on a slow or memory-starved laptop.
    timeout: float = 900.0
    import_mode: str = "minimal"
    extra_imports: tuple[str, ...] = ()
    policy: AxiomPolicy = field(default=DEFAULT_POLICY)
    lake: str = "lake"
    lean_options: tuple[tuple[str, str], ...] = ()
    unicode_types: bool = False  # render ℝ ℕ ℤ ℚ instead of Real Nat Int Rat
    resolve_env_once: bool = True  # False: spawn `lake env lean` on every run (slower)

    @classmethod
    def at(cls, path: str | os.PathLike[str], **kwargs: object) -> LeanProject:
        return cls(Path(path).resolve(), **kwargs)  # type: ignore[arg-type]

    def with_(self, **changes: object) -> LeanProject:
        return replace(self, **changes)  # type: ignore[arg-type]

    # ------------------------------------------------------------- pinned metadata
    @property
    def toolchain(self) -> str | None:
        f = self.path / "lean-toolchain"
        return f.read_text(encoding="utf-8").strip() if f.exists() else None

    def manifest(self) -> dict | None:
        f = self.path / "lake-manifest.json"
        if not f.exists():
            return None
        return json.loads(f.read_text(encoding="utf-8"))

    @property
    def mathlib_revision(self) -> str | None:
        m = self.manifest()
        if not m:
            return None
        for pkg in m.get("packages", []):
            if pkg.get("name") == "mathlib":
                return pkg.get("rev")
        return None

    def manifest_hash(self) -> str | None:
        f = self.path / "lake-manifest.json"
        if not f.exists():
            return None
        return hashlib.sha256(f.read_bytes()).hexdigest()

    def lake_executable(self) -> str | None:
        return shutil.which(self.lake)

    def validate(self) -> None:
        if not self.path.is_dir():
            raise ProjectError(
                f"Lean project not found at {self.path}. Run `pyleanx init` or set PYLEANX_PROJECT."
            )
        for name in TEMPLATE_FILES:
            if not (self.path / name).exists():
                raise ProjectError(f"Lean project {self.path} is missing {name}")
        if self.mathlib_revision is None:
            raise ProjectError(f"{self.path}/lake-manifest.json does not pin mathlib")

    def config_hash(self) -> str:
        """Hash of the three pin files; the resolved Lake environment depends only on these."""
        h = hashlib.sha256()
        for name in TEMPLATE_FILES:
            f = self.path / name
            h.update(name.encode() + b"\0" + (f.read_bytes() if f.exists() else b"") + b"\0")
        return h.hexdigest()

    def lake_env(self, refresh: bool = False, timeout: float = 900.0) -> dict[str, str]:
        """The Lake environment plus the build directories of vendored libraries
        (``pyleanx add``), which are prepended to ``LEAN_PATH``."""
        env = dict(self._lake_env_base(refresh, timeout))
        from .libs import library_lean_paths

        extra = library_lean_paths(self.path)
        if extra:
            env["LEAN_PATH"] = os.pathsep.join([*extra, env["LEAN_PATH"]])
        return env

    def libraries_hash(self) -> str:
        """Hash of vendored library contents ("" without libraries)."""
        from .libs import libraries_hash

        return libraries_hash(self.path)

    def _lake_env_base(self, refresh: bool = False, timeout: float = 900.0) -> dict[str, str]:
        """Environment that ``lake env`` would set (LEAN, LEAN_PATH, LEAN_SYSROOT, ...).

        ``lake env`` costs seconds per call, so it is resolved once per pin
        configuration and cached in ``<project>/.pyleanx/lake-env.json``. Running the
        pinned ``lean`` with this environment is what ``lake env lean`` does.
        """
        cache_file = self.path / ".pyleanx" / "lake-env.json"
        key = self.config_hash()
        if not refresh and cache_file.exists():
            try:
                data = json.loads(cache_file.read_text(encoding="utf-8"))
                env = data.get("env", {})
                if data.get("config_hash") == key and Path(env.get("LEAN", "")).exists():
                    return env
            except (OSError, ValueError):
                pass
        lake = self.lake_executable()
        if lake is None:
            raise ProjectError(f"`{self.lake}` not found on PATH; install elan (see docs)")
        try:
            out = subprocess.run([lake, "env"], cwd=self.path, capture_output=True, text=True,
                                 encoding="utf-8", errors="replace", timeout=timeout,
                                 check=False)
        except subprocess.TimeoutExpired as exc:
            raise ProjectError(f"`lake env` did not finish within {timeout:.0f}s") from exc
        if out.returncode != 0:
            raise ProjectError(f"`lake env` failed in {self.path}: {out.stderr.strip()[:2000]}")
        env = {}
        for line in out.stdout.splitlines():
            k, sep, v = line.partition("=")
            if sep and k.isupper() and (k.startswith(("LEAN", "LAKE", "ELAN"))):
                env[k] = v
        if "LEAN" not in env or "LEAN_PATH" not in env:
            raise ProjectError("`lake env` did not report LEAN/LEAN_PATH")
        cache_file.parent.mkdir(parents=True, exist_ok=True)
        cache_file.write_text(json.dumps({"config_hash": key, "env": env}, indent=2),
                              encoding="utf-8")
        return env

    def mathlib_cache_present(self) -> bool:
        olean = (self.path / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
                 / "Mathlib" / "Tactic" / "Ring.olean")
        return olean.exists()


def find_project(project: LeanProject | str | os.PathLike[str] | None = None) -> LeanProject:
    """The Lean workspace to use: the argument, ``$PYLEANX_PROJECT``, a ``lean-project/`` in the
    current directory or its parents, or ``~/.pyleanx/lean-project``.
    """
    if isinstance(project, LeanProject):
        return project
    if project is not None:
        return LeanProject.at(project)
    env = os.environ.get("PYLEANX_PROJECT")
    if env:
        return LeanProject.at(env)
    cur = Path.cwd().resolve()
    for d in (cur, *cur.parents):
        cand = d / "lean-project"
        if (cand / "lakefile.toml").exists():
            return LeanProject.at(cand)
    return LeanProject.at(USER_PROJECT)


def write_template(target: Path, overwrite: bool = False) -> list[Path]:
    """Copy the pinned template files into ``target``; never overwrites unless asked."""
    target.mkdir(parents=True, exist_ok=True)
    written = []
    for name in TEMPLATE_FILES:
        dst = target / name
        src = TEMPLATE_DIR / name
        if dst.exists():
            if dst.read_bytes() == src.read_bytes():
                continue
            if not overwrite:
                raise ProjectError(
                    f"{dst} exists and differs from the pinned template; refusing to overwrite "
                    "(use --force if you really want to replace it)"
                )
        shutil.copyfile(src, dst)
        written.append(dst)
    return written
