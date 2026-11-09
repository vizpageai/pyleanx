"""External Lean libraries (beyond Mathlib): vendor, build, and use them from PyLeanX.

``pyleanx add`` copies the *import closure* of the requested modules from a pinned git
commit (or a local directory) into the project, checks that the library was written for
the same Lean toolchain and Mathlib revision, and compiles it with the pinned ``lean``
into ``<project>/.pyleanx/libs/<name>/build``. That directory is then on Lean's search
path for every verification, session and declaration export.

Only modules that import Mathlib (and its dependencies) or each other can be vendored;
anything else is reported instead of being silently fetched. The pinned Lake files are
never modified.

Trust: building a library runs its Lean code (macros, tactics) like any Lean build. The
library's theorems are checked by the kernel when compiled, and any theorem you verify
through PyLeanX is still audited (`#print axioms`) including everything it uses.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from collections.abc import Callable, Iterable, Sequence
from dataclasses import asdict, dataclass, field
from pathlib import Path

from .errors import ProjectError
from .names import validate_identifier, validate_qualified_name

__all__ = ["Library", "LibraryError", "add_library", "build_library", "list_libraries",
           "remove_library", "library_lean_paths", "libraries_hash", "module_imports"]

LIBS_FILE = "pyleanx-libs.json"
#: Packages available in every PyLeanX workspace (Mathlib and its dependencies, Lean core).
PROVIDED_ROOTS = ("Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible",
                  "LeanSearchClient", "ImportGraph", "Init", "Std", "Lean", "Lake")
_SHA_RE = re.compile(r"^[0-9a-f]{40}$")


class LibraryError(ProjectError):
    """A library could not be added, vendored or built."""


@dataclass
class Library:
    name: str
    source: str  # git URL or local path
    rev: str  # full commit SHA ("" for local directories)
    subdir: str
    roots: list[str]
    modules: list[str] = field(default_factory=list)  # vendored, dependencies first
    files: dict[str, str] = field(default_factory=dict)  # relative path -> sha256
    lean_options: list[list[str]] = field(default_factory=list)
    toolchain: str = ""
    mathlib_revision: str = ""
    added_at: str = ""

    def root_dir(self, project_path: Path) -> Path:
        return project_path / ".pyleanx" / "libs" / self.name

    def src_dir(self, project_path: Path) -> Path:
        return self.root_dir(project_path) / "src"

    def build_dir(self, project_path: Path) -> Path:
        return self.root_dir(project_path) / "build"

    def content_hash(self) -> str:
        h = hashlib.sha256()
        for k in sorted(self.files):
            h.update(f"{k}\0{self.files[k]}\0".encode())
        h.update(json.dumps(self.lean_options).encode())
        return h.hexdigest()


# =====================================================================================
# manifest
# =====================================================================================


def _manifest_path(project_path: Path) -> Path:
    return project_path / LIBS_FILE


def list_libraries(project: object = None) -> list[Library]:
    """Libraries vendored into the project (``pyleanx libs``)."""
    from .project import find_project

    path = find_project(project).path  # type: ignore[arg-type]
    return _load(path)


def _load(project_path: Path) -> list[Library]:
    f = _manifest_path(project_path)
    if not f.exists():
        return []
    data = json.loads(f.read_text(encoding="utf-8"))
    if data.get("schema") != 1:
        raise LibraryError(f"{f}: unsupported schema {data.get('schema')!r}")
    return [Library(**d) for d in data.get("libraries", [])]


def _save(project_path: Path, libs: Sequence[Library]) -> None:
    f = _manifest_path(project_path)
    data = {"schema": 1, "libraries": [asdict(lib) for lib in sorted(libs, key=lambda x: x.name)]}
    tmp = f.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, f)


def library_lean_paths(project_path: Path) -> list[str]:
    """Build directories of the project's libraries (prepended to ``LEAN_PATH``)."""
    return [str(lib.build_dir(project_path)) for lib in _load(project_path)]


def libraries_hash(project_path: Path) -> str:
    """Hash of every vendored library's content (part of verification fingerprints)."""
    libs = _load(project_path)
    if not libs:
        return ""
    h = hashlib.sha256()
    for lib in sorted(libs, key=lambda x: x.name):
        h.update(f"{lib.name}\0{lib.rev}\0{lib.content_hash()}\0".encode())
    return h.hexdigest()


# =====================================================================================
# fetching sources
# =====================================================================================


def _git(args: list[str], cwd: Path | None = None, timeout: float = 600) -> str:
    git = shutil.which("git")
    if git is None:
        raise LibraryError("git is required to add libraries from a repository")
    env = dict(os.environ, GIT_TERMINAL_PROMPT="0")
    try:
        out = subprocess.run([git, *args], cwd=cwd, capture_output=True, text=True,
                             encoding="utf-8", errors="replace", timeout=timeout, env=env,
                             check=False)
    except subprocess.TimeoutExpired as exc:
        raise LibraryError(f"git {' '.join(args[:2])} timed out") from exc
    if out.returncode != 0:
        raise LibraryError(f"git {' '.join(args)} failed: {out.stderr.strip()[:1500]}")
    return out.stdout


class _Source:
    """Read files of one pinned revision (git, lazily fetched) or of a local directory."""

    def __init__(self, source: str, rev: str, cache_root: Path) -> None:
        self.source = source
        self.local = Path(source) if Path(source).is_dir() else None
        self.rev = ""
        if self.local is not None:
            return
        if not rev:
            raise LibraryError("a git source needs --rev (a commit SHA, tag or branch)")
        sha = rev if _SHA_RE.match(rev) else self._resolve(rev)
        self.rev = sha
        self.repo = cache_root / f"{_slug(source)}.git"
        if not self.repo.exists():
            self.repo.mkdir(parents=True)
            _git(["init", "--bare", "-q", str(self.repo)])
            _git(["remote", "add", "origin", source], cwd=self.repo)
        have = subprocess.run([shutil.which("git") or "git", "cat-file", "-e", f"{sha}^{{commit}}"],
                              cwd=self.repo, capture_output=True, check=False)
        if have.returncode != 0:
            _git(["fetch", "-q", "--depth", "1", "--filter=blob:none", "origin", sha],
                 cwd=self.repo, timeout=1800)

    def _resolve(self, rev: str) -> str:
        out = _git(["ls-remote", self.source, rev])
        for line in out.splitlines():
            sha, _, ref = line.partition("\t")
            if ref in (rev, f"refs/heads/{rev}", f"refs/tags/{rev}", f"refs/tags/{rev}^{{}}"):
                return sha
        raise LibraryError(f"revision {rev!r} not found in {self.source}")

    def read(self, rel: str) -> bytes | None:
        if self.local is not None:
            f = self.local / rel
            return f.read_bytes() if f.is_file() else None
        git = shutil.which("git") or "git"
        out = subprocess.run([git, "show", f"{self.rev}:{rel}"], cwd=self.repo,
                             capture_output=True, timeout=600, check=False,
                             env=dict(os.environ, GIT_TERMINAL_PROMPT="0"))
        return out.stdout if out.returncode == 0 else None


def _slug(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", text)[-80:]


# =====================================================================================
# import closure
# =====================================================================================

_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)


def module_imports(source: str) -> list[str]:
    """Modules imported by a Lean file's header (``import``/``public import``/…)."""
    text = _BLOCK_COMMENT.sub(" ", source)
    out: list[str] = []
    for raw in text.splitlines():
        line = raw.split("--", 1)[0].strip()
        if not line:
            continue
        words = line.split()
        if words[0] in ("module", "prelude"):
            continue
        while words and words[0] in ("public", "private", "meta", "all"):
            words = words[1:]
        if not words or words[0] != "import":
            break  # end of header
        out.extend(w for w in words[1:] if w not in ("all",))
    return out


def _provided(mod: str) -> bool:
    return mod.split(".", 1)[0] in PROVIDED_ROOTS


def _closure(src: _Source, subdir: str, roots: Sequence[str],
             progress: Callable[[str], None]) -> dict[str, bytes]:
    """module -> file bytes for every library module reachable from ``roots``."""
    found: dict[str, bytes] = {}
    missing: dict[str, str] = {}
    stack = list(roots)
    while stack:
        mod = stack.pop()
        if mod in found or _provided(mod):
            continue
        rel = (subdir.rstrip("/") + "/" if subdir else "") + mod.replace(".", "/") + ".lean"
        data = src.read(rel)
        if data is None:
            missing[mod] = rel
            continue
        found[mod] = data
        if len(found) % 25 == 0:
            progress(f"  … {len(found)} modules")
        for imp in module_imports(data.decode("utf-8", errors="replace")):
            if imp not in found:
                stack.append(imp)
    if missing:
        detail = ", ".join(f"{m} ({p})" for m, p in sorted(missing.items())[:10])
        raise LibraryError(
            f"{len(missing)} imported module(s) are neither in the library nor provided by the "
            f"workspace (Mathlib and its dependencies): {detail}. Add their package as another "
            "library first, or choose roots that do not need them.")
    return found


def _topo(mods: dict[str, bytes]) -> list[str]:
    order: list[str] = []
    state: dict[str, int] = {}

    def visit(m: str) -> None:
        if state.get(m) == 2:
            return
        if state.get(m) == 1:
            raise LibraryError(f"import cycle through {m}")
        state[m] = 1
        for imp in module_imports(mods[m].decode("utf-8", errors="replace")):
            if imp in mods:
                visit(imp)
        state[m] = 2
        order.append(m)

    for m in sorted(mods):
        visit(m)
    return order


# =====================================================================================
# add / build / remove
# =====================================================================================


def add_library(
    name: str,
    source: str,
    *,
    rev: str = "",
    subdir: str = "",
    roots: Iterable[str],
    project: object = None,
    build: bool = True,
    lean_options: Iterable[tuple[str, str]] = (),
    allow_version_mismatch: bool = False,
    timeout: float | None = None,
    progress: Callable[[str], None] = print,
) -> Library:
    """Vendor the import closure of ``roots`` from ``source`` and (by default) build it."""
    from .project import find_project

    proj = find_project(project)  # type: ignore[arg-type]
    proj.validate()
    validate_identifier(name, "library name")
    roots = [validate_qualified_name(r, "root module") for r in roots]
    if not roots:
        raise LibraryError("give at least one root module (--module OAI.Analysis.…)")
    opts = [[validate_qualified_name(k, "option name"), str(v)] for k, v in lean_options]
    for _, v in opts:
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", v):
            raise LibraryError(f"unsafe Lean option value {v!r}")
    cache = Path(os.environ.get("PYLEANX_HOME", Path.home() / ".pyleanx")) / "sources"
    progress(f"fetching {source}{' @ ' + rev if rev else ''} …")
    src = _Source(source, rev, cache)
    _check_versions(src, subdir, proj, allow_version_mismatch, progress)
    progress(f"resolving the import closure of {', '.join(roots)} …")
    mods = _closure(src, subdir, roots, progress)
    order = _topo(mods)
    lib = Library(name=name, source=source, rev=src.rev, subdir=subdir, roots=list(roots),
                  modules=order, lean_options=opts, toolchain=proj.toolchain or "",
                  mathlib_revision=proj.mathlib_revision or "",
                  added_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    root = lib.root_dir(proj.path)
    if root.exists():
        shutil.rmtree(root / "src", ignore_errors=True)
    srcdir = lib.src_dir(proj.path)
    for mod, data in mods.items():
        rel = mod.replace(".", "/") + ".lean"
        dst = srcdir / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(data)
        lib.files[rel] = hashlib.sha256(data).hexdigest()
    _write_notice(src, subdir, lib, root)
    others = [x for x in _load(proj.path) if x.name != name]
    clash = {m for x in others for m in x.modules} & set(lib.modules)
    if clash:
        raise LibraryError(f"modules already provided by another library: {sorted(clash)[:5]}")
    _save(proj.path, [*others, lib])
    progress(f"vendored {len(order)} module(s) into {srcdir}")
    if build:
        build_library(name, proj, timeout=timeout, progress=progress)
    return lib


def _check_versions(src: _Source, subdir: str, proj: object, allow: bool,
                    progress: Callable[[str], None]) -> None:
    prefix = (subdir.rstrip("/") + "/") if subdir else ""
    problems = []
    tc = src.read(prefix + "lean-toolchain") or src.read("lean-toolchain")
    want_tc = getattr(proj, "toolchain", None)
    if tc is not None and want_tc and tc.decode().strip() != want_tc:
        problems.append(f"toolchain {tc.decode().strip()} (project: {want_tc})")
    manifest = src.read(prefix + "lake-manifest.json") or src.read("lake-manifest.json")
    want_ml = getattr(proj, "mathlib_revision", None)
    if manifest is not None and want_ml:
        try:
            pkgs = json.loads(manifest).get("packages", [])
            ml = next((p.get("rev") for p in pkgs if p.get("name") == "mathlib"), None)
        except ValueError:
            ml = None
        if ml and ml != want_ml:
            problems.append(f"Mathlib {ml[:12]} (project: {want_ml[:12]})")
    if problems:
        msg = "library was written for " + "; ".join(problems)
        if not allow:
            raise LibraryError(msg + ". Compiled Lean files are version-specific; pass "
                               "--allow-version-mismatch to try anyway.")
        progress("warning: " + msg)


def _write_notice(src: _Source, subdir: str, lib: Library, root: Path) -> None:
    root.mkdir(parents=True, exist_ok=True)
    prefix = (subdir.rstrip("/") + "/") if subdir else ""
    lic = None
    for cand in (prefix + "LICENSE", "LICENSE", "LICENSE.md", "LICENSE.txt", "COPYING"):
        lic = src.read(cand)
        if lic:
            break
    lines = [f"Vendored by PyLeanX from {lib.source}",
             f"revision: {lib.rev or '(local directory)'}", f"subdir: {subdir or '.'}",
             f"modules: {len(lib.modules)} (roots: {', '.join(lib.roots)})", ""]
    if lic:
        lines += ["License of the original project:", "", lic.decode("utf-8", "replace")]
    else:
        lines.append("No LICENSE file was found in the source; check its terms before use.")
    (root / "NOTICE.txt").write_text("\n".join(lines), encoding="utf-8")


def _stamp(lib: Library, mod: str, dep_stamps: dict[str, str], proj: object) -> str:
    h = hashlib.sha256()
    rel = mod.replace(".", "/") + ".lean"
    h.update(lib.files[rel].encode())
    h.update(json.dumps(lib.lean_options).encode())
    h.update(str(getattr(proj, "toolchain", "")).encode())
    h.update(str(getattr(proj, "mathlib_revision", "")).encode())
    for d in sorted(dep_stamps):
        h.update(dep_stamps[d].encode())
    return h.hexdigest()


def build_library(name: str, project: object = None, *, timeout: float | None = None,
                  progress: Callable[[str], None] = print) -> Library:
    """Compile a vendored library (incremental; one ``lean`` process per module)."""
    from .project import find_project

    proj = find_project(project)  # type: ignore[arg-type]
    lib = next((x for x in _load(proj.path) if x.name == name), None)
    if lib is None:
        raise LibraryError(f"no library named {name!r} (see `pyleanx libs`)")
    srcdir, outdir = lib.src_dir(proj.path), lib.build_dir(proj.path)
    outdir.mkdir(parents=True, exist_ok=True)
    stamps_file = lib.root_dir(proj.path) / "build-stamps.json"
    try:
        old = json.loads(stamps_file.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        old = {}
    env = proj.lake_env()
    lean = env.get("LEAN") or shutil.which("lean")
    if not lean:
        raise LibraryError("pinned `lean` not found (run `pyleanx doctor`)")
    run_env = dict(os.environ)
    run_env.update(env)
    paths = [str(p.build_dir(proj.path)) for p in _load(proj.path)]
    run_env["LEAN_PATH"] = os.pathsep.join([*paths, env.get("LEAN_PATH", "")])
    stamps: dict[str, str] = {}
    contents = {m: (srcdir / (m.replace(".", "/") + ".lean")).read_text(encoding="utf-8")
                for m in lib.modules}
    built = skipped = 0
    for i, mod in enumerate(lib.modules, 1):
        deps = {d: stamps[d] for d in module_imports(contents[mod]) if d in stamps}
        stamp = _stamp(lib, mod, deps, proj)
        stamps[mod] = stamp
        rel = mod.replace(".", "/")
        olean = outdir / (rel + ".olean")
        if old.get(mod) == stamp and olean.exists():
            skipped += 1
            continue
        olean.parent.mkdir(parents=True, exist_ok=True)
        opts = [f"-D{k}={v}" for k, v in lib.lean_options]
        cmd = [lean, *opts, "-o", str(olean), "-i", str(outdir / (rel + ".ilean")), rel + ".lean"]
        progress(f"[{i}/{len(lib.modules)}] {mod}")
        t0 = time.monotonic()
        try:
            out = subprocess.run(cmd, cwd=srcdir, env=run_env, capture_output=True, text=True,
                                 encoding="utf-8", errors="replace",
                                 timeout=timeout or max(proj.timeout, 1800), check=False)
        except subprocess.TimeoutExpired as exc:
            raise LibraryError(f"building {mod} timed out") from exc
        if out.returncode != 0:
            stamps_file.write_text(json.dumps({k: v for k, v in stamps.items() if k != mod}),
                                   encoding="utf-8")
            olean.unlink(missing_ok=True)
            msg = (out.stdout + out.stderr).strip()
            raise LibraryError(f"building {mod} failed:\n{msg[-4000:]}")
        built += 1
        stamps_file.write_text(json.dumps(stamps), encoding="utf-8")
        progress(f"      done in {time.monotonic() - t0:.0f}s")
    stamps_file.write_text(json.dumps(stamps), encoding="utf-8")
    progress(f"library {name}: {built} module(s) built, {skipped} up to date")
    return lib


def remove_library(name: str, project: object = None) -> None:
    """Delete a vendored library (sources, build output and manifest entry)."""
    from .project import find_project

    proj = find_project(project)  # type: ignore[arg-type]
    libs = _load(proj.path)
    lib = next((x for x in libs if x.name == name), None)
    if lib is None:
        raise LibraryError(f"no library named {name!r}")
    shutil.rmtree(lib.root_dir(proj.path), ignore_errors=True)
    _save(proj.path, [x for x in libs if x.name != name])
