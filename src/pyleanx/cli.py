"""``pyleanx`` command-line interface.

Trust model: ``show-lean``, ``compile`` and ``check`` *execute* the given Python
script (it is ordinary Python, not sandboxed). Only run scripts you trust.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import platform
import re
import runpy
import shutil
import subprocess
import sys
from pathlib import Path

from . import __version__
from .backend.cache import ResultCache
from .backend.subprocess_backend import verify_all
from .errors import ProjectError, PyLeanXError
from .project import USER_PROJECT, LeanProject, find_project, write_template
from .render.lean import render_module
from .theorem import Theorem


def _utf8_stdout() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]
        except (AttributeError, ValueError):  # pragma: no cover
            pass


def load_theorems(script: str) -> list[Theorem]:
    """Run a trusted script and collect ``THEOREMS`` or ``build()``."""
    path = Path(script)
    if not path.is_file():
        raise PyLeanXError(f"script not found: {script}")
    namespace = runpy.run_path(str(path), run_name="__pyleanx__")
    if "build" in namespace and callable(namespace["build"]):
        thms = namespace["build"]()
    elif "THEOREMS" in namespace:
        thms = namespace["THEOREMS"]
    else:
        raise PyLeanXError(
            f"{script} must define a module-level list THEOREMS or a function build() "
            "returning a list of pl.Theorem"
        )
    if isinstance(thms, Theorem):
        thms = [thms]
    thms = list(thms)
    for t in thms:
        if not isinstance(t, Theorem):
            raise PyLeanXError(f"{script}: expected pl.Theorem objects, got {t!r}")
    return thms


def _project_from(args: argparse.Namespace) -> LeanProject:
    proj = find_project(getattr(args, "project", None))
    if getattr(args, "timeout", None):
        proj = proj.with_(timeout=args.timeout)
    if getattr(args, "mathlib_imports", False):
        proj = proj.with_(import_mode="mathlib")
    if getattr(args, "unicode_types", False):
        proj = proj.with_(unicode_types=True)
    return proj


# ------------------------------------------------------------------------------ init
def cmd_init(args: argparse.Namespace) -> int:
    target = Path(args.directory).expanduser().resolve() if args.directory else USER_PROJECT
    written = write_template(target, overwrite=args.force)
    for p in written:
        print(f"wrote {p}")
    print(f"Lean project: {target}")
    if args.no_cache_get:
        print("skipping `lake exe cache get` (--no-cache-get)")
        return 0
    lake = shutil.which("lake")
    if lake is None:
        print("error: `lake` not found; install elan: https://lean-lang.org/install/manual/",
              file=sys.stderr)
        return 1
    print("running `lake exe cache get` (downloads prebuilt Mathlib; may take a while)...")
    rc = subprocess.run([lake, "exe", "cache", "get"], cwd=target, check=False).returncode
    if rc != 0:
        print(f"error: `lake exe cache get` exited with {rc}", file=sys.stderr)
        return rc
    print(f"done. Use it with PYLEANX_PROJECT={target} (found automatically if it is the "
          f"default {USER_PROJECT}).")
    return 0


# ------------------------------------------------------------------------------ doctor
def _version_of(argv: list[str], cwd: Path | None = None) -> str | None:
    try:
        out = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=120,
                             check=False)
    except (OSError, subprocess.TimeoutExpired):
        return None
    text = (out.stdout or out.stderr).strip()
    return text.splitlines()[0] if out.returncode == 0 and text else None


def cmd_doctor(args: argparse.Namespace) -> int:
    ok = True
    checks: list[tuple[str, bool, str]] = []

    def check(name: str, passed: bool, detail: str) -> None:
        nonlocal ok
        ok = ok and passed
        checks.append((name, passed, detail))

    check("python", sys.version_info >= (3, 11), f"{platform.python_version()} ({sys.executable})")
    check("pyleanx", True, __version__)
    for tool in ("elan", "lake", "lean"):
        exe = shutil.which(tool)
        check(f"{tool} on PATH", exe is not None,
              exe or "missing: install elan from https://lean-lang.org/install/manual/")
    proj = find_project(args.project)
    check("project path", proj.path.is_dir(),
          f"{proj.path}" + ("" if proj.path.is_dir() else "  (run `pyleanx init`)"))
    if proj.path.is_dir():
        try:
            proj.validate()
            check("project files", True, "lean-toolchain, lakefile.toml, lake-manifest.json")
        except ProjectError as exc:
            check("project files", False, str(exc))
        pin = proj.toolchain
        check("pinned toolchain", pin is not None, pin or "missing lean-toolchain")
        mrev = proj.mathlib_revision
        check("pinned mathlib", mrev is not None, mrev or "not in manifest")
        lakefile = proj.path / "lakefile.toml"
        if lakefile.exists() and mrev:
            m = re.search(r'rev\s*=\s*"([0-9a-f]+)"', lakefile.read_text(encoding="utf-8"))
            same = bool(m and m.group(1) == mrev)
            check("lakefile/manifest agree", same,
                  "same mathlib rev" if same else f"lakefile {m and m.group(1)} != manifest {mrev}")
        if shutil.which("lake") and pin:
            # First use of a fresh workspace can take minutes (Lake configures packages).
            try:
                env = proj.lake_env(refresh=True)
                ver = _version_of([env["LEAN"], "--version"], cwd=proj.path)
            except ProjectError as exc:
                ver = None
                check("lake env", False, str(exc))
            expected = pin.split(":")[-1].lstrip("v")
            good = bool(ver and f"version {expected}," in ver)
            check("lean in project", good, ver or "could not run the project's pinned lean")
        from ._domain import catalog_status

        status = catalog_status(mrev)
        checks.append(("domain catalogs", True, status))  # informational only
        check("mathlib cache", proj.mathlib_cache_present(),
              "prebuilt .olean files present" if proj.mathlib_cache_present()
              else f"missing; run `lake exe cache get` in {proj.path}")
    stats = ResultCache().stats()
    check("result cache", True, f"{stats['path']} ({stats['entries']} entries)")

    if args.json:
        print(json.dumps({"ok": ok, "checks": [
            {"name": n, "ok": p, "detail": d} for n, p, d in checks]}, indent=2))
    else:
        for name, passed, detail in checks:
            print(f"[{'ok' if passed else 'FAIL'}] {name}: {detail}")
        print("all checks passed" if ok else "some checks failed")
    return 0 if ok else 1


# ------------------------------------------------------------------------------ show/compile
def cmd_show_lean(args: argparse.Namespace) -> int:
    thms = load_theorems(args.script)
    proj = _project_from(args)
    module = render_module(thms, import_mode=proj.import_mode, extra_imports=proj.extra_imports,
                           unicode_types=proj.unicode_types)
    sys.stdout.write(module.source)
    return 0


def cmd_compile(args: argparse.Namespace) -> int:
    thms = load_theorems(args.script)
    proj = _project_from(args)
    module = render_module(thms, import_mode=proj.import_mode, extra_imports=proj.extra_imports,
                           unicode_types=proj.unicode_types)
    out = Path(args.output) if args.output else Path(args.script).with_suffix(".lean")
    out.write_text(module.source, encoding="utf-8", newline="\n")
    print(f"wrote {out} ({len(thms)} theorem(s)). NOT verified: run `pyleanx check`.")
    return 0


# ------------------------------------------------------------------------------ check
def cmd_check(args: argparse.Namespace) -> int:
    thms = load_theorems(args.script)
    proj = _project_from(args)
    if args.allow_raw_tactics:
        proj = proj.with_(policy=dataclasses.replace(proj.policy, allow_raw_tactics=True))
    results = verify_all(thms, project=proj, use_cache=not args.no_cache)
    if args.json:
        payload = [r.to_dict() for r in results]
        if not args.include_source:
            for p in payload:
                p.pop("lean_source", None)
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        for r in results:
            print(r.summary())
        n_ok = sum(r.verified for r in results)
        print(f"{n_ok}/{len(results)} verified")
    return 0 if results and all(r.verified for r in results) else 1


# ------------------------------------------------------------------------------ cache
def cmd_cache(args: argparse.Namespace) -> int:
    cache = ResultCache()
    if args.action == "stats":
        print(json.dumps(cache.stats(), indent=2))
    else:
        print(f"removed {cache.clear()} cached result(s)")
    return 0


# ------------------------------------------------------------------------------ bank
def cmd_bank(args: argparse.Namespace) -> int:
    from .bank import TheoremBank

    bank = TheoremBank.open(args.bank)
    if args.action == "index":
        entries = bank.index_catalogs(args.project, timeout=args.timeout)
        path = bank.save()
        print(f"indexed {len(entries)} declaration(s) with Lean-reported statements -> {path}")
        return 0
    if args.action == "list":
        for e in bank:
            print(e.summary())
        print(f"{len(bank)} entr{'y' if len(bank) == 1 else 'ies'} in {bank.path}")
        return 0
    if not args.query:
        print(f"error: `bank {args.action}` needs a query/ID", file=sys.stderr)
        return 2
    if args.action == "show":
        e = bank.get(args.query)
        print(json.dumps(e.to_dict(), ensure_ascii=False, indent=2) if args.json else
              e.summary() + "\n\n" + e.statement)
        return 0
    hits = bank.search(args.query, limit=args.limit)
    if args.json:
        print(json.dumps([{"score": h.score, **h.entry.to_dict()} for h in hits],
                         ensure_ascii=False, indent=2))
    else:
        for h in hits:
            print(f"{h.score:5.1f}  {h.entry.summary()}")
        if not hits:
            print("no matches" + ("" if len(bank) else " (empty bank: run `pyleanx bank index`)"))
    return 0 if hits else 1


# ------------------------------------------------------------------------------ infoview
def cmd_infoview(args: argparse.Namespace) -> int:
    from .infoview import DeclViews, infoview

    views = infoview(*args.names, imports=args.imports, project=args.project,
                     timeout=args.timeout)
    views = views if isinstance(views, DeclViews) else (views,)
    if args.json:
        print(json.dumps([{"name": v.name, "signature": v.signature,
                           "binders": [dataclasses.asdict(b) for b in v.binders],
                           "conclusion": v.conclusion, "goal": v.goal} for v in views],
                         ensure_ascii=False, indent=2))
    else:
        print(str(DeclViews(views)))
    return 0


# ------------------------------------------------------------------------------ agent
def cmd_agent(args: argparse.Namespace) -> int:
    from . import agent

    if args.action == "export":
        out = agent.export_jsonl(args.output or "pyleanx-basic.jsonl")
        print(f"wrote {len(agent.basic())} problem statements (no proofs) to {out}")
        return 0
    if args.action == "serve":
        from .agent.server import AgentServer

        return AgentServer(args.project, allow_raw=args.allow_raw).serve()
    problems = agent.basic()
    if args.problems:
        wanted = set(args.problems.split(","))
        problems = [p for p in problems if p.name in wanted]
    report = agent.run_benchmark(problems=problems, project=args.project, mode=args.mode,
                                 timeout=args.timeout)
    print(json.dumps(report.to_dict(), ensure_ascii=False, indent=2) if args.json
          else report.summary())
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="pyleanx", description=__doc__.splitlines()[0])
    p.add_argument("--version", action="version", version=f"pyleanx {__version__}")
    sub = p.add_subparsers(dest="command", required=True)

    s = sub.add_parser("init", help="create the pinned Lean/Mathlib workspace")
    s.add_argument("directory", nargs="?")
    s.add_argument("--force", action="store_true", help="overwrite differing pin files")
    s.add_argument("--no-cache-get", action="store_true")
    s.set_defaults(func=cmd_init)

    s = sub.add_parser("doctor", help="diagnose the Lean/Mathlib environment")
    s.add_argument("--project")
    s.add_argument("--json", action="store_true")
    s.set_defaults(func=cmd_doctor)

    for name, func, help_ in (
        ("show-lean", cmd_show_lean, "print generated Lean for a (trusted) script"),
        ("compile", cmd_compile, "write generated Lean to a file (no verification)"),
        ("check", cmd_check, "verify a (trusted) script's theorems with Lean"),
    ):
        s = sub.add_parser(name, help=help_)
        s.add_argument("script")
        s.add_argument("--project")
        s.add_argument("--mathlib-imports", action="store_true",
                       help="emit `import Mathlib` instead of minimal imports")
        s.add_argument("--unicode-types", action="store_true",
                       help="write ℝ ℕ ℤ ℚ instead of Real Nat Int Rat")
        if name == "compile":
            s.add_argument("-o", "--output")
        if name == "check":
            s.add_argument("--json", action="store_true")
            s.add_argument("--include-source", action="store_true")
            s.add_argument("--no-cache", action="store_true")
            s.add_argument("--timeout", type=float)
            s.add_argument("--allow-raw-tactics", action="store_true",
                           help="permit UNTRUSTED pl.raw_tactic text (screened + audited)")
        s.set_defaults(func=func)

    s = sub.add_parser("cache", help="inspect or clear the verified-result cache")
    s.add_argument("action", choices=["stats", "clear"])
    s.set_defaults(func=cmd_cache)

    s = sub.add_parser("bank", help="local theorem bank: index, search, show, list")
    s.add_argument("action", choices=["index", "search", "show", "list"])
    s.add_argument("query", nargs="?", help="search words, or an ID/alias for `show`")
    s.add_argument("--bank", help="bank file (default: $PYLEANX_BANK or ~/.pyleanx/bank.json)")
    s.add_argument("--project")
    s.add_argument("--limit", type=int, default=10)
    s.add_argument("--timeout", type=float)
    s.add_argument("--json", action="store_true")
    s.set_defaults(func=cmd_bank)

    s = sub.add_parser("infoview", help="show Mathlib/core declarations as Lean states them")
    s.add_argument("names", nargs="+", help="declaration names, e.g. two_mul_le_add_sq")
    s.add_argument("--import", dest="imports", action="append", default=[],
                   help="module to import (repeatable; default: import Mathlib)")
    s.add_argument("--project")
    s.add_argument("--timeout", type=float)
    s.add_argument("--json", action="store_true")
    s.set_defaults(func=cmd_infoview)

    s = sub.add_parser("agent", help="proof-agent tools: benchmark, export problems, serve")
    s.add_argument("action", choices=["bench", "export", "serve"])
    s.add_argument("--project")
    s.add_argument("--mode", choices=["session", "batch"], default="session",
                   help="bench: search on the REPL (session) or batch-check candidates")
    s.add_argument("--problems", help="bench: comma-separated problem names")
    s.add_argument("--timeout", type=float)
    s.add_argument("--json", action="store_true")
    s.add_argument("-o", "--output", help="export: JSONL path")
    s.add_argument("--allow-raw", action="store_true",
                   help="serve: let clients run free-form (screened, audited) tactic text")
    s.set_defaults(func=cmd_agent)
    return p


def main(argv: list[str] | None = None) -> int:
    _utf8_stdout()
    args = build_parser().parse_args(argv)
    try:
        return int(args.func(args))
    except PyLeanXError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
