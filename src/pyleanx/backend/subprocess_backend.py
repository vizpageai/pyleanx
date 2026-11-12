"""Batch verification by running ``lake env lean --json <file>`` in the pinned project.

Decision procedure for each theorem (all must hold for ``verified``):

1. Python-side checks pass (proof present; raw tactics allowed and screened).
2. Lean ran to completion within the timeout and the imports loaded.
3. No ``error`` message lies inside the theorem's span or on its audit line.
4. Exactly one ``#print axioms`` report is attributed to *the line PyLeanX emitted
   for this theorem* and names this theorem (prevents spoofed audit text).
5. Every reported axiom is allowed by the :class:`AxiomPolicy`.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

from ..errors import ProjectError
from ..project import LeanProject, find_project
from ..proofs import contains_raw, iter_raw, screen_raw_tactic
from ..render.lean import RenderedModule, render_module
from .audit import parse_axiom_report
from .cache import ResultCache
from .interface import Diagnostic, Status, VerificationResult

BACKEND_VERSION = "pyleanx-subprocess-1"
_OPTION_RE = re.compile(r"[A-Za-z][A-Za-z0-9_.]*\Z")
_OPTION_VALUE_RE = re.compile(r"[A-Za-z0-9_.]+\Z")


@dataclass
class LeanMessage:
    severity: str
    text: str
    line: int | None
    column: int | None
    end_line: int | None = None
    end_column: int | None = None


@dataclass
class LeanRun:
    returncode: int | None
    messages: list[LeanMessage]
    other_output: str
    timed_out: bool
    duration_ms: float


# ======================================================================================
# Process handling
# ======================================================================================


def _kill_tree(proc: subprocess.Popen) -> None:
    try:
        if sys.platform == "win32":
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=False,
            )
        else:
            os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, OSError):  # pragma: no cover - already gone
        pass
    try:
        proc.kill()
    except OSError:  # pragma: no cover
        pass


def run_lean(project: LeanProject, lean_file: Path, timeout: float) -> LeanRun:
    """Run the pinned Lean on ``lean_file`` (no shell, explicit argv, env and cwd).

    Equivalent to ``lake env lean --json <file>``: by default the Lake environment is
    resolved once per pin configuration (see :meth:`LeanProject.lake_env`) and the
    pinned ``lean`` binary is executed directly with it.
    """
    option_args = []
    for name, value in project.lean_options:
        if not _OPTION_RE.match(name) or not _OPTION_VALUE_RE.match(value):
            raise ProjectError(f"unsafe Lean option {name}={value}")
        if name.startswith("debug."):
            raise ProjectError(f"Lean option {name} is not permitted (it can weaken checking)")
        option_args.append(f"-D{name}={value}")
    env: dict[str, str] | None = None
    if project.resolve_env_once:
        lake_env = project.lake_env()
        argv = [lake_env["LEAN"], "--json"]
        env = {**os.environ, **lake_env}
        env["PATH"] = str(Path(lake_env["LEAN"]).parent) + os.pathsep + env.get("PATH", "")
    else:
        lake = project.lake_executable()
        if lake is None:
            raise ProjectError(f"`{project.lake}` not found on PATH; install elan (see docs)")
        argv = [lake, "env", "lean", "--json"]
    argv += [*option_args, str(lean_file)]
    kwargs: dict = {}
    if sys.platform == "win32":
        kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        kwargs["start_new_session"] = True
    start = time.perf_counter()
    proc = subprocess.Popen(
        argv,
        cwd=project.path,
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        **kwargs,
    )
    timed_out = False
    try:
        out_b, err_b = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        _kill_tree(proc)
        out_b, err_b = proc.communicate()
    duration = (time.perf_counter() - start) * 1000
    out = out_b.decode("utf-8", errors="replace")
    err = err_b.decode("utf-8", errors="replace")
    messages, other = parse_json_messages(out)
    return LeanRun(
        returncode=None if timed_out else proc.returncode,
        messages=messages,
        other_output=(other + ("\n" + err if err else "")).strip(),
        timed_out=timed_out,
        duration_ms=duration,
    )


def parse_json_messages(stdout: str) -> tuple[list[LeanMessage], str]:
    """Parse ``lean --json`` output (one JSON object per line)."""
    messages: list[LeanMessage] = []
    other: list[str] = []
    for line in stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            other.append(line)
            continue
        if not isinstance(obj, dict) or "severity" not in obj:
            other.append(line)
            continue
        pos = obj.get("pos") or {}
        end = obj.get("endPos") or {}
        messages.append(
            LeanMessage(
                severity=str(obj.get("severity")),
                text=str(obj.get("data", "")),
                line=pos.get("line"),
                column=pos.get("column"),
                end_line=end.get("line"),
                end_column=end.get("column"),
            )
        )
    return messages, "\n".join(other)


# ======================================================================================
# Fingerprints
# ======================================================================================


def fingerprint(thm_canonical: object, module: RenderedModule, project: LeanProject) -> str:
    blob = {
        "backend": BACKEND_VERSION,
        "theorem": thm_canonical,
        "lean_source": module.source,
        "toolchain": project.toolchain,
        "mathlib": project.mathlib_revision,
        "manifest_sha256": project.manifest_hash(),
        "policy": project.policy.to_dict(),
        "import_mode": project.import_mode,
        "lean_options": [list(o) for o in project.lean_options],
    }
    libs = project.libraries_hash()
    if libs:  # vendored libraries the module may import (absent: old fingerprints unchanged)
        blob["libraries_sha256"] = libs
    data = json.dumps(blob, sort_keys=True, ensure_ascii=False, default=str).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


# ======================================================================================
# Classification
# ======================================================================================


_NAME_TAKEN = "has already been declared"
_NAME_TAKEN_HINT = (
    "\n[pyleanx] Lean or Mathlib already has a declaration with this name; give the theorem "
    "a distinctive name (e.g. a prefix such as `my_`)."
)


def _diag(msg: LeanMessage, module: RenderedModule) -> Diagnostic:
    span = module.source_map.innermost(msg.line) if msg.line is not None else None
    text = msg.text.strip()
    if msg.severity == "error" and _NAME_TAKEN in text:
        text += _NAME_TAKEN_HINT
    return Diagnostic(
        severity=msg.severity,
        message=text,
        line=msg.line,
        column=msg.column,
        end_line=msg.end_line,
        end_column=msg.end_column,
        span_kind=span.kind if span else None,
        span_label=span.label if span else None,
        python_origin=str(span.origin) if span and span.origin else None,
    )


def _pyleanx_diag(message: str, severity: str = "error") -> Diagnostic:
    return Diagnostic(severity=severity, message=message, source="pyleanx")


def classify(
    run: LeanRun, module: RenderedModule, project: LeanProject
) -> dict[str, tuple[Status, list[Diagnostic], tuple[str, ...] | None]]:
    """Per-theorem (status, diagnostics, axioms) from one Lean run."""
    sm = module.source_map
    names = module.theorem_names
    out: dict[str, tuple[Status, list[Diagnostic], tuple[str, ...] | None]] = {}

    if run.timed_out:
        d = _pyleanx_diag(
            f"Lean did not finish within the timeout ({run.duration_ms / 1000:.0f} s). Most of "
            "that time is usually spent loading Mathlib, which is slow on the first run after "
            "a reboot or when memory is low; retry with a larger limit, e.g. "
            "thm.verify(timeout=1800) or `pyleanx check --timeout 1800`.")
        return {n: (Status.TIMEOUT, [d], None) for n in names}

    header = next(s for s in sm.spans if s.kind == "header")
    header_errors = [
        m for m in run.messages
        if m.severity == "error" and (m.line is None or header.contains(m.line))
    ]
    if header_errors:
        diags = [_diag(m, module) for m in header_errors]
        diags.append(_pyleanx_diag(
            "imports failed to load; is the Mathlib cache present (`lake exe cache get`) and "
            "are the requested modules part of the pinned Mathlib?"))
        return {n: (Status.ENVIRONMENT_ERROR, diags, None) for n in names}

    def_spans = [s for s in sm.spans if s.kind in ("definition", "library_fact")]
    def_errors = [m for m in run.messages if m.severity == "error" and m.line is not None
                  and any(s.contains(m.line) for s in def_spans)]
    if def_errors:
        # A broken definition or shipped fact invalidates every theorem (fail closed).
        diags = [_diag(m, module) for m in def_errors]
        diags.append(_pyleanx_diag(
            "a definition or library fact in this Lean file failed to elaborate"))
        return {n: (Status.REJECTED, diags, None) for n in names}

    header_notes = [_diag(m, module) for m in run.messages
                    if m.line is not None and header.contains(m.line)]
    for name in names:
        span = sm.theorem_span(name)
        audit_line = sm.audit_line(name)
        assert span is not None
        # The theorem, its `avoid=` check (an error there rejects it) and its axiom audit.
        checks = [s for s in sm.spans if s.kind == "avoid_check" and s.theorem == name]
        # theorems this proof cites (emitted above it): their errors reject this theorem
        cited = [s for s in sm.spans if s.kind == "cited_theorem" and s.theorem == name]
        cited_errors = [s for s in cited if any(
            m.severity == "error" and m.line is not None and s.contains(m.line)
            for m in run.messages)]
        mine = [
            m for m in run.messages
            if m.line is not None and (span.contains(m.line) or m.line == audit_line
                                       or any(c.contains(m.line) for c in checks))
        ]
        diags = header_notes + [_diag(m, module) for m in mine]
        errors = [m for m in mine if m.severity == "error"]
        for span in cited_errors:
            diags.extend(_diag(m, module) for m in run.messages
                         if m.severity == "error" and m.line is not None
                         and span.contains(m.line))
            diags.append(_pyleanx_diag(f"the {span.label}, which this proof cites, was not "
                                       "accepted by Lean"))
        if errors or cited_errors:
            out[name] = (Status.REJECTED, diags, None)
            continue
        reports = []
        for m in mine:
            if m.line == audit_line and m.severity == "information":
                rep = parse_axiom_report(m.text)
                if rep is not None and rep.theorem == name:
                    reports.append(rep)
        if len(reports) != 1:
            diags.append(_pyleanx_diag(
                f"expected exactly one axiom report for {name} at line {audit_line}, "
                f"found {len(reports)}; refusing to mark verified"))
            out[name] = (Status.POLICY_REJECTED, diags, None)
            continue
        axioms = reports[0].axioms
        problems = project.policy.check(axioms)
        if problems:
            diags.extend(_pyleanx_diag(p) for p in problems)
            out[name] = (Status.POLICY_REJECTED, diags, axioms)
            continue
        out[name] = (Status.VERIFIED, diags, axioms)

    if run.returncode not in (0, None):
        # Nonzero exit must be explained by an attributed error; otherwise distrust everything.
        any_rejected = any(st is Status.REJECTED for st, _, _ in out.values())
        stray = [m for m in run.messages if m.severity == "error"]
        if not any_rejected:
            env_diags = [_pyleanx_diag(f"Lean exited with code {run.returncode}: "
                                       f"{run.other_output[:2000]}")]
            env_diags.extend(_diag(m, module) for m in stray)
            return {n: (Status.ENVIRONMENT_ERROR, env_diags, None) for n in names}
    return out


# ======================================================================================
# Public entry point
# ======================================================================================


def verify_all(
    theorems: Sequence,
    project: LeanProject | str | os.PathLike[str] | None = None,
    *,
    use_cache: bool = True,
    timeout: float | None = None,
    keep_files: bool = False,
    cache: ResultCache | None = None,
) -> list[VerificationResult]:
    """Verify ``theorems`` in one Lean process; one result per theorem, in order.

    Theorems are emitted in the given order, so a later theorem may use an earlier
    one via ``pl.ref(earlier)``; it then inherits its axioms (and failures).
    """
    proj = find_project(project)
    timeout = timeout if timeout is not None else proj.timeout
    cache = cache or ResultCache()
    policy_dict = proj.policy.to_dict()
    results: list[VerificationResult | None] = [None] * len(theorems)
    to_check: list[int] = []

    for i, thm in enumerate(theorems):
        base = dict(theorem=thm.name, toolchain=proj.toolchain,
                    mathlib_revision=proj.mathlib_revision, policy=policy_dict)
        if thm.proof is None:
            results[i] = VerificationResult(
                status=Status.REJECTED, lean_source=thm.to_lean(proj),
                diagnostics=[_pyleanx_diag("no proof supplied; call thm.prove(...)")], **base)
            continue
        raw = contains_raw(thm.proof)
        if raw:
            problems: list[str] = []
            if not proj.policy.allow_raw_tactics:
                problems.append("proof contains pl.raw_tactic(...) (untrusted text) but the "
                                "policy does not set allow_raw_tactics=True")
            for r in iter_raw(thm.proof):
                problems.extend(f"raw tactic rejected: {p}" for p in screen_raw_tactic(r.text))
            if problems:
                results[i] = VerificationResult(
                    status=Status.POLICY_REJECTED, lean_source=thm.to_lean(proj),
                    diagnostics=[_pyleanx_diag(p) for p in problems], raw_tactics_used=True,
                    **base)
                continue
        to_check.append(i)

    if not to_check:
        return results  # type: ignore[return-value]

    check_thms = [theorems[i] for i in to_check]
    module = render_module(check_thms, import_mode=proj.import_mode,
                           extra_imports=proj.extra_imports, unicode_types=proj.unicode_types)
    fps = {theorems[i].name: fingerprint(theorems[i].canonical(), module, proj) for i in to_check}

    if use_cache:
        cached = {i: cache.get(fps[theorems[i].name]) for i in to_check}
        if all(c is not None for c in cached.values()):
            for i, c in cached.items():
                results[i] = c
            return results  # type: ignore[return-value]

    def env_error(message: str) -> None:
        for i in to_check:
            results[i] = VerificationResult(
                theorem=theorems[i].name, status=Status.ENVIRONMENT_ERROR,
                diagnostics=[_pyleanx_diag(message)], lean_source=module.source,
                toolchain=proj.toolchain, mathlib_revision=proj.mathlib_revision,
                source_map=[s.to_dict() for s in module.source_map.for_theorem(theorems[i].name)],
                fingerprint=fps[theorems[i].name], policy=policy_dict,
                raw_tactics_used=contains_raw(theorems[i].proof))

    try:
        proj.validate()
    except ProjectError as exc:
        env_error(str(exc))
        return results  # type: ignore[return-value]

    work = proj.path / ".pyleanx" / "build" / uuid.uuid4().hex
    work.mkdir(parents=True, exist_ok=True)
    lean_file = work / "PyLeanXCheck.lean"
    lean_file.write_text(module.source, encoding="utf-8", newline="\n")
    try:
        run = run_lean(proj, lean_file, timeout)
    except (ProjectError, OSError) as exc:
        env_error(str(exc))
        return results  # type: ignore[return-value]
    finally:
        if not keep_files:
            shutil.rmtree(work, ignore_errors=True)

    verdicts = classify(run, module, proj)
    for i in to_check:
        thm = theorems[i]
        status, diags, axioms = verdicts[thm.name]
        res = VerificationResult(
            theorem=thm.name, status=status, diagnostics=diags, axioms=axioms,
            lean_source=module.source, toolchain=proj.toolchain,
            mathlib_revision=proj.mathlib_revision,
            source_map=[s.to_dict() for s in module.source_map.for_theorem(thm.name)],
            duration_ms=run.duration_ms, cache_hit=False, fingerprint=fps[thm.name],
            policy=policy_dict, raw_tactics_used=contains_raw(thm.proof))
        if use_cache:
            cache.put(res)
        results[i] = res
    return results  # type: ignore[return-value]
