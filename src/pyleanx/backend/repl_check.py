"""Fast checking in a persistent Lean REPL: ``thm.check()`` / ``pl.check_all``.

The batch backend (``verify``) starts a fresh Lean process for every file, so each run pays
for loading Mathlib and for re-checking every shipped fact and cited theorem: minutes per
edit. Here the same Lean source is checked in a persistent REPL, in three pieces:

1. the imports, loaded once per import set (the REPL keeps the environment);
2. the *preamble* -- definitions, shipped facts and the theorems the proofs cite, with their
   ``#print axioms`` lines -- elaborated once and cached by its exact text;
3. the theorems themselves, re-elaborated on every check in the cached environment.

Lean's messages are mapped back to lines of the full file and classified by exactly the
code the batch backend uses (``classify``): the same error attribution, the same
``#print axioms`` audit and the same policy. The source is the same text ``verify()``
would check; only the process is reused.

Results say ``backend="repl"`` and are never stored in the verification cache. Use
``verify()`` (fresh process, archived result with fingerprint) for the record.
"""

from __future__ import annotations

import hashlib
import threading
import time
from collections.abc import Sequence
from dataclasses import dataclass

from ..project import LeanProject, find_project
from ..proofs import contains_raw
from ..render.lean import RenderedModule, render_module
from .interface import Diagnostic, Status, VerificationResult
from .subprocess_backend import LeanMessage, LeanRun, _pyleanx_diag, classify, verify_all

BACKEND = "repl"
#: import sets kept alive in one REPL process before it is restarted (memory bound)
MAX_IMPORT_SETS = 2


@dataclass
class _Chunks:
    imports: tuple[str, ...]
    options: list[str]
    preamble: tuple[int, int] | None  # 1-based inclusive file lines
    main: tuple[int, int]


def split_module(module: RenderedModule) -> _Chunks:
    """Split a rendered file into imports, a cacheable preamble and the main theorems."""
    lines = module.source.splitlines()
    sm = module.source_map
    header = next(s for s in sm.spans if s.kind == "header")
    options = [ln for ln in lines[header.start_line - 1:header.end_line]
               if ln.startswith("set_option")]
    main_starts = [sm.theorem_span(n).start_line for n in module.theorem_names]  # type: ignore[union-attr]
    first_main = min(main_starts)
    # comment lines directly above the first main theorem belong to it
    pre_end = first_main - 1
    pre_start = header.end_line + 1
    preamble = (pre_start, pre_end) if any(
        ln.strip() for ln in lines[pre_start - 1:pre_end]) else None
    return _Chunks(tuple(module.imports), options, preamble, (first_main, len(lines)))


class _PreambleCache:
    """Environments after elaborating a preamble, keyed by (REPL, imports, preamble text)."""

    def __init__(self) -> None:
        self._envs: dict[tuple[int, str], tuple[int, list[LeanMessage]]] = {}
        self._lock = threading.Lock()

    def get(self, key: tuple[int, str]) -> tuple[int, list[LeanMessage]] | None:
        with self._lock:
            return self._envs.get(key)

    def put(self, key: tuple[int, str], value: tuple[int, list[LeanMessage]]) -> None:
        with self._lock:
            self._envs[key] = value

    def clear(self) -> None:
        with self._lock:
            self._envs.clear()


_PREAMBLES = _PreambleCache()


def _run_chunk(repl, code: str, env: int, first_line: int, n_opts: int,
               timeout: float) -> tuple[int | None, list[LeanMessage], bool]:
    """Elaborate ``code`` in ``env``; messages get line numbers of the full file."""
    resp = repl._run(repl._li.Command(cmd=code, env=env), timeout)
    out: list[LeanMessage] = []
    if isinstance(resp, repl._LeanError):
        out.append(LeanMessage("error", str(getattr(resp, "message", resp)), None, None))
        return None, out, True
    for m in getattr(resp, "messages", []) or []:
        pos = getattr(m, "start_pos", None)
        end = getattr(m, "end_pos", None)
        line = getattr(pos, "line", None)
        file_line = None if line is None else line - n_opts + first_line - 1
        end_line = getattr(end, "line", None)
        # the REPL says "info" where `lean --json` says "information"
        severity = {"info": "information"}.get(m.severity, m.severity)
        out.append(LeanMessage(
            severity, m.data, file_line, getattr(pos, "column", None),
            None if end_line is None else end_line - n_opts + first_line - 1,
            getattr(end, "column", None)))
    return resp.env, out, False


_ATEXIT = False


def _stop_repls_at_exit() -> None:
    """A REPL holds Mathlib in memory (GBs); never leave one behind when Python exits."""
    global _ATEXIT
    if not _ATEXIT:
        import atexit

        from .leaninteract import shutdown_repls

        atexit.register(shutdown_repls)
        _ATEXIT = True


def check_all(theorems: Sequence, project: LeanProject | str | None = None, *,
              timeout: float | None = None, launch: str = "auto",
              _retry: bool = True) -> list[VerificationResult]:
    """Check ``theorems`` in the shared REPL; same verdicts as :func:`verify_all`, faster.

    If the REPL fails (it can be refused memory, or crash), it is restarted once; if that
    fails too, the batch backend checks the theorems.
    """
    from .leaninteract import ReplError, ReplTimeout, get_repl, shutdown_repls

    _stop_repls_at_exit()

    proj = find_project(project)
    timeout = timeout if timeout is not None else proj.timeout
    # theorems the batch backend refuses before running Lean (no proof, raw tactics) are
    # refused the same way here
    pre = [t for t in theorems if t.proof is None or contains_raw(t.proof)]
    if pre:
        return verify_all(theorems, project=proj, use_cache=False, timeout=timeout)
    module = render_module(list(theorems), import_mode=proj.import_mode,
                           extra_imports=proj.extra_imports, unicode_types=proj.unicode_types)
    chunks = split_module(module)
    lines = module.source.splitlines()
    t0 = time.monotonic()
    try:
        repl = get_repl(proj, launch=launch)
        if tuple(sorted(chunks.imports)) not in repl._envs and len(repl._envs) >= MAX_IMPORT_SETS:
            # Each import set keeps its whole environment in the REPL's memory; restart the
            # process rather than let it grow without bound (one re-import is the price).
            from .leaninteract import shutdown_repls

            shutdown_repls()
            _PREAMBLES.clear()
            repl = get_repl(proj, launch=launch)
        env = repl.import_env(chunks.imports, timeout)
        messages: list[LeanMessage] = []
        failed = False
        if chunks.preamble is not None:
            s, e = chunks.preamble
            text = "\n".join(chunks.options + lines[s - 1:e])
            key = (id(repl), hashlib.sha256(
                ("\n".join(sorted(chunks.imports)) + "\0" + text).encode()).hexdigest())
            hit = _PREAMBLES.get(key)
            if hit is None:
                new_env, msgs, failed = _run_chunk(repl, text, env, s, len(chunks.options),
                                                   timeout)
                if new_env is not None and not any(m.severity == "error" for m in msgs):
                    _PREAMBLES.put(key, (new_env, msgs))
                hit = (new_env if new_env is not None else env, msgs)
            env, pre_msgs = hit
            messages.extend(pre_msgs)
        if not failed:
            s, e = chunks.main
            text = "\n".join(chunks.options + lines[s - 1:e])
            _, msgs, failed = _run_chunk(repl, text, env, s, len(chunks.options), timeout)
            messages.extend(msgs)
    except ReplTimeout:
        _PREAMBLES.clear()
        run = LeanRun(None, [], "", True, (time.monotonic() - t0) * 1000)
        return _results(theorems, module, proj, run)
    except (ReplError, ValueError, OSError) as exc:  # incl. unparseable REPL output
        shutdown_repls()
        _PREAMBLES.clear()
        if _retry:
            return check_all(theorems, project=proj, timeout=timeout, launch=launch,
                             _retry=False)
        res = verify_all(theorems, project=proj, use_cache=False, timeout=timeout)
        for r in res:
            r.diagnostics.append(_pyleanx_diag(
                f"the fast REPL check was unavailable ({exc}); checked by the batch backend",
                severity="information"))
        return res
    has_error = failed or any(m.severity == "error" for m in messages)
    run = LeanRun(1 if has_error else 0, messages, "", False, (time.monotonic() - t0) * 1000)
    return _results(theorems, module, proj, run)


def _results(theorems: Sequence, module: RenderedModule, proj: LeanProject,
             run: LeanRun) -> list[VerificationResult]:
    verdicts = classify(run, module, proj)
    out = []
    for thm in theorems:
        status, diags, axioms = verdicts[thm.name]
        out.append(VerificationResult(
            theorem=thm.name, status=status, diagnostics=list(diags), axioms=axioms,
            lean_source=module.source, toolchain=proj.toolchain,
            mathlib_revision=proj.mathlib_revision,
            source_map=[s.to_dict() for s in module.source_map.for_theorem(thm.name)],
            duration_ms=run.duration_ms, cache_hit=False, fingerprint="",
            policy=proj.policy.to_dict(), raw_tactics_used=False, backend=BACKEND))
    return out


def clear_preamble_cache() -> None:
    _PREAMBLES.clear()


__all__ = ["check_all", "clear_preamble_cache", "split_module", "Diagnostic", "Status"]
