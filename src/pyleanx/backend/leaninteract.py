"""Persistent Lean REPL transport via LeanInteract (M5): for interactive sessions only.

Nothing returned from here is ever treated as verification. Sessions turn their
tactic history into an ordinary proof that the batch backend checks and audits.

The only module that imports ``lean_interact``; its API surface used here is
``LeanREPLConfig``, ``LocalProject``, ``LeanServer``, ``Command``, ``ProofStep`` and
``lean_interact.interface.LeanError`` (verified against lean-interact 0.11.6).

Launch modes
------------
LeanInteract normally runs its compiled ``repl`` executable. Some managed Windows
machines block newly built executables. ``launch="auto"`` probes the binary and,
if the OS refuses to start it, runs the same REPL program through the pinned
``lean --run REPL/Main.lean`` instead (the REPL modules are already compiled to
``.olean``; Lean's own elaboration runs natively either way).
"""

from __future__ import annotations

import logging
import os
import subprocess
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from ..errors import ProjectError, PyLeanXError
from ..project import LeanProject
from .cache import default_cache_dir

#: Pinned REPL revision (LeanInteract picks the tag matching our Lean toolchain).
REPL_REV = "v1.3.19"
LEAN_INTERACT_VERSION = "0.11.6"


class ReplError(PyLeanXError):
    """The interactive REPL could not be started or crashed."""


class ReplTimeout(ReplError):
    """A REPL request exceeded its timeout (the REPL process was killed)."""


@dataclass(frozen=True)
class ReplMessage:
    severity: str
    text: str
    line: int | None = None
    column: int | None = None


@dataclass(frozen=True)
class StepOutcome:
    """Raw outcome of one REPL request, normalised away from LeanInteract types."""

    ok: bool
    proof_state: int | None
    goals: tuple[str, ...]
    status: str  # REPL proof status, e.g. "Completed", "Incomplete: open goals remain"
    messages: tuple[ReplMessage, ...]
    error: str | None = None


def _quiet_info(record: logging.LogRecord) -> bool:
    return record.levelno >= logging.WARNING


def _require() -> Any:
    # LeanInteract logs Windows long-path advice at INFO on import; keep warnings/errors.
    # (A filter survives its own setLevel/handler reset, which happens at import time.)
    li_logger = logging.getLogger("lean_interact")
    if _quiet_info not in li_logger.filters:
        li_logger.addFilter(_quiet_info)
    try:
        import lean_interact
    except ImportError as exc:  # pragma: no cover - depends on environment
        raise ProjectError(
            "interactive sessions need LeanInteract: pip install 'pyleanx[interactive]'"
        ) from exc
    return lean_interact


def _messages(resp: Any) -> tuple[ReplMessage, ...]:
    out = []
    for m in getattr(resp, "messages", []) or []:
        pos = getattr(m, "start_pos", None)
        out.append(ReplMessage(m.severity, m.data, getattr(pos, "line", None),
                               getattr(pos, "column", None)))
    return tuple(out)


def _clean(message: str) -> str:
    """Drop LeanInteract's generic ``Lean error:`` header line."""
    text = message.strip()
    if text.startswith("Lean error:"):
        text = text[len("Lean error:"):].strip()
    return text or message


def _binary_blocked(repl_dir: Path) -> bool:
    """True if the OS refuses to execute the compiled REPL (e.g. AppLocker)."""
    exe = repl_dir / ".lake" / "build" / "bin" / ("repl.exe" if os.name == "nt" else "repl")
    if not exe.exists():
        return False
    try:
        subprocess.run([str(exe)], stdin=subprocess.DEVNULL, capture_output=True, timeout=60,
                       check=False)
    except PermissionError:
        return True
    except OSError as exc:
        return getattr(exc, "winerror", None) == 5
    except subprocess.TimeoutExpired:
        return False
    return False


class LeanRepl:
    """One persistent REPL process for one :class:`LeanProject`.

    Import environments are cached by import set, so many sessions share one
    Mathlib load. Thread-safe at the request level (LeanInteract locks internally).
    """

    def __init__(self, project: LeanProject, launch: str = "auto", verbose: bool = False) -> None:
        if launch not in ("auto", "binary", "interpreted"):
            raise ValueError("launch must be 'auto', 'binary' or 'interpreted'")
        li = _require()
        project.validate()
        self.project = project
        self._li = li
        from lean_interact.interface import LeanError  # not re-exported at top level

        self._LeanError = LeanError
        cache_dir = default_cache_dir() / "leaninteract"
        self._config = li.LeanREPLConfig(
            project=li.LocalProject(directory=str(project.path), auto_build=False),
            repl_rev=REPL_REV,
            cache_dir=str(cache_dir),
            verbose=verbose,
        )
        repl_dir = Path(self._config._cache_repl_dir)
        if launch == "auto":
            launch = "interpreted" if _binary_blocked(repl_dir) else "binary"
        self.launch = launch
        self._server = self._make_server(repl_dir)
        self._envs: dict[tuple[str, ...], int] = {}
        self._lock = threading.Lock()

    def _make_server(self, repl_dir: Path) -> Any:
        li = self._li
        if self.launch == "binary":
            return li.LeanServer(self._config)
        project = self.project

        class InterpretedServer(li.LeanServer):  # type: ignore[misc, name-defined]
            def start(self) -> None:
                env = {**os.environ, **project.lake_env()}
                lib = repl_dir / ".lake" / "build" / "lib" / "lean"
                env["LEAN_PATH"] = str(lib) + os.pathsep + env["LEAN_PATH"]
                self._proc = subprocess.Popen(
                    [env["LEAN"], "--run", str(repl_dir / "REPL" / "Main.lean")],
                    cwd=str(project.path), env=env, stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, encoding="utf-8",
                    text=True, bufsize=1, start_new_session=True,
                )

        return InterpretedServer(self._config)

    # ------------------------------------------------------------------ requests
    def import_env(self, imports: tuple[str, ...], timeout: float) -> int:
        key = tuple(sorted(imports))
        with self._lock:
            if key in self._envs:
                return self._envs[key]
        # A REPL command must be non-empty; with no imports, a harmless option command.
        code = "\n".join(f"import {m}" for m in key) or "set_option autoImplicit false"
        resp = self._run(self._li.Command(cmd=code), timeout)
        errors = [m for m in _messages(resp) if m.severity == "error"]
        if errors:
            raise ReplError("imports failed in the REPL: " + "; ".join(m.text for m in errors))
        with self._lock:
            self._envs[key] = resp.env
        return resp.env

    def open_statement(self, code: str, env: int, timeout: float) -> StepOutcome:
        resp = self._run(self._li.Command(cmd=code, env=env), timeout)
        msgs = _messages(resp)
        if isinstance(resp, self._LeanError):
            return StepOutcome(False, None, (), "Error", msgs, _clean(resp.message))
        errors = [m for m in msgs if m.severity == "error"]
        sorries = getattr(resp, "sorries", []) or []
        if errors or len(sorries) != 1 or sorries[0].proof_state is None:
            detail = "; ".join(m.text for m in errors) or "statement did not open a proof state"
            return StepOutcome(False, None, (), "Error", msgs, detail)
        s = sorries[0]
        return StepOutcome(True, s.proof_state, (s.goal,), "Incomplete: open goals remain", msgs)

    def step(self, proof_state: int, tactic: str, timeout: float) -> StepOutcome:
        resp = self._run(self._li.ProofStep(proof_state=proof_state, tactic=tactic), timeout)
        msgs = _messages(resp)
        if isinstance(resp, self._LeanError):
            return StepOutcome(False, None, (), "Error", msgs, _clean(resp.message))
        errors = [m for m in msgs if m.severity == "error"]
        if errors:
            return StepOutcome(False, None, (), "Error", msgs, "; ".join(m.text for m in errors))
        return StepOutcome(True, resp.proof_state, tuple(resp.goals), resp.proof_status, msgs)

    def _run(self, request: Any, timeout: float) -> Any:
        try:
            return self._server.run(request, timeout=timeout)
        except TimeoutError as exc:
            self._envs.clear()  # LeanInteract killed the process; states are gone
            raise ReplTimeout(str(exc)) from exc
        except (BrokenPipeError, ConnectionAbortedError, ChildProcessError, OSError) as exc:
            self._envs.clear()
            raise ReplError(f"the Lean REPL stopped: {exc}") from exc

    def is_alive(self) -> bool:
        try:
            return bool(self._server.is_alive())
        except Exception:  # noqa: BLE001
            return False

    def close(self) -> None:
        try:
            self._server.kill()
        except Exception:  # noqa: BLE001 - best effort
            pass
        self._envs.clear()


_REPLS: dict[tuple, LeanRepl] = {}
_REPLS_LOCK = threading.Lock()


def get_repl(project: LeanProject, launch: str = "auto") -> LeanRepl:
    """Shared REPL for this project configuration (created on first use)."""
    key = (str(project.path), project.config_hash(), launch)
    with _REPLS_LOCK:
        repl = _REPLS.get(key)
        if repl is None or not repl.is_alive():
            if repl is not None:
                repl.close()
            repl = LeanRepl(project, launch=launch)
            _REPLS[key] = repl
        return repl


def shutdown_repls() -> int:
    """Stop all shared REPL processes; returns how many were stopped."""
    with _REPLS_LOCK:
        n = len(_REPLS)
        for repl in _REPLS.values():
            repl.close()
        _REPLS.clear()
    return n
