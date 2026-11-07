"""Interactive proving (M5): see goals, apply tactics one at a time, undo.

    s = thm.session()          # persistent Lean REPL; imports load once per project
    s.goals                    # ('x y : ℝ\\n⊢ (x + y) ^ 2 = ...',)
    s.apply(pl.ring())         # StepResult(ok=True, goals=())
    s.verify()                 # batch check + axiom audit of the recorded script

A session is an *aid*. ``is_complete`` only reports what the REPL says about the
current tactic state; nothing is verified until :meth:`ProofSession.verify` runs the
full batch backend (fresh Lean process, ``#print axioms`` audit, policy).
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from .backend.leaninteract import LeanRepl, ReplError, StepOutcome, get_repl
from .errors import TacticError
from .imports import resolve_imports, tactic_imports
from .project import LeanProject, find_project
from .proofs import Steps, Tactic, contains_raw, iter_raw, screen_raw_tactic, steps
from .render.lean import render_open_statement, render_tactic_lines

if TYPE_CHECKING:
    from .backend.interface import VerificationResult
    from .theorem import Theorem

#: Tactic modules preloaded for Mathlib-based statements, so common tactics never
#: force a re-import mid-session.
COMMON_TACTIC_IMPORTS = (
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Tactic.Positivity",
    "Mathlib.Tactic.Ring",
)


class Goals(tuple):
    """Tuple of goal strings (Lean's pretty-printed hypotheses ⊢ target)."""

    def _repr_markdown_(self) -> str:
        if not self:
            return "**No goals** (the REPL reports the proof complete; call `.verify()`)"
        parts = [f"**{len(self)} goal{'s' if len(self) != 1 else ''}**"]
        parts += [f"```lean\n{g}\n```" for g in self]
        return "\n\n".join(parts)

    def __str__(self) -> str:
        return "\n\n".join(self) if self else "no goals"


@dataclass(frozen=True)
class StepResult:
    """Outcome of :meth:`ProofSession.apply` / :meth:`ProofSession.peek`."""

    ok: bool
    tactic: str
    goals: Goals
    error: str | None = None
    status: str = ""
    messages: tuple[str, ...] = field(default=())

    @property
    def complete(self) -> bool:
        return self.ok and not self.goals

    def __bool__(self) -> bool:  # `if s.apply(...):` reads naturally
        return self.ok

    def _repr_markdown_(self) -> str:
        if not self.ok:
            return f"❌ `{self.tactic}` failed:\n\n```\n{self.error}\n```"
        return f"✔ `{self.tactic}`\n\n" + self.goals._repr_markdown_()


@dataclass(frozen=True)
class _State:
    proof_state: int
    goals: Goals
    status: str


class ProofSession:
    """Step-by-step proof of one :class:`~pyleanx.Theorem` on a shared Lean REPL."""

    def __init__(
        self,
        theorem: Theorem,
        project: LeanProject | str | None = None,
        *,
        timeout: float = 600.0,
        launch: str = "auto",
        preload: Iterable[str] | None = None,
    ) -> None:
        self.theorem = theorem
        self.project = find_project(project)
        self.timeout = timeout
        self.launch = launch
        base = set(resolve_imports([theorem], self.project.extra_imports))
        if preload is None:
            preload = COMMON_TACTIC_IMPORTS if any(m.startswith("Mathlib") for m in base) else ()
        self._imports = tuple(sorted(base | set(preload)))
        self._history: list[Tactic] = []
        self._states: list[_State] = []
        self._open()

    # ------------------------------------------------------------------ plumbing
    def _repl(self) -> LeanRepl:
        return get_repl(self.project, self.launch)

    def _open(self) -> None:
        """(Re)open the statement and replay the recorded history."""
        repl = self._repl()
        env = repl.import_env(self._imports, self.timeout)
        code = render_open_statement(self.theorem, self.project.unicode_types)
        out = repl.open_statement(code, env, self.timeout)
        if not out.ok or out.proof_state is None:
            raise TacticError(f"Lean rejected the statement of {self.theorem.name}: {out.error}")
        self._states = [_State(out.proof_state, Goals(out.goals), out.status)]
        for t in self._history:
            res = self._step(t)
            if not res.ok or res.proof_state is None:  # pragma: no cover - deterministic replay
                raise ReplError(f"replaying `{_text(t)}` failed after a REPL restart: {res.error}")
            self._states.append(_State(res.proof_state, Goals(res.goals), res.status))

    def _step(self, tactic: Tactic) -> StepOutcome:
        state = self._states[-1].proof_state
        try:
            return self._repl().step(state, _text(tactic), self.timeout)
        except ReplError:
            # REPL crashed or timed out: restart once, replay, retry.
            self._open()
            return self._repl().step(self._states[-1].proof_state, _text(tactic), self.timeout)

    def _check_allowed(self, tactic: Tactic) -> None:
        if not contains_raw(tactic):
            return
        if not self.project.policy.allow_raw_tactics:
            raise TacticError("pl.raw_tactic(...) is untrusted text; the project's policy must set "
                              "allow_raw_tactics=True to use it, even interactively")
        for r in iter_raw(tactic):
            problems = screen_raw_tactic(r.text)
            if problems:
                raise TacticError("raw tactic rejected: " + "; ".join(problems))

    def _ensure_imports(self, tactic: Tactic) -> None:
        needed = set(tactic_imports(tactic)) - set(self._imports)
        if needed:  # new modules: new import environment, replay history there
            self._imports = tuple(sorted(set(self._imports) | needed))
            self._open()

    # ------------------------------------------------------------------ public API
    @property
    def goals(self) -> Goals:
        return self._states[-1].goals

    @property
    def is_complete(self) -> bool:
        """No goals remain according to the REPL. NOT a verification result."""
        return not self.goals and self._states[-1].status.startswith("Completed")

    @property
    def history(self) -> tuple[Tactic, ...]:
        return tuple(self._history)

    @property
    def script(self) -> Steps | None:
        return steps(*self._history) if self._history else None

    def peek(self, tactic: Tactic) -> StepResult:
        """Try ``tactic`` on the current state without recording it."""
        return self._try(tactic, commit=False)

    def apply(self, *tactics: Tactic) -> StepResult:
        """Apply tactics in order; stop at the first failure (state left unchanged)."""
        if not tactics:
            raise TacticError("apply() needs at least one tactic")
        result: StepResult | None = None
        for t in tactics:
            result = self._try(t, commit=True)
            if not result.ok:
                break
        assert result is not None
        return result

    def _try(self, tactic: Tactic, commit: bool) -> StepResult:
        if not isinstance(tactic, Tactic):
            raise TacticError(f"expected a tactic such as pl.ring(), got {tactic!r}")
        self._check_allowed(tactic)
        self._ensure_imports(tactic)
        out = self._step(tactic)
        msgs = tuple(m.text for m in out.messages if m.severity != "error")
        if not out.ok or out.proof_state is None:
            return StepResult(False, _text(tactic), self.goals, out.error, out.status, msgs)
        goals = Goals(out.goals)
        if commit:
            self._history.append(tactic)
            self._states.append(_State(out.proof_state, goals, out.status))
        return StepResult(True, _text(tactic), goals, None, out.status, msgs)

    def undo(self, n: int = 1) -> Goals:
        if n < 0 or n > len(self._history):
            raise TacticError(f"cannot undo {n} step(s); history has {len(self._history)}")
        for _ in range(n):
            self._history.pop()
            self._states.pop()
        return self.goals

    def reset(self) -> Goals:
        return self.undo(len(self._history))

    def finish(self) -> Theorem:
        """Attach the recorded tactics as the theorem's proof (still unverified)."""
        if not self._history:
            raise TacticError("no tactics applied yet")
        if not self.is_complete:
            raise TacticError(f"proof incomplete: {len(self.goals)} goal(s) remain")
        self.theorem.prove(self.script)  # type: ignore[arg-type]
        return self.theorem

    def verify(self, *, use_cache: bool = True, timeout: float | None = None) -> VerificationResult:
        """Authoritative check: fresh batch Lean run + axiom audit of the recorded script."""
        return self.finish().verify(self.project, use_cache=use_cache, timeout=timeout)

    def __repr__(self) -> str:
        return (f"<ProofSession {self.theorem.name}: {len(self._history)} step(s), "
                f"{len(self.goals)} goal(s)>")

    def _repr_markdown_(self) -> str:
        head = f"**Session** `{self.theorem.name}` — {len(self._history)} step(s)"
        if self._history:
            head += "\n\n```lean\n" + "\n".join(_text(t) for t in self._history) + "\n```"
        return head + "\n\n" + self.goals._repr_markdown_()


def _text(t: Tactic) -> str:
    return "\n".join(render_tactic_lines(t))


def open_session(theorem: Theorem, project: LeanProject | str | None = None,
                 **kwargs: object) -> ProofSession:
    return ProofSession(theorem, project, **kwargs)  # type: ignore[arg-type]
