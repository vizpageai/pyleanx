"""A proof environment for AI agents (observe / act / undo / verify) on a Lean REPL.

    env = ProofEnv(thm)                       # needs pyleanx[interactive]
    obs = env.observe()                       # JSON-ready: statement, hypotheses, goals
    env.act("nlinarith [sq_nonneg (a - b)]")  # text -> tactic IR (raw only if allowed)
    result = env.verify()                     # batch Lean + axiom audit; the only verdict

Tool-calling LLMs can drive it through :data:`TOOLS` (JSON schemas) and
:meth:`ProofEnv.call_tool`. Nothing an agent does here can mark a theorem verified:
the REPL reporting "no goals" is recorded as ``complete``; ``verified`` comes only
from :meth:`verify`, i.e. a fresh batch Lean run and the ``#print axioms`` audit.
"""

from __future__ import annotations

import dataclasses
import json
import time
from collections.abc import Callable
from typing import TYPE_CHECKING, Any

from ..errors import PyLeanXError, TacticError
from ..project import LeanProject, find_project
from ..proofs import Tactic
from ..render.lean import render_statement
from .parse import TacticParser

if TYPE_CHECKING:
    from ..backend.interface import VerificationResult
    from ..session import ProofSession
    from ..theorem import Theorem

TOOLS: list[dict[str, Any]] = [
    {
        "name": "get_state",
        "description": "Current hypotheses and open goals of the proof (Lean pretty-printed).",
        "input_schema": {"type": "object", "properties": {}},
    },
    {
        "name": "apply_tactic",
        "description": ("Run ONE Lean 4 tactic on the current goal, e.g. `nlinarith [sq_nonneg "
                        "(a - b)]`, `intro x`, `rw [mul_comm]`. On failure the state is "
                        "unchanged and Lean's error is returned."),
        "input_schema": {"type": "object", "properties": {"tactic": {"type": "string"}},
                         "required": ["tactic"]},
    },
    {
        "name": "undo",
        "description": "Undo the last successful tactic.",
        "input_schema": {"type": "object", "properties": {}},
    },
    {
        "name": "verify",
        "description": ("When no goals remain: check the whole proof with a fresh Lean run "
                        "and an axiom audit. Only this can report verified=true."),
        "input_schema": {"type": "object", "properties": {}},
    },
]


class ProofEnv:
    """One theorem, one agent. Records a transcript of every action."""

    def __init__(
        self,
        theorem: Theorem,
        project: LeanProject | str | None = None,
        *,
        allow_raw: bool = False,
        max_steps: int = 200,
        session_factory: Callable[..., ProofSession] | None = None,
        **session_kwargs: Any,
    ) -> None:
        proj = find_project(project)
        if allow_raw and not proj.policy.allow_raw_tactics:
            # Explicit opt-in: free-form AI text runs (screened) and is audited at the end.
            proj = proj.with_(policy=dataclasses.replace(proj.policy, allow_raw_tactics=True))
        self.project = proj
        self.theorem = theorem
        self.allow_raw = allow_raw
        self.max_steps = max_steps
        self.parser = TacticParser(allow_raw=allow_raw)
        if session_factory is None:
            from ..session import ProofSession as session_factory  # noqa: N813
        self.session = session_factory(theorem, proj, **session_kwargs)
        self.transcript: list[dict[str, Any]] = []
        self.steps_taken = 0
        self.result: VerificationResult | None = None
        self._log("open", statement=self.statement, goals=list(self.session.goals))

    # ------------------------------------------------------------------ observation
    @property
    def statement(self) -> str:
        return render_statement(self.theorem, self.project.unicode_types)

    def observe(self) -> dict[str, Any]:
        goals = list(self.session.goals)
        return {
            "theorem": self.theorem.name,
            "statement": self.statement,
            "hypotheses": [f"{h.name} : {h.prop.to_lean()}" for h in self.theorem.assumptions],
            "goals": goals,
            "history": [str(t) for t in self.session.history],
            "steps_taken": self.steps_taken,
            "complete": self.session.is_complete,
            "verified": bool(self.result and self.result.verified),
        }

    # ------------------------------------------------------------------ actions
    def to_tactic(self, action: str | Tactic | list) -> Tactic:
        if isinstance(action, Tactic):
            return action
        if isinstance(action, list):  # canonical tactic JSON, e.g. ["linarith", []]
            from ..serialize import _Decoder

            dec = _Decoder({v.name: v for v in self.theorem.variables})
            dec.in_proof = True
            return dec.tactic(action)
        return self.parser.parse(action)

    def act(self, action: str | Tactic | list) -> dict[str, Any]:
        """Apply one tactic. Returns ``{"ok", "error", "goals", "complete", ...}``."""
        if self.steps_taken >= self.max_steps:
            return self._log("act", action=str(action), ok=False,
                             error=f"step budget exhausted ({self.max_steps})")
        self.steps_taken += 1
        try:
            tactic = self.to_tactic(action)
        except PyLeanXError as exc:
            return self._log("act", action=str(action), ok=False, error=str(exc))
        try:
            r = self.session.apply(tactic)
        except PyLeanXError as exc:
            return self._log("act", action=str(action), tactic=str(tactic), ok=False,
                             error=str(exc))
        return self._log("act", action=str(action), tactic=r.tactic, ok=r.ok, error=r.error,
                         goals=list(r.goals), complete=self.session.is_complete,
                         messages=list(r.messages))

    def peek(self, action: str | Tactic | list) -> dict[str, Any]:
        tactic = self.to_tactic(action)
        r = self.session.peek(tactic)
        return {"ok": r.ok, "error": r.error, "goals": list(r.goals), "tactic": r.tactic}

    def undo(self) -> dict[str, Any]:
        try:
            goals = self.session.undo()
        except TacticError as exc:
            return self._log("undo", ok=False, error=str(exc))
        return self._log("undo", ok=True, goals=list(goals))

    def verify(self, *, use_cache: bool = True,
               timeout: float | None = None) -> VerificationResult | None:
        """The authoritative check (batch Lean + axiom audit). None if goals remain."""
        if not self.session.is_complete:
            self._log("verify", ok=False, error="goals remain; nothing to verify")
            return None
        self.result = self.session.verify(use_cache=use_cache, timeout=timeout)
        self._log("verify", ok=self.result.verified, status=str(self.result.status),
                  axioms=list(self.result.axioms or ()),
                  errors=[str(d) for d in self.result.errors])
        return self.result

    # ------------------------------------------------------------------ tool calling
    def call_tool(self, name: str, arguments: dict[str, Any] | None = None) -> dict[str, Any]:
        """Dispatch one call from :data:`TOOLS` (JSON in, JSON-ready dict out)."""
        args = arguments or {}
        if name == "get_state":
            return self.observe()
        if name == "apply_tactic":
            out = self.act(str(args.get("tactic", "")))
            return {k: out[k] for k in ("ok", "error", "goals", "complete") if k in out}
        if name == "undo":
            return self.undo()
        if name == "verify":
            res = self.verify()
            if res is None:
                return {"verified": False, "error": "goals remain"}
            return {"verified": res.verified, "status": str(res.status),
                    "axioms": list(res.axioms or ()), "errors": [str(d) for d in res.errors]}
        return {"ok": False, "error": f"unknown tool {name!r}"}

    # ------------------------------------------------------------------ transcript
    def _log(self, event: str, **data: Any) -> dict[str, Any]:
        rec = {"event": event, "t": round(time.time(), 3), **data}
        self.transcript.append(rec)
        return rec

    def transcript_jsonl(self) -> str:
        return "\n".join(json.dumps(r, ensure_ascii=False, default=str)
                         for r in self.transcript) + "\n"
