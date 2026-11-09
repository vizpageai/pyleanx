"""Proposers (where tactics come from) and proof search (how they are tried).

A *proposer* is any callable ``observation -> list[str | Tactic]`` returning candidate
next tactics, best first. An LLM is just another proposer. Two baselines ship here:

* :class:`AutomationProposer`: introduction rules + Lean/Mathlib automation.
* :class:`RetrievalProposer`: lemmas found in a :class:`~pyleanx.TheoremBank` by
  searching with the goal text (``apply``/``rw``/``simp [...]``/``linarith [...]``).

:func:`search_proof` does depth-first search with backtracking on a REPL session;
:func:`try_proofs` checks whole candidate proofs with the batch backend (no REPL).
Both report ``verified`` only from a batch Lean run with the axiom audit.
"""

from __future__ import annotations

import re
import time
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

from ..errors import PyLeanXError
from ..proofs import Tactic
from .env import ProofEnv

if TYPE_CHECKING:
    from ..backend.interface import VerificationResult
    from ..bank import TheoremBank
    from ..project import LeanProject
    from ..theorem import Theorem

Proposer = Callable[[dict[str, Any]], Sequence["str | Tactic"]]

CLOSERS = ("rfl", "norm_num", "simp", "ring", "linarith", "positivity", "nlinarith",
           "omega", "decide", "assumption", "aesop", "exact?")


def _target(goal: str) -> str:
    return goal.split("⊢", 1)[-1].strip()


def _binder_names(binders: str) -> list[str]:
    """``(x y : ℝ) {n : ℕ}`` or ``x y : ℝ`` or ``x y`` -> ``["x", "y", ...]``."""
    groups = re.findall(r"[({\[]\s*([^:(){}\[\]]+?)\s*:", binders)
    if not groups:
        groups = [binders.split(":", 1)[0]]
    return [n for g in groups for n in g.split() if re.fullmatch(r"[^\W\d][\w']*", n)]


def _fresh(goal: str, base: str) -> str:
    taken = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", goal))
    i = 1
    while f"{base}{i}" in taken:
        i += 1
    return f"{base}{i}"


class AutomationProposer:
    """Structural steps first (intro, constructor), then closing automation."""

    def __init__(self, closers: Iterable[str] = CLOSERS) -> None:
        self.closers = tuple(closers)

    def __call__(self, obs: dict[str, Any]) -> list[str]:
        if not obs["goals"]:
            return []
        goal = obs["goals"][0]
        target = _target(goal)
        out: list[str] = []
        if target.startswith("∀") and "," in target:
            names = _binder_names(target[1:target.index(",")])
            if names:
                out.append("intro " + " ".join(names))
        elif "→" in target or target.startswith("¬"):
            out.append("intro " + _fresh(goal, "h"))
        if "∧" in target or "↔" in target:
            out.append("constructor")
        names = _context_vars(goal)
        if target.startswith("∃"):
            out += ["use 0", "use 1"] + [f"use {v} + 1" for v in names]
        real = [v for v, ty in _context_typed(goal) if ty in ("ℝ", "Real", "ℚ", "ℤ")]
        if len(real) >= 2:
            a, b = real[0], real[1]
            out.append(f"nlinarith [sq_nonneg ({a} - {b}), sq_nonneg ({a} + {b})]")
        out.extend(self.closers)
        return out


def _context_typed(goal: str) -> list[tuple[str, str]]:
    """(name, type) for variables declared in the goal's context (``a b : ℝ``)."""
    out = []
    for line in goal.splitlines():
        if line.startswith("⊢") or " : " not in line:
            continue
        names, _, ty = line.partition(" : ")
        for n in names.split():
            if re.fullmatch(r"[^\W\d][\w']*", n):
                out.append((n, ty.strip()))
    return out


def _context_vars(goal: str) -> list[str]:
    return [n for n, ty in _context_typed(goal) if ty in ("ℕ", "Nat", "ℤ", "Int", "ℝ", "Real")]


class RetrievalProposer:
    """Bank search on the goal text; proposes the hits' Lean names in a few shapes."""

    def __init__(self, bank: TheoremBank, k: int = 3) -> None:
        self.bank = bank
        self.k = k

    def __call__(self, obs: dict[str, Any]) -> list[str]:
        if not obs["goals"]:
            return []
        query = " ".join(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", _target(obs["goals"][0])))
        names = [h.entry.lean_name for h in self.bank.search(query, limit=self.k)
                 if h.entry.kind == "declaration"]
        out = []
        for n in names:
            out += [f"apply {n}", f"rw [{n}]", f"simp [{n}]", f"nlinarith [{n}]"]
        return out


class ChainProposer:
    def __init__(self, *proposers: Proposer) -> None:
        self.proposers = proposers

    def __call__(self, obs: dict[str, Any]) -> list:
        seen: set[str] = set()
        out = []
        for p in self.proposers:
            for c in p(obs):
                if str(c) not in seen:
                    seen.add(str(c))
                    out.append(c)
        return out


@dataclass
class ProofAttempt:
    theorem: str
    status: str  # "verified" | "rejected" | "incomplete" | "error"
    script: list[str] = field(default_factory=list)
    result: VerificationResult | None = None
    expansions: int = 0
    seconds: float = 0.0
    transcript: list[dict[str, Any]] = field(default_factory=list)
    error: str | None = None

    @property
    def verified(self) -> bool:
        return self.status == "verified" and self.result is not None and self.result.verified

    def to_dict(self) -> dict[str, Any]:
        return {"theorem": self.theorem, "status": self.status, "verified": self.verified,
                "script": self.script, "expansions": self.expansions,
                "seconds": round(self.seconds, 3), "error": self.error,
                "result": self.result.to_dict() if self.result is not None else None}


def search_proof(
    theorem: Theorem,
    proposer: Proposer | None = None,
    project: LeanProject | str | None = None,
    *,
    max_depth: int = 6,
    max_expansions: int = 80,
    allow_raw: bool = False,
    env: ProofEnv | None = None,
    verify_timeout: float | None = None,
) -> ProofAttempt:
    """Depth-first proof search with backtracking; batch-verifies the first complete script."""
    start = time.perf_counter()
    proposer = proposer or AutomationProposer()
    try:
        env = env or ProofEnv(theorem, project, allow_raw=allow_raw,
                              max_steps=max_expansions)
    except PyLeanXError as exc:
        return ProofAttempt(theorem.name, "error", error=str(exc),
                            seconds=time.perf_counter() - start)
    seen: set[tuple[str, ...]] = {tuple(env.observe()["goals"])}
    budget = {"n": 0}

    def dfs(depth: int) -> bool:
        if env.session.is_complete:
            return True
        if depth >= max_depth:
            return False
        for cand in proposer(env.observe()):
            if budget["n"] >= max_expansions:
                return False
            budget["n"] += 1
            out = env.act(cand)
            if not out.get("ok"):
                continue
            key = tuple(out.get("goals", ()))
            if out.get("complete") or (key not in seen and dfs_after(key, depth)):
                return True
            env.undo()
        return False

    def dfs_after(key: tuple[str, ...], depth: int) -> bool:
        seen.add(key)
        return dfs(depth + 1)

    found = dfs(0)
    attempt = ProofAttempt(theorem.name, "incomplete", expansions=budget["n"])
    attempt.script = [str(t) for t in env.session.history]
    if found:
        res = env.verify(timeout=verify_timeout)
        attempt.result = res
        attempt.status = "verified" if res is not None and res.verified else "rejected"
    attempt.transcript = env.transcript
    attempt.seconds = time.perf_counter() - start
    return attempt


def try_proofs(
    theorem: Theorem,
    candidates: Sequence[Tactic],
    project: LeanProject | str | None = None,
    *,
    timeout: float | None = None,
) -> ProofAttempt:
    """REPL-free baseline: check whole candidate proofs in ONE batch Lean run.

    Each candidate is attached to a renamed copy of the statement; the first copy Lean
    verifies is then re-verified under the real name (a second run), so the returned
    result is about *this* theorem, with its own audit.
    """
    from ..backend.subprocess_backend import verify_all
    from ..serialize import theorem_from_canonical

    start = time.perf_counter()
    base = theorem.canonical()
    copies = []
    for i, cand in enumerate(candidates):
        data = dict(base, name=f"{theorem.name}__cand{i}", proof=None)
        copy = theorem_from_canonical(data, imports=theorem.imports)
        copy.prove(cand)
        copies.append(copy)
    if not copies:
        return ProofAttempt(theorem.name, "incomplete", error="no candidates")
    results = verify_all(copies, project=project, use_cache=False, timeout=timeout)
    attempt = ProofAttempt(theorem.name, "incomplete", expansions=len(copies))
    for cand, r in zip(candidates, results, strict=True):
        attempt.transcript.append({"event": "candidate", "tactic": str(cand),
                                   "status": str(r.status)})
    winner = next((c for c, r in zip(candidates, results, strict=True) if r.verified), None)
    if winner is not None:
        theorem.prove(winner)
        res = theorem.verify(project, use_cache=False, timeout=timeout)
        attempt.result = res
        attempt.script = str(winner).splitlines()
        attempt.status = "verified" if res.verified else "rejected"
    attempt.seconds = time.perf_counter() - start
    return attempt
