"""Certifiers: proofs searched for in Python, checked by Lean.

Importing this package registers every certifier below with the justification engine
(:func:`pyleanx.justify.register_certifier`). Each one reads the mathematics of a step (its
statement and the statements in scope) and proposes a certificate, a tactic that Lean only
has to check; the step's ordinary alternatives still follow. Nothing here is trusted.

* ``polynomial``: ``P = Q`` from cited equalities (ℕ, ℤ, ℚ, ℝ), as
  ``linear_combination c₁ * h₁ + …``;
* ``inequality``: ``P ≤ Q``, ``P < Q`` (≥, >) from cited (in)equalities, by a
  Positivstellensatz search (products of hypotheses, sums of squares) as a linear
  program, as ``linear_combination λ₁ * h₁ + λ₂ * sq_nonneg (…) + …``;
* ``witness``: ``∃ x, P x``, a witness solved for, then the instance proved by the other
  certifiers, as ``exact ⟨w, …⟩``;
* ``divisibility``: ``a ∣ b`` (ℕ, ℤ) from cited divisibilities and equalities, as
  ``exact ⟨q, by linear_combination …⟩``.

Terms that are not ring arithmetic (``Real.sin x``, ``√x``, ``x / y``, ℕ subtraction, …)
are treated as opaque atoms, so these certifiers apply in any Mathlib domain whose step is
algebraic in such terms. Needs sympy and scipy (``pip install pyleanx[certify]``): linear
programs are solved by HiGHS and re-verified exactly (without scipy, sympy's exact simplex
is tried; it finds fewer certificates). Opt-in because it changes the generated Lean:

    import pyleanx.certifiers            # every certifier
    pyleanx.certifiers.disable()         # unregister them again
"""

from __future__ import annotations

from collections.abc import Iterator
from typing import Any

from ..justify import Goal, register_certifier, unregister_certifier

#: Lean modules the certificates use
IMPORTS = ("Mathlib.Tactic.LinearCombination", "Mathlib.Tactic.Positivity",
           "Mathlib.Algebra.Order.Ring.Unbundled.Basic")
NAMES: list[str] = []


def facts(goal: Goal) -> Iterator[tuple[str, Any]]:
    """``(Lean proof term, statement)`` for every usable statement of ``goal``, with
    conjunctions split into their parts (``h.1``, ``h.2.1``, …)."""
    from ..expr import Logic

    def split(proof: str, stmt: Any) -> Iterator[tuple[str, Any]]:
        if isinstance(stmt, Logic) and stmt.op == "and":
            yield from split(f"{proof}.1", stmt.lhs)
            yield from split(f"{proof}.2", stmt.rhs)
        else:
            yield proof, stmt

    for name, stmt in goal.usable:
        yield from split(name, stmt)


def _register(name: str, certify: Any, priority: float) -> None:
    register_certifier(name, certify, priority=priority, imports=IMPORTS)
    if name not in NAMES:
        NAMES.append(name)


def enable() -> None:
    """Register every certifier (done on import)."""
    from . import divisibility, inequality, polynomial, witness

    _register(polynomial.NAME, polynomial.certify, 10)
    _register(inequality.NAME, inequality.certify, 20)
    _register(divisibility.NAME, divisibility.certify, 30)
    _register(witness.NAME, witness.certify, 40)


def disable() -> None:
    """Unregister every certifier of this package."""
    for name in NAMES:
        unregister_certifier(name)


enable()

__all__ = ["IMPORTS", "disable", "enable", "facts"]
