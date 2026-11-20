"""``P = Q`` from cited equalities: ``linear_combination c₁ * h₁ + …``.

``P - Q = Σ cᵢ·(aᵢ - bᵢ)`` for polynomials ``cᵢ`` found by linear algebra over ℚ
(unknown coefficients for every monomial up to a degree bound). Inside Lean, finding the
``cᵢ`` is a search (``linarith`` only for constant coefficients and linear facts,
``nlinarith`` by multiplying hypotheses pairwise, within the time budget); here Lean
checks the identity once with ``ring1``. Over ℕ the certificate uses ``linear_combination``'s
formal subtraction; ℕ subtraction in a statement is an opaque atom.
"""

from __future__ import annotations

from typing import Any

from ..justify import Goal
from ._algebra import RING_SORTS, Translator, Unsupported, ideal_combination, sort_of

NAME = "polynomial"


def equality(stmt: Any) -> tuple[Any, Any] | None:
    from ..expr import Compare

    if isinstance(stmt, Compare) and stmt.op == "eq":
        return stmt.lhs, stmt.rhs
    return None


def ring_sort(*exprs: Any) -> str | None:
    for e in exprs:
        s = sort_of(e)
        if s is not None:
            return s if s in RING_SORTS else None
    return None


def equalities(goal: Goal, tr: Translator) -> list[tuple[str, Any]]:
    """``(proof, a - b)`` for the usable equalities of ``tr``'s sort."""
    from . import facts

    out = []
    for proof, stmt in facts(goal):
        eq = equality(stmt)
        if eq is None or ring_sort(*eq) != tr.sort:
            continue
        a, b = tr.try_poly(eq[0]), tr.try_poly(eq[1])
        if a is not None and b is not None and a != b:
            out.append((proof, a - b))
    return out


def inverse_facts(goal: Goal, tr: Translator
                  ) -> tuple[list[tuple[str, Any]], list[tuple[str, Any, bool]]]:
    """For every inverse atom ``q⁻¹`` of ``tr``: the equation ``q * q⁻¹ = 1`` (proof, poly)
    when ``q ≠ 0`` is known, and ``q⁻¹ > 0`` (proof, poly, strict) when ``q > 0`` is.

    ``q ≠ 0`` comes from a fact ``q ≠ 0``, ``0 < q`` / ``q > 0`` or ``q < 0``, else from
    ``positivity`` (which Lean checks like everything else)."""
    from ..expr import Compare, Lit
    from ..render.lean import render_expr
    from . import facts

    def is_zero(e: Any) -> bool:
        return isinstance(e, Lit) and e.value == 0

    eqs: list[tuple[str, Any]] = []
    pos: list[tuple[str, Any, bool]] = []
    for sym, q in list(tr.inverses.items()):
        text = render_expr(q)
        nonzero = positive = None
        for proof, stmt in facts(goal):
            if not isinstance(stmt, Compare):
                continue
            sides = (render_expr(stmt.lhs), render_expr(stmt.rhs))
            if stmt.op == "ne" and text in sides and (is_zero(stmt.lhs) or is_zero(stmt.rhs)):
                nonzero = nonzero or (proof if is_zero(stmt.rhs) else f"{proof}.symm")
            elif (stmt.op == "lt" and is_zero(stmt.lhs) and sides[1] == text) or \
                    (stmt.op == "gt" and is_zero(stmt.rhs) and sides[0] == text):
                nonzero = nonzero or f"(ne_of_gt {proof})"
                positive = positive or proof
            elif (stmt.op == "lt" and is_zero(stmt.rhs) and sides[0] == text) or \
                    (stmt.op == "gt" and is_zero(stmt.lhs) and sides[1] == text):
                nonzero = nonzero or f"(ne_of_lt {proof})"
        if nonzero is None:
            sort = {"Rat": "ℚ", "Real": "ℝ"}.get(tr.sort, tr.sort)
            nonzero = f"(show ({text} : {sort}) ≠ 0 by positivity)"
        eqs.append((f"(mul_inv_cancel₀ {nonzero})", tr.poly(q) * sym - 1))
        if positive is not None:
            pos.append((f"(inv_pos.mpr {positive})", sym, True))
    return eqs, pos


def certify(goal: Goal) -> str | None:
    eq = equality(goal.statement)
    if eq is None:
        return None
    sort = ring_sort(*eq)
    if sort is None:
        return None
    try:
        tr = Translator(sort)
        target = tr.poly(eq[0]) - tr.poly(eq[1])
    except Unsupported:
        return None
    import sympy as sp

    target = sp.expand(target)
    gens = equalities(goal, tr)
    gens += inverse_facts(goal, tr)[0]
    if target == 0 or not gens:
        return None          # `ring` alone, or nothing usable
    found = ideal_combination(target, [g for _, g in gens], tr.symbols,
                              integral=not tr.field)
    if found is None:
        return None
    cs, _ = found
    try:
        text = tr.combination([(c, proof) for c, (proof, _) in zip(cs, gens, strict=True)])
    except Unsupported:
        return None
    return f"linear_combination {text}" if text else None


__all__ = ["NAME", "certify", "equalities", "equality", "ring_sort"]
