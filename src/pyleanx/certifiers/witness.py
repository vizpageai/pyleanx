"""``∃ x, P x``: find a witness in Python, then prove ``P w`` with the other certifiers.

Witnesses are proposed in this order: solutions of the equations in ``P`` (solved for the
bound variables with sympy, possibly in terms of other variables: ``∃ y, x + y = 3`` gives
``y = 3 - x``), then simple terms (small numbers, the other variables ± 1, …). A proposal
is kept when every conjunct of the instance either is closed and numerically true, or gets
a certificate from the other certifiers (:meth:`pyleanx.justify.Goal.certify`). Lean then
checks ``exact ⟨w, (by …), …⟩``: the witness is a proposal like any other.
"""

from __future__ import annotations

from collections.abc import Iterator
from fractions import Fraction
from itertools import product
from typing import Any

from ..justify import Goal
from ._algebra import RING_SORTS, Translator, Unsupported, sort_of

NAME = "witness"
#: witnesses tried per statement
MAX_TRIES = 24
#: closing tactics tried after the certificates for a conjunct of the instance
CLOSERS = ("norm_num", "ring1", "linarith", "positivity", "ring_nf", "simp")


def _conjuncts(e: Any) -> list[Any]:
    from ..expr import Logic

    if isinstance(e, Logic) and e.op == "and":
        return [*_conjuncts(e.lhs), *_conjuncts(e.rhs)]
    return [e]


def _closed_truth(e: Any) -> bool | None:
    """The truth of a statement without free variables (None if it has some, or cannot
    be evaluated)."""
    from ..numeric import evaluate
    from ..ops import free_vars

    if free_vars(e):
        return None
    try:
        return bool(evaluate(e, {}))
    except Exception:  # noqa: BLE001 - not evaluable: unknown
        return None


def _solutions(body: Any, variables: tuple[Any, ...], tr: Translator) -> Iterator[list[Any]]:
    """Witness tuples solving the equations of ``body`` (as polynomials of ``tr``)."""
    import sympy as sp

    from .polynomial import equality

    eqs = []
    for c in _conjuncts(body):
        eq = equality(c)
        if eq is not None:
            a, b = tr.try_poly(eq[0]), tr.try_poly(eq[1])
            if a is not None and b is not None:
                eqs.append(sp.expand(a - b))
    syms = [tr.poly(v) for v in variables]
    if not eqs:
        return
    try:
        sols = sp.solve(eqs, syms, dict=True)
    except Exception:  # noqa: BLE001 - sympy could not solve: no proposal
        return
    for sol in sols[:MAX_TRIES]:
        values = []
        for s in syms:
            v = sp.expand(sol.get(s, sp.Integer(0)))
            if v.has(sp.I) or not v.is_polynomial(*tr.symbols) or \
                    any(not a.is_Rational for a in v.atoms(sp.Number)):
                break
            values.append(v)
        else:
            if all(not (v.free_symbols & set(syms)) for v in values):
                yield values


def _simple(variables: tuple[Any, ...], tr: Translator, others: list[Any]) -> Iterator[list[Any]]:
    import sympy as sp

    numbers = [Fraction(v) for v in (0, 1, 2, -1, Fraction(1, 2), 3, -2, 10)]
    if tr.sort == "Nat":
        numbers = [v for v in numbers if v >= 0 and v.denominator == 1]
    elif not tr.field:
        numbers = [v for v in numbers if v.denominator == 1]
    pool: list[Any] = [sp.Rational(v.numerator, v.denominator) for v in numbers]
    for o in others[:3]:
        pool += [o, o + 1, 2 * o] + ([o - 1] if tr.sort != "Nat" else [])
    if len(variables) > 2:
        return
    yield from (list(t) for t in product(pool, repeat=len(variables)))


def _identity(part: Any, tr: Translator) -> bool:
    """Is ``part`` an equality that holds identically (``ring1`` proves it)?"""
    from .polynomial import equality

    eq = equality(part)
    if eq is None:
        return False
    a, b = tr.try_poly(eq[0]), tr.try_poly(eq[1])
    return a is not None and b is not None and a == b


def _proof_of(goal: Goal, part: Any, tr: Translator) -> str | None:
    certs = goal.certify(part)
    truth = _closed_truth(part)
    if not certs and truth is not True and not _identity(part, tr):
        return None
    if truth is False:
        return None
    alts = [*certs, *CLOSERS]
    return "(by first | " + " | ".join(alts) + ")"


def certify(goal: Goal) -> str | None:
    from ..expr import Quant
    from ..ops import substitute
    from ..render.lean import render_expr

    stmt = goal.statement
    if not (isinstance(stmt, Quant) and stmt.kind == "exists"):
        return None
    variables = tuple(stmt.vars)
    sorts = {sort_of(v) for v in variables}
    if len(sorts) != 1 or not sorts <= set(RING_SORTS):
        return None
    try:
        tr = Translator(sorts.pop())  # type: ignore[arg-type]
        for v in variables:
            tr.poly(v)
        for c in _conjuncts(stmt.body):
            for side in getattr(c, "children", lambda: ())():
                tr.try_poly(side)
    except Unsupported:
        return None
    bound = {id(tr.poly(v)) for v in variables}
    others = [s for s in tr.symbols if id(s) not in bound]
    tried = 0
    seen: set[str] = set()
    for values in [*_solutions(stmt.body, variables, tr), *_simple(variables, tr, others)]:
        if tried >= MAX_TRIES:
            break
        try:
            exprs = [tr.expr(v) for v in values]
        except (Unsupported, KeyError):
            continue
        key = repr([render_expr(e) for e in exprs])
        if key in seen:
            continue
        seen.add(key)
        tried += 1
        inst = substitute(stmt.body, *zip(variables, exprs, strict=True))
        proofs = [_proof_of(goal, part, tr) for part in _conjuncts(inst)]
        if any(p is None for p in proofs):
            continue
        return "exact ⟨" + ", ".join([*(render_expr(e) for e in exprs),
                                       *(p for p in proofs if p)]) + "⟩"
    return None


__all__ = ["CLOSERS", "MAX_TRIES", "NAME", "certify"]
