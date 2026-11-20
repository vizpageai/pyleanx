"""``P ≤ Q`` / ``P < Q`` (and ``≥``, ``>``): a Positivstellensatz certificate by linear programming.

The gap ``Q - P`` is written as

    Σ λᵢ·aᵢ  +  Σ μⱼ·(cited equality)ⱼ  +  c,        λᵢ ≥ 0, c ≥ 0 numbers, μⱼ polynomials,

where the ``aᵢ`` are known to be nonnegative: the cited inequalities, their pairwise
products, a cited inequality times a square, squares ``m²`` and ``(m ± m')²`` of monomials
(a *diagonally dominant* sum of squares, which a linear program can search), and terms
known to be nonnegative (``√x``, ``|x|``, ``exp x``, ``↑n``). For ``<`` some strict part
must be used. Lean receives ``linear_combination λ₁ * h₁ + λ₂ * mul_nonneg … + …`` and
checks it with one ring normalisation, instead of ``nlinarith``'s search over products of
hypotheses within the time budget.

Terms that are not ring arithmetic are atoms (see ``_algebra``), so the search applies to
inequalities between, e.g., trigonometric or exponential terms when the step is algebraic
in them.
"""

from __future__ import annotations

from math import ceil
from typing import Any

from ..justify import Goal
from ._algebra import Translator, Unsupported, degree, monomials, nonneg_combination
from .polynomial import equalities, ring_sort

NAME = "inequality"
#: heads of terms Lean's ``positivity`` proves nonnegative (``True``: positive)
NONNEG_HEADS: dict[str, bool] = {"Real.sqrt": False, "abs": False, "Real.exp": True,
                                 "Real.cosh": True, "norm": False, "Nat.factorial": True}
#: the largest number of candidate nonnegative terms offered to the linear program
MAX_ATOMS = 900
_ORDERED = ("Int", "Rat", "Real")
_LEAN_SORT = {"Int": "ℤ", "Rat": "ℚ", "Real": "ℝ"}


def register_nonneg(lean_head: str, *, positive: bool = False) -> None:
    """Declare that ``positivity`` proves terms ``lean_head …`` nonnegative (or positive);
    a domain pack can add its own (e.g. a norm or a measure)."""
    NONNEG_HEADS[lean_head] = positive


def _relation(stmt: Any) -> tuple[str, Any, Any] | None:
    """``("le" | "lt", smaller, larger)`` for an inequality."""
    from ..expr import Compare

    if not isinstance(stmt, Compare):
        return None
    if stmt.op in ("le", "lt"):
        return stmt.op, stmt.lhs, stmt.rhs
    if stmt.op in ("ge", "gt"):
        return ("le" if stmt.op == "ge" else "lt"), stmt.rhs, stmt.lhs
    return None


def _hypotheses(goal: Goal, tr: Translator) -> list[tuple[str, Any, bool]]:
    """``(proof of smaller ≤/< larger, larger - smaller, strict)`` for usable inequalities."""
    from ..expr import Compare
    from . import facts

    out = []
    for proof, stmt in facts(goal):
        rel = _relation(stmt)
        if rel is None or ring_sort(rel[1], rel[2]) != tr.sort:
            continue
        a, b = tr.try_poly(rel[1]), tr.try_poly(rel[2])
        if a is None or b is None:
            continue
        if isinstance(stmt, Compare) and stmt.op == "ge":
            proof = f"(ge_iff_le.mp {proof})"
        elif isinstance(stmt, Compare) and stmt.op == "gt":
            proof = f"(gt_iff_lt.mp {proof})"
        out.append((proof, b - a, rel[0] == "lt"))
    return out


def _nonneg_atoms(tr: Translator) -> list[tuple[str, Any, bool]]:
    from ..expr import App, Cast

    out = []
    for text, (sym, e) in tr.atoms.items():
        positive = None
        if isinstance(e, App) and e.func.lean_name in NONNEG_HEADS:
            positive = NONNEG_HEADS[e.func.lean_name]
        elif isinstance(e, Cast) and getattr(e.arg.sort, "name", None) == "Nat":
            positive = False
        if positive is None:
            continue
        rel = "<" if positive else "≤"
        out.append((f"(show (0 : {_LEAN_SORT[tr.sort]}) {rel} {text} by positivity)", sym,
                    positive))
    return out


def candidates(target: Any, hyps: list[tuple[str, Any, bool]], tr: Translator,
               eq_polys: list[Any]) -> list[tuple[str, Any, bool]]:
    """The nonnegative terms offered to the linear program: ``(proof, poly, strict)``."""
    import sympy as sp

    syms = tr.symbols
    top = max([degree(target, syms), *(degree(g, syms) for _, g, _ in hyps),
               *(degree(g, syms) for g in eq_polys)], default=0)
    half = max(1, ceil(top / 2))
    out: list[tuple[str, Any, bool]] = list(hyps) + _nonneg_atoms(tr)

    def le(proof: str, strict: bool) -> str:
        return f"(le_of_lt {proof})" if strict else proof

    # products of two hypotheses
    for i, (p1, g1, s1) in enumerate(hyps):
        for p2, g2, s2 in hyps[i:]:
            if degree(g1 * g2, syms) > top:
                continue
            if s1 and s2:
                out.append((f"(mul_pos (sub_pos.mpr {p1}) (sub_pos.mpr {p2}))", g1 * g2, True))
            else:
                out.append((f"(mul_nonneg (sub_nonneg.mpr {le(p1, s1)}) "
                            f"(sub_nonneg.mpr {le(p2, s2)}))", g1 * g2, False))
    # squares: m², (m ± m')² for monomials m, m' (a diagonally dominant sum of squares)
    basis = [m for m in monomials(syms, half) if m != 1] + [sp.Integer(1)]
    squares: list[Any] = [m for m in basis if m != 1]
    for i, m in enumerate(basis):
        for m2 in basis[i + 1:]:
            squares.extend((m - m2, m + m2))
    squares = [q for q in squares if 2 * degree(q, syms) <= top or top <= 1]
    for q in squares:
        out.append((f"(sq_nonneg ({tr.lean(q)}))", sp.expand(q ** 2), False))
    # a hypothesis times a square
    for p, g, s in hyps:
        dg = degree(g, syms)
        for q in squares:
            if dg + 2 * degree(q, syms) <= top:
                out.append((f"(mul_nonneg (sub_nonneg.mpr {le(p, s)}) "
                            f"(sq_nonneg ({tr.lean(q)})))", sp.expand(g * q ** 2), False))
    # no duplicates (by polynomial), at most MAX_ATOMS
    seen: set[Any] = set()
    unique = []
    for proof, poly, strict in out:
        key = (sp.expand(poly), strict)
        if key[0] == 0 or key in seen:
            continue
        seen.add(key)
        unique.append((proof, key[0], strict))
    return unique[:MAX_ATOMS]


def certify(goal: Goal) -> str | None:
    rel = _relation(goal.statement)
    if rel is None:
        return None
    kind, small, large = rel
    sort = ring_sort(small, large)
    if sort not in _ORDERED:
        return None
    import sympy as sp

    try:
        tr = Translator(sort)
        target = sp.expand(tr.poly(large) - tr.poly(small))
    except Unsupported:
        return None
    hyps = _hypotheses(goal, tr)
    eqs = equalities(goal, tr)
    atoms = candidates(target, hyps, tr, [g for _, g in eqs])
    if not atoms and not eqs:
        return None
    try:
        found = nonneg_combination(target, [(p, s) for _, p, s in atoms],
                                   [g for _, g in eqs], tr.symbols,
                                   strict=kind == "lt", integral=not tr.field)
    except Unsupported:
        return None
    if found is None:
        return None
    lam, mus, _ = found
    try:
        terms = [(lv, proof) for lv, (proof, _, _) in zip(lam, atoms, strict=True) if lv != 0]
        terms += [(mu, proof) for mu, (proof, _) in zip(mus, eqs, strict=True)]
        text = tr.combination(terms)
    except Unsupported:
        return None
    tactic = f"linear_combination {text}" if text else "linear_combination"
    if goal.statement.op in ("ge", "gt"):
        from ..expr import Compare
        from ..render.lean import render_expr

        flipped = Compare("le" if kind == "le" else "lt", small, large)
        tactic = f"(show {render_expr(flipped)}; {tactic})"
    return tactic


__all__ = ["MAX_ATOMS", "NAME", "NONNEG_HEADS", "candidates", "certify", "register_nonneg"]
