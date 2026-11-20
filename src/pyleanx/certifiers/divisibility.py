"""``a ∣ b`` over ℕ and ℤ: the quotient found in Python.

Each cited divisibility ``hᵢ : aᵢ ∣ cᵢ`` is opened (``obtain ⟨kᵢ, hkᵢ⟩ := hᵢ``, so
``cᵢ = aᵢ * kᵢ``); then a quotient ``q`` is sought with ``b = a * q`` modulo those equations
and the cited equalities, by the same linear algebra as the polynomial certifier (``q`` is
the coefficient of ``a`` in an ideal combination). Lean checks
``exact ⟨q, by linear_combination …⟩``.
"""

from __future__ import annotations

from typing import Any

from ..justify import Goal
from ._algebra import Translator, Unsupported, ideal_combination, sort_of
from .polynomial import equalities

NAME = "divisibility"


def head(e: Any) -> str | None:
    """The Lean name a term applies (``App`` or ``pl.apply`` of a constant), if any."""
    from ..expr import App

    if isinstance(e, App):
        return str(e.func.lean_name)
    fn = getattr(e, "fn", None)
    name = getattr(fn, "name", None) if fn is not None else None
    return name if isinstance(name, str) else None


def _dvd(stmt: Any) -> tuple[Any, Any] | None:
    args: Any = getattr(stmt, "args", ())
    if head(stmt) == "Dvd.dvd" and len(args) == 2:
        return args[0], args[1]
    return None


def certify(goal: Goal) -> str | None:
    import sympy as sp

    from . import facts

    d = _dvd(goal.statement)
    if d is None:
        return None
    sort = sort_of(d[0]) or sort_of(d[1])
    if sort not in ("Nat", "Int"):
        return None
    try:
        tr = Translator(sort)
        a, b = sp.expand(tr.poly(d[0])), sp.expand(tr.poly(d[1]))
    except Unsupported:
        return None
    if a == 0:
        return None
    opened: list[tuple[str, str, Any]] = []      # (hypothesis, k name, c - a k)
    for proof, stmt in facts(goal):
        dd = _dvd(stmt)
        if dd is None or (sort_of(dd[0]) or sort_of(dd[1])) != sort:
            continue
        ai, ci = tr.try_poly(dd[0]), tr.try_poly(dd[1])
        if ai is None or ci is None:
            continue
        k = f"pyleanx_k{len(opened) + 1}"
        ksym = sp.Symbol(f"k{len(opened) + 1}")
        tr.atoms[k] = (ksym, None)
        opened.append((proof, k, sp.expand(ci - ai * ksym)))
    eqs = equalities(goal, tr)
    gens = [a, *(g for _, _, g in opened), *(g for _, g in eqs)]
    syms = [s for s in tr.symbols]
    found = ideal_combination(b, gens, syms, integral=True)
    if found is None:
        return None
    (q, *rest), _ = found
    if sort == "Nat" and any(c < 0 for c in sp.Poly(q, *syms).coeffs()):
        return None
    try:
        q_text = tr.lean(q)
        comb = tr.combination(
            [(c, f"pyleanx_hk{i + 1}") for i, c in enumerate(rest[:len(opened)])]
            + [(c, proof) for c, (proof, _) in zip(rest[len(opened):], eqs, strict=True)])
    except Unsupported:
        return None
    steps = [f"obtain ⟨{k}, pyleanx_hk{i + 1}⟩ := {proof}"
             for i, (proof, k, _) in enumerate(opened)]
    check = f"linear_combination {comb}" if comb else "ring"
    steps.append(f"exact ⟨{q_text}, by {check}⟩")
    return "(" + "; ".join(steps) + ")"


__all__ = ["NAME", "certify"]
