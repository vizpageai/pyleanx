"""Certificates for polynomial equalities: ``linear_combination``, found in Python.

A step ``P = Q`` citing equalities ``h₁ : a₁ = b₁, …`` follows by ring arithmetic when
``P - Q = c₁·(a₁ - b₁) + … + cₖ·(aₖ - bₖ)`` for polynomials ``cᵢ``. Inside Lean, finding
the ``cᵢ`` is a search (``linarith`` only for constants and linear facts, ``nlinarith`` by
multiplying hypotheses pairwise, within the time budget). Here the ``cᵢ`` are found by
linear algebra over ℚ (unknown coefficients for every monomial up to a degree bound), and
Lean receives ``linear_combination c₁ * h₁ + …``, which it checks with a single ``ring1``.

Opt-in (importing this module registers the certifier; it changes the generated Lean):

    import pyleanx.ring_certificates      # needs sympy

Sorts: Int, Rat, Real (commutative rings; ℕ has no subtraction). Over Int only integer
coefficients are used. Nothing here is trusted: a wrong certificate fails Lean's check and
the step's ordinary alternatives still run.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations_with_replacement
from typing import Any

from .justify import Goal, register_certifier

NAME = "ring.linear_combination"
IMPORTS = ("Mathlib.Tactic.LinearCombination",)
#: largest number of unknown coefficients tried (the linear system's size)
MAX_UNKNOWNS = 600
_RINGS = ("Int", "Rat", "Real")


class _Unsupported(Exception):
    pass


def _poly(e: Any, syms: dict[str, Any], sort: list[str]) -> Any:
    """``e`` as a sympy polynomial expression over the variables in ``syms``."""
    import sympy

    from .expr import BinOp, Lit, Neg, Var
    from .render.lean import render_expr

    if isinstance(e, Var):
        if e.sort is None or e.sort.name not in _RINGS:
            raise _Unsupported(e)
        if sort and sort[0] != e.sort.name:
            raise _Unsupported("mixed sorts")
        sort[:] = [e.sort.name]
        text = render_expr(e)
        if text not in syms:
            syms[text] = sympy.Symbol(f"v{len(syms)}")
        return syms[text]
    if isinstance(e, Lit):
        return sympy.Rational(e.value.numerator, e.value.denominator)
    if isinstance(e, Neg):
        return -_poly(e.arg, syms, sort)
    if isinstance(e, BinOp):
        if e.op in ("add", "sub", "mul"):
            a, b = _poly(e.lhs, syms, sort), _poly(e.rhs, syms, sort)
            return a + b if e.op == "add" else a - b if e.op == "sub" else a * b
        if e.op == "pow" and isinstance(e.rhs, Lit) and e.rhs.value.denominator == 1 \
                and 0 <= e.rhs.value <= 12:
            return _poly(e.lhs, syms, sort) ** int(e.rhs.value)
    raise _Unsupported(type(e).__name__)


def _equality(stmt: Any) -> tuple[Any, Any] | None:
    from .expr import Compare

    if isinstance(stmt, Compare) and stmt.op == "eq":
        return stmt.lhs, stmt.rhs
    return None


def find_coefficients(target: Any, gens: list[Any], gens_vars: list[Any],
                      integral: bool) -> list[Any] | None:
    """Polynomials ``c`` with ``target == Σ cᵢ·gensᵢ`` (identically), or None.

    Degrees are tried from small to large, so the certificate is as simple as found.
    """
    import sympy

    vs = list(gens_vars)
    tdeg = sympy.Poly(target, *vs).total_degree() if vs else 0
    gdeg = [sympy.Poly(g, *vs).total_degree() if vs else 0 for g in gens]
    for extra in (0, 1, 2):
        monos_of: list[list[Any]] = []
        unknowns: list[Any] = []
        for d in gdeg:
            top = max(0, tdeg - d) + extra
            monos = [sympy.Integer(1)] + [sympy.Mul(*c) for k in range(1, top + 1)
                                          for c in combinations_with_replacement(vs, k)]
            monos_of.append(monos)
            base = len(unknowns)
            unknowns.extend(sympy.Symbol(f"u{base + j}") for j in range(len(monos)))
        if len(unknowns) > MAX_UNKNOWNS:
            return None
        k = 0
        cs = []
        for monos in monos_of:
            cs.append(sum(unknowns[k + j] * m for j, m in enumerate(monos)))
            k += len(monos)
        residual = sympy.expand(target - sum(c * g for c, g in zip(cs, gens, strict=True)))
        eqs = sympy.Poly(residual, *vs).coeffs() if vs else [residual]
        sol = sympy.linsolve(eqs, unknowns)
        if not sol:
            continue
        (values,) = tuple(sol)
        free = {s: 0 for v in values for s in v.free_symbols}
        values = [sympy.nsimplify(v.subs(free)) for v in values]
        result = []
        k = 0
        for monos in monos_of:
            result.append(sympy.expand(sum(values[k + j] * m for j, m in enumerate(monos))))
            k += len(monos)
        if integral and any(not c.is_integer for r in result
                            for c in sympy.Poly(r, *vs).coeffs()):
            continue
        return result
    return None


def _lean(poly: Any, names: dict[Any, str]) -> str:
    """A polynomial (sympy) as Lean text over the variables' Lean names."""
    import sympy

    vs = sorted(names, key=lambda s: int(s.name[1:]))
    p = sympy.Poly(poly, *vs)
    parts = []
    for powers, coeff in p.terms():           # sympy's order: deterministic
        c = Fraction(int(coeff.p), int(coeff.q))
        factors = [names[v] if k == 1 else f"{names[v]} ^ {k}"
                   for v, k in zip(vs, powers, strict=True) if k]
        num = str(abs(c.numerator)) if c.denominator == 1 else \
            f"{abs(c.numerator)} / {c.denominator}"
        if factors:
            body = " * ".join(factors if abs(c) == 1 else [num, *factors])
        else:
            body = num
        parts.append(("- " if c < 0 else "+ ") + body)
    text = " ".join(parts) if parts else "+ 0"
    return text[2:] if text.startswith("+ ") else "-" + text[2:]


def certify(goal: Goal) -> str | None:
    """``linear_combination …`` proving ``goal`` from the cited equalities, or None."""
    try:
        import sympy
    except ImportError:  # pragma: no cover - the certifier needs sympy
        return None
    eq = _equality(goal.statement)
    if eq is None:
        return None
    given: list[tuple[str, tuple[Any, Any]]] = []
    for name, stmt in goal.given:
        e = _equality(stmt)
        if e is not None:
            given.append((name, e))
    if not given:
        return None
    syms: dict[str, Any] = {}
    sort: list[str] = []
    try:
        target = sympy.expand(_poly(eq[0], syms, sort) - _poly(eq[1], syms, sort))
        gens, names = [], []
        for name, (a, b) in given:
            try:
                s2 = list(sort)
                g = sympy.expand(_poly(a, syms, s2) - _poly(b, syms, s2))
            except _Unsupported:
                continue
            if g != 0 and s2 == sort:
                gens.append(g)
                names.append(name)
    except _Unsupported:
        return None
    if target == 0 or not gens:
        return None   # `ring` alone, or nothing usable cited
    var_of = {v: k for k, v in syms.items()}
    cs = find_coefficients(target, gens, list(var_of), integral=sort == ["Int"])
    if cs is None:
        return None
    terms = []
    for c, name in zip(cs, names, strict=True):
        if c == 0:
            continue
        if c == 1:
            terms.append(f"+ {name}")
        elif c == -1:
            terms.append(f"- {name}")
        else:
            terms.append(f"+ ({_lean(c, var_of)}) * {name}")
    text = " ".join(terms)
    text = text[2:] if text.startswith("+ ") else "-" + text[2:]
    return f"linear_combination {text}"


register_certifier(NAME, certify, priority=10, imports=IMPORTS)

__all__ = ["IMPORTS", "NAME", "certify", "find_coefficients"]
