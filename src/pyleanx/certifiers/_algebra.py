"""Shared algebra for certifiers: expressions as polynomials, exact linear algebra, LP.

An expression of a ring sort (ℕ, ℤ, ℚ, ℝ) becomes a sympy polynomial whose variables are
*atoms*: PyLeanX variables, and every subterm that is not ring arithmetic (``Real.sin x``,
``√x``, ``x / y``, truncated ``a - b`` in ℕ, ``n % 3``, …), each named by its Lean text.
Treating such a subterm as an opaque atom is sound: a certificate that holds for every
value of the atom holds for its actual value. So the same certificates apply to
trigonometric, exponential or combinatorial statements whose reasoning is algebraic.

Every search here only *proposes*; Lean checks the result. Everything is exact (ℚ):
floating-point LP solutions are rounded and then re-verified exactly before use.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from fractions import Fraction
from itertools import combinations_with_replacement
from typing import Any

RING_SORTS = ("Nat", "Int", "Rat", "Real")
FIELD_SORTS = ("Rat", "Real")
#: the largest linear system solved for one certificate (unknown coefficients)
MAX_UNKNOWNS = 1500


class Unsupported(Exception):  # noqa: N818 - control flow: "no certificate here"
    pass


def sort_of(e: Any) -> str | None:
    s = getattr(e, "sort", None)
    return getattr(s, "name", None)


def sympy() -> Any:
    try:
        import sympy as sp
    except ImportError as exc:  # pragma: no cover - certifiers need sympy
        raise Unsupported("sympy is not installed (pip install pyleanx[certify])") from exc
    return sp


class Translator:
    """Expressions of one ring sort as sympy polynomials over atoms (and back)."""

    def __init__(self, sort: str) -> None:
        if sort not in RING_SORTS:
            raise Unsupported(sort)
        self.sort = sort
        self.atoms: dict[str, tuple[Any, Any]] = {}   # Lean text -> (symbol, Expr)
        #: symbol of an inverse atom ``q⁻¹`` -> the denominator ``q`` (an Expr)
        self.inverses: dict[Any, Any] = {}

    @property
    def field(self) -> bool:
        return self.sort in FIELD_SORTS

    @property
    def symbols(self) -> list[Any]:
        return [s for s, _ in self.atoms.values()]

    def _atom(self, e: Any) -> Any:
        from ..render.lean import render_expr

        text = render_expr(e)
        if text not in self.atoms:
            self.atoms[text] = (sympy().Symbol(f"a{len(self.atoms)}"), e)
        return self.atoms[text][0]

    def poly(self, e: Any) -> Any:
        """``e`` as a polynomial (raises :class:`Unsupported` for another sort or a
        proposition)."""
        from ..expr import BinOp, Lit, Neg, Var

        sp = sympy()
        s = sort_of(e)
        if isinstance(e, Lit):
            if s is not None and s != self.sort:
                raise Unsupported("literal of another sort")
            return sp.Rational(e.value.numerator, e.value.denominator)
        if s != self.sort:
            raise Unsupported(f"{s} is not {self.sort}")
        if isinstance(e, Var):
            return self._atom(e)
        if isinstance(e, Neg) and self.sort != "Nat":
            return -self.poly(e.arg)
        if isinstance(e, BinOp):
            if e.op == "add":
                return self.poly(e.lhs) + self.poly(e.rhs)
            if e.op == "mul":
                return self.poly(e.lhs) * self.poly(e.rhs)
            if e.op == "sub" and self.sort != "Nat":     # ℕ: truncated, an atom
                return self.poly(e.lhs) - self.poly(e.rhs)
            if e.op == "pow" and isinstance(e.rhs, Lit) and e.rhs.value.denominator == 1 \
                    and 0 <= e.rhs.value <= 16:
                return self.poly(e.lhs) ** int(e.rhs.value)
            if e.op == "div" and self.field and isinstance(e.rhs, Lit) and e.rhs.value != 0:
                return self.poly(e.lhs) / sp.Rational(e.rhs.value.numerator,
                                                      e.rhs.value.denominator)
            if e.op == "div" and self.field:
                # x / q = x * q⁻¹, as Lean's `ring` normalises it; q⁻¹ is an atom tied to q
                # by q * q⁻¹ = 1 when q ≠ 0 is known (see inverse_facts)
                return self.poly(e.lhs) * self.inverse(e.rhs)
        if getattr(e, "is_prop", False):
            raise Unsupported("a proposition")
        return self._atom(e)       # any other term of this sort: opaque

    def inverse(self, q: Any) -> Any:
        """The atom ``q⁻¹``."""
        from ..render.lean import render_expr

        self.poly(q)        # q's own atoms first (and its sort checked)
        text = f"({render_expr(q)})⁻¹"
        if text not in self.atoms:
            sym = sympy().Symbol(f"a{len(self.atoms)}")
            self.atoms[text] = (sym, None)
            self.inverses[sym] = q
        return self.atoms[text][0]

    def try_poly(self, e: Any) -> Any | None:
        try:
            return sympy().expand(self.poly(e))
        except Unsupported:
            return None

    # --- back to Lean ------------------------------------------------------------------
    def _atom_text(self, sym: Any) -> str:
        for text, (s, _) in self.atoms.items():
            if s == sym:
                return text if _simple(text) else f"({text})"
        raise KeyError(sym)

    def number(self, c: Any) -> Fraction:
        f = Fraction(int(c.p), int(c.q))
        if f.denominator != 1 and not self.field:
            raise Unsupported(f"coefficient {f} is not an integer in {self.sort}")
        return f

    def lean(self, poly: Any) -> str:
        """A polynomial as Lean text (sympy's term order: deterministic)."""
        sp = sympy()
        poly = sp.expand(poly)
        if poly == 0:
            return "0"
        syms = sorted(poly.free_symbols, key=lambda s: int(s.name[1:]))
        if not syms:
            return _num(self.number(sp.Rational(poly)))
        parts = []
        for powers, coeff in sp.Poly(poly, *syms).terms():
            c = self.number(coeff)
            factors = [self._atom_text(v) if k == 1 else f"{self._atom_text(v)} ^ {k}"
                       for v, k in zip(syms, powers, strict=True) if k]
            body = " * ".join(factors if abs(c) == 1 and factors else
                              [_num(abs(c)), *factors])
            parts.append(("- " if c < 0 else "+ ") + body)
        text = " ".join(parts)
        return text[2:] if text.startswith("+ ") else "-" + text[2:]

    def expr(self, poly: Any) -> Any:
        """A polynomial as a PyLeanX expression of this sort (for sub-goals)."""
        from .. import types
        from ..expr import Lit

        sp = sympy()
        sort = getattr(types, self.sort)
        poly = sp.expand(poly)
        syms = sorted(poly.free_symbols, key=lambda s: int(s.name[1:]))
        by_sym = {s: e for s, e in self.atoms.values()}
        if not syms:
            return Lit(self.number(sp.Rational(poly)), sort)
        total: Any = None
        for powers, coeff in sp.Poly(poly, *syms).terms():
            c = self.number(coeff)
            factors = [by_sym[v] if k == 1 else by_sym[v] ** k
                       for v, k in zip(syms, powers, strict=True) if k]
            term: Any = None
            for f in factors:
                term = f if term is None else term * f
            if term is None or abs(c) != 1:
                lit = Lit(abs(c), sort)
                term = lit if term is None else lit * term
            if total is None:
                total = -term if c < 0 else term
            else:
                total = total - term if c < 0 else total + term
        return total

    def combination(self, terms: Sequence[tuple[Any, str]]) -> str:
        """``c₁ * p₁ + c₂ * p₂ + …`` for ``linear_combination`` (``pᵢ`` proof terms).

        In ℕ every coefficient is split into monomials with the sign outside, since
        ``linear_combination`` handles subtraction formally there but a coefficient is a
        term of ℕ.
        """
        sp = sympy()
        out: list[str] = []
        for c, proof in terms:
            c = sp.expand(c)
            if c == 0:
                continue
            pieces = [c]
            if self.sort == "Nat" and c.free_symbols:
                syms = sorted(c.free_symbols, key=lambda s: int(s.name[1:]))
                pieces = [coeff * sp.Mul(*[v ** k for v, k in zip(syms, pw, strict=True)])
                          for pw, coeff in sp.Poly(c, *syms).terms()]
            for piece in pieces:
                neg = piece.could_extract_minus_sign()
                mag = -piece if neg else piece
                sign = "- " if neg else "+ "
                if mag == 1:
                    out.append(sign + proof)
                else:
                    text = self.lean(mag)
                    out.append(sign + (text if _simple(text) else f"({text})") + f" * {proof}")
        if not out:
            return ""
        text = " ".join(out)
        return text[2:] if text.startswith("+ ") else "-" + text[2:]


def _simple(text: str) -> bool:
    return all(ch.isalnum() or ch in "_.'" for ch in text) or (
        text.startswith("(") and text.endswith(")") and _balanced(text[1:-1]))


def _balanced(text: str) -> bool:
    depth = 0
    for ch in text:
        depth += ch == "("
        depth -= ch == ")"
        if depth < 0:
            return False
    return depth == 0


def _num(c: Fraction) -> str:
    c = abs(c)
    return str(c.numerator) if c.denominator == 1 else f"{c.numerator} / {c.denominator}"


def degree(p: Any, syms: Sequence[Any]) -> int:
    sp = sympy()
    if not syms or not sp.expand(p).free_symbols:
        return 0
    return int(sp.Poly(p, *syms).total_degree())


def monomials(syms: Sequence[Any], top: int) -> list[Any]:
    """All monomials of total degree ≤ ``top`` (``1`` first), in a fixed order."""
    sp = sympy()
    return [sp.Integer(1)] + [sp.Mul(*c) for k in range(1, top + 1)
                              for c in combinations_with_replacement(syms, k)]


def ideal_combination(target: Any, gens: Sequence[Any], syms: Sequence[Any], *,
                      integral: bool, constant: bool = False,
                      extra_degree: Iterable[int] = (0, 1, 2)) -> tuple[list[Any], Any] | None:
    """Polynomials ``cᵢ`` (and, with ``constant``, a number ``k``) with
    ``target == Σ cᵢ·gensᵢ + k`` identically; ``None`` if none of bounded degree exists.

    Degrees are tried from small to large, so the certificate is as simple as found.
    """
    sp = sympy()
    syms = list(syms)
    tdeg = degree(target, syms)
    gdeg = [degree(g, syms) for g in gens]
    for extra in extra_degree:
        blocks: list[list[Any]] = []
        unknowns: list[Any] = []
        for d in gdeg:
            ms = monomials(syms, max(0, tdeg - d) + extra)
            base = len(unknowns)
            unknowns.extend(sp.Symbol(f"u{base + j}") for j in range(len(ms)))
            blocks.append(ms)
        k = sp.Symbol("k_const") if constant else sp.Integer(0)
        if len(unknowns) > MAX_UNKNOWNS:
            return None
        cs, pos = [], 0
        for ms in blocks:
            cs.append(sum((unknowns[pos + j] * m for j, m in enumerate(ms)), sp.Integer(0)))
            pos += len(ms)
        residual = sp.expand(target - k - sum((c * g for c, g in zip(cs, gens, strict=True)),
                                              sp.Integer(0)))
        eqs = sp.Poly(residual, *syms).coeffs() if syms else [residual]
        allu = [*unknowns, *([k] if constant else [])]
        sol = sp.linsolve(eqs, allu) if allu else (sp.FiniteSet(()) if residual == 0 else
                                                   sp.EmptySet)
        if not sol:
            continue
        (values,) = tuple(sol)
        free = {s: 0 for v in values for s in v.free_symbols}
        values = [sp.nsimplify(v.subs(free)) for v in values]
        result, pos = [], 0
        for ms in blocks:
            result.append(sp.expand(sum((values[pos + j] * m for j, m in enumerate(ms)),
                                        sp.Integer(0))))
            pos += len(ms)
        kval = values[-1] if constant else sp.Integer(0)
        if integral and not all(_integral_poly(c, syms) for c in [*result, kval]):
            continue
        return result, kval
    return None


def _integral_poly(p: Any, syms: Sequence[Any]) -> bool:
    sp = sympy()
    p = sp.expand(p)
    if not p.free_symbols:
        return bool(sp.Rational(p).q == 1)
    return all(c.is_integer for c in sp.Poly(p, *syms).coeffs())


def nonneg_combination(target: Any, atoms: Sequence[tuple[Any, bool]], gens: Sequence[Any],
                       syms: Sequence[Any], *, strict: bool, integral: bool
                       ) -> tuple[list[Any], list[Any], Any] | None:
    """``target == Σ λᵢ·atomᵢ + Σ μⱼ·gensⱼ + c`` with numbers ``λᵢ ≥ 0``, ``c ≥ 0`` and
    polynomials ``μⱼ``; with ``strict``, ``c > 0`` or some ``λᵢ > 0`` on a strict atom.

    ``atoms`` are ``(polynomial known ≥ 0 (or > 0 when strict), strict)``. Returns
    ``(λ, μ, c)`` exactly, or ``None``. Solved as a linear program (HiGHS when scipy is
    installed, rounded and re-verified exactly; otherwise sympy's exact simplex).
    """
    sp = sympy()
    syms = list(syms)
    top = max([degree(target, syms), *(degree(a, syms) for a, _ in atoms)], default=0)
    mu_blocks = [monomials(syms, max(0, top - degree(g, syms))) for g in gens]
    n_l, n_mu = len(atoms), sum(len(b) for b in mu_blocks)
    if n_l + n_mu + 1 > MAX_UNKNOWNS:
        return None
    columns: list[Any] = [sp.expand(a) for a, _ in atoms]
    for g, ms in zip(gens, mu_blocks, strict=True):
        columns.extend(sp.expand(m * g) for m in ms)
    columns.append(sp.Integer(1))
    rows: dict[Any, dict[int, Any]] = {}

    def coeffs(p: Any) -> dict[Any, Any]:
        if not syms:
            return {(): sp.Rational(p)} if p != 0 else {}
        return {m: c for m, c in sp.Poly(p, *syms).terms() if c != 0}

    for j, col in enumerate(columns):
        for mono, c in coeffs(col).items():
            rows.setdefault(mono, {})[j] = c
    rhs = coeffs(sp.expand(target))
    for mono in rhs:
        rows.setdefault(mono, {})
    monos = sorted(rows, key=str)
    strict_cols = [i for i, (_, st) in enumerate(atoms) if st] + [len(columns) - 1]

    def exact_check(lam: list[Fraction]) -> tuple[list[Any], list[Any], Any] | None:
        lam_s = [sp.Rational(x.numerator, x.denominator) for x in lam]
        residual = sp.expand(target - sum((lv * a for lv, (a, _) in zip(lam_s, atoms,
                                                                        strict=True)),
                                          sp.Integer(0)))
        found = ideal_combination(residual, list(gens), syms, integral=integral,
                                  constant=True, extra_degree=(0, 1))
        if found is None:
            return None
        mus, c = found
        if c < 0 or (strict and c == 0 and not any(lam[i] > 0 for i in strict_cols[:-1])):
            return None
        if sp.expand(target) == 0:
            # a contradiction (0 < 0) is scale-free: the smallest whole coefficients
            from math import lcm

            scale = sp.Rational(lcm(*(x.denominator for x in lam if x)), 1) if any(lam) else 1
            lam_s = [lv * scale for lv in lam_s]
            mus = [sp.expand(m * scale) for m in mus]
            c = c * scale
            lam = [Fraction(int(v.p), int(v.q)) for v in map(sp.Rational, lam_s)]
        if integral and not all(x.denominator == 1 for x in lam):
            return None
        return lam_s, mus, c

    try:
        import numpy as np
        from scipy.optimize import linprog as sp_linprog
    except ImportError:
        np = None
    if np is not None:
        n = len(columns)
        a_eq = np.zeros((len(monos), n))
        b_eq = np.zeros(len(monos))
        for r, mono in enumerate(monos):
            for j, c in rows[mono].items():
                a_eq[r, j] = float(c)
            b_eq[r] = float(rhs.get(mono, 0))
        bounds = [(0, 1e4)] * n_l + [(-1e4, 1e4)] * n_mu + [(0, 1e4)]
        cost = np.zeros(n)
        cost[:n_l] = 1.0
        a_ub = b_ub = None
        if strict:     # c + Σ strict λ ≥ 1e-3
            a_ub = np.zeros((1, n))
            for j in strict_cols:
                a_ub[0, j] = -1.0
            b_ub = np.array([-1e-3])
        res = sp_linprog(cost, A_ub=a_ub, b_ub=b_ub, A_eq=a_eq, b_eq=b_eq, bounds=bounds,
                         method="highs")
        if res.status != 0:
            return None
        for den in (1, 2, 4, 6, 12, 24, 100, 10_000):
            lam = [Fraction(0) if x < 1e-9 else Fraction(x).limit_denominator(den)
                   for x in res.x[:n_l]]
            found = exact_check(lam)
            if found is not None:
                return found
        support = [i for i, x in enumerate(res.x[:n_l]) if x > 1e-9]
    else:
        support = list(range(n_l))
    # exact LP on the support (sympy's rational simplex)
    cols = support + list(range(n_l, len(columns)))
    a_rows = [[rows[m].get(j, 0) for j in cols] for m in monos]
    b = [rhs.get(m, 0) for m in monos]
    cost_e = [1 if j < n_l else 0 for j in cols]
    free = [n_l <= j < len(columns) - 1 for j in cols]
    ub = [[-1 if j in strict_cols else 0 for j in cols]] if strict else []
    xs = _exact_lp(cost_e, ub, [-sp.Rational(1, 1000)] if strict else [], a_rows, b, free)
    if xs is None:
        return None
    lam_full = [Fraction(0)] * n_l
    for k, j in enumerate(cols):
        if j < n_l:
            v = sp.Rational(xs[k])
            lam_full[j] = Fraction(int(v.p), int(v.q))
    return exact_check(lam_full)


def _exact_lp(cost: list[Any], a_ub: list[list[Any]], b_ub: list[Any], a_eq: list[list[Any]],
              b_eq: list[Any], free: list[bool]) -> list[Any] | None:
    """Minimise ``cost·x`` subject to ``a_ub·x ≤ b_ub``, ``a_eq·x = b_eq``, ``x ≥ 0`` except
    where ``free``, in exact rationals (sympy). Equalities become two inequalities and a
    free variable the difference of two nonnegative ones: sympy's ``linprog`` is given
    only ``A·x ≤ b`` with ``x ≥ 0`` (the form it handles reliably). ``None``: infeasible."""
    sp = sympy()
    from sympy.solvers.simplex import linprog as exact_linprog

    def expand(row: list[Any]) -> list[Any]:
        out: list[Any] = []
        for v, f in zip(row, free, strict=True):
            out += [v, -v] if f else [v]
        return out

    rows = [expand(r) for r in a_ub] + [expand(r) for r in a_eq] + \
        [[-v for v in expand(r)] for r in a_eq]
    rhs = [*b_ub, *b_eq, *(-v for v in b_eq)]
    if not rows:
        return [0] * len(cost)
    try:
        _, xs = exact_linprog(sp.Matrix([expand(cost)]), sp.Matrix(rows), sp.Matrix(rhs))
    except Exception:  # noqa: BLE001 - infeasible or unbounded: no certificate
        return None
    # sympy's simplex has returned infeasible points on degenerate systems: check exactly
    if any(x < 0 for x in xs) or any(
            sum((v * x for v, x in zip(row, xs, strict=True)), sp.Integer(0)) > r
            for row, r in zip(rows, rhs, strict=True)):
        return None
    out, k = [], 0
    for f in free:
        out.append(xs[k] - xs[k + 1] if f else xs[k])
        k += 2 if f else 1
    return out


__all__ = ["FIELD_SORTS", "MAX_UNKNOWNS", "RING_SORTS", "Translator", "Unsupported",
           "degree", "ideal_combination", "monomials", "nonneg_combination", "sort_of"]
