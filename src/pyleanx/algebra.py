"""Basic algebra: identities and inequalities over ordered fields (thin Mathlib wrappers).

    import pyleanx as pl
    from pyleanx import algebra as alg

    a, b = pl.symbols("a b", pl.Real)
    alg.identity("sq_sum", (a + b)**2, a**2 + 2*a*b + b**2).verify()   # by ring
    alg.am_gm_two("amgm", a, b).verify()                              # 2ab ≤ a²+b²

Abstractions and limitations
----------------------------
* ``identity``/``inequality`` use the concrete sorts ``pl.Nat/Int/Rat/Real``. Abstract
  structures are type parameters: ``G = alg.group("G")`` states a theorem for every group.
* ``LEMMAS`` are *references* to Mathlib declarations at :data:`VERIFIED_MATHLIB`. A
  reference asserts nothing; Lean checks every use.
* Helper constructors only build :class:`~pyleanx.Theorem` objects with a suggested
  proof; ``verify()`` is still the only thing that can report ``verified``.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence

from ._domain import CATALOG_VERSION, VERIFIED_MATHLIB, collect_lemmas, lemma
from .binders import free_vars
from .errors import SortError
from .expr import Expr, Var, _as_prop, _compare
from .proofs import Tactic, nlinarith, positivity
from .proofs import ring as _ring_tactic
from .theorem import Theorem
from .types import LeanType, type_param

_ORDER_RING = "Mathlib.Algebra.Order.Ring.Unbundled.Basic"
_COMMUTE = "Mathlib.Algebra.Ring.Commute"
_ABS = "Mathlib.Algebra.Order.Ring.Abs"
_GROUP_ABS = "Mathlib.Algebra.Order.Group.Unbundled.Abs"
_FIELD = "Mathlib.Algebra.Order.Field.Basic"

sq_nonneg = lemma("sq_nonneg", _ORDER_RING)
mul_self_nonneg = lemma("mul_self_nonneg", _ORDER_RING)
two_mul_le_add_sq = lemma("two_mul_le_add_sq", _ORDER_RING)
four_mul_le_sq_add = lemma("four_mul_le_sq_add", _ORDER_RING)
add_sq = lemma("add_sq", _COMMUTE)
sub_sq = lemma("sub_sq", _COMMUTE)
add_pow_two = lemma("add_pow_two", _COMMUTE)
mul_self_sub_mul_self = lemma("mul_self_sub_mul_self", _COMMUTE)
sq_sub_sq = lemma("sq_sub_sq", _COMMUTE)
mul_pow = lemma("mul_pow", "Mathlib.Algebra.Group.Basic")
two_mul = lemma("two_mul", "Mathlib.Algebra.Ring.Defs")
sq_abs = lemma("sq_abs", _ABS)
abs_mul_abs_self = lemma("abs_mul_abs_self", _ABS)
abs_mul = lemma("abs_mul", _ABS)
abs_nonneg = lemma("abs_nonneg", _GROUP_ABS)
abs_sub_comm = lemma("abs_sub_comm", _GROUP_ABS)
abs_add_le = lemma("abs_add_le", _GROUP_ABS)
sub_nonneg = lemma("sub_nonneg", _ABS)
# Not `add_pos`: at the pinned Mathlib it means `b < c → 0 < a → b < c + a`; use
# `positivity` or `linarith` for `0 < a + b`.
mul_pos = lemma("mul_pos", _ORDER_RING)
div_pos = lemma("div_pos", _FIELD)

#: The triangle inequality |a + b| ≤ |a| + |b|, cited by name.
triangle_inequality = lemma("abs_add_le", _GROUP_ABS, label="triangle inequality")

# ---------------------------------------------------------------------------------------
# Abstract structures: "let G be a group"
# ---------------------------------------------------------------------------------------

_GROUP = "Mathlib.Algebra.Group.Defs"
_DIVINV = "Mathlib.Algebra.Group.DivInvMonoid"


def group(name: str = "G") -> LeanType:
    """*Let G be a group* (multiplicative): elements are ``pl.symbols("a b", G)``."""
    return type_param(name, "Group", imports=[_GROUP], label="group")


def abelian_group(name: str = "G") -> LeanType:
    """*Let G be an abelian group* (multiplicative, ``CommGroup``)."""
    return type_param(name, "CommGroup", imports=[_GROUP], label="abelian group")


def ring(name: str = "R") -> LeanType:
    """*Let R be a ring* (not necessarily commutative)."""
    return type_param(name, "Ring", imports=["Mathlib.Algebra.Ring.Defs"], label="ring")


def comm_ring(name: str = "R") -> LeanType:
    """*Let R be a commutative ring*."""
    return type_param(name, "CommRing", imports=["Mathlib.Algebra.Ring.Defs"],
                      label="commutative ring")


def field(name: str = "F") -> LeanType:
    """*Let F be a field*."""
    return type_param(name, "Field", imports=["Mathlib.Algebra.Field.Defs"], label="field")


def inv(x: object) -> Expr:
    """``x⁻¹``, the inverse in a group (``Inv.inv x``)."""
    from .terms import apply, const

    tex = "{0}^{{-1}}" if isinstance(x, Var) else r"\left({0}\right)^{{-1}}"
    return apply(const("Inv.inv", imports=(_GROUP,), latex=tex), x)


mul_assoc = lemma("mul_assoc", _GROUP, label="associativity")
one_mul = lemma("one_mul", _GROUP, label="1·a = a")
mul_one = lemma("mul_one", _GROUP, label="a·1 = a")
mul_inv_cancel = lemma("mul_inv_cancel", _GROUP, label="a·a⁻¹ = 1")
inv_mul_cancel = lemma("inv_mul_cancel", _GROUP, label="a⁻¹·a = 1")
mul_left_cancel = lemma("mul_left_cancel", _GROUP, label="cancellation: ab = ac gives b = c")
mul_inv_rev = lemma("mul_inv_rev", _DIVINV, label="(ab)⁻¹ = b⁻¹a⁻¹")
inv_eq_of_mul_eq_one = lemma("inv_eq_of_mul_eq_one_right", _DIVINV,
                             label="if ab = 1 then a⁻¹ = b")

LEMMAS = collect_lemmas(globals())

__all__ = ["identity", "inequality", "nonneg", "am_gm_two", "group", "abelian_group",
           "ring", "comm_ring", "field", "inv", "LEMMAS", "VERIFIED_MATHLIB",
           "CATALOG_VERSION", *LEMMAS]


def _variables(parts: Sequence[Expr], variables: Iterable[Var] | None) -> list[Var]:
    if variables is not None:
        return list(variables)
    out: list[Var] = []
    for p in parts:
        for v in free_vars(p):
            if all(v.uid != w.uid for w in out):
                out.append(v)
    return out


def identity(name: str, lhs: object, rhs: object, *, variables: Iterable[Var] | None = None,
             proof: Tactic | None = None) -> Theorem:
    """``∀ vars, lhs = rhs``, proved by ``ring`` unless another proof is given."""
    concl = _compare("eq", lhs, rhs)
    return Theorem(name, _variables([concl], variables), None, concl,
                   proof=proof if proof is not None else _ring_tactic())


def inequality(name: str, lhs: object, op: str, rhs: object, *, assumptions: object = None,
               variables: Iterable[Var] | None = None, proof: Tactic | None = None) -> Theorem:
    """``lhs op rhs`` with ``op`` one of ``"<=" "<" ">=" ">"``, written orientation kept.

    The default proof is ``nlinarith`` (with hypotheses); pass a better one if known.
    """
    ops = {"<=": "le", "<": "lt", ">=": "ge", ">": "gt", "≤": "le", "≥": "ge"}
    if op not in ops:
        raise SortError(f"inequality op must be one of {sorted(ops)}, got {op!r}")
    concl = _compare(ops[op], lhs, rhs)
    hyps = assumptions
    parts: list[Expr] = [concl]
    if isinstance(hyps, dict):
        parts += [_as_prop(h, "assumption") for h in hyps.values()]
    elif isinstance(hyps, (list, tuple)):
        parts += [h[1] if isinstance(h, tuple) else h for h in hyps]
    elif isinstance(hyps, Expr):
        parts.append(hyps)
    return Theorem(name, _variables(parts, variables), hyps, concl,
                   proof=proof if proof is not None else nlinarith())


def nonneg(name: str, term: object, *, assumptions: object = None,
           variables: Iterable[Var] | None = None, proof: Tactic | None = None) -> Theorem:
    """``0 ≤ term``, proved by ``positivity`` unless another proof is given."""
    return inequality(name, 0, "<=", term, assumptions=assumptions, variables=variables,
                      proof=proof if proof is not None else positivity())


def am_gm_two(name: str, a: Var, b: Var) -> Theorem:
    """Two-variable AM-GM in polynomial form: ``2 * a * b ≤ a ^ 2 + b ^ 2``."""
    return inequality(name, 2 * a * b, "<=", a**2 + b**2, variables=[a, b],
                      proof=nlinarith(sq_nonneg(a - b)))
