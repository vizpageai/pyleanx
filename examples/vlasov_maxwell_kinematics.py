"""Case study: the kinematic layer of OpenAI's relativistic Vlasov-Maxwell formalization.

Source: https://github.com/openai/math/tree/main/lean/OAI/Analysis/VlasovMaxwell
(Apache-2.0; same Lean v4.34.1 and Mathlib d13f23b723b8 pins as PyLeanX).

That development defines vectors as `EuclideanSpace ℝ (Fin 3)` with

    dot a b   = ∑ i, a i * b i
    cross a b = (a₁b₂ - a₂b₁, a₂b₀ - a₀b₂, a₀b₁ - a₁b₀)
    q v       = √(1 + ‖v‖²)            (relativistic energy / mass)
    velocity v = v / q v

PyLeanX has no vector sort yet, so here a vector is three real symbols and `dot`, `cross`
and `q` are ordinary Python functions that *build* expressions. Each theorem below is the
coordinate form of an OAI lemma (named in its docstring). They are checked by Lean like any
other PyLeanX theorem, and later ones cite earlier ones (`pl.ref(thm)(...)`), all in one
Lean run.

These are coordinate *restatements*, not the OAI lemmas themselves: Lean checks them, but
it does not check that they are equivalent to OAI's `EuclideanSpace` statements. See
docs/case-studies/vlasov-maxwell.md for what a faithful port would need.

Run:  python examples/vlasov_maxwell_kinematics.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import analysis as an

Vec = tuple  # three real expressions


def vec(name: str) -> Vec:
    """Three real coordinates name0, name1, name2."""
    return pl.symbols(f"{name}0 {name}1 {name}2", pl.Real)


def dot(a: Vec, b: Vec) -> pl.Expr:
    return a[0]*b[0] + a[1]*b[1] + a[2]*b[2]


def cross(a: Vec, b: Vec) -> Vec:
    return (a[1]*b[2] - a[2]*b[1], a[2]*b[0] - a[0]*b[2], a[0]*b[1] - a[1]*b[0])


def norm(a: Vec) -> pl.Expr:
    return pl.sqrt(dot(a, a))


def q(v: Vec) -> pl.Expr:
    return pl.sqrt(1 + dot(v, v))


a, b, c, v, E, B = vec("a"), vec("b"), vec("c"), vec("v"), vec("E"), vec("B")
SQ = pl.ref("sq_nonneg")
SQRT = "Mathlib.Analysis.Real.Sqrt"           # module of Real.sqrt and its lemmas
sqrt_mul = pl.ref("Real.sqrt_mul", imports=[SQRT])          # 0 ≤ x → √(x*y) = √x * √y
sqrt_le_sqrt = pl.ref("Real.sqrt_le_sqrt", imports=[SQRT])  # x ≤ y → √x ≤ √y
one_le_sqrt_mpr = pl.ref("Real.one_le_sqrt.mpr", imports=[SQRT])  # 1 ≤ x → 1 ≤ √x
div_lt_one = pl.ref("div_lt_one", imports=["Mathlib.Algebra.Order.Field.Basic"])

# ---------------------------------------------------------------- vector algebra (ring)
# OAI Flow/ExtendedLorentz.lean: dot_cross_self_left. The magnetic force does no work.
dot_cross_self_left = pl.Theorem(
    "vm_dot_cross_self_left", [*a, *b],
    conclusion=dot(a, cross(a, b)) == 0, proof=pl.ring())

# OAI: dot_cross_cycle (scalar triple product is cyclic).
dot_cross_cycle = pl.Theorem(
    "vm_dot_cross_cycle", [*a, *b, *c],
    conclusion=dot(a, cross(b, c)) == dot(b, cross(c, a)), proof=pl.ring())

# OAI: cross_antisymm (componentwise; OAI uses `ext i; fin_cases i`).
cross_antisymm = pl.Theorem(
    "vm_cross_antisymm", [*a, *b],
    conclusion=pl.And(*[cross(a, b)[i] == -cross(b, a)[i] for i in range(3)]),
    proof=pl.constructor() >> pl.branches(
        pl.ring(), pl.constructor() >> pl.branches(pl.ring(), pl.ring())))

# OAI: cross_dot_square (Lagrange's identity).
lagrange = pl.Theorem(
    "vm_cross_dot_square", [*a, *b],
    conclusion=dot(cross(a, b), cross(a, b)) == dot(a, a)*dot(b, b) - dot(a, b)**2,
    proof=pl.ring())

# ---------------------------------------------------------------- norms (√, citing above)
# Helper: ‖a‖² ≥ 0 (needed as the side condition of √ lemmas).
dot_self_nonneg = pl.Theorem(
    "vm_dot_self_nonneg", [*a], conclusion=pl.Le(0, dot(a, a)),
    proof=pl.nlinarith(SQ(a[0]), SQ(a[1]), SQ(a[2])))  # positivity cannot see a*a terms

# Squared form of OAI norm_cross_le.
cross_sq_le = pl.Theorem(
    "vm_cross_sq_le", [*a, *b],
    conclusion=dot(cross(a, b), cross(a, b)) <= dot(a, a)*dot(b, b),
    proof=pl.nlinarith(SQ(dot(a, b))))

# OAI: norm_cross_le, ‖a × b‖ ≤ ‖a‖‖b‖.
norm_cross_le = pl.Theorem(
    "vm_norm_cross_le", [*a, *b],
    conclusion=norm(cross(a, b)) <= norm(a)*norm(b),
    proof=pl.rw(pl.rev(sqrt_mul(pl.ref(dot_self_nonneg)(*a), dot(b, b))))
    >> pl.exact(sqrt_le_sqrt(
        pl.ref(cross_sq_le)(*a, *b))))

# OAI: poynting_norm_le_energy, |E × B| ≤ (|E|² + |B|²)/2 (Poynting vector vs. energy).
poynting = pl.Theorem(
    "vm_poynting_norm_le_energy", [*E, *B],
    conclusion=norm(cross(E, B)) <= (dot(E, E) + dot(B, B)) / 2,
    proof=pl.nlinarith(pl.ref(norm_cross_le)(*E, *B),
                       SQ(norm(E) - norm(B)),
                       an.sq_sqrt(pl.ref(dot_self_nonneg)(*E)),
                       an.sq_sqrt(pl.ref(dot_self_nonneg)(*B))))

# ---------------------------------------------------------------- relativistic kinematics
# Helper: 1 ≤ 1 + ‖v‖².
one_le_one_add = pl.Theorem(
    "vm_one_le_one_add_dot_self", [*v], conclusion=pl.Le(1, 1 + dot(v, v)),
    proof=pl.nlinarith(SQ(v[0]), SQ(v[1]), SQ(v[2])))

# OAI Continuation/IncrementBootstrap.lean: one_le_q, q v ≥ 1 (γ ≥ 1).
one_le_q = pl.Theorem(
    "vm_one_le_q", [*v], conclusion=pl.Le(1, q(v)),
    proof=pl.exact(one_le_sqrt_mpr(
        pl.ref(one_le_one_add)(*v))))

# OAI: q_sq, q² = 1 + ‖v‖².
q_sq = pl.Theorem(
    "vm_q_sq", [*v], conclusion=q(v)**2 == 1 + dot(v, v),
    proof=pl.exact(an.sq_sqrt(pl.ref("le_trans")(pl.ref("zero_le_one"),
                                                  pl.ref(one_le_one_add)(*v)))))

# OAI Retarded/ConeMotion.lean: norm_velocity_lt_one, squared: ‖v/q‖² < 1 (speed < c).
speed_sq_lt_one = pl.Theorem(
    "vm_speed_sq_lt_one", [*v],
    conclusion=dot(v, v) / q(v)**2 < 1,
    proof=pl.rw(pl.ref(q_sq)(*v))
    >> pl.rw(div_lt_one(
        pl.ref("lt_of_lt_of_le")(pl.ref("zero_lt_one"), pl.ref(one_le_one_add)(*v))))
    >> pl.linarith())

THEOREMS = [dot_cross_self_left, dot_cross_cycle, cross_antisymm, lagrange,
            dot_self_nonneg, cross_sq_le, norm_cross_le, poynting,
            one_le_one_add, one_le_q, q_sq, speed_sq_lt_one]

if __name__ == "__main__":
    print(norm_cross_le.to_lean())
    results = pl.verify_all(THEOREMS, timeout=1800)
    for r in results:
        print(r.summary())
    n = sum(r.verified for r in results)
    print(f"{n}/{len(results)} verified")
    raise SystemExit(0 if n == len(results) else 1)
