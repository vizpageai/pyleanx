"""Gate for the general Lean vocabulary (M11-M13) against real Lean + Mathlib:
open types, fun, ∑, norms and scalar multiplication, definitions, structures, structured
proofs (have/calc/obtain/induction) and pl.auto. Negative cases must be rejected."""

from __future__ import annotations

import pytest

import pyleanx as pl

pytestmark = pytest.mark.lean

BIGOPS = "Mathlib.Algebra.BigOperators.Group.Finset.Basic"


def build() -> tuple[list[pl.Theorem], list[pl.Theorem]]:
    V = pl.EuclideanSpace(3)
    c = pl.var("c", pl.Real)
    x = pl.var("x", V)
    norm_smul = pl.Theorem(
        "gen_norm_smul", [c, x],
        conclusion=pl.norm(pl.smul(c, x)) == pl.norm(c) * pl.norm(x),
        proof=pl.exact(pl.ref("norm_smul", ["Mathlib.Analysis.Normed.MulAction"])(c, x)))

    fun_beta = pl.Theorem(
        "gen_fun_beta", [], conclusion=pl.app(pl.fun(lambda k: k + 1, pl.Nat), 2) == pl.nat(3),
        proof=pl.auto())

    n = pl.var("n", pl.Nat)
    rng = pl.const("Finset.range", imports=["Mathlib.Data.Finset.Range"])
    odd_sum = pl.Theorem(
        "gen_sum_odd", [n],
        conclusion=pl.sum(rng(n), lambda i: 2 * i + 1, sort=pl.Nat) == n**2,
        proof=pl.induction(
            "n", zero=pl.simp(),
            succ=pl.rw(pl.ref("Finset.sum_range_succ", [BIGOPS]), "ih") >> pl.ring()))

    # definitions + structured proof
    Vec = pl.define_type("GenVec", V)

    @pl.define(returns=pl.Real)
    def gen_q(v: Vec):
        """Relativistic energy per unit mass."""
        return pl.sqrt(1 + pl.norm(v)**2)

    v = pl.var("v", Vec)
    one_le_q = pl.Theorem(
        "gen_one_le_q", [v], conclusion=pl.Le(1, gen_q(v)),
        proof=pl.proof(
            pl.unfold(gen_q),
            pl.have("h", pl.Le(1, 1 + pl.norm(v)**2), pl.auto(pl.ref("sq_nonneg")(pl.norm(v)))),
            pl.exact(pl.ref("Real.one_le_sqrt.mpr")("h"))))

    @pl.structure
    class GenPoint:
        px: pl.Real
        py: pl.Real

    struct = pl.Theorem(
        "gen_struct_field", [], conclusion=pl.mk(GenPoint, px=1, py=2).px == pl.real(1),
        proof=pl.rfl())

    a, b = pl.symbols("a b", pl.Real)
    calc_thm = pl.Theorem(
        "gen_calc", [a, b], conclusion=(a + b)**2 <= 2 * (a**2 + b**2),
        proof=pl.calc((a + b)**2,
                      ("=", a**2 + 2*a*b + b**2, pl.ring()),
                      ("<=", a**2 + (a**2 + b**2) + b**2,
                       pl.nlinarith(pl.ref("sq_nonneg")(a - b))),
                      ("=", 2 * (a**2 + b**2))))

    k, y, z = pl.var("k", pl.Int), pl.var("y", pl.Int), pl.var("z", pl.Int)
    w = pl.var("w", pl.Int)  # named by `obtain` inside the proof
    obtain_thm = pl.Theorem(
        "gen_obtain", [k], assumptions={"h": pl.Exists(y, k == 2 * y)},
        conclusion=pl.Exists(z, k * k == 4 * z),
        proof=pl.proof(pl.obtain("w hw", "h"), pl.use(w**2), pl.rw("hw"), pl.ring()))

    good = [norm_smul, fun_beta, odd_sum, one_le_q, struct, calc_thm, obtain_thm]

    # ---- must be rejected
    false_vec = pl.Theorem(
        "gen_false_norm", [c, x], conclusion=pl.norm(pl.smul(c, x)) == c * pl.norm(x),
        proof=pl.auto())  # false for c < 0
    return good, [false_vec]


def test_general_vocabulary_verifies_and_rejects(lean_project):
    good, bad = build()
    results = pl.verify_all([*good, *bad], project=lean_project, timeout=1800)
    by = {r.theorem: r for r in results}
    for t in good:
        r = by[t.name]
        print(r.summary())
        assert r.verified, (t.name, [d.message for d in r.errors])
    for t in bad:
        assert not by[t.name].verified


def test_broken_definition_rejects_whole_file(lean_project):
    @pl.define(returns=pl.Real)
    def gen_broken(x: pl.Real):
        return pl.app(pl.const("Real.no_such_function"), x)

    x = pl.var("x", pl.Real)
    uses = pl.Theorem("gen_uses_broken", [x], conclusion=gen_broken(x) == gen_broken(x),
                      proof=pl.rfl())
    unrelated = pl.Theorem("gen_unrelated", [x], conclusion=x == x, proof=pl.rfl())
    results = pl.verify_all([uses, unrelated], project=lean_project, timeout=1800)
    assert not any(r.verified for r in results)
