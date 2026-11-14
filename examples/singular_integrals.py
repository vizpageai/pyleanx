"""Real-variable harmonic analysis, proved as written proofs and checked by Lean.

Following Stein, *Singular Integrals and Differentiability Properties of Functions*, ch. I §1,
and Tao's notes on the Hardy–Littlewood maximal inequality. Every theorem here is a PyLeanX
written proof: each step is a sentence with its reason (a Mathlib theorem or an earlier
theorem of this file), and Lean checks every step. Nothing in this file is assumed.

1. ``vitali_finite``     — Vitali covering lemma for a finite family of intervals.
2. ``covering_bound``    — if the average of |f| over each interval Iᵢ exceeds α, then
                            α · |⋃ Iᵢ| ≤ 4 ‖f‖₁ (the heart of the maximal inequality).

Run:  python examples/singular_integrals.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import realvar as rv

s, v = pl.symbols("s v", rv.Indices)
u = pl.symbol("u", rv.IndexSet)
c, r = pl.symbols("c r", rv.Family)
f = pl.symbol("f", rv.RFun)
alpha, x = pl.symbols("α x", pl.Real)
i, j = pl.symbols("i j", pl.Nat)


def I(k: object, scale: object = 1) -> pl.Expr:  # noqa: E741, E743, N802 - the book notation
    """The interval I_k = [c_k − r_k, c_k + r_k] (dilated by ``scale``)."""
    if isinstance(scale, int) and scale == 1:
        return rv.interval(c(k), r(k))
    return rv.interval(c(k), scale * r(k))


def covers(S: pl.Expr, V: pl.Expr) -> pl.Expr:  # noqa: N803
    """Every interval I_i, i ∈ S, lies in the 4-fold dilate of some I_j, j ∈ V."""
    a, b = pl.symbols("i j", pl.Nat)
    return pl.Forall(a, pl.Implies(rv.mem(a, S), pl.Exists(b, pl.And(
        rv.mem(b, V), rv.subset(I(a), I(b, 4))))))


def nonneg_radii(S: pl.Expr) -> pl.Expr:
    a = pl.symbol("i", pl.Nat)
    return pl.Forall(a, pl.Implies(rv.mem(a, S), 0 <= r(a)))


# -----------------------------------------------------------------------------------------
# 1. The Vitali covering lemma for finitely many intervals
# -----------------------------------------------------------------------------------------

def _vitali_proof() -> pl.Tactic:
    a = pl.symbol("i", pl.Nat)
    claim, choose = pl.claim, pl.choose
    return pl.proof(
        claim(pl.Forall(a, pl.Implies(rv.mem(a, s), r(a) <= pl.sum(s, lambda k: r(k),
                                                                     sort=pl.Nat))),
              because=[rv.single_le_sum, "hr"],
              note="each radius is at most the sum of the radii"),
        choose(u, such_that=pl.And(rv.subset(u, rv.as_set(s)), rv.disjoint_intervals(u, c, r),
                                   covers(rv.as_set(s), u)),
               because=[rv.vitali_mathlib, "step1"], names="hus hdisj hcov",
               note="Vitali's selection with dilation factor 4 > 3"),
        claim(rv.finite(rv.as_set(s)), because=rv.finset_finite),
        claim(rv.finite(u), because=[rv.finite_subset, "step3", "hus"],
              note="u ⊆ s and s is finite"),
        choose(v, such_that=rv.as_set(v) == u, because=[rv.finite_as_finset, "step4"],
               names="hv", note="index the finite set u by a finite set v"),
        pl.take(v),
        claim(rv.subset(rv.as_set(v), rv.as_set(s)), because=["hv", "hus"]),
        claim(rv.subset(v, s), because=[rv.coe_subset, "step7"]),
        claim(rv.disjoint_intervals(rv.as_set(v), c, r), because=["hv", "hdisj"]),
        claim(covers(rv.as_set(s), rv.as_set(v)), because=["hv", "hcov"]),
        pl.conclude(),
    )


vitali_finite = pl.Theorem(
    "vitali_covering_finite", [s, c, r],
    assumptions={"hr": nonneg_radii(s)},
    conclusion=pl.Exists(v, pl.And(rv.subset(v, s), rv.disjoint_intervals(rv.as_set(v), c, r),
                                   covers(rv.as_set(s), rv.as_set(v)))),
    proof=_vitali_proof(),
)


# -----------------------------------------------------------------------------------------
# 2. Integrals over disjoint intervals add up to at most ‖f‖₁
# -----------------------------------------------------------------------------------------

def _disjoint_proof() -> pl.Tactic:
    claim = pl.claim
    union_v = rv.union(v, c, r)
    abs_f = lambda t: pl.abs(f(t))  # noqa: E731
    k = pl.symbol("j", pl.Nat)
    return pl.proof(
        claim(rv.integrable(rv.abs_fun(f)), because=[rv.integrable_abs, "hf"]),
        claim(pl.Forall(k, pl.Implies(rv.mem(k, v), rv.integrable_on(rv.abs_fun(f), I(k)))),
              because=[rv.integrable_on_of_integrable, "step1"]),
        claim(pl.integral(abs_f, within=union_v) == pl.sum(v, lambda t: pl.integral(
            abs_f, within=I(t)), sort=pl.Nat),
            because=[rv.integral_disjoint_union, rv.interval_measurable, "hd", "step2"],
            note="the intervals are disjoint and measurable"),
        claim(rv.ae_nonneg(rv.abs_fun(f)), because=[rv.everywhere_ae, rv.abs_nonneg]),
        claim(pl.integral(abs_f, within=union_v) <= rv.l1_norm(f),
              because=[rv.set_integral_le, "step1", "step4"],
              note="|f| ≥ 0, so the integral over a subset is smaller"),
        pl.conclude(),
    )


disjoint_integrals = pl.Theorem(
    "integrals_over_disjoint_intervals", [f, v, c, r],
    assumptions={"hf": rv.integrable(f), "hd": rv.disjoint_intervals(rv.as_set(v), c, r)},
    conclusion=pl.sum(v, lambda t: pl.integral(lambda y: pl.abs(f(y)), within=I(t)),
                      sort=pl.Nat) <= rv.l1_norm(f),
    proof=_disjoint_proof(),
)


# -----------------------------------------------------------------------------------------
# 3. The covering bound: α |⋃ Iᵢ| ≤ 4 ‖f‖₁ when every average exceeds α
# -----------------------------------------------------------------------------------------

def _covering_proof() -> pl.Tactic:
    claim, choose = pl.claim, pl.choose
    union_s = rv.union(s, c, r)
    union_v4 = rv.union(v, c, r, scale=4)
    abs_f = lambda t: pl.abs(f(t))  # noqa: E731
    sum_v = lambda body: pl.sum(v, body, sort=pl.Nat)  # noqa: E731
    return pl.proof(
        choose(v, such_that=pl.And(rv.subset(v, s), rv.disjoint_intervals(rv.as_set(v), c, r),
                                   covers(rv.as_set(s), rv.as_set(v))),
               because=[vitali_finite, "hr"], names="hvs hvd hvc",
               note="Vitali covering lemma (theorem 1)"),
        claim(rv.subset(union_s, union_v4), name="hcover", note="every Iᵢ lies in some 4Iⱼ",
              proof=pl.proof(
                  pl.fix(x, assume={"hx": rv.mem(x, union_s)}),
                  choose(i, such_that=pl.And(rv.mem(i, s), rv.mem(x, I(i))),
                         because=[rv.mem_union, "hx"], names="his hxi"),
                  choose(j, such_that=pl.And(rv.mem(j, rv.as_set(v)), rv.subset(I(i), I(j, 4))),
                         because=["hvc", "his"], names="hjv hsub"),
                  claim(rv.mem(x, I(j, 4)), because=["hsub", "hxi"]),
                  pl.conclude(because=rv.mem_union),
              )),
        claim(rv.finite_measure(union_v4),
              because=[rv.union_finite_measure, rv.finset_finite, rv.interval_finite_measure],
              note="finitely many intervals"),
        claim(rv.measure(union_s) <= rv.measure(union_v4),
              because=[rv.measure_mono, "hcover", rv.lt_ne, "step3"],
              note="monotonicity of measure"),
        claim(rv.measure(union_v4) <= sum_v(lambda k: rv.measure(I(k, 4))),
              because=rv.measure_union_le, note="subadditivity"),
        claim(pl.Forall(j, pl.Implies(rv.mem(j, v), 0 <= r(j))), note="v ⊆ s",
              proof=pl.proof(
                  pl.fix(j, assume={"hj": rv.mem(j, v)}),
                  claim(rv.mem(j, s), because=["hvs", "hj"]),
                  pl.conclude(because="hr"),
              )),
        claim(pl.Forall(j, pl.Implies(rv.mem(j, v),
                                      rv.measure(I(j, 4)) == 4 * rv.measure(I(j)))),
              note="|4I| = 8r = 4|I|",
              proof=pl.proof(
                  pl.fix(j, assume={"hj": rv.mem(j, v)}),
                  claim(0 <= r(j), because=["step6", "hj"]),
                  claim(rv.measure(I(j)) == 2 * r(j), because=[rv.measure_interval, "step7_2"]),
                  claim(0 <= 4 * r(j), because=[rv.mul_nonneg, "step7_2"]),
                  claim(rv.measure(I(j, 4)) == 2 * (4 * r(j)),
                        because=[rv.measure_interval, "step7_4"]),
                  pl.conclude(),
              )),
        claim(sum_v(lambda k: rv.measure(I(k, 4))) == sum_v(lambda k: 4 * rv.measure(I(k))),
              because=[rv.sum_congr, "step7"]),
        claim(sum_v(lambda k: 4 * rv.measure(I(k))) == 4 * sum_v(lambda k: rv.measure(I(k))),
              because=rv.mul_sum),
        claim(pl.Forall(j, pl.Implies(rv.mem(j, v), alpha * rv.measure(I(j))
                                      <= pl.integral(abs_f, within=I(j)))),
              note="the average over each Iⱼ exceeds α",
              proof=pl.proof(
                  pl.fix(j, assume={"hj": rv.mem(j, v)}),
                  claim(rv.mem(j, s), because=["hvs", "hj"]),
                  claim(rv.average_exceeds(f, alpha, c(j), r(j)), because="hbig"),
                  pl.conclude(),
              )),
        claim(sum_v(lambda k: alpha * rv.measure(I(k)))
              <= sum_v(lambda k: pl.integral(abs_f, within=I(k))),
              because=[rv.sum_le_sum, "step10"]),
        claim(alpha * sum_v(lambda k: rv.measure(I(k)))
              == sum_v(lambda k: alpha * rv.measure(I(k))), because=rv.mul_sum),
        claim(sum_v(lambda k: pl.integral(abs_f, within=I(k))) <= rv.l1_norm(f),
              because=[disjoint_integrals, "hf", "hvd"],
              note="the Iⱼ are disjoint, so the integrals add up to at most ∫|f|"),
        pl.conclude(note="α|⋃Iᵢ| ≤ α·4∑|Iⱼ| = 4∑α|Iⱼ| ≤ 4∑∫_{Iⱼ}|f| ≤ 4‖f‖₁"),
    )


covering_bound = pl.Theorem(
    "maximal_covering_bound", [f, alpha, s, c, r],
    assumptions={"hf": rv.integrable(f), "hα": alpha > 0, "hr": nonneg_radii(s),
                 "hbig": pl.Forall(i, pl.Implies(rv.mem(i, s),
                                                 rv.average_exceeds(f, alpha, c(i), r(i))))},
    conclusion=alpha * rv.measure(rv.union(s, c, r)) <= 4 * rv.l1_norm(f),
    proof=_covering_proof(),
)

THEOREMS = [vitali_finite, disjoint_integrals, covering_bound]

if __name__ == "__main__":
    import sys

    results = pl.verify_all(THEOREMS, timeout=3600)
    ok = True
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
        if not res.verified:
            for d in res.errors[:4]:
                print("   ", d.span_label, "|", d.message[:400].replace("\n", " | "))
        ok = ok and res.verified
    sys.exit(0 if ok else 1)
