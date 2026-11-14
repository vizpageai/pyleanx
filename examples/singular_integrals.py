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

#: families of intervals are indexed by points of ℝ (so a compact set can index its own cover)
IDX = pl.Real
s, v = pl.symbols("s v", rv.finset_of(IDX))
u = pl.symbol("u", rv.set_of(IDX))
c, r = pl.symbols("c r", pl.Fn(IDX, pl.Real))
f = pl.symbol("f", rv.RFun)
alpha, x = pl.symbols("α x", pl.Real)
i, j = pl.symbols("i j", IDX)


def I(k: object, scale: object = 1) -> pl.Expr:  # noqa: E741, E743, N802 - the book notation
    """The interval I_k = [c_k − r_k, c_k + r_k] (dilated by ``scale``)."""
    if isinstance(scale, int) and scale == 1:
        return rv.interval(c(k), r(k))
    return rv.interval(c(k), scale * r(k))


def covers(S: pl.Expr, V: pl.Expr) -> pl.Expr:  # noqa: N803
    """Every interval I_i, i ∈ S, lies in the 4-fold dilate of some I_j, j ∈ V."""
    a, b = pl.symbols("i j", IDX)
    return pl.Forall(a, pl.Implies(rv.mem(a, S), pl.Exists(b, pl.And(
        rv.mem(b, V), rv.subset(I(a), I(b, 4))))))


def nonneg_radii(S: pl.Expr) -> pl.Expr:
    a = pl.symbol("i", IDX)
    return pl.Forall(a, pl.Implies(rv.mem(a, S), 0 <= r(a)))


# -----------------------------------------------------------------------------------------
# 1. The Vitali covering lemma for finitely many intervals
# -----------------------------------------------------------------------------------------

def _vitali_proof() -> pl.Tactic:
    a = pl.symbol("i", IDX)
    claim, choose = pl.claim, pl.choose
    return pl.proof(
        claim(pl.Forall(a, pl.Implies(rv.mem(a, s), r(a) <= pl.sum(s, lambda k: r(k),
                                                                     sort=IDX))),
              because=[rv.single_le_sum, "hr"],
              note="each radius is at most the sum of the radii"),
        choose(u, such_that=pl.And(rv.subset(u, rv.as_set(s, IDX)),
                                   rv.disjoint_intervals(u, c, r, index=IDX),
                                   covers(rv.as_set(s, IDX), u)),
               because=[rv.vitali_mathlib, "step1"], names="hus hdisj hcov",
               note="Vitali's selection with dilation factor 4 > 3"),
        claim(rv.finite(rv.as_set(s, IDX)), because=rv.finset_finite),
        claim(rv.finite(u), because=[rv.finite_subset, "step3", "hus"],
              note="u ⊆ s and s is finite"),
        choose(v, such_that=rv.as_set(v, IDX) == u, because=[rv.finite_as_finset, "step4"],
               names="hv", note="index the finite set u by a finite set v"),
        pl.take(v),
        claim(rv.subset(rv.as_set(v, IDX), rv.as_set(s, IDX)), because=["hv", "hus"]),
        claim(rv.subset(v, s), because=[rv.coe_subset, "step7"]),
        claim(rv.disjoint_intervals(rv.as_set(v, IDX), c, r, index=IDX), because=["hv", "hdisj"]),
        claim(covers(rv.as_set(s, IDX), rv.as_set(v, IDX)), because=["hv", "hcov"]),
        pl.conclude(),
    )


vitali_finite = pl.Theorem(
    "vitali_covering_finite", [s, c, r],
    assumptions={"hr": nonneg_radii(s)},
    conclusion=pl.Exists(v, pl.And(rv.subset(v, s),
                                   rv.disjoint_intervals(rv.as_set(v, IDX), c, r, index=IDX),
                                   covers(rv.as_set(s, IDX), rv.as_set(v, IDX)))),
    proof=_vitali_proof(),
)


# -----------------------------------------------------------------------------------------
# 2. Integrals over disjoint intervals add up to at most ‖f‖₁
# -----------------------------------------------------------------------------------------

def _disjoint_proof() -> pl.Tactic:
    claim = pl.claim
    union_v = rv.union(v, c, r, index=IDX)
    abs_f = lambda t: pl.abs(f(t))  # noqa: E731
    k = pl.symbol("j", IDX)
    return pl.proof(
        claim(rv.integrable(rv.abs_fun(f)), because=[rv.integrable_abs, "hf"]),
        claim(pl.Forall(k, pl.Implies(rv.mem(k, v), rv.integrable_on(rv.abs_fun(f), I(k)))),
              because=[rv.integrable_on_of_integrable, "step1"]),
        claim(pl.integral(abs_f, within=union_v) == pl.sum(v, lambda t: pl.integral(
            abs_f, within=I(t)), sort=IDX),
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
    assumptions={"hf": rv.integrable(f),
                 "hd": rv.disjoint_intervals(rv.as_set(v, IDX), c, r, index=IDX)},
    conclusion=pl.sum(v, lambda t: pl.integral(lambda y: pl.abs(f(y)), within=I(t)),
                      sort=IDX) <= rv.l1_norm(f),
    proof=_disjoint_proof(),
)


# -----------------------------------------------------------------------------------------
# 3. The covering bound: α |⋃ Iᵢ| ≤ 4 ‖f‖₁ when every average exceeds α
# -----------------------------------------------------------------------------------------

def _covering_proof() -> pl.Tactic:
    claim, choose = pl.claim, pl.choose
    union_s = rv.union(s, c, r, index=IDX)
    union_v4 = rv.union(v, c, r, scale=4, index=IDX)
    abs_f = lambda t: pl.abs(f(t))  # noqa: E731
    sum_v = lambda body: pl.sum(v, body, sort=IDX)  # noqa: E731
    return pl.proof(
        choose(v, such_that=pl.And(rv.subset(v, s),
                                   rv.disjoint_intervals(rv.as_set(v, IDX), c, r, index=IDX),
                                   covers(rv.as_set(s, IDX), rv.as_set(v, IDX))),
               because=[vitali_finite, "hr"], names="hvs hvd hvc",
               note="Vitali covering lemma (theorem 1)"),
        claim(rv.subset(union_s, union_v4), name="hcover", note="every Iᵢ lies in some 4Iⱼ",
              proof=pl.proof(
                  pl.fix(x, assume={"hx": rv.mem(x, union_s)}),
                  choose(i, such_that=pl.And(rv.mem(i, s), rv.mem(x, I(i))),
                         because=[rv.mem_union, "hx"], names="his hxi"),
                  choose(j, such_that=pl.And(rv.mem(j, rv.as_set(v, IDX)),
                                             rv.subset(I(i), I(j, 4))),
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
    conclusion=alpha * rv.measure(rv.union(s, c, r, index=IDX)) <= 4 * rv.l1_norm(f),
    proof=_covering_proof(),
)


# -----------------------------------------------------------------------------------------
# 4. The Hardy–Littlewood maximal inequality on compact sets
# -----------------------------------------------------------------------------------------
# {Mf > α} is the set of x having an interval [x − ρ, x + ρ] on which the average of |f|
# exceeds α. For a compact K inside it: α |K| ≤ 4 ‖f‖₁.

K = pl.symbol("K", rv.set_of(pl.Real))
b = pl.symbol("b", rv.set_of(pl.Real))
t = pl.symbol("t", rv.finset_of(pl.Real))
R = pl.symbol("R", pl.Fn(pl.Real, pl.Real))
rho, y, z = pl.symbols("ρ y z", pl.Real)


def _avg(p: object, q: object) -> pl.Expr:
    return rv.average_exceeds(f, alpha, p, q)


def _maximal_proof() -> pl.Tactic:
    claim, choose, fix = pl.claim, pl.choose, pl.fix
    balls_K = pl.union(K, lambda q: rv.ball(q, R(q)), sort=pl.Real)
    balls_b = pl.union(b, lambda q: rv.ball(q, R(q)), sort=pl.Real)
    intervals_t = pl.union(t, lambda q: rv.interval(q, R(q)), sort=pl.Real)
    return pl.proof(
        claim(pl.Forall(x, pl.Exists(rho, pl.Implies(rv.mem(x, K),
                                                     pl.And(0 < rho, _avg(x, rho))))),
              name="hloc", note="for x ∈ K take the interval from the hypothesis",
              proof=pl.proof(
                  fix(x),
                  pl.cases_on(
                      pl.case(rv.mem(x, K),
                              choose(rho, such_that=pl.And(0 < rho, _avg(x, rho)),
                                     because=["hsub", "h"], names="hρ"),
                              pl.take(rho),
                              pl.conclude(),
                              name="h"),
                      pl.case(pl.Not(rv.mem(x, K)),
                              pl.take(1),
                              pl.conclude(note="x ∉ K: nothing to show"),
                              name="h"),
                  ),
              )),
        choose(R, such_that=pl.Forall(x, pl.Implies(rv.mem(x, K),
                                                    pl.And(0 < R(x), _avg(x, R(x))))),
               because=[rv.axiom_of_choice, "hloc"], names="hR",
               note="choose a radius R(x) for every x ∈ K"),
        claim(rv.subset(K, balls_K), name="hKcov", note="each x ∈ K lies in its own interval",
              proof=pl.proof(
                  fix(y, assume={"hy": rv.mem(y, K)}),
                  claim(pl.And(0 < R(y), _avg(y, R(y))), because=["hR", "hy"]),
                  claim(0 < R(y), because="hKcov_2"),
                  claim(rv.mem(y, rv.ball(y, R(y))), because=[rv.mem_ball_self, "hKcov_3"]),
                  pl.conclude(because=rv.mem_union),
              )),
        choose(b, such_that=pl.And(rv.subset(b, K), rv.finite(b), rv.subset(K, balls_b)),
               because=[rv.compact_finite_subcover, "hK", rv.ball_open, "hKcov"],
               names="hbK hbfin hbcov", note="K is compact: finitely many centres b suffice"),
        choose(t, such_that=rv.as_set(t, pl.Real) == b, because=[rv.finite_as_finset, "hbfin"],
               names="ht", note="index the finitely many centres by a finite set t"),
        claim(rv.subset(K, intervals_t), name="hKt",
              note="K is covered by the closed intervals around the points of t",
              proof=pl.proof(
                  fix(y, assume={"hy": rv.mem(y, K)}),
                  claim(rv.mem(y, balls_b), because=["hbcov", "hy"]),
                  choose(z, such_that=pl.And(rv.mem(z, b), rv.mem(y, rv.ball(z, R(z)))),
                         because=[rv.mem_union, "hKt_2"], names="hzb hyz"),
                  claim(rv.mem(z, rv.as_set(t, pl.Real)), because=["ht", "hzb"]),
                  claim(rv.mem(z, t), because=[rv.mem_coe, "hKt_4"]),
                  claim(rv.mem(y, rv.interval(z, R(z))), because=[rv.ball_in_interval, "hyz"]),
                  pl.conclude(because=rv.mem_union),
              )),
        claim(pl.Forall(x, pl.Implies(rv.mem(x, t), pl.And(0 < R(x), _avg(x, R(x))))),
              name="hgood", note="every centre in t is a point of K",
              proof=pl.proof(
                  fix(x, assume={"hx": rv.mem(x, t)}),
                  claim(rv.mem(x, rv.as_set(t, pl.Real)), because=[rv.mem_coe, "hx"]),
                  claim(rv.mem(x, b), because=["ht", "hgood_2"]),
                  claim(rv.mem(x, K), because=["hbK", "hgood_3"]),
                  pl.conclude(because=["hR", "hgood_4"]),
              )),
        claim(pl.Forall(x, pl.Implies(rv.mem(x, t), 0 <= R(x))), name="hrt",
              proof=pl.proof(
                  fix(x, assume={"hx": rv.mem(x, t)}),
                  claim(pl.And(0 < R(x), _avg(x, R(x))), because=["hgood", "hx"]),
                  claim(0 < R(x), because="hrt_2"),
                  pl.conclude(),
              )),
        claim(pl.Forall(x, pl.Implies(rv.mem(x, t), _avg(x, R(x)))), name="hbigt",
              proof=pl.proof(
                  fix(x, assume={"hx": rv.mem(x, t)}),
                  claim(pl.And(0 < R(x), _avg(x, R(x))), because=["hgood", "hx"]),
                  pl.conclude(because="hbigt_2"),
              )),
        claim(alpha * rv.measure(intervals_t) <= 4 * rv.l1_norm(f),
              because=[covering_bound, "hf", "hα", "hrt", "hbigt"],
              note="the covering bound (theorem 3)"),
        claim(rv.finite_measure(intervals_t),
              because=[rv.union_finite_measure, rv.finset_finite, rv.interval_finite_measure]),
        claim(rv.measure(K) <= rv.measure(intervals_t),
              because=[rv.measure_mono, "hKt", rv.lt_ne, "step11"]),
        claim(alpha * rv.measure(K) <= alpha * rv.measure(intervals_t),
              because=[rv.mul_le_mul_left, "step12", "hα"]),
        pl.conclude(),
    )


maximal_inequality = pl.Theorem(
    "hardy_littlewood_maximal_compact", [f, alpha, K],
    assumptions={"hf": rv.integrable(f), "hα": alpha > 0, "hK": rv.is_compact(K),
                 "hsub": pl.Forall(x, pl.Implies(rv.mem(x, K), pl.Exists(rho, pl.And(
                     0 < rho, _avg(x, rho)))))},
    conclusion=alpha * rv.measure(K) <= 4 * rv.l1_norm(f),
    proof=_maximal_proof(),
)


# -----------------------------------------------------------------------------------------
# 5. The weak (1,1) inequality on measurable sets (Stein ch. I §1, Theorem 1(b))
# -----------------------------------------------------------------------------------------
# For a measurable E ⊆ {Mf > α} of finite measure: α |E| ≤ 4 ‖f‖₁.
# Proof: if not, inner regularity gives a compact K ⊆ E with |K| > 4‖f‖₁/α,
# contradicting theorem 4.

E = pl.symbol("E", rv.set_of(pl.Real))


def _weak_type_proof() -> pl.Tactic:
    claim, fix = pl.claim, pl.fix
    norm = rv.l1_norm(f)
    a = 4 * norm / alpha
    return pl.proof(
        pl.suppose_not(4 * norm < alpha * rv.measure(E), name="hcon"),
        claim(rv.ae_nonneg(rv.abs_fun(f)), because=[rv.everywhere_ae, rv.abs_nonneg]),
        claim(0 <= norm, because=[rv.integral_nonneg_ae, "step2"]),
        claim(a < rv.measure(E), because=[rv.div_lt_iff, "hα", "hcon"],
              note="4‖f‖₁ < α|E|"),
        claim(0 <= a, because=[rv.div_nonneg, "step3", "hα"]),
        claim(rv.of_real(a) < rv.vol(E),
              because=[rv.of_real_lt, rv.measure_real_def, "step5", "hEfin", "step4"]),
        pl.choose(K, such_that=pl.And(rv.subset(K, E), rv.is_compact(K),
                                      rv.of_real(a) < rv.vol(K)),
                  because=[rv.inner_regular, "hE", "hEfin", "step6"], names="hKE hKc hKa",
                  note="inner regularity of Lebesgue measure"),
        claim(rv.finite_measure_ne(K), because=[rv.subset_finite_measure, "hKE", "hEfin"]),
        claim(a < rv.measure(K), because=[rv.of_real_lt, rv.measure_real_def, "step5", "step8",
                       "hKa"]),
        claim(pl.Forall(x, pl.Implies(rv.mem(x, K), pl.Exists(rho, pl.And(
            0 < rho, _avg(x, rho))))), name="hKsub", note="K ⊆ E",
            proof=pl.proof(
                fix(x, assume={"hx": rv.mem(x, K)}),
                claim(rv.mem(x, E), because=["hKE", "hx"]),
                pl.conclude(because="hsub"),
            )),
        claim(alpha * rv.measure(K) <= 4 * norm,
              because=[maximal_inequality, "hf", "hα", "hKc", "hKsub"],
              note="theorem 4 for the compact set K"),
        claim(alpha * a < alpha * rv.measure(K), because=[rv.mul_lt_mul_left, "step9", "hα"]),
        claim(alpha != 0, because=[rv.ne_of_gt, "hα"]),
        claim(alpha * a == 4 * norm, because=[rv.mul_div_cancel, "step13"],
              note="α · (4‖f‖₁/α) = 4‖f‖₁"),
        pl.conclude(note="4‖f‖₁ = α·(4‖f‖₁/α) < α|K| ≤ 4‖f‖₁ is impossible"),
    )


weak_type = pl.Theorem(
    "hardy_littlewood_weak_type", [f, alpha, E],
    assumptions={"hf": rv.integrable(f), "hα": alpha > 0, "hE": rv.measurable(E),
                 "hEfin": rv.finite_measure_ne(E),
                 "hsub": pl.Forall(x, pl.Implies(rv.mem(x, E), pl.Exists(rho, pl.And(
                     0 < rho, _avg(x, rho)))))},
    conclusion=alpha * rv.measure(E) <= 4 * rv.l1_norm(f),
    proof=_weak_type_proof(),
)

THEOREMS = [vitali_finite, disjoint_integrals, covering_bound, maximal_inequality, weak_type]

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
