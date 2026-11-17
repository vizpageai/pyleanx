"""The Calderón–Zygmund decomposition on ℝ, as PyLeanX written proofs checked by Lean.

Stein, *Singular Integrals*, ch. I §3 (the decomposition via the maximal function). Fix f
locally integrable and α > 0, and let Ω = {Mf > α}: the points x having an interval
[x − ρ, x + ρ] on which the average of |f| exceeds α. Theorems 7 and 8
(``examples/singular_integrals.py``) show that Ω is open and |Ω| ≤ 8‖f·1{|f|>α/2}‖₁/α.
Here:

    15. An interval that meets the complement of Ω has average ≤ 2α:
        if a ∈ [c − r, c + r] and a ∉ Ω, then ∫_{[c−r, c+r]} |f| ≤ 2α · |[c − r, c + r]|.
    16. |f| ≤ α almost everywhere off Ω (Lebesgue's differentiation theorem).
    17. The decomposition: Ω is open, |Ω| ≤ 8‖f·1{|f|>α/2}‖₁/α, |f| ≤ α a.e. off Ω, and
        every interval meeting ℝ ∖ Ω has average ≤ 2α.

So f is "good" (bounded by α) off Ω and has controlled averages on the intervals that make
up Ω. (Writing Ω as a disjoint union of intervals — its connected components, or a Whitney
decomposition — is not yet in the vocabulary.)

Run:  python examples/calderon_zygmund.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import pyleanx as pl
from pyleanx import realvar as rv

sys.path.insert(0, str(Path(__file__).resolve().parent))
from singular_integrals import level_set_bound, level_set_open  # noqa: E402

f = pl.symbol("f", rv.RFun)
alpha, a, c, r, x, rho = pl.symbols("α a c r x ρ", pl.Real)

E = rv.level_set(f, alpha)


def _int(S: object) -> pl.Expr:
    return pl.integral(lambda w: pl.abs(f(w)), within=S)


def _in_level_set(p: object, rad: object, exceeds: str, pos: str) -> pl.Tactic:
    """p ∈ {Mf > α}, witnessed by the interval [p − rad, p + rad]."""
    return pl.proof(
        pl.suffices(pl.Exists(rho, pl.And(0 < rho, rv.average_exceeds(f, alpha, p, rho))),
                    because=rv.mem_set_of),
        pl.take(rad, such_that=0 < rad, because=pos),
        pl.conclude(because=exceeds),
    )


# -----------------------------------------------------------------------------------------
# 15. An interval meeting the complement of Ω has average ≤ 2α
# -----------------------------------------------------------------------------------------
# I = [c − r, c + r] lies inside J = [a − 2r, a + 2r] because a ∈ I; and J has average ≤ α
# because a ∉ Ω. So ∫_I |f| ≤ ∫_J |f| ≤ α|J| = 2α|I|.

def _interval_proof() -> pl.Tactic:
    claim = pl.claim
    I, J = rv.interval(c, r), rv.interval(a, 2 * r)  # noqa: E741
    return pl.proof(
        claim(rv.dist(c, a) <= r, because=[rv.mem_interval, "haI"], name="hca"),
        claim(r + rv.dist(c, a) <= 2 * r, name="hsum"),
        claim(rv.subset(I, J), because=[rv.interval_in_interval, "hsum"], name="hIJ",
              note="a ∈ I, so I ⊆ [a − 2r, a + 2r]"),
        claim(rv.integrable_on(f, J), because=[rv.integrable_on_compact, "hf", rv.interval_compact],
              name="hfJ"),
        claim(rv.integrable_on(rv.abs_fun(f), J), because=[rv.integrable_abs, "hfJ"],
              name="hafJ"),
        claim(rv.ae_nonneg_on(rv.abs_fun(f), J), because=[rv.everywhere_ae, rv.abs_nonneg],
              name="hpos"),
        claim(rv.ae_subset(I, J), because=[rv.subset_ae, "hIJ"], name="hae"),
        claim(_int(I) <= _int(J), because=[rv.set_integral_mono_set, "hafJ", "hpos", "hae"],
              name="h1", note="I ⊆ J and |f| ≥ 0"),
        claim(0 < 2 * r, name="h2r"),
        claim(_int(J) <= alpha * rv.measure(J), name="h2", note="a ∉ {Mf > α}",
              proof=pl.proof(
                  pl.suppose_not(name="hneg"),
                  claim(alpha * rv.measure(J) < _int(J), because=[rv.not_le, "hneg"],
                        name="hgt"),
                  claim(rv.mem(a, E), name="haE", proof=_in_level_set(a, 2 * r, "hgt", "h2r")),
                  pl.conclude(because=["ha", "haE"]),
              )),
        claim(0 <= r, name="hr0"),
        claim(0 <= 2 * r, name="h2r0"),
        claim(rv.measure(I) == 2 * r, because=[rv.measure_interval, "hr0"], name="hmI"),
        claim(rv.measure(J) == 2 * (2 * r), because=[rv.measure_interval, "h2r0"], name="hmJ"),
        claim(alpha * rv.measure(J) == 2 * alpha * rv.measure(I), because=["hmJ", "hmI"],
              name="hαJ", note="|J| = 2|I|"),
        pl.conclude(because=["h1", "h2", "hαJ"]),
    )


interval_average = pl.Theorem(
    "cz_interval_average", [f, alpha, a, c, r],
    assumptions={"hf": rv.locally_integrable(f), "hr": r > 0,
                 "haI": rv.mem(a, rv.interval(c, r)), "ha": pl.Not(rv.mem(a, E))},
    conclusion=_int(rv.interval(c, r)) <= 2 * alpha * rv.measure(rv.interval(c, r)),
    proof=_interval_proof(),
)


# -----------------------------------------------------------------------------------------
# 16. |f| ≤ α almost everywhere off Ω
# -----------------------------------------------------------------------------------------
# For a.e. x the averages of |f| over [x − r, x + r] tend to |f(x)| (Lebesgue). If x ∉ Ω,
# every one of these averages is ≤ α, so the limit |f(x)| is ≤ α.

def _avg(p: object, rad: object) -> pl.Expr:
    return _int(rv.interval(p, rad)) / rv.measure(rv.interval(p, rad))


def _good_proof() -> pl.Tactic:
    claim, fix = pl.claim, pl.fix
    s = pl.symbol("s", pl.Real)
    lim = lambda p: rv.tendsto_zero_plus(lambda t: _avg(p, t), pl.abs(f(p)))  # noqa: E731
    return pl.proof(
        claim(rv.almost_every(lim), because=[rv.lebesgue_differentiation, "hf"], name="hdiff"),
        claim(pl.Forall(x, pl.Implies(lim(x), pl.Implies(pl.Not(rv.mem(x, E)),
                                                          pl.abs(f(x)) <= alpha))),
              name="hpt", note="at a point where the averages converge",
              proof=pl.proof(
                  fix(x, assume={"hlim": lim(x), "hx": pl.Not(rv.mem(x, E))}),
                  claim(pl.Forall(s, pl.Implies(s > 0, _avg(x, s) <= alpha)), name="hall",
                        note="x ∉ {Mf > α}: no average around x exceeds α",
                        proof=pl.proof(
                            fix(s, assume={"hs": s > 0}),
                            claim(_int(rv.interval(x, s)) <= alpha * rv.measure(rv.interval(x, s)),
                                  name="hle", proof=pl.proof(
                                      pl.suppose_not(name="hneg"),
                                      claim(alpha * rv.measure(rv.interval(x, s))
                                            < _int(rv.interval(x, s)),
                                            because=[rv.not_le, "hneg"], name="hgt"),
                                      claim(rv.mem(x, E), name="hxE",
                                            proof=_in_level_set(x, s, "hgt", "hs")),
                                      pl.conclude(because=["hx", "hxE"]),
                                  )),
                            claim(0 <= s, name="hs0"),
                            claim(rv.measure(rv.interval(x, s)) == 2 * s,
                                  because=[rv.measure_interval, "hs0"], name="hm"),
                            claim(rv.measure(rv.interval(x, s)) > 0, because="hm", name="hmpos"),
                            pl.conclude(because=[rv.div_le_iff, "hmpos", "hle"]),
                        )),
                  claim(rv.eventually_zero_plus(lambda t: _avg(x, t) <= alpha),
                        because=[rv.eventually_of_pos, "hall"], name="hev"),
                  pl.conclude(because=rv.le_of_tendsto("hlim", "hev"),
                              note="a limit of averages ≤ α is ≤ α"),
              )),
        pl.conclude(because=[rv.ae_mono, "hdiff", "hpt"]),
    )


good_part = pl.Theorem(
    "cz_good_part", [f, alpha],
    assumptions={"hf": rv.locally_integrable(f)},
    conclusion=rv.almost_every(lambda p: pl.Implies(pl.Not(rv.mem(p, E)),
                                                    pl.abs(f(p)) <= alpha)),
    proof=_good_proof(),
)


# -----------------------------------------------------------------------------------------
# 17. The Calderón–Zygmund decomposition
# -----------------------------------------------------------------------------------------

def _cz_proof() -> pl.Tactic:
    claim = pl.claim
    return pl.proof(
        claim(rv.is_open(E), because=[level_set_open, "hf", "hα"], note="theorem 7"),
        claim(rv.vol(E) <= rv.of_real(8 * rv.l1_norm(rv.cut(f, alpha / 2)) / alpha),
              because=[level_set_bound, "hf", "hg", "hα"], note="theorem 8"),
        claim(rv.almost_every(lambda p: pl.Implies(pl.Not(rv.mem(p, E)), pl.abs(f(p)) <= alpha)),
              because=[good_part, "hf"], note="theorem 16"),
        claim(pl.Forall([a, c, r], pl.Implies(r > 0, rv.mem(a, rv.interval(c, r)),
                                               pl.Not(rv.mem(a, E)),
                                               _int(rv.interval(c, r))
                                               <= 2 * alpha * rv.measure(rv.interval(c, r)))),
              because=[interval_average, "hf"], note="theorem 15"),
        pl.conclude(),
    )


decomposition = pl.Theorem(
    "calderon_zygmund", [f, alpha],
    assumptions={"hf": rv.locally_integrable(f), "hg": rv.integrable(rv.cut(f, alpha / 2)),
                 "hα": alpha > 0},
    conclusion=pl.And(
        rv.is_open(E),
        rv.vol(E) <= rv.of_real(8 * rv.l1_norm(rv.cut(f, alpha / 2)) / alpha),
        rv.almost_every(lambda p: pl.Implies(pl.Not(rv.mem(p, E)), pl.abs(f(p)) <= alpha)),
        pl.Forall([a, c, r], pl.Implies(r > 0, rv.mem(a, rv.interval(c, r)),
                                         pl.Not(rv.mem(a, E)),
                                         _int(rv.interval(c, r))
                                         <= 2 * alpha * rv.measure(rv.interval(c, r))))),
    proof=_cz_proof(),
)

THEOREMS = [interval_average, good_part, decomposition]

if __name__ == "__main__":
    results = pl.verify_all(THEOREMS, timeout=3600)
    ok = True
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
        if not res.verified:
            for d in res.errors[:4]:
                print("   ", d.span_label, "|", d.message[:400].replace("\n", " | "))
        ok = ok and res.verified
    sys.exit(0 if ok else 1)
