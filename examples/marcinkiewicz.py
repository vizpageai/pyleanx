"""The Lᵖ bound for the maximal function (Stein, *Singular Integrals*, ch. I §1, Theorem 1(c)),
as PyLeanX written proofs checked by Lean.

From the weak-type bound of ``singular_integrals.py`` (theorem 8),
μ{Mf > t} ≤ 8 ∫|f·1{|f|>t/2}| / t, Stein integrates in t:

    p ∫₀^∞ t^{p−1} μ{Mf > t} dt ≤ 8p ∫₀^∞ t^{p−2} ∫|f|·1{|f|>t/2} dx dt
                               = 8p ∫ |f(x)| ∫₀^{2|f(x)|} t^{p−2} dt dx      (Tonelli)
                               = (8p·2^{p−1}/(p−1)) ∫ |f|^p,

and the left side is ‖Mf‖_p^p by the layer-cake formula. This file proves the computation:

9a. ∫₀^{2a} t^{p−2} dt = (2a)^{p−1}/(p−1)                      (the inner integral)
9b. p t^{p−1} · (8/t)·I = 8p t^{p−2} I, in [0, ∞]              (the weight)
9c. (2a)^{p−1} · a = 2^{p−1} a^p                                (the powers)

Run:  python examples/marcinkiewicz.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import realvar as rv

p, a, t, I_ = pl.symbols("p a t I", pl.Real)
rp = rv.rpow


# -----------------------------------------------------------------------------------------
# 9a. The inner integral
# -----------------------------------------------------------------------------------------

inner_integral = pl.Theorem(
    "inner_power_integral", [p, a],
    assumptions={"hp": 1 < p, "ha": 0 <= a},
    conclusion=pl.integral(lambda s: rp(s, p - 2), bounds=(0, 2 * a))
    == rp(2 * a, p - 1) / (p - 1),
    proof=pl.proof(
        pl.claim(-1 < p - 2, name="hr", note="p > 1"),
        pl.claim(pl.integral(lambda s: rp(s, p - 2), bounds=(0, 2 * a))
                 == (rp(2 * a, p - 2 + 1) - rp(pl.real(0), p - 2 + 1)) / (p - 2 + 1),
                 because=[rv.integral_rpow, rv.or_inl, "hr"], name="hint",
                 note="∫ t^r = t^{r+1}/(r+1) for r > −1"),
        pl.claim(p - 2 + 1 == p - 1, name="hexp"),
        pl.claim(p - 1 > 0, name="hp1"),
        pl.claim(p - 1 != 0, because=[rv.ne_of_gt, "hp1"], name="hp1ne"),
        pl.claim(rp(pl.real(0), p - 1) == 0, because=[rv.zero_rpow, "hp1ne"], name="hzero"),
        pl.conclude(because=["hexp", "hzero", rv.sub_zero, "hint"]),
    ),
)


# -----------------------------------------------------------------------------------------
# 9b. The weight: p t^{p−1} · (8/t) I = 8p t^{p−2} I  (in [0, ∞])
# -----------------------------------------------------------------------------------------

weight = pl.Theorem(
    "maximal_weight_algebra", [p, t, I_],
    assumptions={"hp": 1 < p, "ht": 0 < t, "hI": 0 <= I_},
    conclusion=rv.of_real(p * rp(t, p - 1)) * rv.of_real(8 / t * I_)
    == rv.of_real(8 * p * rp(t, p - 2) * I_),
    proof=pl.proof(
        pl.claim(t != 0, because=[rv.ne_of_gt, "ht"], name="ht0"),
        pl.claim(rp(t, p - 2 + 1) == rp(t, p - 2) * t, because=[rv.rpow_add_one, "ht0"],
                 name="hadd"),
        pl.claim(p - 2 + 1 == p - 1, name="hexp"),
        pl.claim(rp(t, p - 1) == rp(t, p - 2) * t, because=["hexp", "hadd"], name="hpow"),
        pl.claim(t * (8 / t) == 8, because=[rv.mul_div_cancel, "ht0"], name="hcancel"),
        pl.chain(p * (rp(t, p - 2) * t) * (8 / t * I_),
                 ("=", p * rp(t, p - 2) * (t * (8 / t)) * I_, None, "rearrange"),
                 ("=", p * rp(t, p - 2) * 8 * I_, "hcancel", "t · (8/t) = 8"),
                 ("=", 8 * p * rp(t, p - 2) * I_),
                 name="halg"),
        pl.claim(p * rp(t, p - 1) * (8 / t * I_) == 8 * p * rp(t, p - 2) * I_,
                 because=["hpow", "halg"], name="hreal"),
        pl.claim(0 <= t, name="ht_nn"),
        pl.claim(0 <= rp(t, p - 1), because=[rv.rpow_nonneg, "ht_nn"], name="hpow_nn"),
        pl.claim(0 <= p * rp(t, p - 1), because=[rv.mul_nonneg, "hpow_nn"], name="hw_nn"),
        pl.claim(rv.of_real(p * rp(t, p - 1) * (8 / t * I_))
                 == rv.of_real(p * rp(t, p - 1)) * rv.of_real(8 / t * I_),
                 because=[rv.of_real_mul, "hw_nn"], name="hmul"),
        pl.chain(rv.of_real(p * rp(t, p - 1)) * rv.of_real(8 / t * I_),
                 ("=", rv.of_real(p * rp(t, p - 1) * (8 / t * I_)), "hmul"),
                 ("=", rv.of_real(8 * p * rp(t, p - 2) * I_), "hreal")),
    ),
)


# -----------------------------------------------------------------------------------------
# 9c. The powers: (2a)^{p−1} · a = 2^{p−1} a^p
# -----------------------------------------------------------------------------------------

powers = pl.Theorem(
    "maximal_power_identity", [p, a],
    assumptions={"hp": 1 < p, "ha": 0 <= a},
    conclusion=rp(2 * a, p - 1) * a == rp(pl.real(2), p - 1) * rp(a, p),
    proof=pl.proof(
        pl.claim(rp(2 * a, p - 1) == rp(pl.real(2), p - 1) * rp(a, p - 1),
                 because=[rv.mul_rpow, "ha"], name="hsplit", note="(2a)^r = 2^r a^r"),
        pl.cases_on(
            pl.case(a == 0,
                    pl.claim(p != 0, name="hp0"),
                    pl.claim(p - 1 != 0, name="hp10"),
                    pl.claim(rp(a, p) == 0, because=["h", rv.zero_rpow, "hp0"]),
                    pl.claim(rp(a, p - 1) == 0, because=["h", rv.zero_rpow, "hp10"]),
                    pl.conclude(because=["hsplit", "h"]),
                    name="h"),
            pl.case(pl.Not(a == 0),
                    pl.claim(a != 0, because="h", name="ha0"),
                    pl.claim(rp(a, p - 1 + 1) == rp(a, p - 1) * a,
                             because=[rv.rpow_add_one, "ha0"], name="hadd"),
                    pl.claim(p - 1 + 1 == p, name="hexp"),
                    pl.claim(rp(a, p) == rp(a, p - 1) * a, because=["hexp", "hadd"],
                             name="hpow"),
                    pl.conclude(because=["hsplit", "hpow"]),
                    name="h"),
        ),
    ),
)

THEOREMS = [inner_integral, weight, powers]

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
