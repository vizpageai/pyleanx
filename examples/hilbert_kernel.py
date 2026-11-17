"""The Hilbert kernel 1/x away from its singularity, as PyLeanX written proofs checked by Lean.

Stein, *Singular Integrals*, ch. II §2–3. The weak type (1,1) bound for the Hilbert transform
applies the Calderón–Zygmund decomposition f = g + Σ bⱼ, where each bad part bⱼ lives on an
interval Iⱼ and has mean zero. Away from Iⱼ the kernel 1/(x − y) is smooth, and the mean zero
lets one subtract its value at the centre of Iⱼ. That gives a decay of order 1/|x − y₀|². Here
I = [y₀ − t, y₀ + t]:

    18. Smoothness of the kernel: if 2|y − y₀| ≤ |x − y₀|, then
        |1/(x − y) − 1/(x − y₀)| ≤ 2|y − y₀|/|x − y₀|².
    19. Cancellation: if ∫_I b = 0 and x lies outside I, then
        ∫_I b(y)/(x − y) dy = ∫_I (b(y)/(x − y) − b(y)/(x − y₀)) dy.
    20. Decay away from I: if ∫_I b = 0 and |x − y₀| > 2t, then
        |∫_I b(y)/(x − y) dy| ≤ (2t/|x − y₀|²) ∫_I |b|.
    21. Hörmander's estimate: away from 2I, the integral of |∫_I b(y)/(x − y) dy| is at most
        2∫_I |b|. Integrate 20 over |x − y₀| > 2t, using ∫_{|x−y₀|>s} dx/(x − y₀)² = 2/s.

Run:  python examples/hilbert_kernel.py
"""

from __future__ import annotations

import sys

import pyleanx as pl
from pyleanx import realvar as rv

b = pl.symbol("b", rv.RFun)
x, y, y0, t = pl.symbols("x y y₀ t", pl.Real)

I = rv.interval(y0, t)  # noqa: E741 - the interval of the book


def _k(p: object, q: object) -> pl.Expr:
    """The kernel 1/(p − q)."""
    return 1 / (p - q)


# -----------------------------------------------------------------------------------------
# 18. Smoothness of the kernel
# -----------------------------------------------------------------------------------------
# Subtract the fractions: 1/(x − y) − 1/(x − y₀) = (y − y₀)/((x − y)(x − y₀)). When y is
# close to y₀ compared with x, |x − y| ≥ |x − y₀|/2, so the denominator is ≥ |x − y₀|²/2.

def _smooth_proof() -> pl.Tactic:
    claim = pl.claim
    dx, dy, dxy = pl.abs(x - y0), pl.abs(y - y0), pl.abs(x - y)
    return pl.proof(
        claim(dx <= dxy + dy, because=rv.triangle, name="htri"),
        claim(dx / 2 <= dxy, because=["htri", "h"], name="hhalf",
              note="|y − y₀| ≤ |x − y₀|/2"),
        claim(dxy > 0, because=["hhalf", "h0"], name="hpos"),
        claim(x - y != 0, because=[rv.abs_pos, "hpos"], name="hne1"),
        claim(x - y0 != 0, because=[rv.abs_pos, "h0"], name="hne2"),
        claim(_k(x, y) - _k(x, y0) == (y - y0) / ((x - y) * (x - y0)),
              because=["hne1", "hne2"], name="heq", note="subtract the fractions"),
        claim(pl.abs(_k(x, y) - _k(x, y0)) == dy / (dxy * dx),
              because=["heq", rv.abs_div, rv.abs_mul], name="habs"),
        claim((dx / 2) * dx <= dxy * dx, because=[rv.mul_le_mul_right, "hhalf"], name="hden",
              note="the denominator is at least |x − y₀|²/2"),
        claim((dx / 2) * dx > 0, because="h0", name="hdpos"),
        claim(dy / (dxy * dx) <= dy / ((dx / 2) * dx),
              because=[rv.div_le_div_left, "hdpos", "hden"], name="hbound"),
        claim(dx != 0, because=[rv.ne_of_gt, "h0"], name="hdx"),
        claim(dy / ((dx / 2) * dx) == 2 * dy / dx ** 2, because="hdx", name="halg"),
        pl.conclude(because=["habs", "hbound", "halg"]),
    )


kernel_smooth = pl.Theorem(
    "hilbert_kernel_smooth", [x, y, y0],
    assumptions={"h": 2 * pl.abs(y - y0) <= pl.abs(x - y0), "h0": pl.abs(x - y0) > 0},
    conclusion=pl.abs(_k(x, y) - _k(x, y0)) <= 2 * pl.abs(y - y0) / pl.abs(x - y0) ** 2,
    proof=_smooth_proof(),
)


# -----------------------------------------------------------------------------------------
# 19. Cancellation
# -----------------------------------------------------------------------------------------
# ∫_I b(y)/(x − y₀) dy = (∫_I b)/(x − y₀) = 0, so subtracting it changes nothing.

def _bk(p: object) -> pl.Expr:
    return pl.integral(lambda w: b(w) / (p - w), within=I)


def _bdiff(p: object) -> pl.Expr:
    return pl.integral(lambda w: b(w) / (p - w) - b(w) / (p - y0), within=I)


def _cancel_proof() -> pl.Tactic:
    claim = pl.claim
    return pl.proof(
        claim(rv.integrable_on(pl.fun(lambda w: b(w) / (x - w), pl.Real), I),
              because=[rv.kernel_integrable, "hb", "hx"], name="hk"),
        claim(rv.integrable_on(pl.fun(lambda w: b(w) / (x - y0), pl.Real), I),
              because=[rv.integrable_div_const, "hb"], name="hk0"),
        claim(_bdiff(x) == _bk(x) - pl.integral(lambda w: b(w) / (x - y0), within=I),
              because=[rv.integral_sub, "hk", "hk0"], name="hsplit"),
        claim(pl.integral(lambda w: b(w) / (x - y0), within=I)
              == pl.integral(lambda w: b(w), within=I) / (x - y0),
              because=rv.integral_div, name="hdiv"),
        claim(pl.integral(lambda w: b(w) / (x - y0), within=I) == 0,
              because=["hdiv", "hmean"], name="hzero", note="b has mean zero on I"),
        pl.conclude(because=["hsplit", "hzero"]),
    )


cancellation = pl.Theorem(
    "hilbert_kernel_cancellation", [b, x, y0, t],
    assumptions={"hb": rv.integrable_on(b, I), "hx": t < pl.abs(x - y0),
                 "hmean": pl.integral(lambda w: b(w), within=I) == 0},
    conclusion=_bk(x) == _bdiff(x),
    proof=_cancel_proof(),
)


# -----------------------------------------------------------------------------------------
# 20. Decay away from I
# -----------------------------------------------------------------------------------------
# By 19, ∫_I b(y)/(x − y) dy = ∫_I b(y)(1/(x − y) − 1/(x − y₀)) dy, and by 18 the bracket is
# at most 2|y − y₀|/|x − y₀|² ≤ 2t/|x − y₀|² for y ∈ I.

def _decay_proof() -> pl.Tactic:
    claim, fix = pl.claim, pl.fix
    C = 2 * t / pl.abs(x - y0) ** 2
    dK = _k(x, y) - _k(x, y0)
    return pl.proof(
        claim(t < pl.abs(x - y0), because=["hx", "ht"], name="htx"),
        claim(_bk(x) == _bdiff(x), because=[cancellation, "hb", "htx", "hmean"],
              name="hcanc", note="theorem 19"),
        claim(pl.Forall(y, pl.Implies(rv.mem(y, I),
                                      pl.abs(b(y) / (x - y) - b(y) / (x - y0))
                                      <= pl.abs(b(y)) * C)),
              name="hpt", note="the kernel is smooth on I (theorem 18)",
              proof=pl.proof(
                  fix(y, assume={"hy": rv.mem(y, I)}),
                  claim(rv.dist(y, y0) <= t, because=[rv.mem_interval_dist, "hy"], name="hd"),
                  claim(pl.abs(y - y0) <= t, because=[rv.real_dist, "hd"], name="hyt"),
                  claim(2 * pl.abs(y - y0) <= pl.abs(x - y0), because=["hyt", "hx"],
                        name="h2"),
                  claim(pl.abs(x - y0) > 0, because=["hx", "ht"], name="h0"),
                  claim(pl.abs(dK) <= 2 * pl.abs(y - y0) / pl.abs(x - y0) ** 2,
                        because=[kernel_smooth, "h2", "h0"], name="hK", note="theorem 18"),
                  claim(b(y) / (x - y) - b(y) / (x - y0) == b(y) * dK, name="hfac"),
                  claim(pl.abs(b(y) / (x - y) - b(y) / (x - y0)) == pl.abs(b(y)) * pl.abs(dK),
                        because=["hfac", rv.abs_mul], name="habs"),
                  claim(2 * pl.abs(y - y0) / pl.abs(x - y0) ** 2 <= C,
                        because=[rv.div_le_div_right, "hyt"], name="hK2"),
                  claim(pl.abs(b(y)) * pl.abs(dK) <= pl.abs(b(y)) * C,
                        because=[rv.mul_le_mul_left, "hK", "hK2"], name="hmul"),
                  pl.conclude(because=["habs", "hmul"]),
              )),
        claim(rv.integrable_on(rv.abs_fun(b), I), because=[rv.integrable_abs, "hb"],
              name="hab"),
        claim(rv.integrable_on(pl.fun(lambda w: pl.abs(b(w)) * C, pl.Real), I),
              because=[rv.integrable_mul_const, "hab"], name="hgint"),
        claim(rv.measurable(I), because=rv.interval_measurable, name="hI"),
        claim(pl.abs(_bdiff(x)) <= pl.integral(lambda w: pl.abs(b(w)) * C, within=I),
              because=[rv.abs_integral_le, "hI", "hgint", "hpt"], name="hint"),
        claim(pl.integral(lambda w: pl.abs(b(w)) * C, within=I)
              == pl.integral(lambda w: pl.abs(b(w)), within=I) * C,
              because=rv.integral_mul_const, name="hpull"),
        claim(pl.abs(_bk(x)) == pl.abs(_bdiff(x)), because="hcanc", name="hsame"),
        pl.conclude(because=["hsame", "hint", "hpull"]),
    )


decay = pl.Theorem(
    "hilbert_kernel_decay", [b, x, y0, t],
    assumptions={"hb": rv.integrable_on(b, I), "ht": t > 0, "hx": 2 * t < pl.abs(x - y0),
                 "hmean": pl.integral(lambda w: b(w), within=I) == 0},
    conclusion=pl.abs(_bk(x))
    <= 2 * t / pl.abs(x - y0) ** 2 * pl.integral(lambda w: pl.abs(b(w)), within=I),
    proof=_decay_proof(),
)


# -----------------------------------------------------------------------------------------
# 21. Hörmander's estimate: the bad part is integrable away from 2I
# -----------------------------------------------------------------------------------------
# Integrate 20 over S = {|x − y₀| > 2t}: with A = ∫_I |b|,
#   ∫_S |∫_I b(y)/(x − y) dy| dx ≤ 2tA ∫_S dx/(x − y₀)² = 2tA · 2/(2t) = 2A.
# The left side is a [0, ∞]-valued integral, so no integrability has to be proved for it.

S = rv.pred_set(lambda u: 2 * t < pl.abs(u - y0), pl.Real)


def _hormander_proof() -> pl.Tactic:
    claim, fix = pl.claim, pl.fix
    u = pl.symbol("u", pl.Real)
    A = pl.integral(lambda w: pl.abs(b(w)), within=I)
    C = 2 * t * A
    k = lambda p: 1 / (p - y0) ** 2  # noqa: E731
    Ck = lambda p: C * k(p)  # noqa: E731
    return pl.proof(
        claim(2 * t > 0, because="ht", name="h2t"),
        claim(rv.measurable(S), because=rv.outside_measurable, name="hS"),
        claim(rv.measurable(I), because=rv.interval_measurable, name="hI"),
        claim(A >= 0, because=[rv.set_integral_nonneg, "hI"], name="hA"),
        claim(C >= 0, because=[rv.mul_nonneg, "h2t", "hA"], name="hC"),
        claim(pl.Forall(x, pl.Implies(rv.mem(x, S), rv.of_real(pl.abs(_bk(x)))
                                      <= rv.of_real(Ck(x)))),
              name="hpt", note="theorem 20 at each x with |x − y₀| > 2t",
              proof=pl.proof(
                  fix(x, assume={"hx": rv.mem(x, S)}),
                  claim(2 * t < pl.abs(x - y0), because="hx", name="hxo"),
                  claim(pl.abs(_bk(x)) <= 2 * t / pl.abs(x - y0) ** 2 * A,
                        because=[decay, "hb", "ht", "hxo", "hmean"], name="hd",
                        note="theorem 20"),
                  claim(2 * t / pl.abs(x - y0) ** 2 * A == Ck(x), because=rv.sq_abs,
                        name="heq"),
                  pl.conclude(because=[rv.of_real_le, "hd", "heq"]),
              )),
        claim(rv.lintegral(lambda p: rv.of_real(pl.abs(_bk(p))), within=S)
              <= rv.lintegral(lambda p: rv.of_real(Ck(p)), within=S),
              because=[rv.set_lintegral_mono, "hS", "hpt"], name="hmono"),
        claim(rv.integrable_on(pl.fun(k, pl.Real), S),
              because=[rv.integrable_inv_sq_outside, "h2t"], name="hk"),
        claim(rv.integrable_on(pl.fun(Ck, pl.Real), S),
              because=[rv.integrable_const_mul, "hk"], name="hCk"),
        claim(pl.Forall(u, 0 <= Ck(u)), name="hnn0",
              proof=pl.proof(fix(u), pl.conclude(because=[rv.mul_nonneg, "hC"]))),
        claim(rv.ae_nonneg_on(pl.fun(Ck, pl.Real), S), because=[rv.everywhere_ae, "hnn0"],
              name="hnn"),
        claim(rv.of_real(pl.integral(Ck, within=S))
              == rv.lintegral(lambda p: rv.of_real(Ck(p)), within=S),
              because=[rv.of_real_integral, "hCk", "hnn"], name="hofr",
              note="the same integral taken in [0, ∞]: the integrand is integrable and ≥ 0"),
        claim(pl.integral(Ck, within=S) == C * pl.integral(k, within=S),
              because=rv.integral_const_mul, name="hcm"),
        claim(pl.integral(k, within=S) == 2 / (2 * t),
              because=[rv.integral_inv_sq_outside, "h2t"], name="hval"),
        claim(C * pl.integral(k, within=S) == C * (2 / (2 * t)), because="hval", name="hsub"),
        claim(t != 0, because=[rv.ne_of_gt, "ht"], name="ht0"),
        claim(C * (2 / (2 * t)) == 2 * A, because="ht0", name="halg"),
        claim(pl.integral(Ck, within=S) == 2 * A, because=["hcm", "hsub", "halg"],
              name="htot"),
        pl.chain(rv.lintegral(lambda p: rv.of_real(pl.abs(_bk(p))), within=S),
                 ("<=", rv.lintegral(lambda p: rv.of_real(Ck(p)), within=S), "hmono"),
                 ("=", rv.of_real(pl.integral(Ck, within=S)), "hofr"),
                 ("=", rv.of_real(2 * A), "htot")),
    )


hormander = pl.Theorem(
    "hilbert_kernel_hormander", [b, y0, t],
    assumptions={"hb": rv.integrable_on(b, I), "ht": t > 0,
                 "hmean": pl.integral(lambda w: b(w), within=I) == 0},
    conclusion=rv.lintegral(lambda p: rv.of_real(pl.abs(_bk(p))), within=S)
    <= rv.of_real(2 * pl.integral(lambda w: pl.abs(b(w)), within=I)),
    proof=_hormander_proof(),
)

THEOREMS = [kernel_smooth, cancellation, decay, hormander]

if __name__ == "__main__":
    results = pl.verify_all(THEOREMS, timeout=3600)
    ok = True
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
        if not res.verified:
            for d in res.errors[:6]:
                print("   ", d.span_label, "|", d.message[:500].replace("\n", " | "))
        ok = ok and res.verified
    sys.exit(0 if ok else 1)
