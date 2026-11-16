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

from singular_integrals import level_set_bound

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

# -----------------------------------------------------------------------------------------
# 9e. The inner integral in t, for a fixed point x (a = |f(x)|)
# -----------------------------------------------------------------------------------------
# int_(0,oo) 8p t^(p-2) * (a 1{t < 2a}) dt = 8p a (2a)^(p-1)/(p-1)

def _ind(t: object) -> pl.Expr:
    return rv.indicator(rv.Iio(2 * a), pl.fun(lambda s: a, pl.Real))(t)


def _integrand(t: object) -> pl.Expr:
    return rv.of_real(8 * p * rp(t, p - 2) * _ind(t))


def _G(t: object) -> pl.Expr:  # noqa: N802
    return rv.indicator(rv.Iio(2 * a), pl.fun(lambda s: rv.of_real(8 * p * a * rp(s, p - 2)),
                                              pl.Real))(t)


def _G_plain(t: object) -> pl.Expr:  # noqa: N802
    return rv.of_real(8 * p * a * rp(t, p - 2))


def _h(s: object) -> pl.Expr:
    return 8 * p * a * rp(s, p - 2)


def _pw(s: object) -> pl.Expr:
    return rp(s, p - 2)


def _inner_proof() -> pl.Tactic:
    claim, fix, chain = pl.claim, pl.fix, pl.chain
    s_ = pl.symbol("s", pl.Real)
    Ioo = rv.Ioo(0, 2 * a)
    Ioc = rv.Ioc(0, 2 * a)
    in_ioi = rv.mem(t, rv.Ioi(0))
    case_in = pl.case(
        t < 2 * a,
        claim(rv.mem(t, rv.Iio(2 * a)), because=[rv.mem_Iio, "h"], name="hin"),
        claim(_ind(t) == a, because=[rv.indicator_of_mem, "hin"], name="hind"),
        claim(_G(t) == _G_plain(t), because=[rv.indicator_of_mem, "hin"], name="hG"),
        chain(_integrand(t),
              ("=", rv.of_real(8 * p * rp(t, p - 2) * a), "hind"),
              ("=", _G_plain(t), None, "rearrange"),
              ("=", _G(t), "hG")),
        name="h")
    case_out = pl.case(
        pl.Not(t < 2 * a),
        claim(pl.Not(rv.mem(t, rv.Iio(2 * a))), because=[rv.mem_Iio, "h"], name="hout"),
        claim(_ind(t) == 0, because=[rv.indicator_of_not_mem, "hout"], name="hind"),
        claim(_G(t) == 0, because=[rv.indicator_of_not_mem, "hout"], name="hG"),
        chain(_integrand(t),
              ("=", rv.of_real(8 * p * rp(t, p - 2) * 0), "hind"),
              ("=", 0, [rv.mul_zero, rv.of_real_zero]),
              ("=", _G(t), "hG")),
        name="h")
    return pl.proof(
        claim(pl.Forall(t, pl.Implies(in_ioi, _integrand(t) == _G(t))), name="hpt",
              note="on (0, oo) the integrand is 8pa t^(p-2) on (0, 2a) and 0 after",
              proof=pl.proof(fix(t, assume={"ht": in_ioi}), pl.cases_on(case_in, case_out))),
        claim(rv.lintegral(_integrand, within=rv.Ioi(0)) == rv.lintegral(_G, within=rv.Ioi(0)),
              because=[rv.set_lintegral_congr, rv.measurable_Ioi, "hpt"], name="h2"),
        claim(rv.lintegral(_G, within=rv.Ioi(0))
              == rv.lintegral_nested(_G_plain, within=rv.Iio(2 * a), inside=rv.Ioi(0)),
              because=[rv.lintegral_indicator, rv.measurable_Iio], name="h3"),
        claim(rv.lintegral_nested(_G_plain, within=rv.Iio(2 * a), inside=rv.Ioi(0))
              == rv.lintegral(_G_plain, within=Ioo),
              because=[rv.restrict_restrict, rv.measurable_Iio, rv.iio_inter_ioi], name="h4",
              note="(-oo, 2a) and (0, oo) meet in (0, 2a)"),
        claim(-1 < p - 2, name="hr"),
        claim(rv.interval_integrable(pl.fun(_pw, pl.Real), 0, 2 * a),
              because=[rv.rpow_interval_integrable, "hr"], name="hii"),
        claim(0 <= 2 * a, name="h2a"),
        claim(rv.integrable_on(pl.fun(_pw, pl.Real), Ioc),
              because=[rv.interval_integrable_Ioc, "h2a", "hii"], name="hioc"),
        claim(rv.integrable_on(pl.fun(_pw, pl.Real), Ioo),
              because=[rv.integrable_on_mono, "hioc", rv.ioo_sub_ioc], name="hioo"),
        claim(rv.integrable_on(pl.fun(_h, pl.Real), Ioo),
              because=[rv.integrable_const_mul, "hioo"], name="hint"),
        claim(0 <= 8 * p, name="h8p"),
        claim(0 <= 8 * p * a, because=[rv.mul_nonneg, "h8p", "ha"], name="hc0"),
        claim(pl.Forall(s_, pl.Implies(rv.mem(s_, Ioo), 0 <= _h(s_))), name="hpos",
              proof=pl.proof(
                  fix(s_, assume={"hs": rv.mem(s_, Ioo)}),
                  claim(0 < s_, because="hs", name="hs_pos"),
                  claim(0 <= s_, name="hs0"),
                  claim(0 <= rp(s_, p - 2), because=[rv.rpow_nonneg, "hs0"], name="hsp"),
                  pl.conclude(because=[rv.mul_nonneg, "hc0", "hsp"]),
              )),
        claim(rv.ae_nonneg_on(pl.fun(_h, pl.Real), Ioo),
              because=[rv.ae_on_set, rv.measurable_Ioo, "hpos"], name="hnn"),
        claim(rv.of_real(pl.integral(_h, within=Ioo)) == rv.lintegral(_G_plain, within=Ioo),
              because=[rv.of_real_integral, "hint", "hnn"], name="h8"),
        claim(pl.integral(_h, within=Ioc) == pl.integral(_h, within=Ioo),
              because=rv.integral_ioc_ioo, name="h9"),
        claim(pl.integral(_h, bounds=(0, 2 * a)) == pl.integral(_h, within=Ioc),
              because=[rv.interval_integral_ioc, "h2a"], name="h10"),
        claim(pl.integral(_h, bounds=(0, 2 * a))
              == 8 * p * a * pl.integral(_pw, bounds=(0, 2 * a)),
              because=rv.interval_const_mul, name="h11"),
        claim(pl.integral(_pw, bounds=(0, 2 * a)) == rp(2 * a, p - 1) / (p - 1),
              because=[inner_integral, "hp", "ha"], name="h12", note="lemma 9a"),
        chain(rv.lintegral(_integrand, within=rv.Ioi(0)),
              ("=", rv.lintegral(_G, within=rv.Ioi(0)), "h2"),
              ("=", rv.lintegral_nested(_G_plain, within=rv.Iio(2 * a), inside=rv.Ioi(0)), "h3"),
              ("=", rv.lintegral(_G_plain, within=Ioo), "h4"),
              ("=", rv.of_real(pl.integral(_h, within=Ioo)), "h8"),
              ("=", rv.of_real(pl.integral(_h, within=Ioc)), "h9"),
              ("=", rv.of_real(pl.integral(_h, bounds=(0, 2 * a))), "h10"),
              ("=", rv.of_real(8 * p * a * pl.integral(_pw, bounds=(0, 2 * a))), "h11"),
              ("=", rv.of_real(8 * p * a * (rp(2 * a, p - 1) / (p - 1))), "h12")),
    )


inner_t_integral = pl.Theorem(
    "maximal_inner_t_integral", [p, a],
    assumptions={"hp": 1 < p, "ha": 0 <= a},
    conclusion=rv.lintegral(_integrand, within=rv.Ioi(0))
    == rv.of_real(8 * p * a * (rp(2 * a, p - 1) / (p - 1))),
    proof=_inner_proof(),
)

# -----------------------------------------------------------------------------------------
# 9d. The bound at a fixed level t: the weight times the level-set bound is one integral
# -----------------------------------------------------------------------------------------
# p t^(p-1) * 8 (int |g_t|) / t = int 8p t^(p-2) |g_t(x)| dx   (in [0, oo]), g_t = f 1{|f| > t/2}

f = pl.symbol("f", rv.RFun)


def _g(tt: object) -> pl.Expr:
    return rv.cut(f, tt / 2)


def _level_proof() -> pl.Tactic:
    claim, chain = pl.claim, pl.chain
    g = _g(t)
    norm_g = rv.l1_norm(g)
    c = 8 * p * rp(t, p - 2)
    xx = pl.symbol("x", pl.Real)
    return pl.proof(
        claim(rv.ae_nonneg(rv.abs_fun(g)), because=[rv.everywhere_ae, rv.abs_nonneg], name="hg0"),
        claim(0 <= norm_g, because=[rv.integral_nonneg_ae, "hg0"], name="hI"),
        claim(rv.of_real(8 * norm_g / t) == rv.of_real(8 / t * norm_g), name="hform",
              note="8I/t = (8/t)I"),
        claim(rv.of_real(p * rp(t, p - 1)) * rv.of_real(8 / t * norm_g)
              == rv.of_real(c * norm_g), because=[weight, "hp", "ht", "hI"], name="hw",
              note="lemma 9b"),
        claim(pl.integral(lambda w: c * pl.abs(g(w))) == c * norm_g,
              because=rv.integral_const_mul, name="hconst"),
        claim(rv.integrable(rv.abs_fun(g)), because=[rv.integrable_abs, "hg"], name="hgi"),
        claim(rv.integrable(pl.fun(lambda w: c * pl.abs(g(w)), pl.Real)),
              because=[rv.integrable_const_mul, "hgi"], name="hci"),
        claim(0 <= t, name="ht0"),
        claim(0 <= rp(t, p - 2), because=[rv.rpow_nonneg, "ht0"], name="htp"),
        claim(0 <= 8 * p, name="h8p"),
        claim(0 <= c, because=[rv.mul_nonneg, "h8p", "htp"], name="hc"),
        claim(pl.Forall(xx, 0 <= c * pl.abs(g(xx))), name="hpt",
              proof=pl.proof(
                  pl.fix(xx),
                  claim(0 <= pl.abs(g(xx)), because=rv.abs_nonneg, name="hpt_abs"),
                  pl.conclude(because=[rv.mul_nonneg, "hc", "hpt_abs"]),
              )),
        claim(rv.ae_nonneg(pl.fun(lambda w: c * pl.abs(g(w)), pl.Real)),
              because=[rv.everywhere_ae, "hpt"], name="hcnn"),
        claim(rv.of_real(pl.integral(lambda w: c * pl.abs(g(w))))
              == rv.lintegral(lambda w: rv.of_real(c * pl.abs(g(w)))),
              because=[rv.of_real_integral, "hci", "hcnn"], name="hlin"),
        chain(rv.of_real(p * rp(t, p - 1)) * rv.of_real(8 * norm_g / t),
              ("=", rv.of_real(p * rp(t, p - 1)) * rv.of_real(8 / t * norm_g), "hform"),
              ("=", rv.of_real(c * norm_g), "hw"),
              ("=", rv.of_real(pl.integral(lambda w: c * pl.abs(g(w)))), "hconst"),
              ("=", rv.lintegral(lambda w: rv.of_real(c * pl.abs(g(w)))), "hlin")),
    )


level_integral = pl.Theorem(
    "maximal_level_integral", [f, p, t],
    assumptions={"hp": 1 < p, "ht": 0 < t, "hg": rv.integrable(_g(t))},
    conclusion=rv.of_real(p * rp(t, p - 1)) * rv.of_real(8 * rv.l1_norm(_g(t)) / t)
    == rv.lintegral(lambda w: rv.of_real(8 * p * rp(t, p - 2) * pl.abs(_g(t)(w)))),
    proof=_level_proof(),
)

# -----------------------------------------------------------------------------------------
# 9. The Lp bound: p int_0^oo t^(p-1) mu{Mf > t} dt <= (8p 2^(p-1)/(p-1)) int |f|^p
# -----------------------------------------------------------------------------------------
# By the layer-cake formula the left side is the p-th power of the Lp norm of Mf.

x = pl.symbol("x", pl.Real)
q = pl.symbol("q", pl.Prod(pl.Real, pl.Real))
CONST = 8 * p * rp(pl.real(2), p - 1) / (p - 1)


def _F(tt: object, xx: object) -> pl.Expr:  # noqa: N802
    return rv.of_real(8 * p * rp(tt, p - 2) * pl.abs(rv.cut(f, tt / 2)(xx)))


def _prodset() -> pl.Expr:
    return rv.pred_set(lambda r: pl.field(r, "1") / 2 < pl.abs(f(pl.field(r, "2"))),
                       pl.Prod(pl.Real, pl.Real))


def _prod_ind(qq: object) -> pl.Expr:
    return rv.indicator(_prodset(), pl.fun(lambda r: pl.abs(f(pl.field(r, "2"))),
                                           pl.Prod(pl.Real, pl.Real)))(qq)


def _Gq(qq: object) -> pl.Expr:  # noqa: N802
    return rv.of_real(8 * p * rp(pl.field(qq, "1"), p - 2) * _prod_ind(qq))


def _int9e(tt: object, aa: object) -> pl.Expr:
    return rv.of_real(8 * p * rp(tt, p - 2)
                      * rv.indicator(rv.Iio(2 * aa), pl.fun(lambda s: aa, pl.Real))(tt))


def _lp_proof() -> pl.Tactic:
    claim, fix, chain, case, cases_on = pl.claim, pl.fix, pl.chain, pl.case, pl.cases_on
    Ioi0 = rv.Ioi(0)
    w = lambda tt: rv.of_real(p * rp(tt, p - 1))  # noqa: E731
    E = lambda tt: rv.level_set(f, tt)  # noqa: E731
    mu = rv.volume_on_half_line_times_line()
    F2 = pl.fun(lambda tt, xx: _F(tt, xx), [pl.Real, pl.Real])
    G = pl.fun(_Gq, pl.Prod(pl.Real, pl.Real))
    q1, q2 = pl.field(q, "1"), pl.field(q, "2")
    a_x = pl.abs(f(x))
    final = lambda xx: rv.of_real(8 * p * pl.abs(f(xx))  # noqa: E731
                                  * (rp(2 * pl.abs(f(xx)), p - 1) / (p - 1)))
    return pl.proof(
        # 1. the level-set bound at every t > 0 (theorem 8 and lemma 9d)
        claim(pl.Forall(t, pl.Implies(rv.mem(t, Ioi0), w(t) * rv.vol(E(t))
                                      <= rv.lintegral(lambda xx: _F(t, xx)))),
              name="hstep", note="theorem 8 at level t, then lemma 9d",
              proof=pl.proof(
                  fix(t, assume={"ht": rv.mem(t, Ioi0)}),
                  claim(0 < t, because=[rv.mem_Ioi, "ht"], name="ht0"),
                  claim(rv.integrable(rv.cut(f, t / 2)), because=["hg", "ht0"], name="hgt"),
                  claim(rv.vol(E(t)) <= rv.of_real(8 * rv.l1_norm(rv.cut(f, t / 2)) / t),
                        because=[level_set_bound, "hloc", "hgt", "ht0"], name="hE"),
                  chain(w(t) * rv.vol(E(t)),
                        ("<=", w(t) * rv.of_real(8 * rv.l1_norm(rv.cut(f, t / 2)) / t),
                         [rv.mul_le_mul_left_ennreal, "hE"]),
                        ("=", rv.lintegral(lambda xx: _F(t, xx)),
                         [level_integral, "hp", "ht0", "hgt"])),
              )),
        claim(rv.lintegral(lambda tt: w(tt) * rv.vol(E(tt)), within=Ioi0)
              <= rv.lintegral(lambda tt: rv.lintegral(lambda xx: _F(tt, xx)), within=Ioi0),
              because=[rv.set_lintegral_mono, rv.measurable_Ioi, "hstep"], name="hmono"),
        # 2. measurability on (0, oo) x R, through the product-set form of the truncation
        claim(pl.Forall(q, _F(q1, q2) == _Gq(q)), name="hbridge",
              note="|f 1{|f|>t/2}(x)| = 1{t/2 < |f(x)|} |f(x)|",
              proof=pl.proof(
                  fix(q),
                  cases_on(
                      case(q1 / 2 < pl.abs(f(q2)),
                           claim(rv.mem(q2, rv.above(f, q1 / 2)), because=[rv.mem_set_of, "h"],
                                 name="hin1"),
                           claim(rv.cut(f, q1 / 2)(q2) == f(q2),
                                 because=[rv.indicator_of_mem, "hin1"], name="hcut"),
                           claim(rv.mem(q, _prodset()), because=[rv.mem_set_of, "h"], name="hin2"),
                           claim(_prod_ind(q) == pl.abs(f(q2)),
                                 because=[rv.indicator_of_mem, "hin2"], name="hind"),
                           chain(_F(q1, q2),
                                 ("=", rv.of_real(8 * p * rp(q1, p - 2) * pl.abs(f(q2))), "hcut"),
                                 ("=", _Gq(q), "hind")),
                           name="h"),
                      case(pl.Not(q1 / 2 < pl.abs(f(q2))),
                           claim(pl.Not(rv.mem(q2, rv.above(f, q1 / 2))),
                                 because=[rv.mem_set_of, "h"], name="hout1"),
                           claim(rv.cut(f, q1 / 2)(q2) == 0,
                                 because=[rv.indicator_of_not_mem, "hout1"], name="hcut"),
                           claim(pl.Not(rv.mem(q, _prodset())), because=[rv.mem_set_of, "h"],
                                 name="hout2"),
                           claim(_prod_ind(q) == 0, because=[rv.indicator_of_not_mem, "hout2"],
                                 name="hind"),
                           chain(_F(q1, q2),
                                 ("=", rv.of_real(8 * p * rp(q1, p - 2) * pl.abs(pl.real(0))),
                                  "hcut"),
                                 ("=", rv.of_real(8 * p * rp(q1, p - 2) * 0), rv.abs_zero),
                                 ("=", _Gq(q), "hind")),
                           name="h"),
                  ),
              )),
        claim(rv.measurable_fn(pl.fun(lambda r: pl.abs(f(pl.field(r, "2"))),
                                      pl.Prod(pl.Real, pl.Real))), name="hm_abs"),
        claim(rv.measurable_fn(pl.fun(lambda r: pl.field(r, "1") / 2,
                                      pl.Prod(pl.Real, pl.Real))), name="hm_half"),
        claim(rv.measurable(_prodset()), because=[rv.measurable_set_lt, "hm_half", "hm_abs"],
              name="hm_set"),
        claim(rv.measurable_fn(pl.fun(_prod_ind, pl.Prod(pl.Real, pl.Real))),
              because=[rv.measurable_indicator, "hm_abs", "hm_set"], name="hm_ind"),
        claim(rv.measurable_fn(pl.fun(lambda r: 8 * p * rp(pl.field(r, "1"), p - 2),
                                      pl.Prod(pl.Real, pl.Real))), name="hm_pow"),
        claim(rv.measurable_fn(pl.fun(lambda r: 8 * p * rp(pl.field(r, "1"), p - 2)
                                      * _prod_ind(r), pl.Prod(pl.Real, pl.Real))),
              because=[rv.measurable_mul, "hm_pow", "hm_ind"], name="hm_prod"),
        claim(rv.measurable_fn(G), because=[rv.measurable_of_real, "hm_prod"], name="hm_G"),
        claim(rv.uncurry(F2) == G, because=[rv.fun_ext, "hbridge"], name="heq"),
        claim(rv.ae_measurable(G, mu), because=[rv.measurable_ae, "hm_G"], name="hae_G"),
        claim(rv.ae_measurable(rv.uncurry(F2), mu), because=["heq", "hae_G"], name="hae"),
        # 3. Tonelli
        claim(rv.lintegral(lambda tt: rv.lintegral(lambda xx: _F(tt, xx)), within=Ioi0)
              == rv.lintegral(lambda xx: rv.lintegral(lambda tt: _F(tt, xx), within=Ioi0)),
              because=[rv.tonelli, "hae"], name="hswap", note="Tonelli"),
        # 4. the inner integral in t for each x (lemma 9e with a = |f(x)|)
        claim(pl.Forall(x, rv.lintegral(lambda tt: _F(tt, x), within=Ioi0) == final(x)),
              name="hinner", note="lemma 9e with a = |f(x)|",
              proof=pl.proof(
                  fix(x),
                  claim(pl.Forall(t, pl.Implies(rv.mem(t, Ioi0), _F(t, x) == _int9e(t, a_x))),
                        name="htr", note="t/2 < |f(x)| iff t < 2|f(x)|",
                        proof=pl.proof(
                            fix(t, assume={"ht": rv.mem(t, Ioi0)}),
                            cases_on(
                                case(t / 2 < a_x,
                                     claim(t < 2 * a_x, name="h2"),
                                     claim(rv.mem(x, rv.above(f, t / 2)),
                                           because=[rv.mem_set_of, "h"], name="hin1"),
                                     claim(rv.cut(f, t / 2)(x) == f(x),
                                           because=[rv.indicator_of_mem, "hin1"], name="hcut"),
                                     claim(rv.mem(t, rv.Iio(2 * a_x)), because=[rv.mem_Iio, "h2"],
                                           name="hin2"),
                                     claim(rv.indicator(rv.Iio(2 * a_x),
                                                        pl.fun(lambda s: a_x, pl.Real))(t) == a_x,
                                           because=[rv.indicator_of_mem, "hin2"], name="hind"),
                                     chain(_F(t, x),
                                           ("=", rv.of_real(8 * p * rp(t, p - 2) * a_x), "hcut"),
                                           ("=", _int9e(t, a_x), "hind")),
                                     name="h"),
                                case(pl.Not(t / 2 < a_x),
                                     claim(pl.Not(t < 2 * a_x), name="h2"),
                                     claim(pl.Not(rv.mem(x, rv.above(f, t / 2))),
                                           because=[rv.mem_set_of, "h"], name="hout1"),
                                     claim(rv.cut(f, t / 2)(x) == 0,
                                           because=[rv.indicator_of_not_mem, "hout1"],
                                           name="hcut"),
                                     claim(pl.Not(rv.mem(t, rv.Iio(2 * a_x))),
                                           because=[rv.mem_Iio, "h2"], name="hout2"),
                                     claim(rv.indicator(rv.Iio(2 * a_x),
                                                        pl.fun(lambda s: a_x, pl.Real))(t) == 0,
                                           because=[rv.indicator_of_not_mem, "hout2"],
                                           name="hind"),
                                     chain(_F(t, x),
                                           ("=", rv.of_real(8 * p * rp(t, p - 2)
                                                            * pl.abs(pl.real(0))), "hcut"),
                                           ("=", rv.of_real(8 * p * rp(t, p - 2) * 0),
                                            rv.abs_zero),
                                           ("=", _int9e(t, a_x), "hind")),
                                     name="h"),
                            ),
                        )),
                  claim(rv.lintegral(lambda tt: _F(tt, x), within=Ioi0)
                        == rv.lintegral(lambda tt: _int9e(tt, a_x), within=Ioi0),
                        because=[rv.set_lintegral_congr, rv.measurable_Ioi, "htr"],
                        name="hcongr9"),
                  claim(0 <= a_x, because=rv.abs_nonneg, name="ha0"),
                  claim(rv.lintegral(lambda tt: _int9e(tt, a_x), within=Ioi0) == final(x),
                        because=[inner_t_integral, "hp", "ha0"], name="h9e"),
                  chain(rv.lintegral(lambda tt: _F(tt, x), within=Ioi0),
                        ("=", rv.lintegral(lambda tt: _int9e(tt, a_x), within=Ioi0), "hcongr9"),
                        ("=", final(x), "h9e")),
              )),
        claim(rv.lintegral(lambda xx: rv.lintegral(lambda tt: _F(tt, xx), within=Ioi0))
              == rv.lintegral(final), because=[rv.lintegral_congr, "hinner"], name="hcongr"),
        # 5. the constants (lemma 9c)
        claim(0 <= CONST, name="hC0", note="p > 1",
              proof=pl.proof(
                  claim(0 < rp(pl.real(2), p - 1), name="h2p", because=rv.rpow_pos_two),
                  claim(0 < p - 1, name="hp1"),
                  pl.conclude(because=[rv.div_nonneg, rv.mul_nonneg]),
              )),
        claim(pl.Forall(x, final(x) == rv.of_real(CONST) * rv.of_real(rp(a_x, p))),
              name="halg", note="8p a (2a)^(p-1)/(p-1) = C a^p by lemma 9c",
              proof=pl.proof(
                  fix(x),
                  claim(0 <= a_x, because=rv.abs_nonneg, name="ha0"),
                  claim(rp(2 * a_x, p - 1) * a_x == rp(pl.real(2), p - 1) * rp(a_x, p),
                        because=[powers, "hp", "ha0"], name="h9c"),
                  chain(8 * p * a_x * (rp(2 * a_x, p - 1) / (p - 1)),
                        ("=", 8 * p / (p - 1) * (rp(2 * a_x, p - 1) * a_x), None, "rearrange"),
                        ("=", 8 * p / (p - 1) * (rp(pl.real(2), p - 1) * rp(a_x, p)), "h9c"),
                        ("=", CONST * rp(a_x, p)),
                        name="hreal"),
                  chain(final(x),
                        ("=", rv.of_real(CONST * rp(a_x, p)), "hreal"),
                        ("=", rv.of_real(CONST) * rv.of_real(rp(a_x, p)),
                         [rv.of_real_mul, "hC0"])),
              )),
        claim(rv.lintegral(final)
              == rv.lintegral(lambda xx: rv.of_real(CONST) * rv.of_real(rp(pl.abs(f(xx)), p))),
              because=[rv.lintegral_congr, "halg"], name="hcongr2"),
        claim(rv.lintegral(lambda xx: rv.of_real(CONST) * rv.of_real(rp(pl.abs(f(xx)), p)))
              == rv.of_real(CONST) * rv.lintegral(lambda xx: rv.of_real(rp(pl.abs(f(xx)), p))),
              because=[rv.lintegral_const_mul, rv.of_real_ne_top], name="hpull"),
        chain(rv.lintegral(lambda tt: w(tt) * rv.vol(E(tt)), within=Ioi0),
              ("<=", rv.lintegral(lambda tt: rv.lintegral(lambda xx: _F(tt, xx)), within=Ioi0),
               "hmono"),
              ("=", rv.lintegral(lambda xx: rv.lintegral(lambda tt: _F(tt, xx), within=Ioi0)),
               "hswap"),
              ("=", rv.lintegral(final), "hcongr"),
              ("=", rv.lintegral(lambda xx: rv.of_real(CONST) * rv.of_real(rp(pl.abs(f(xx)), p))),
               "hcongr2"),
              ("=", rv.of_real(CONST) * rv.lintegral(lambda xx: rv.of_real(rp(pl.abs(f(xx)), p))),
               "hpull")),
    )


maximal_Lp = pl.Theorem(
    "hardy_littlewood_Lp", [f, p],
    assumptions={"hp": 1 < p, "hfm": rv.measurable_fn(f), "hloc": rv.locally_integrable(f),
                 "hg": pl.Forall(t, pl.Implies(0 < t, rv.integrable(rv.cut(f, t / 2))))},
    conclusion=rv.lintegral(lambda t: rv.of_real(p * rp(t, p - 1))
                            * rv.vol(rv.level_set(f, t)), within=rv.Ioi(0))
    <= rv.of_real(CONST) * rv.lintegral(lambda x: rv.of_real(rp(pl.abs(f(x)), p))),
    proof=_lp_proof(),
)

THEOREMS = [inner_integral, weight, powers, inner_t_integral, level_integral, maximal_Lp]

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
