"""The intervals of an open set, and the Calderón–Zygmund intervals, as PyLeanX written proofs.

Stein, *Singular Integrals*, ch. I §3–4. An open set Ω ⊆ ℝ of finite measure falls apart into
disjoint open intervals (a, b) whose endpoints lie outside Ω. For Ω = {Mf > α} these are the
Calderón–Zygmund intervals: the average of |f| over each of them is at most 2α.

    22. Left endpoint: if U is open, x ∈ U and some y ≤ x lies outside U, then
        a = sup{y ≤ x : y ∉ U} satisfies a < x, a ∉ U, and (a, x] ⊆ U.
    23. Right endpoint: the same on the right, with b = inf{y ≥ x : y ∉ U}.
    24. Two such intervals that meet coincide: if a₁, b₁, a₂, b₂ ∉ U, (a₁, b₁) ⊆ U,
        (a₂, b₂) ⊆ U and the intervals share a point, then a₁ = a₂ and b₁ = b₂.
    25. If |U| < ∞, then U misses a point on each side of every x (half-lines have
        infinite measure).
    26. The Calderón–Zygmund intervals: for Ω = {Mf > α}, every x ∈ Ω lies in an interval
        (a, b) ⊆ Ω with a, b ∉ Ω and ∫_[a,b] |f| ≤ 2α(b − a).

Run:  python examples/cz_intervals.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import pyleanx as pl
from pyleanx import realvar as rv

sys.path.insert(0, str(Path(__file__).resolve().parent))
from calderon_zygmund import interval_average  # noqa: E402
from singular_integrals import level_set_bound, level_set_open  # noqa: E402

U = pl.symbol("U", rv.set_of(pl.Real))
x, y, z, a, b = pl.symbols("x y z a b", pl.Real)
a1, b1, a2, b2, z0 = pl.symbols("a₁ b₁ a₂ b₂ z₀", pl.Real)
f = pl.symbol("f", rv.RFun)
alpha = pl.symbol("α", pl.Real)
E = rv.level_set(f, alpha)


def _out_left(S: object) -> pl.Expr:
    """Some point ≤ x lies outside S."""
    return pl.Exists(y, pl.And(y <= x, pl.Not(rv.mem(y, S))))


def _out_right(S: object) -> pl.Expr:
    """Some point ≥ x lies outside S."""
    return pl.Exists(y, pl.And(x <= y, pl.Not(rv.mem(y, S))))


# -----------------------------------------------------------------------------------------
# 22–23. The endpoints of the interval of U around x
# -----------------------------------------------------------------------------------------
# The points ≤ x outside U form a closed set, bounded above by x; its supremum a belongs to
# it, so a ∉ U and a ≤ x (in fact a < x since x ∈ U). A point between a and x outside U
# would be ≤ a.

def _left_proof() -> pl.Tactic:
    claim = pl.claim
    L = rv.pred_set(lambda q: pl.And(q <= x, pl.Not(rv.mem(q, U))), pl.Real)
    s = rv.sup_of(L)
    return pl.proof(
        claim(rv.is_closed(L), because=[rv.left_part_closed, "hU"], name="hcl"),
        claim(rv.bdd_above(L), because=rv.left_part_bdd, name="hbdd"),
        claim(rv.nonempty(L), because="h", name="hne"),
        claim(rv.mem(s, L), because=[rv.closed_sup_mem, "hcl", "hne", "hbdd"], name="hmem"),
        claim(pl.And(s <= x, pl.Not(rv.mem(s, U))), because=[rv.mem_set_of, "hmem"],
              name="hs"),
        claim(s <= x, because="hs", name="hle"),
        claim(pl.Not(rv.mem(s, U)), because="hs", name="hout"),
        claim(x != s, because=rv.ne_of_mem_of_not_mem("hx", "hout"), name="hxs"),
        claim(s < x, because=[rv.lt_of_le_of_ne, "hle", "hxs"], name="hlt"),
        claim(pl.Forall(z, pl.Implies(s < z, z <= x, rv.mem(z, U))), name="hall",
              note="a point of (sup, x] outside U would be ≤ sup",
              proof=pl.proof(
                  pl.fix(z, assume={"hz1": s < z, "hz2": z <= x}),
                  pl.suppose_not(name="hzU"),
                  claim(rv.mem(z, L), because=[rv.mem_set_of, "hz2", "hzU"], name="hzL"),
                  claim(z <= s, because=[rv.le_sup, "hbdd", "hzL"], name="hzs"),
                  pl.conclude(because=["hz1", "hzs"]),
              )),
        pl.take(s),
        pl.conclude(because=["hlt", "hout", "hall"]),
    )


left_endpoint = pl.Theorem(
    "open_left_endpoint", [U, x],
    assumptions={"hU": rv.is_open(U), "hx": rv.mem(x, U), "h": _out_left(U)},
    conclusion=pl.Exists(a, pl.And(a < x, pl.Not(rv.mem(a, U)),
                                   pl.Forall(z, pl.Implies(a < z, z <= x, rv.mem(z, U))))),
    proof=_left_proof(),
)


def _right_proof() -> pl.Tactic:
    claim = pl.claim
    R = rv.pred_set(lambda q: pl.And(x <= q, pl.Not(rv.mem(q, U))), pl.Real)
    i = rv.inf_of(R)
    return pl.proof(
        claim(rv.is_closed(R), because=[rv.right_part_closed, "hU"], name="hcl"),
        claim(rv.bdd_below(R), because=rv.right_part_bdd, name="hbdd"),
        claim(rv.nonempty(R), because="h", name="hne"),
        claim(rv.mem(i, R), because=[rv.closed_inf_mem, "hcl", "hne", "hbdd"], name="hmem"),
        claim(pl.And(x <= i, pl.Not(rv.mem(i, U))), because=[rv.mem_set_of, "hmem"],
              name="hs"),
        claim(x <= i, because="hs", name="hge"),
        claim(pl.Not(rv.mem(i, U)), because="hs", name="hout"),
        claim(x != i, because=rv.ne_of_mem_of_not_mem("hx", "hout"), name="hxi"),
        claim(x < i, because=[rv.lt_of_le_of_ne, "hge", "hxi"], name="hlt"),
        claim(pl.Forall(z, pl.Implies(x <= z, z < i, rv.mem(z, U))), name="hall",
              note="a point of [x, inf) outside U would be ≥ inf",
              proof=pl.proof(
                  pl.fix(z, assume={"hz1": x <= z, "hz2": z < i}),
                  pl.suppose_not(name="hzU"),
                  claim(rv.mem(z, R), because=[rv.mem_set_of, "hz1", "hzU"], name="hzR"),
                  claim(i <= z, because=[rv.inf_le, "hbdd", "hzR"], name="hiz"),
                  pl.conclude(because=["hz2", "hiz"]),
              )),
        pl.take(i),
        pl.conclude(because=["hlt", "hout", "hall"]),
    )


right_endpoint = pl.Theorem(
    "open_right_endpoint", [U, x],
    assumptions={"hU": rv.is_open(U), "hx": rv.mem(x, U), "h": _out_right(U)},
    conclusion=pl.Exists(b, pl.And(x < b, pl.Not(rv.mem(b, U)),
                                   pl.Forall(z, pl.Implies(x <= z, z < b, rv.mem(z, U))))),
    proof=_right_proof(),
)


# -----------------------------------------------------------------------------------------
# 24. Two intervals of U that meet coincide
# -----------------------------------------------------------------------------------------
# If a₁ < a₂, then a₂ lies strictly inside (a₁, b₁) (it is below the common point), so
# a₂ ∈ U, which it is not. The same for the other three comparisons.

def _inside(p: object, lo: object, hi: object, name: str, out: str, lt: str) -> pl.Tactic:
    """lo < p < hi with (lo, hi) ⊆ U contradicts p ∉ U."""
    return pl.proof(
        pl.claim(rv.mem(p, U), because=[name, lt], name="hin"),
        pl.conclude(because=[out, "hin"]),
    )


def _meet_proof() -> pl.Tactic:
    claim, sn = pl.claim, pl.suppose_not
    return pl.proof(
        claim(a2 <= a1, name="h1", note="else a₂ would lie in (a₁, b₁)", proof=pl.proof(
            sn(name="hn"), claim(a1 < a2, because=[rv.not_le, "hn"], name="hlt"),
            _inside(a2, a1, b1, "hI1", "ha2", "hlt"))),
        claim(a1 <= a2, name="h2", note="else a₁ would lie in (a₂, b₂)", proof=pl.proof(
            sn(name="hn"), claim(a2 < a1, because=[rv.not_le, "hn"], name="hlt"),
            _inside(a1, a2, b2, "hI2", "ha1", "hlt"))),
        claim(b1 <= b2, name="h3", note="else b₂ would lie in (a₁, b₁)", proof=pl.proof(
            sn(name="hn"), claim(b2 < b1, because=[rv.not_le, "hn"], name="hlt"),
            _inside(b2, a1, b1, "hI1", "hb2", "hlt"))),
        claim(b2 <= b1, name="h4", note="else b₁ would lie in (a₂, b₂)", proof=pl.proof(
            sn(name="hn"), claim(b1 < b2, because=[rv.not_le, "hn"], name="hlt"),
            _inside(b1, a2, b2, "hI2", "hb1", "hlt"))),
        claim(a1 == a2, because=["h1", "h2"], name="ha"),
        claim(b1 == b2, because=["h3", "h4"], name="hb"),
        pl.conclude(),
    )


def _open_interval_in(lo: object, hi: object, S: object) -> pl.Expr:
    return pl.Forall(z, pl.Implies(lo < z, z < hi, rv.mem(z, S)))


intervals_meet = pl.Theorem(
    "open_intervals_meet", [U, a1, b1, a2, b2, z0],
    assumptions={"ha1": pl.Not(rv.mem(a1, U)), "hb1": pl.Not(rv.mem(b1, U)),
                 "hI1": _open_interval_in(a1, b1, U),
                 "ha2": pl.Not(rv.mem(a2, U)), "hb2": pl.Not(rv.mem(b2, U)),
                 "hI2": _open_interval_in(a2, b2, U),
                 "hz1": pl.And(a1 < z0, z0 < b1), "hz2": pl.And(a2 < z0, z0 < b2)},
    conclusion=pl.And(a1 == a2, b1 == b2),
    proof=_meet_proof(),
)


# -----------------------------------------------------------------------------------------
# 25. A set of finite measure misses a point on each side of x
# -----------------------------------------------------------------------------------------
# Otherwise (−∞, x] ⊆ U (or [x, ∞) ⊆ U), and |U| ≥ ∞.

def _side_proof(half: pl.Expr, mem_half: object, vol_half: object, le: object,
                missing: pl.Expr) -> pl.Tactic:
    claim = pl.claim
    return pl.proof(
        pl.suppose_not(name="hn"),
        claim(rv.subset(half, U), name="hsub", proof=pl.proof(
            pl.fix(y, assume={"hy": rv.mem(y, half)}),
            claim(le, because=[mem_half, "hy"], name="hyx"),
            pl.suppose_not(name="hyU"),
            claim(missing, name="hex",
                  proof=pl.proof(pl.take(y), pl.conclude(because=["hyx", "hyU"]))),
            pl.conclude(because=["hn", "hex"]),
        )),
        claim(rv.vol(half) <= rv.vol(U), because=[rv.measure_mono_ennreal, "hsub"],
              name="hmono"),
        claim(rv.vol(half) == rv.infinity(), because=vol_half, name="htop"),
        claim(rv.infinity() <= rv.vol(U), because=["hmono", "htop"], name="hle"),
        claim(pl.Not(rv.infinity() <= rv.vol(U)), because=[rv.not_le_of_gt, "hfin"],
              name="hnot"),
        pl.conclude(because=["hnot", "hle"]),
    )


finite_sides = pl.Theorem(
    "finite_measure_misses_both_sides", [U, x],
    assumptions={"hfin": rv.finite_measure(U)},
    conclusion=pl.And(_out_left(U), _out_right(U)),
    proof=pl.proof(
        pl.claim(_out_left(U), name="hl", note="(−∞, x] has infinite measure",
                 proof=_side_proof(rv.Iic(x), rv.mem_Iic, rv.volume_Iic, y <= x,
                                   _out_left(U))),
        pl.claim(_out_right(U), name="hr", note="[x, ∞) has infinite measure",
                 proof=_side_proof(rv.Ici(x), rv.mem_Ici, rv.volume_Ici, x <= y,
                                   _out_right(U))),
        pl.conclude(),
    ),
)


# -----------------------------------------------------------------------------------------
# 26. The Calderón–Zygmund intervals
# -----------------------------------------------------------------------------------------
# Ω = {Mf > α} is open (theorem 7) of finite measure (theorem 8), so by 22, 23 and 25 each
# x ∈ Ω lies in an interval (a, b) ⊆ Ω with a, b ∉ Ω. [a, b] contains the point a ∉ Ω, so
# by theorem 15 the average of |f| over [a, b] is at most 2α.

def _int(S: object) -> pl.Expr:
    return pl.integral(lambda w: pl.abs(f(w)), within=S)


def _cz_proof() -> pl.Tactic:
    claim = pl.claim
    c, r = (a + b) / 2, (b - a) / 2
    J = rv.interval(c, r)
    return pl.proof(
        claim(rv.is_open(E), because=[level_set_open, "hf", "hα"], name="hopen",
              note="theorem 7"),
        claim(rv.vol(E) <= rv.of_real(8 * rv.l1_norm(rv.cut(f, alpha / 2)) / alpha),
              because=[level_set_bound, "hf", "hg", "hα"], name="hvol", note="theorem 8"),
        claim(rv.finite_measure(E), because=[rv.lt_of_le_of_lt, "hvol", rv.of_real_lt_top],
              name="hfin"),
        claim(pl.And(_out_left(E), _out_right(E)), because=[finite_sides, "hfin"],
              name="hsides", note="theorem 25"),
        claim(_out_left(E), because="hsides", name="hl"),
        claim(_out_right(E), because="hsides", name="hr"),
        pl.choose(a, such_that=pl.And(a < x, pl.Not(rv.mem(a, E)),
                                      pl.Forall(z, pl.Implies(a < z, z <= x, rv.mem(z, E)))),
                  because=[left_endpoint, "hopen", "hx", "hl"], names="hax haE hla",
                  note="theorem 22"),
        pl.choose(b, such_that=pl.And(x < b, pl.Not(rv.mem(b, E)),
                                      pl.Forall(z, pl.Implies(x <= z, z < b, rv.mem(z, E)))),
                  because=[right_endpoint, "hopen", "hx", "hr"], names="hxb hbE hrb",
                  note="theorem 23"),
        claim(_open_interval_in(a, b, E), name="hmid", note="(a, x] and [x, b) lie in Ω",
              proof=pl.proof(
                  pl.fix(z, assume={"hz1": a < z, "hz2": z < b}),
                  pl.cases_on(
                      pl.case(z <= x, pl.conclude(because=["hla", "hz1", "h"]), name="h"),
                      pl.case(x <= z, pl.conclude(because=["hrb", "h", "hz2"]), name="h"),
                      because=rv.le_total),
              )),
        claim(r > 0, because=["hax", "hxb"], name="hr0"),
        claim(c - a == r, name="hcr"),
        claim(pl.abs(c - a) == c - a, because=[rv.abs_of_pos, "hcr", "hr0"], name="habs"),
        claim(rv.dist(c, a) == pl.abs(c - a), because=rv.real_dist, name="hdist",
              note="the distance from the centre to a"),
        claim(rv.dist(c, a) <= r, because=["hdist", "habs", "hcr"], name="hd"),
        claim(rv.mem(a, J), because=[rv.mem_interval, "hd"], name="haJ",
              note="a is the left end of [a, b]"),
        claim(_int(J) <= 2 * alpha * rv.measure(J),
              because=[interval_average, "hf", "hr0", "haJ", "haE"], name="h15",
              note="theorem 15: [a, b] contains a ∉ Ω"),
        claim(0 <= r, because="hr0", name="hr00"),
        claim(rv.measure(J) == 2 * r, because=[rv.measure_interval, "hr00"], name="hm"),
        claim(2 * alpha * rv.measure(J) == 2 * alpha * (b - a), because="hm", name="hm2"),
        claim(J == rv.Icc(a, b), because=rv.icc_as_interval, name="hJ"),
        claim(_int(rv.Icc(a, b)) == _int(J), because="hJ", name="hsame"),
        claim(_int(rv.Icc(a, b)) <= 2 * alpha * (b - a), because=["hsame", "h15", "hm2"],
              name="havg"),
        pl.take(a, b),
        pl.conclude(because=["hax", "hxb", "haE", "hbE", "hmid", "havg"]),
    )


cz_intervals = pl.Theorem(
    "calderon_zygmund_intervals", [f, alpha, x],
    assumptions={"hf": rv.locally_integrable(f), "hg": rv.integrable(rv.cut(f, alpha / 2)),
                 "hα": alpha > 0, "hx": rv.mem(x, E)},
    conclusion=pl.Exists([a, b], pl.And(a < x, x < b, pl.Not(rv.mem(a, E)),
                                        pl.Not(rv.mem(b, E)), _open_interval_in(a, b, E),
                                        _int(rv.Icc(a, b)) <= 2 * alpha * (b - a))),
    proof=_cz_proof(),
)

THEOREMS = [left_endpoint, right_endpoint, intervals_meet, finite_sides, cz_intervals]

if __name__ == "__main__":
    results = pl.verify_all(THEOREMS, timeout=3600)
    ok = True
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
        if not res.verified:
            for d in res.errors[:6]:
                print("   ", d.span_label, "|", d.message[:700].replace("\n", " | "))
        ok = ok and res.verified
    sys.exit(0 if ok else 1)
