"""Chapter: an interval meeting {Mf ≤ α} has average at most 2α (Calderón–Zygmund).

Stein, *Singular Integrals*, ch. I §3. Let f be locally integrable and Ω = {Mf > α}: the
points x with an interval [x − ρ, x + ρ] on which the average of |f| exceeds α. If
a ∈ I = [c − r, c + r] and a ∉ Ω, then ∫_I |f| ≤ 2α|I|. The proof, as Stein gives it: I lies
inside J = [a − 2r, a + 2r]; J has average at most α because a ∉ Ω; and |J| = 2|I|.

PyLeanX's core example (``examples/calderon_zygmund.py``) proves the same theorem in 16
steps, 7 of them side conditions (f and |f| integrable on J, |f| ≥ 0 a.e., I ⊆ J a.e.,
2r > 0, r ≥ 0, 2r ≥ 0). With this package imported they are supplied by its rules, and the
proof below is the textbook's. Lean checks it:
``python -m pyleanx_analysis.chapters.calderon_zygmund``.
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import realvar as rv

f = pl.symbol("f", rv.RFun)
alpha, a, c, r, rho = pl.symbols("α a c r ρ", pl.Real)

#: Ω = {Mf > α}
omega = rv.level_set(f, alpha)


def _int(S: object) -> pl.Expr:
    return pl.integral(lambda w: pl.abs(f(w)), within=S)


I, J = rv.interval(c, r), rv.interval(a, 2 * r)  # noqa: E741

interval_average = pl.Theorem(
    "cz_interval_average_textbook", [f, alpha, a, c, r],
    assumptions={"hf": rv.locally_integrable(f), "hr": r > 0,
                 "haI": rv.mem(a, I), "ha": pl.Not(rv.mem(a, omega))},
    conclusion=_int(I) <= 2 * alpha * rv.measure(I),
    proof=pl.proof(
        pl.claim(rv.dist(c, a) <= r, because=[rv.mem_interval, "haI"], name="hca"),
        pl.claim(r + rv.dist(c, a) <= 2 * r, name="hsum"),
        pl.claim(rv.subset(I, J), because=[rv.interval_in_interval, "hsum"], name="hIJ",
                 note="a ∈ I, so I ⊆ [a − 2r, a + 2r]"),
        pl.claim(_int(I) <= _int(J), because=rv.set_integral_mono_set, name="h1",
                 note="I ⊆ J and |f| ≥ 0"),
        pl.claim(_int(J) <= alpha * rv.measure(J), name="h2", note="a ∉ {Mf > α}",
                 proof=pl.proof(
                     pl.suppose_not(name="hneg"),
                     pl.claim(alpha * rv.measure(J) < _int(J), because=[rv.not_le, "hneg"],
                              name="hgt"),
                     pl.claim(rv.mem(a, omega), name="haE", proof=pl.proof(
                         pl.suffices(pl.Exists(rho, pl.And(0 < rho, rv.average_exceeds(
                             f, alpha, a, rho))), because=rv.mem_set_of),
                         pl.take(2 * r, such_that=0 < 2 * r),
                         pl.conclude(because="hgt"),
                     )),
                     pl.conclude(because=["ha", "haE"]),
                 )),
        pl.claim(rv.measure(I) == 2 * r, because=rv.measure_interval, name="hmI"),
        pl.claim(rv.measure(J) == 2 * (2 * r), because=rv.measure_interval, name="hmJ"),
        pl.claim(alpha * rv.measure(J) == 2 * alpha * rv.measure(I), because=["hmJ", "hmI"],
                 name="hαJ", note="|J| = 2|I|"),
        pl.conclude(because=["h1", "h2", "hαJ"]),
    ),
)

THEOREMS = [interval_average]

if __name__ == "__main__":
    import sys

    results = pl.verify_all(THEOREMS, timeout=3600)
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
    sys.exit(0 if all(r.verified for r in results) else 1)
