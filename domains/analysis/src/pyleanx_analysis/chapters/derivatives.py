"""Chapter: derivatives of functions given by a formula.

A function is given by a hypothesis, as in a textbook ("let f(t) = t² + 1"); the proof says
that f is that function and then differentiates it. ``thm.sanity_check()`` evaluates the
derivative numerically on random points (a wrong derivative is reported with the point);
Lean checks the proof. ``python -m pyleanx_analysis.chapters.derivatives`` verifies them.
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import analysis as real

f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))
x, t = pl.symbols("x t", pl.Real)

#: funext: two functions that agree at every point are equal
funext = pl.ref("funext")

# ---------------------------------------------------------------------------------------
# 1. f(t) = t² + 1 has derivative 2x
# ---------------------------------------------------------------------------------------
square_plus_one = pl.Theorem(
    "deriv_square_plus_one", [f, x],
    assumptions={"hf": pl.Forall(t, f(t) == t ** 2 + 1)},
    conclusion=real.deriv(f, x) == 2 * x,
    proof=pl.proof(
        pl.claim(f == pl.fun(lambda s: s ** 2 + 1, pl.Real), because=[funext, "hf"],
                 name="hdef", note="f is the function t ↦ t² + 1"),
        pl.conclude(because="hdef"),
    ),
)

# ---------------------------------------------------------------------------------------
# 2. f(t) = sin(t)·t: the product rule
# ---------------------------------------------------------------------------------------
sin_times_t = pl.Theorem(
    "deriv_sin_times_t", [f, x],
    assumptions={"hf": pl.Forall(t, f(t) == real.sin(t) * t)},
    conclusion=real.deriv(f, x) == real.cos(x) * x + real.sin(x),
    proof=pl.proof(
        pl.claim(f == pl.fun(lambda s: real.sin(s) * s, pl.Real), because=[funext, "hf"],
                 name="hdef", note="f is the function t ↦ sin(t)·t"),
        pl.conclude(because="hdef"),
    ),
)

THEOREMS = [square_plus_one, sin_times_t]

if __name__ == "__main__":
    import sys

    results = pl.verify_all(THEOREMS, timeout=3600)
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
    sys.exit(0 if all(r.verified for r in results) else 1)
