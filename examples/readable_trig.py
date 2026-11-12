"""sin²x + cos²x = 1, proved the way a calculus course proves it, and checked by Lean.

Let f(t) = sin²t + cos²t. Then f is differentiable and f′ = 2 sin cos − 2 cos sin = 0,
so f is constant: f(x) = f(0) = 0² + 1² = 1.

Mathlib's own proof of this fact goes through the complex exponential; this file is a
different, elementary proof of the same statement. ``avoid=`` makes sure it really is:
Lean's automation is not allowed to use Mathlib's sin²+cos²=1 lemmas, and a Lean check
after the theorem fails verification if the proof refers to them anyway.

Run:  python examples/readable_trig.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import analysis as an

x, t = pl.symbols("x t", pl.Real)
f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))

pythagorean_identity = pl.Theorem(
    "pythagorean_identity", [x],
    conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
    avoid=[an.sin_sq_add_cos_sq, an.cos_sq_add_sin_sq],
    proof=pl.proof(
        pl.let(f, lambda t: an.sin(t)**2 + an.cos(t)**2),
        pl.claim(an.differentiable(f), note="sin and cos are differentiable"),
        pl.claim(pl.Forall(t, an.deriv(f, t) == 0),
                 because=[an.deriv_sin, an.deriv_cos],
                 note="f′(t) = 2 sin t cos t − 2 cos t sin t = 0"),
        pl.claim(f(x) == f(0), because=an.constant_of_zero_derivative),
        pl.claim(f(0) == 1, because=[an.sin_zero, an.cos_zero]),
        pl.conclude(),
    ),
)

if __name__ == "__main__":
    result = pythagorean_identity.verify(timeout=1800)
    print(pythagorean_identity.prose(result))
    raise SystemExit(0 if result.verified else 1)
