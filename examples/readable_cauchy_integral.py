"""Cauchy's integral formula, proved from Cauchy's theorem, and checked by Lean.

If f is holomorphic on the closed disc |z − c| ≤ R and |w − c| < R, then

    ∮_{|z−c|=R} f(z)/(z − w) dz = 2πi f(w).

Proof: let g(z) = (f(z) − f(w))/(z − w) for z ≠ w and g(w) = f′(w). g is continuous on
the closed disc and holomorphic except possibly at w, so ∮ g = 0 by Cauchy's theorem. On
the circle z ≠ w, so f(z)/(z − w) = g(z) + f(w)/(z − w). Hence
∮ f(z)/(z − w) dz = 0 + f(w) ∮ dz/(z − w) = 2πi f(w).

The proof must not use Mathlib's own Cauchy integral formula, nor its removable-singularity
theorem (which Mathlib derives from the formula): ``avoid=`` makes Lean check that.

Run:  python examples/readable_cauchy_integral.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import complex_analysis as ca

f, g = pl.symbols("f g", pl.Fn(ca.C, ca.C))
c, w, z = pl.symbols("c w z", ca.C)
R = pl.symbol("R", pl.Real)


def over_z_minus_w(value):
    """(z − w)⁻¹ · value, as a function of z on the circle."""
    return lambda z: pl.smul(ca.inv(z - w), value(z))


cauchy_integral_formula = pl.Theorem(
    "cauchy_integral_formula", [f, c, w, R],
    assumptions={"hf": ca.holomorphic_on(f, ca.closed_ball(c, R)),
                 "hw": ca.mem(w, ca.ball(c, R))},
    conclusion=ca.circle_integral(over_z_minus_w(f), c, R) == pl.smul(ca.two_pi_i(), f(w)),
    avoid=ca.INTEGRAL_FORMULA,
    proof=pl.proof(
        pl.let(g, ca.difference_quotient(f, w),
               note="g(z) = (f(z) − f(w))/(z − w) for z ≠ w, and g(w) = f′(w)"),
        pl.claim(R > 0, because=ca.radius_pos("hw"), name="hR"),
        pl.claim(ca.continuous_on(g, ca.closed_ball(c, R)), because=ca.quotient_continuous),
        pl.claim(pl.Forall(z, pl.Implies(ca.mem(z, ca.minus_point(ca.ball(c, R), w)),
                                         ca.differentiable_at(g, z))),
                 because=ca.quotient_differentiable),
        pl.claim(ca.circle_integral(lambda z: g(z), c, R) == 0, because=ca.cauchy_theorem,
                 name="cauchy"),
        pl.chain(ca.circle_integral(over_z_minus_w(f), c, R),
                 ("=", ca.circle_integral(lambda z: g(z), c, R)
                  + ca.circle_integral(over_z_minus_w(lambda _: f(w)), c, R),
                  ca.integrate_termwise),
                 ("=", 0 + ca.circle_integral(over_z_minus_w(lambda _: f(w)), c, R), "cauchy"),
                 ("=", pl.smul(ca.circle_integral(lambda z: ca.inv(z - w), c, R), f(w)),
                  ca.integral_smul_const),
                 ("=", pl.smul(ca.two_pi_i(), f(w)), ca.kernel_integral("hw"))),
    ),
)

if __name__ == "__main__":
    result = cauchy_integral_formula.verify(timeout=1800)
    print(cauchy_integral_formula.prose(result))
    raise SystemExit(0 if result.verified else 1)
