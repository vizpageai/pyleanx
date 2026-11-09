"""Algebra, analysis and plane geometry with the M6 domain modules.

Run: python examples/domains.py   (geometry imports are large: several minutes here)
"""

import pyleanx as pl
from pyleanx import algebra as alg
from pyleanx import analysis as an
from pyleanx import geometry as geo

a, b = pl.symbols("a b", pl.Real)
x = pl.symbol("x", pl.Real)
A, B, C = geo.points("A B C")

theorems = [
    # algebra: helpers pick a standard proof (ring / positivity / nlinarith)
    alg.identity("binomial_square", (a + b)**2, a**2 + 2*a*b + b**2),
    alg.am_gm_two("am_gm_two", a, b),
    # analysis: reuse Mathlib facts about Real.sin/cos/sqrt
    pl.Theorem("pythagorean_identity", [x],
               conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
               proof=pl.exact(an.sin_sq_add_cos_sq(x))),
    # geometry on the plane ℝ²
    pl.Theorem("triangle_angle_sum", [A, B, C], assumptions={"h": B != A},
               conclusion=geo.angle(A, B, C) + geo.angle(B, C, A) + geo.angle(C, A, B) == pl.pi(),
               proof=pl.exact(geo.angle_add_angle_add_angle_eq_pi(C, pl.hyp("h")))),
    pl.Theorem("pythagoras", [A, B, C], assumptions={"right": geo.angle(A, B, C) == pl.pi() / 2},
               conclusion=geo.dist(A, C) * geo.dist(A, C)
               == geo.dist(A, B) * geo.dist(A, B) + geo.dist(C, B) * geo.dist(C, B),
               proof=pl.rw(geo.pythagoras_iff) >> pl.exact("right")),
]

for t in theorems:
    print(t.name, " $" + t.to_latex() + "$")

results = pl.verify_all(theorems, timeout=1800)  # one Lean process for all of them
for r in results:
    print(r.summary())
raise SystemExit(0 if all(r.verified for r in results) else 1)
