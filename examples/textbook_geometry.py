"""High-school geometry textbook proofs, written step by step and checked by Lean.

1. In an isosceles triangle, the median to the base is perpendicular to the base
   (SSS congruence, CPCTC, angles on a straight line).
2. Opposite sides of a parallelogram are equal (alternate interior angles, ASA, CPCTC).
3. An angle inscribed in a semicircle is a right angle, so AP² + PB² = AB²
   (Thales, Pythagoras).
4. The base angles of an isosceles right triangle are 45° (isosceles triangle, angle sum).
5. The segment joining the midpoints of two sides is parallel to the third side and half
   as long (midsegment theorem), so the medial triangle has half the perimeter.

Run:  python examples/textbook_geometry.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import geometry as geo

A, B, C, D, M, N, O, P = geo.points("A B C D M N O P")  # noqa: E741
dist, angle = geo.dist, geo.angle
pi = pl.analysis.pi

# 1. ------------------------------------------------------------------------------------
isosceles_median = pl.Theorem(
    "isosceles_median_perpendicular", [A, B, C, M],
    assumptions={"hABC": geo.triangle(A, B, C), "hiso": dist(A, B) == dist(A, C),
                 "hM": geo.is_midpoint(M, B, C)},
    conclusion=geo.right_angle(A, M, B),
    proof=pl.proof(
        pl.claim(dist(B, M) == dist(C, M), because=geo.midpoint_equal_halves),
        pl.claim(geo.congruent((B, M, A), (C, M, A)), because=geo.sss,
                 note="SSS: BM = CM, MA = MA, AB = AC"),
        pl.claim(angle(B, M, A) == angle(C, M, A), because=geo.cpctc_angle_b),
        pl.claim(B != C, because=geo.distinct_bc("hABC")),
        pl.claim(angle(B, M, C) == pi(), because=geo.midpoint_straight),
        pl.claim(angle(A, M, B) + angle(A, M, C) == pi(), because=geo.linear_pair),
        pl.conclude(because=geo.angle_comm, note="two equal angles adding up to 180°"),
    ),
)

# 2. ------------------------------------------------------------------------------------
parallelogram_sides = pl.Theorem(
    "parallelogram_opposite_sides_equal", [A, B, C, D],
    assumptions={"h": geo.parallelogram(A, B, C, D)},
    conclusion=pl.And(dist(A, B) == dist(C, D), dist(C, B) == dist(A, D)),
    proof=pl.proof(
        pl.claim(geo.triangle(A, B, C), because="h"),
        pl.claim(geo.parallel(geo.line(A, B), geo.line(C, D)), because="h"),
        pl.claim(geo.parallel(geo.line(C, B), geo.line(A, D)), because="h"),
        pl.claim(geo.opposite_sides(B, D, A, C), because=geo.parallelogram_diagonal_sides,
                 note="the diagonal AC separates B and D"),
        pl.claim(geo.opposite_sides(B, D, C, A), because=geo.parallelogram_diagonal_sides),
        pl.claim(angle(B, A, C) == angle(A, C, D), because=geo.alternate_angles,
                 note="alternate interior angles, AB ∥ CD"),
        pl.claim(angle(B, C, A) == angle(C, A, D), because=geo.alternate_angles,
                 note="alternate interior angles, CB ∥ AD"),
        pl.claim(geo.triangle(B, A, C), because="step1", note="the same triangle"),
        pl.claim(angle(B, A, C) == angle(D, C, A), because=geo.angle_comm),
        pl.claim(angle(A, C, B) == angle(C, A, D), because=geo.angle_comm),
        pl.claim(dist(A, C) == dist(C, A), because=geo.dist_comm),
        pl.claim(geo.congruent((B, A, C), (D, C, A)), because=geo.asa),
        pl.claim(dist(B, A) == dist(D, C), because=geo.cpctc_ab),
        pl.claim(dist(C, B) == dist(A, D), because=geo.cpctc_ca),
        pl.conclude(because=geo.dist_comm),
    ),
)

# 3. ------------------------------------------------------------------------------------
semicircle = pl.Theorem(
    "angle_in_semicircle", [A, B, O, P],
    assumptions={"hO": geo.is_midpoint(O, A, B), "hP": dist(P, O) == dist(A, O)},
    conclusion=dist(A, B) * dist(A, B) == dist(A, P) * dist(A, P) + dist(B, P) * dist(B, P),
    proof=pl.proof(
        pl.claim(geo.right_angle(A, P, B), because=geo.thales,
                 note="P lies on the circle with diameter AB"),
        pl.conclude(because=geo.pythagoras_iff),
    ),
)

# 4. ------------------------------------------------------------------------------------
isosceles_right = pl.Theorem(
    "isosceles_right_triangle_base_angles", [A, B, C],
    assumptions={"hABC": geo.triangle(A, B, C), "hright": geo.right_angle(A, B, C),
                 "hiso": dist(B, A) == dist(B, C)},
    conclusion=angle(B, A, C) == pi() / 4,
    proof=pl.proof(
        pl.claim(angle(B, A, C) == angle(B, C, A), because=geo.isosceles_base_angles),
        pl.claim(A != B, because=geo.distinct_ab("hABC")),
        pl.claim(angle(A, B, C) + angle(B, C, A) + angle(C, A, B) == pi(), because=geo.angle_sum),
        pl.conclude(because=geo.angle_comm, note="2·∠BAC + 90° = 180°"),
    ),
)

# 5. ------------------------------------------------------------------------------------
medial_triangle = pl.Theorem(
    "medial_triangle_half_perimeter", [A, B, C, M, N, P],
    assumptions={"hM": geo.is_midpoint(M, A, B), "hN": geo.is_midpoint(N, A, C),
                 "hP": geo.is_midpoint(P, B, C)},
    conclusion=dist(M, N) + dist(N, P) + dist(P, M)
    == (dist(A, B) + dist(B, C) + dist(C, A)) / 2,
    proof=pl.proof(
        pl.claim(geo.parallel(geo.line(M, N), geo.line(B, C)), because=geo.midsegment_parallel),
        pl.claim(dist(M, N) == dist(B, C) / 2, because=geo.midsegment_length),
        pl.claim(geo.is_midpoint(M, B, A), because=geo.midpoint_comm),
        pl.claim(geo.is_midpoint(N, C, A), because=geo.midpoint_comm),
        pl.claim(geo.is_midpoint(P, C, B), because=geo.midpoint_comm),
        pl.claim(dist(P, N) == dist(B, A) / 2, because=geo.midsegment_length,
                 note="midsegment of triangle CBA"),
        pl.claim(dist(M, P) == dist(A, C) / 2, because=geo.midsegment_length,
                 note="midsegment of triangle BAC"),
        pl.conclude(because=geo.dist_comm),
    ),
)

THEOREMS = [isosceles_median, parallelogram_sides, semicircle, isosceles_right,
            medial_triangle]

if __name__ == "__main__":
    results = pl.verify_all(THEOREMS, timeout=1800)
    ok = True
    for thm, result in zip(THEOREMS, results, strict=True):
        print(thm.prose(result), "\n")
        ok = ok and result.verified
    raise SystemExit(0 if ok else 1)
