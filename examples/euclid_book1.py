"""Propositions from Euclid, Book I, as textbook written proofs checked by Lean.

Each proof states its steps and cites the textbook fact behind each one by name
(``geo.angle_add_angle_add_angle_eq_pi``); the printed proof shows the fact in words
("the angles of a triangle add up to 180°"). Side conditions a textbook leaves implicit
(the vertices of a triangle are distinct, ∠ABC = ∠CBA, the order in which a triangle's
vertices are listed) are supplied by PyLeanX and checked by Lean like everything else.

    E1  (I.5, I.32)  The angles of an equilateral triangle are 60°.
    E2  (I.32)       The acute angles of a right triangle add up to 90°.
    E3               The base angles of an isosceles right triangle are 45°.
    E4  (I.32)       An exterior angle equals the sum of the two remote interior angles.
    E5  (I.15)       Vertical angles are equal.
    E6               The midsegment of a triangle is parallel to the third side and half as long.
    E7  (I.8)        The median to the base of an isosceles triangle bisects the apex angle
                     (SSS, then corresponding parts of congruent triangles).

Run:  python examples/euclid_book1.py
"""

from __future__ import annotations

import sys

import pyleanx as pl
from pyleanx import geometry as geo
from pyleanx.analysis import pi

A, B, C, D, M, N, O = geo.points("A B C D M N O")  # noqa: E741
ang, dist = geo.angle, geo.dist

equilateral = pl.Theorem(
    "euclid_equilateral_angles", [A, B, C],
    assumptions={"hABC": geo.triangle(A, B, C),
                 "h1": dist(A, B) == dist(A, C), "h2": dist(B, A) == dist(B, C)},
    conclusion=ang(A, B, C) == pi() / 3,
    proof=pl.proof(
        pl.claim(ang(A, B, C) == ang(A, C, B), because=[geo.isosceles_base_angles, "h1"],
                 name="e1"),
        pl.claim(ang(B, A, C) == ang(B, C, A), because=[geo.isosceles_base_angles, "h2"],
                 name="e2"),
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because=geo.angle_add_angle_add_angle_eq_pi, name="sum"),
        pl.conclude(because=["e1", "e2", "sum"]),
    ),
)

right_triangle = pl.Theorem(
    "euclid_right_triangle_acute_angles", [A, B, C],
    assumptions={"hABC": geo.triangle(A, B, C), "hC": geo.right_angle(A, C, B)},
    conclusion=ang(C, A, B) + ang(A, B, C) == pi() / 2,
    proof=pl.proof(
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because=geo.angle_add_angle_add_angle_eq_pi, name="sum"),
        pl.conclude(because=["sum", "hC"]),
    ),
)

isosceles_right = pl.Theorem(
    "euclid_isosceles_right_triangle", [A, B, C],
    assumptions={"hABC": geo.triangle(A, B, C), "hC": geo.right_angle(A, C, B),
                 "hiso": dist(C, A) == dist(C, B)},
    conclusion=ang(C, A, B) == pi() / 4,
    proof=pl.proof(
        pl.claim(ang(C, A, B) == ang(C, B, A), because=[geo.isosceles_base_angles, "hiso"],
                 name="e"),
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because=geo.angle_add_angle_add_angle_eq_pi, name="sum"),
        pl.conclude(because=["e", "sum", "hC"]),
    ),
)

exterior = pl.Theorem(
    "euclid_exterior_angle", [A, B, C, D],
    assumptions={"hABC": geo.triangle(A, B, C), "hD": geo.strictly_between(C, B, D)},
    conclusion=ang(A, C, D) == ang(C, A, B) + ang(A, B, C),
    proof=pl.proof(
        pl.claim(ang(B, C, D) == pi(), because=[geo.straight_angle, "hD"], name="hstraight",
                 note="C lies between B and D"),
        pl.claim(ang(A, C, B) + ang(A, C, D) == pi(),
                 because=[geo.linear_pair, "hstraight"],
                 name="pair"),
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because=geo.angle_add_angle_add_angle_eq_pi, name="sum"),
        pl.conclude(because=["pair", "sum"]),
    ),
)

vertical = pl.Theorem(
    "euclid_vertical_angles", [A, B, C, D, O],
    assumptions={"hAB": geo.strictly_between(O, A, B), "hCD": geo.strictly_between(O, C, D)},
    conclusion=ang(A, O, C) == ang(B, O, D),
    proof=pl.proof(
        pl.claim(ang(A, O, B) == pi(), because=[geo.straight_angle, "hAB"], name="h1"),
        pl.claim(ang(C, O, D) == pi(), because=[geo.straight_angle, "hCD"], name="h2"),
        pl.conclude(because=[geo.vertical_angles, "h1", "h2"]),
    ),
)

midsegment = pl.Theorem(
    "euclid_midsegment", [A, B, C, M, N],
    assumptions={"hM": geo.is_midpoint(M, A, B), "hN": geo.is_midpoint(N, A, C)},
    conclusion=pl.And(geo.parallel(geo.line(M, N), geo.line(B, C)),
                      dist(M, N) == dist(B, C) / 2),
    proof=pl.proof(
        pl.claim(geo.parallel(geo.line(M, N), geo.line(B, C)),
                 because=[geo.midsegment_parallel, "hM", "hN"], name="hpar"),
        pl.claim(dist(M, N) == dist(B, C) / 2,
                 because=[geo.midsegment_length, "hM", "hN"], name="hlen"),
        pl.conclude(because=["hpar", "hlen"]),
    ),
)

median_bisects = pl.Theorem(
    "euclid_median_bisects_apex", [A, B, C, M],
    assumptions={"hABC": geo.triangle(A, B, C), "hiso": dist(A, B) == dist(A, C),
                 "hM": geo.is_midpoint(M, B, C)},
    conclusion=ang(M, A, B) == ang(M, A, C),
    proof=pl.proof(
        pl.claim(dist(B, M) == dist(C, M),
                 because=geo.midpoint_equal_halves),
        pl.claim(geo.congruent((B, M, A), (C, M, A)), because=geo.sss,
                 note="SSS: BM = CM, MA = MA, AB = AC", name="hcong"),
        # "by CPCTC": the family of corresponding parts; Lean uses the part it needs
        pl.conclude(because=[geo.cpctc, "hcong"]),
    ),
)

THEOREMS = [equilateral, right_triangle, isosceles_right, exterior, vertical, midsegment,
            median_bisects]

if __name__ == "__main__":
    check = pl.check_all if "--fast" in sys.argv else pl.verify_all
    results = check(THEOREMS, timeout=3600)
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
    sys.exit(0 if all(r.verified for r in results) else 1)
