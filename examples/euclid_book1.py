"""Propositions from Euclid, Book I, as textbook written proofs checked by Lean.

Each proof states its steps and cites the textbook fact behind each one, in words
("the angles of a triangle add up to 180°"). Side conditions a textbook leaves implicit
(the vertices of a triangle are distinct, ∠ABC = ∠CBA, the order in which a triangle's
vertices are listed) are supplied by PyLeanX and checked by Lean like everything else.

    E1  (I.5, I.32)  The angles of an equilateral triangle are 60°.
    E2  (I.32)       The acute angles of a right triangle add up to 90°.
    E3               The base angles of an isosceles right triangle are 45°.
    E4  (I.32)       An exterior angle equals the sum of the two remote interior angles.
    E5  (I.15)       Vertical angles are equal.
    E6               The midsegment of a triangle is parallel to the third side and half as long.

Run:  python examples/euclid_book1.py
"""

from __future__ import annotations

import sys

import pyleanx as pl
from pyleanx import geometry as geo
from pyleanx.analysis import pi

A, B, C, D, M, N, O = geo.points("A B C D M N O")  # noqa: E741
ang, dist = geo.angle, geo.dist
ISOSCELES = "the base angles of an isosceles triangle are equal"

equilateral = pl.Theorem(
    "euclid_equilateral_angles", [A, B, C],
    assumptions={"hABC": geo.triangle(A, B, C),
                 "h1": dist(A, B) == dist(A, C), "h2": dist(B, A) == dist(B, C)},
    conclusion=ang(A, B, C) == pi() / 3,
    proof=pl.proof(
        pl.claim(ang(A, B, C) == ang(A, C, B), because=[ISOSCELES, "h1"],
                 name="e1"),
        pl.claim(ang(B, A, C) == ang(B, C, A), because=[ISOSCELES, "h2"],
                 name="e2"),
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because="the angles of a triangle add up to 180°", name="sum"),
        pl.conclude(because=["e1", "e2", "sum"]),
    ),
)

right_triangle = pl.Theorem(
    "euclid_right_triangle_acute_angles", [A, B, C],
    assumptions={"hABC": geo.triangle(A, B, C), "hC": geo.right_angle(A, C, B)},
    conclusion=ang(C, A, B) + ang(A, B, C) == pi() / 2,
    proof=pl.proof(
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because="the angles of a triangle add up to 180°", name="sum"),
        pl.conclude(because=["sum", "hC"]),
    ),
)

isosceles_right = pl.Theorem(
    "euclid_isosceles_right_triangle", [A, B, C],
    assumptions={"hABC": geo.triangle(A, B, C), "hC": geo.right_angle(A, C, B),
                 "hiso": dist(C, A) == dist(C, B)},
    conclusion=ang(C, A, B) == pi() / 4,
    proof=pl.proof(
        pl.claim(ang(C, A, B) == ang(C, B, A), because=[ISOSCELES, "hiso"],
                 name="e"),
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because="the angles of a triangle add up to 180°", name="sum"),
        pl.conclude(because=["e", "sum", "hC"]),
    ),
)

exterior = pl.Theorem(
    "euclid_exterior_angle", [A, B, C, D],
    assumptions={"hABC": geo.triangle(A, B, C), "hD": geo.strictly_between(C, B, D)},
    conclusion=ang(A, C, D) == ang(C, A, B) + ang(A, B, C),
    proof=pl.proof(
        pl.claim(ang(B, C, D) == pi(), because=["straight angle", "hD"], name="hstraight",
                 note="C lies between B and D"),
        pl.claim(ang(A, C, B) + ang(A, C, D) == pi(),
                 because=["angles on a straight line add up to 180°", "hstraight"],
                 name="pair"),
        pl.claim(ang(A, B, C) + ang(B, C, A) + ang(C, A, B) == pi(),
                 because="the angles of a triangle add up to 180°", name="sum"),
        pl.conclude(because=["pair", "sum"]),
    ),
)

vertical = pl.Theorem(
    "euclid_vertical_angles", [A, B, C, D, O],
    assumptions={"hAB": geo.strictly_between(O, A, B), "hCD": geo.strictly_between(O, C, D)},
    conclusion=ang(A, O, C) == ang(B, O, D),
    proof=pl.proof(
        pl.claim(ang(A, O, B) == pi(), because=["straight angle", "hAB"], name="h1"),
        pl.claim(ang(C, O, D) == pi(), because=["straight angle", "hCD"], name="h2"),
        pl.conclude(because=["vertical angles are equal", "h1", "h2"]),
    ),
)

midsegment = pl.Theorem(
    "euclid_midsegment", [A, B, C, M, N],
    assumptions={"hM": geo.is_midpoint(M, A, B), "hN": geo.is_midpoint(N, A, C)},
    conclusion=pl.And(geo.parallel(geo.line(M, N), geo.line(B, C)),
                      dist(M, N) == dist(B, C) / 2),
    proof=pl.proof(
        pl.claim(geo.parallel(geo.line(M, N), geo.line(B, C)),
                 because=["midsegment parallel to the third side", "hM", "hN"], name="hpar"),
        pl.claim(dist(M, N) == dist(B, C) / 2,
                 because=["midsegment half the third side", "hM", "hN"], name="hlen"),
        pl.conclude(because=["hpar", "hlen"]),
    ),
)

THEOREMS = [equilateral, right_triangle, isosceles_right, exterior, vertical, midsegment]

if __name__ == "__main__":
    check = pl.check_all if "--fast" in sys.argv else pl.verify_all
    results = check(THEOREMS, timeout=3600)
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
    sys.exit(0 if all(r.verified for r in results) else 1)
