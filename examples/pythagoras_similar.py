"""Pythagoras' theorem from similar triangles, written as in a geometry textbook.

Lemma (the leg rule). In a right triangle ABC (right angle at C) with altitude CD,
AC² = AD·AB.
    The triangles ABC and ACD share the angle at A and both have a right angle, so they
    are similar (AA); corresponding sides are proportional: AC/AB = AD/AC.

Theorem (Pythagoras). In a right triangle ABC (right angle at C), AC² + BC² = AB².
    Drop the altitude CD. By the leg rule, AC² = AD·AB, and similarly (exchanging A and B)
    BC² = BD·BA.
    Adding, AC² + BC² = (AD + DB)·AB = AB².

Lean checks both proofs. Mathlib's own Pythagoras theorem is not used.

Run:  python examples/pythagoras_similar.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import geometry as geo

A, B, C, D = geo.points("A B C D")
AB, AC, BC = geo.dist(A, B), geo.dist(A, C), geo.dist(B, C)
AD, BD, DB, BA = geo.dist(A, D), geo.dist(B, D), geo.dist(D, B), geo.dist(B, A)

leg_rule = pl.Theorem(
    "leg_rule", [A, B, C, D],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hC": geo.right_angle(A, C, B),
        "hD": geo.strictly_between(D, A, B),
        "hAD": geo.right_angle(A, D, C),
    },
    conclusion=AC ** 2 == AD * AB,
    proof=pl.proof(
        pl.claim(geo.angle(B, A, C) == geo.angle(C, A, D), because=[geo.common_angle, "hD"],
                 name="hA"),
        pl.claim(geo.similar((B, A, C), (C, A, D)),
                 because=[geo.similar_AA, "hABC", "hA", "hC", "hAD"], name="sim",
                 note="AA: a common angle and a right angle"),
        pl.conclude(because=geo.proportional_sides("sim"), note="AC/AB = AD/AC"),
    ),
)

pythagoras = pl.Theorem(
    "pythagoras_similar_triangles", [A, B, C],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hC": geo.right_angle(A, C, B),
    },
    conclusion=AC ** 2 + BC ** 2 == AB ** 2,
    proof=pl.proof(
        pl.choose(D, such_that=pl.And(geo.strictly_between(D, A, B), geo.right_angle(A, D, C),
                                      geo.right_angle(B, D, C)),
                  because=[geo.altitude_to_hypotenuse, "hABC", "hC"],
                  names="hD hAD hBD"),
        pl.claim(AC ** 2 == AD * AB, because=[leg_rule, "hABC", "hC", "hD", "hAD"],
                 name="h1", note="the leg rule at A"),
        pl.similarly("h1", exchange=(A, B), name="h2"),
        pl.claim(AB == AD + DB, because=[geo.segment_addition, "hD"], name="hseg"),
        pl.chain(AC ** 2 + BC ** 2,
                 ("=", AD * AB + BD * BA, ["h1", "h2"]),
                 ("=", (AD + DB) * AB, geo.dist_comm),
                 ("=", AB ** 2, "hseg")),
    ),
)

THEOREMS = [leg_rule, pythagoras]

if __name__ == "__main__":
    results = pl.verify_all(THEOREMS, timeout=1800)
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
        for d in res.errors[:6]:
            print("   ", d.span_label, "|", d.message[:600].replace("\n", " | "))
    raise SystemExit(0 if all(r.verified for r in results) else 1)
