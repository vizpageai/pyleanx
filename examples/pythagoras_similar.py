"""Pythagoras' theorem from similar triangles, as a PyLeanX written proof checked by Lean.

In triangle ABC with a right angle at C, AC² + BC² = AB².

Proof (as in a geometry course):
  * Draw the altitude from C (every triangle has one): D on line AB with CD ⊥ AB
    (``geo.perpendicular(geo.line(C, D), geo.line(A, B))``). The angles at A and B of a
    right triangle are acute, so D lies strictly between A and B, and ∠ADC = ∠BDC = π/2.
  * △BAC ∼ △CAD: they share the angle at A, and both have a right angle (at C and at D).
    So AC/AB = AD/AC, i.e. AC² = AD·AB.
  * △ABC ∼ △CBD: they share the angle at B, and both have a right angle.
    So BC/BA = BD/BC, i.e. BC² = BD·BA.
  * Adding, AC² + BC² = (AD + DB)·AB = AB², by segment addition.

It does not cite Mathlib's Pythagoras (``geo.pythagoras_iff``), which would be circular.

Run:  python examples/pythagoras_similar.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import geometry as geo
from pyleanx.analysis import pi

A, B, C, D = geo.points("A B C D")
AB, AC, BC = geo.dist(A, B), geo.dist(A, C), geo.dist(B, C)
AD, DB = geo.dist(A, D), geo.dist(D, B)
BA, BD = geo.dist(B, A), geo.dist(B, D)
ang = geo.angle


def _proof() -> pl.Tactic:
    claim = pl.claim
    return pl.proof(
        # ---- draw the altitude from C (every triangle has one) and locate its foot
        pl.choose(D, such_that=pl.And(geo.on_line(D, geo.line(A, B)),
                                      geo.perpendicular(geo.line(C, D), geo.line(A, B))),
                  because=[geo.altitude, "hABC"], names="hDl hperp",
                  note="draw the altitude from C; let D be its foot"),
        claim(ang(C, A, B) < pi() / 2, because=[geo.right_triangle_acute, "hABC", "hC"],
              name="hA"),
        claim(ang(C, B, A) < pi() / 2, because=[geo.right_triangle_acute, "hABC", "hC"],
              name="hB"),
        claim(A != B, because=[geo.distinct_ab, "hABC"], name="hAB"),
        claim(geo.strictly_between(D, A, B),
              because=[geo.foot_between, "hAB", "hDl", "hperp", "hA", "hB"], name="hD",
              note="the angles at A and B are acute"),
        claim(geo.right_angle(A, D, C), because=[geo.foot_right_angles, "hDl", "hperp"],
              name="hAD"),
        claim(geo.right_angle(B, D, C), because=[geo.foot_right_angles, "hDl", "hperp"],
              name="hBD"),
        claim(geo.triangle(B, A, C), because="hABC", name="hBAC"),
        claim(AB > 0, because=[geo.triangle_sides_pos, "hABC"], name="hAB0"),
        claim(AC > 0, because=[geo.triangle_sides_pos, "hABC"], name="hAC0"),
        claim(BC > 0, because=[geo.triangle_sides_pos, "hBAC"], name="hBC0"),
        claim(BA > 0, because=[geo.triangle_sides_pos, "hBAC"], name="hBA0"),
        # ---- △BAC ∼ △CAD: common angle at A, right angles at C and D
        claim(ang(D, A, C) == ang(B, A, C), because=[geo.angle_on_segment, "hD"], name="hA",
              note="D lies on ray AB"),
        claim(ang(C, A, D) == ang(D, A, C), because=geo.angle_comm, name="hA'"),
        claim(ang(B, A, C) == ang(C, A, D), because=["hA", "hA'"], name="a1",
              note="the common angle at A"),
        claim(ang(A, C, B) == ang(A, D, C), because=["hC", "hAD"], name="a2",
              note="both are right angles"),
        claim(geo.similar((B, A, C), (C, A, D)), because=[geo.similar_AA, "hBAC", "a1", "a2"],
              name="sim1"),
        claim(AC / AB == AD / AC, because=[geo.similar_sides_at, "sim1", "hBAC"],
              name="ratio1"),
        claim(AC * AC == AD * AB, because=[geo.cross_multiply, "ratio1"], name="h1"),
        # ---- △ABC ∼ △CBD: common angle at B, right angles at C and D
        claim(ang(D, B, C) == ang(A, B, C), because=[geo.angle_on_segment, "hD"], name="hB",
              note="D lies on ray BA"),
        claim(ang(C, B, D) == ang(D, B, C), because=geo.angle_comm, name="hB'"),
        claim(ang(A, B, C) == ang(C, B, D), because=["hB", "hB'"], name="b1",
              note="the common angle at B"),
        claim(ang(B, C, A) == ang(A, C, B), because=geo.angle_comm, name="hC'"),
        claim(ang(B, C, A) == ang(B, D, C), because=["hC'", "hC", "hBD"], name="b2",
              note="both are right angles"),
        claim(geo.similar((A, B, C), (C, B, D)), because=[geo.similar_AA, "hABC", "b1", "b2"],
              name="sim2"),
        claim(BC / BA == BD / BC, because=[geo.similar_sides_at, "sim2", "hABC"],
              name="ratio2"),
        claim(BC * BC == BD * BA, because=[geo.cross_multiply, "ratio2"], name="h2"),
        # ---- add the two
        claim(BA == AB, because=geo.dist_comm, name="hBA"),
        claim(BD == DB, because=geo.dist_comm, name="hBD'"),
        claim(AB == AD + DB, because=[geo.segment_addition, "hD"], name="hseg"),
        pl.chain(AC ** 2 + BC ** 2,
                 ("=", AD * AB + BD * BA, ["h1", "h2"]),
                 ("=", AD * AB + DB * BA, "hBD'"),
                 ("=", AD * AB + DB * AB, "hBA"),
                 ("=", (AD + DB) * AB),
                 ("=", AB ** 2, "hseg", "segment addition: AD + DB = AB")),
    )


pythagoras = pl.Theorem(
    "pythagoras_similar_triangles", [A, B, C],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hC": geo.right_angle(A, C, B),          # AC ⊥ BC
    },
    conclusion=AC ** 2 + BC ** 2 == AB ** 2,
    proof=_proof(),
)

if __name__ == "__main__":
    result = pythagoras.verify(timeout=1800)
    print(pythagoras.prose(result))
    for d in result.errors[:6]:
        print("   ", d.span_label, "|", d.message[:600].replace("\n", " | "))
    raise SystemExit(0 if result.verified else 1)
