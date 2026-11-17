"""Pythagoras' theorem from similar triangles, as a PyLeanX written proof checked by Lean.

In triangle ABC with a right angle at C, drop the altitude from C; its foot D lies strictly
between A and B, and CD ⊥ AB. Perpendicular lines are stated as right angles:
``geo.right_angle(A, D, C)`` is ∠ADC = π/2, i.e. CD ⊥ AB at D.

Proof (as in a geometry course):
  * △ACB ∼ △ADC: both have a right angle (at C and at D), and ∠CBA = ∠DCA because each is
    π/2 − ∠A (angle sums, and ∠CAD = ∠CAB since D lies on ray AB). So AD/AC = AC/AB,
    i.e. AC² = AD·AB.
  * △BCA ∼ △BDC in the same way, so BC² = DB·AB.
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
        # ---- the facts about the figure
        claim(A != C, because=[geo.distinct_ac, "hABC"], name="hAC"),
        claim(B != C, because=[geo.distinct_bc, "hABC"], name="hBC"),
        claim(D != A, because=[geo.between_ne_left, "hD"], name="hDA"),
        claim(D != B, because=[geo.between_ne_right, "hD"], name="hDB"),
        claim(geo.strictly_between(D, B, A), because=[geo.between_reverse, "hD"], name="hD'"),
        claim(geo.triangle(A, C, B), because="hABC", name="hACB"),
        claim(geo.triangle(B, C, A), because="hABC", name="hBCA"),
        claim(AB > 0, because=[geo.triangle_sides_pos, "hABC"], name="hAB0"),
        claim(AC > 0, because=[geo.triangle_sides_pos, "hABC"], name="hAC0"),
        claim(BC > 0, because=[geo.triangle_sides_pos, "hBCA"], name="hBC0"),
        claim(BA > 0, because=[geo.triangle_sides_pos, "hBCA"], name="hBA0"),
        # ---- △ACB ∼ △ADC
        claim(ang(D, A, C) == ang(B, A, C), because=[geo.angle_along_ray, "hD"], name="hA",
              note="D lies on ray AB"),
        claim(ang(C, A, D) == ang(D, A, C), because=geo.angle_comm, name="hA'"),
        claim(ang(A, C, B) + ang(C, B, A) + ang(B, A, C) == pi(),
              because=[geo.angle_sum, "hAC"], name="sum1", note="angle sum in △ACB"),
        claim(ang(A, D, C) + ang(D, C, A) + ang(C, A, D) == pi(),
              because=[geo.angle_sum, "hDA"], name="sum2", note="angle sum in △ADC"),
        claim(ang(A, C, B) == ang(A, D, C), because=["hC", "hAD"], name="r1",
              note="both are right angles"),
        claim(ang(C, B, A) == ang(D, C, A), because=["sum1", "sum2", "hC", "hAD", "hA", "hA'"],
              name="r2", note="both are π/2 − ∠A"),
        claim(geo.similar((A, C, B), (A, D, C)), because=[geo.similar_AA, "hACB", "r1", "r2"],
              name="sim1"),
        claim(AD / AC == AC / AB, because=[geo.similar_sides, "sim1", "hACB"], name="ratio1",
              note="similar triangles have proportional sides"),
        claim(AD * AB == AC * AC, because=[geo.cross_multiply, "ratio1"], name="h1"),
        # ---- △BCA ∼ △BDC
        claim(ang(D, B, C) == ang(A, B, C), because=[geo.angle_along_ray, "hD'"], name="hB",
              note="D lies on ray BA"),
        claim(ang(C, B, D) == ang(D, B, C), because=geo.angle_comm, name="hB'"),
        claim(ang(B, C, A) == ang(A, C, B), because=geo.angle_comm, name="hC'"),
        claim(ang(B, C, A) + ang(C, A, B) + ang(A, B, C) == pi(),
              because=[geo.angle_sum, "hBC"], name="sum3", note="angle sum in △BCA"),
        claim(ang(B, D, C) + ang(D, C, B) + ang(C, B, D) == pi(),
              because=[geo.angle_sum, "hDB"], name="sum4", note="angle sum in △BDC"),
        claim(ang(B, C, A) == ang(B, D, C), because=["hC'", "hC", "hBD"], name="r3",
              note="both are right angles"),
        claim(ang(C, A, B) == ang(D, C, B), because=["sum3", "sum4", "r3", "hB", "hB'"],
              name="r4", note="both are π/2 − ∠B"),
        claim(geo.similar((B, C, A), (B, D, C)), because=[geo.similar_AA, "hBCA", "r3", "r4"],
              name="sim2"),
        claim(BD / BC == BC / BA, because=[geo.similar_sides, "sim2", "hBCA"], name="ratio2",
              note="similar triangles have proportional sides"),
        claim(BD * BA == BC * BC, because=[geo.cross_multiply, "ratio2"], name="h2"),
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
    "pythagoras_similar_triangles", [A, B, C, D],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hC": geo.right_angle(A, C, B),          # AC ⊥ BC
        "hD": geo.strictly_between(D, A, B),     # D is on the hypotenuse
        "hAD": geo.right_angle(A, D, C),         # CD ⊥ AB
        "hBD": geo.right_angle(B, D, C),
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
