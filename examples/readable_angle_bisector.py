"""The angle bisector theorem, proved with the side-splitter theorem, checked by Lean.

In triangle ABC, let D lie on side BC with ∠BAD = ∠DAC (AD bisects the angle at A).
Then BD/DC = AB/AC.

Proof (auxiliary line): extend BA beyond A to E with AE = AC. Triangle ACE is isosceles,
so the line EC is parallel to the bisector AD. In triangle BEC, A lies on BE, D on BC and
AD ∥ EC, so by the side-splitter theorem BA/BE = BD/BC, i.e. BA/(BA + AE) = BD/(BD + DC).
Hence BA/AE = BD/DC, and AE = AC gives BD/DC = AB/AC.

The side-splitter theorem is the one proved in ``readable_side_splitter.py``: it is cited
as a theorem object, so its proof is re-checked in the same Lean run.

Run:  python examples/readable_angle_bisector.py
"""

from __future__ import annotations

from readable_side_splitter import side_splitter  # the proved side-splitter theorem

import pyleanx as pl
from pyleanx import geometry as geo

A, B, C, D, E = geo.points("A B C D E")
dist = geo.dist

angle_bisector = pl.Theorem(
    "angle_bisector", [A, B, C, D],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hD": geo.strictly_between(D, B, C),
        "hbis": geo.angle(B, A, D) == geo.angle(D, A, C),
    },
    conclusion=dist(B, D) / dist(D, C) == dist(A, B) / dist(A, C),
    proof=pl.proof(
        # the auxiliary construction
        pl.let(E, geo.extend_beyond(B, A, dist(A, C)),
               note="extend BA beyond A to E with AE = AC"),
        pl.claim(geo.on_segment(A, B, E), because=geo.extension_between),
        pl.claim(dist(A, E) == dist(A, C), because=geo.extension_length),
        pl.claim(geo.parallel(geo.line(A, D), geo.line(E, C)), because=geo.bisector_parallel),
        # the side-splitter theorem in triangle BEC
        pl.claim(geo.triangle(B, E, C), because=geo.extension_triangle),
        pl.claim(geo.on_segment(D, B, C), because=pl.ref("Sbtw.wbtw")("hD")),
        pl.claim(dist(B, A) / dist(B, E) == dist(B, D) / dist(B, C), because=side_splitter,
                 name="split"),
        # the algebra
        pl.claim(dist(B, A) + dist(A, E) == dist(B, E), because=geo.dist_add_dist("step2"),
                 name="hBE"),
        pl.claim(dist(B, D) + dist(D, C) == dist(B, C), because=geo.dist_add_dist("step6"),
                 name="hBC"),
        pl.claim(dist(B, A) / (dist(B, A) + dist(A, E)) == dist(B, D) / (dist(B, D) + dist(D, C)),
                 because=["split", "hBE", "hBC"], note="BE = BA + AE and BC = BD + DC"),
        pl.claim(dist(A, C) > 0, because=geo.triangle_sides_pos),
        pl.claim(dist(D, C) > 0, because=geo.between_dist_pos),
        pl.claim(dist(B, A) / dist(A, E) == dist(B, D) / dist(D, C), because=geo.componendo,
                 name="ratio"),
        pl.chain(dist(B, D) / dist(D, C),
                 ("=", dist(B, A) / dist(A, E), "ratio"),
                 ("=", dist(A, B) / dist(A, C), ["step3", geo.dist_comm], "AE = AC")),
    ),
)

if __name__ == "__main__":
    result = angle_bisector.verify(timeout=1800)
    print(angle_bisector.prose(result))
    raise SystemExit(0 if result.verified else 1)
