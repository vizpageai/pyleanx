"""The side-splitter theorem, proved with similar triangles, and checked by Lean.

In triangle ABC, let D lie on side AB and E on side AC with DE ∥ BC. Then
AD/AB = AE/AC.

Proof (as in a geometry course): DE ∥ BC gives two pairs of corresponding angles,
∠ABC = ∠ADE and ∠BCA = ∠DEA. So △ABC ∼ △ADE (AA), and corresponding sides of
similar triangles are proportional.

Compare examples/side_splitter.py (coordinates) and examples/side_splitter_vectors.py
(vectors): same theorem, machine-style proofs.

Run:  python examples/readable_side_splitter.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import geometry as geo

A, B, C, D, E = geo.points("A B C D E")

side_splitter = pl.Theorem(
    "side_splitter_similar", [A, B, C, D, E],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hD": geo.on_segment(D, A, B),
        "hE": geo.on_segment(E, A, C),
        "hP": geo.parallel(geo.line(D, E), geo.line(B, C)),
    },
    conclusion=geo.dist(A, D) / geo.dist(A, B) == geo.dist(A, E) / geo.dist(A, C),
    proof=pl.proof(
        pl.claim(geo.angle(A, B, C) == geo.angle(A, D, E), because=geo.corresponding_angles),
        pl.claim(geo.angle(B, C, A) == geo.angle(D, E, A), because=geo.corresponding_angles),
        pl.claim(geo.similar((A, B, C), (A, D, E)), because=geo.similar_AA),
        pl.conclude(because=geo.similar_sides),
    ),
)

if __name__ == "__main__":
    result = side_splitter.verify(timeout=1800)
    print(side_splitter.prose(result))
    raise SystemExit(0 if result.verified else 1)
