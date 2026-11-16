"""The side-splitter theorem, proved with similar triangles, and checked by Lean.

In triangle ABC, let D lie on side AB and E on side AC with DE ∥ BC. Then
AD/AB = AE/AC.

Proof (as in a geometry course): DE ∥ BC gives two pairs of corresponding angles,
∠ABC = ∠ADE and ∠BCA = ∠DEA. So △ABC ∼ △ADE (AA), and corresponding sides of
similar triangles are proportional.

The textbook form AD/DB = AE/EC (the parallel splits the two sides proportionally) follows
for D, E strictly inside the sides: segment addition gives AB = AD + DB and AC = AE + EC,
so AD/(AD + DB) = AE/(AE + EC), and componendo gives AD/DB = AE/EC.

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

dist = geo.dist

side_splitter_parts = pl.Theorem(
    "side_splitter_parts", [A, B, C, D, E],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hD": geo.strictly_between(D, A, B),
        "hE": geo.strictly_between(E, A, C),
        "hP": geo.parallel(geo.line(D, E), geo.line(B, C)),
    },
    conclusion=dist(A, D) / dist(D, B) == dist(A, E) / dist(E, C),
    proof=pl.proof(
        pl.claim(geo.on_segment(D, A, B), because=pl.ref("Sbtw.wbtw")("hD"), name="hD'"),
        pl.claim(geo.on_segment(E, A, C), because=pl.ref("Sbtw.wbtw")("hE"), name="hE'"),
        pl.claim(dist(A, D) / dist(A, B) == dist(A, E) / dist(A, C), because=side_splitter,
                 name="split", note="the side-splitter theorem (similar triangles)"),
        pl.claim(dist(A, D) + dist(D, B) == dist(A, B), because=geo.dist_add_dist("hD'"),
                 name="hAB", note="segment addition: AD + DB = AB"),
        pl.claim(dist(A, E) + dist(E, C) == dist(A, C), because=geo.dist_add_dist("hE'"),
                 name="hAC", note="segment addition: AE + EC = AC"),
        pl.claim(dist(A, D) / (dist(A, D) + dist(D, B)) == dist(A, E) / (dist(A, E) + dist(E, C)),
                 because=["split", "hAB", "hAC"], name="hsum"),
        pl.claim(dist(D, B) > 0, because=[geo.between_dist_pos, "hD"], name="hDB"),
        pl.claim(dist(E, C) > 0, because=[geo.between_dist_pos, "hE"], name="hEC"),
        pl.conclude(because=[geo.componendo, "hsum", "hDB", "hEC"]),
    ),
)

if __name__ == "__main__":
    results = pl.verify_all([side_splitter, side_splitter_parts], timeout=1800)
    for thm, result in zip([side_splitter, side_splitter_parts], results, strict=True):
        print(thm.prose(result), "\n")
    raise SystemExit(0 if all(r.verified for r in results) else 1)
