"""The side-splitter theorem, proved with similar triangles, and checked by Lean.

In triangle ABC, let D lie on side AB and E on side AC with DE ∥ BC. Then
AD/AB = AE/AC.

Proof (as in a geometry course): DE ∥ BC gives two pairs of corresponding angles,
∠ABC = ∠ADE and ∠BCA = ∠DEA. So △ABC ∼ △ADE (AA), and corresponding sides of
similar triangles are proportional.

The textbook form AD/DB = AE/EC (the parallel splits the two sides proportionally) follows
for D, E strictly inside the sides: segment addition gives AB = AD + DB and AC = AE + EC,
so flipping AD/AB = AE/AC gives (AD + DB)/AD = (AE + EC)/AE, i.e.
1 + DB/AD = 1 + EC/AE; subtract 1 and flip back.

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

AD, DB, AB = geo.dist(A, D), geo.dist(D, B), geo.dist(A, B)
AE, EC, AC = geo.dist(A, E), geo.dist(E, C), geo.dist(A, C)

side_splitter_parts = pl.Theorem(
    "side_splitter_parts", [A, B, C, D, E],
    assumptions={
        "hABC": geo.triangle(A, B, C),
        "hD": geo.strictly_between(D, A, B),
        "hE": geo.strictly_between(E, A, C),
        "hP": geo.parallel(geo.line(D, E), geo.line(B, C)),
    },
    conclusion=AD / DB == AE / EC,
    proof=pl.proof(
        pl.claim(geo.angle(A, B, C) == geo.angle(A, D, E), because=geo.corresponding_angles),
        pl.claim(geo.angle(B, C, A) == geo.angle(D, E, A), because=geo.corresponding_angles),
        pl.claim(geo.similar((A, B, C), (A, D, E)), because=geo.similar_AA),
        pl.claim(AD / AB == AE / AC, because=geo.similar_sides, name="ratio"),
        pl.claim(AB / AD == AC / AE, because=[geo.flip_ratio, "ratio"], name="flipped"),
        pl.claim(AB == AD + DB, because=[geo.segment_addition, "hD"], name="hAB"),
        pl.claim(AC == AE + EC, because=[geo.segment_addition, "hE"], name="hAC"),
        pl.claim((AD + DB) / AD == (AE + EC) / AE, because=["flipped", "hAB", "hAC"],
                 name="sub", note="substitute AB = AD + DB and AC = AE + EC"),
        pl.claim(AD > 0, because=[geo.between_dist_pos, "hD"], name="hAD"),
        pl.claim(AE > 0, because=[geo.between_dist_pos, "hE"], name="hAE"),
        pl.claim((AD + DB) / AD == 1 + DB / AD, because=[geo.split_fraction, "hAD"], name="s1"),
        pl.claim((AE + EC) / AE == 1 + EC / AE, because=[geo.split_fraction, "hAE"], name="s2"),
        pl.claim(DB / AD == EC / AE, because=["sub", "s1", "s2"], name="rest",
                 note="subtract 1 from both sides"),
        pl.conclude(because=[geo.flip_ratio, "rest"]),
    ),
)

if __name__ == "__main__":
    results = pl.verify_all([side_splitter, side_splitter_parts], timeout=1800)
    for thm, result in zip([side_splitter, side_splitter_parts], results, strict=True):
        print(thm.prose(result), "\n")
    raise SystemExit(0 if all(r.verified for r in results) else 1)
