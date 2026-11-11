"""The side-splitter (triangle proportionality) theorem, checked by Lean + Mathlib.

A line parallel to one side of a triangle cuts the other two sides in the same ratio.

Triangle ABC in the plane, with coordinates A = (a₁, a₂), B = (b₁, b₂), C = (c₁, c₂).
  * D lies on line AB:   D = A + s·(B − A)       (s = AD / AB)
  * E lies on line AC:   E = A + t·(C − A)       (t = AE / AC)
  * DE ∥ BC:             E − D = k·(C − B) for some k
  * ABC is a real triangle (not collinear): the cross product (B − A) × (C − A) ≠ 0.
Then s = t, i.e. AD/AB = AE/AC (and so AD/DB = AE/EC as well).

The proof, step by step:
  1. Subtract the equations for D and E: (t − k)(C − A) = (s − k)(B − A), per coordinate.
  2. Cross with (B − A) and (C − A): (t − k)·cross = 0 and (s − k)·cross = 0.
  3. cross ≠ 0, so t = k and s = k; hence s = t.

Run:  python examples/side_splitter.py
"""

from __future__ import annotations

import pyleanx as pl

M = pl.mathlib
a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, s, t, k = pl.symbols(
    "a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ s t k", pl.Real)

# u = B − A, v = C − A, and their cross product
u1, u2 = b1 - a1, b2 - a2
v1, v2 = c1 - a1, c2 - a2
cross = u1 * v2 - u2 * v1

H = pl.hyp
side_splitter = pl.Theorem(
    "side_splitter", [a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, s, t, k],
    assumptions={
        "hD1": d1 == a1 + s * u1, "hD2": d2 == a2 + s * u2,      # D on AB
        "hE1": e1 == a1 + t * v1, "hE2": e2 == a2 + t * v2,      # E on AC
        "hP1": e1 - d1 == k * (c1 - b1),                          # DE ∥ BC
        "hP2": e2 - d2 == k * (c2 - b2),
        "hABC": pl.Not(cross == 0),                               # A, B, C not collinear
    },
    conclusion=s == t,                                            # AD/AB = AE/AC
    proof=pl.proof(
        # 1. (t − k)·v = (s − k)·u, coordinate by coordinate
        pl.have("h1", (t - k) * v1 == (s - k) * u1, proof=pl.linarith()),
        pl.have("h2", (t - k) * v2 == (s - k) * u2, proof=pl.linarith()),
        # 2. multiply out against the cross product
        pl.have("kt", (t - k) * cross == 0, proof=pl.calc(
            (t - k) * cross,
            ("=", u1 * ((t - k) * v2) - u2 * ((t - k) * v1), pl.ring()),
            ("=", u1 * ((s - k) * u2) - u2 * ((s - k) * u1), pl.rw(H("h1"), H("h2"))),
            ("=", 0, pl.ring()))),
        pl.have("ks", (s - k) * cross == 0, proof=pl.calc(
            (s - k) * cross,
            ("=", v2 * ((s - k) * u1) - v1 * ((s - k) * u2), pl.ring()),
            ("=", v2 * ((t - k) * v1) - v1 * ((t - k) * v2),
             pl.rw(pl.rev(H("h1")), pl.rev(H("h2")))),
            ("=", 0, pl.ring()))),
        # 3. the cross product is not zero, so t − k = 0 and s − k = 0
        pl.have("tk", t - k == 0,
                proof=pl.exact(M.eq_zero_of_ne_zero_of_mul_right_eq_zero(H("hABC"), H("kt")))),
        pl.have("sk", s - k == 0,
                proof=pl.exact(M.eq_zero_of_ne_zero_of_mul_right_eq_zero(H("hABC"), H("ks")))),
        pl.linarith(H("tk"), H("sk")),
    ),
)

if __name__ == "__main__":
    r = side_splitter.verify(timeout=1800)
    print(r)
    raise SystemExit(0 if r.verified else 1)
