"""The side-splitter theorem without coordinates: points and vectors in the plane.

A, B, C, D, E are points of the Euclidean plane (Mathlib's ``EuclideanSpace ℝ (Fin 2)``);
no coordinates are mentioned anywhere.
  * D lies on line AB:     D − A = s • (B − A)          (s = AD / AB)
  * E lies on line AC:     E − A = t • (C − A)          (t = AE / AC)
  * DE ∥ BC:               E − D = k • (C − B)
  * A, B, C not collinear: the vectors C − A and B − A are linearly independent
    (Mathlib's ``LinearIndependent ℝ ![C − A, B − A]``).
Then s = t, i.e. AD/AB = AE/AC.

The proof:
  1. E − D = (E − A) − (D − A) and C − B = (C − A) − (B − A), so the hypotheses give
         t • (C − A) − s • (B − A) = k • (C − A) − k • (B − A),
     i.e.  t • (C − A) + k • (B − A) = k • (C − A) + s • (B − A).
  2. Coefficients of linearly independent vectors are unique
     (``LinearIndependent.eq_of_pair``): t = k and k = s.  Hence s = t.

Run:  python examples/side_splitter_vectors.py
"""

from __future__ import annotations

import pyleanx as pl

M, H = pl.mathlib, pl.hyp
Plane = pl.EuclideanSpace(2)
A, B, C, D, E = pl.symbols("A B C D E", Plane)
s, t, k = pl.symbols("s t k", pl.Real)

# ![C − A, B − A] and "C − A, B − A are linearly independent over ℝ"
vec_cons = pl.const("Matrix.vecCons", imports=["Mathlib.Data.Fin.VecNotation"])
pair = pl.app(vec_cons, C - A, pl.app(vec_cons, B - A, pl.const("Matrix.vecEmpty")))
independent = pl.app(pl.const("LinearIndependent",
                              imports=["Mathlib.LinearAlgebra.LinearIndependent.Lemmas"]),
                     pl.Real, pair)

side_splitter_vec = pl.Theorem(
    "side_splitter_vec", [A, B, C, D, E, s, t, k],
    assumptions={
        "hD": D - A == pl.smul(s, B - A),        # D on line AB
        "hE": E - A == pl.smul(t, C - A),        # E on line AC
        "hP": E - D == pl.smul(k, C - B),        # DE ∥ BC
        "hABC": independent,                     # A, B, C not collinear
    },
    conclusion=s == t,                           # AD/AB = AE/AC
    proof=pl.proof(
        # 1. rewrite the parallel condition in terms of C − A and B − A
        pl.have("key",
                pl.smul(t, C - A) + pl.smul(k, B - A) == pl.smul(k, C - A) + pl.smul(s, B - A),
                proof=pl.rw(pl.rev(M.sub_eq_sub_iff_add_eq_add), pl.rev(M.smul_sub),
                            pl.rev(H("hD")), pl.rev(H("hE")),
                            M.sub_sub_sub_cancel_right, M.sub_sub_sub_cancel_right,
                            H("hP"))),
        # 2. unique coefficients: t = k and k = s
        pl.obtain("htk hks", M.LinearIndependent.eq_of_pair(H("hABC"), H("key"))),
        pl.linarith(H("htk"), H("hks")),
    ),
)

if __name__ == "__main__":
    r = side_splitter_vec.verify(timeout=1800)
    print(r)
    raise SystemExit(0 if r.verified else 1)
