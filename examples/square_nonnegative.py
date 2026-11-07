"""x^2 >= 0 for every real x, proved by `positivity`; plus a variant using a Mathlib lemma."""

import pyleanx as pl

x = pl.symbol("x", pl.Real)

square_nonneg = pl.Theorem("square_nonneg", variables=[x], conclusion=x**2 >= 0)
square_nonneg.prove(pl.positivity())

# Same fact, proved by citing a Mathlib lemma applied to x.
square_nonneg_lemma = pl.Theorem(
    "square_nonneg_by_lemma",
    variables=[x],
    conclusion=0 <= x**2,  # note: renders as `x ^ 2 ≥ 0` (Python reflects the comparison)
    proof=pl.exact(pl.mathlib.sq_nonneg(x)),
)

THEOREMS = [square_nonneg, square_nonneg_lemma]

if __name__ == "__main__":
    for r in pl.verify_all(THEOREMS):
        print(r.summary())
