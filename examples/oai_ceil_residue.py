"""A real lemma from OpenAI's `openai/math`, rewritten in PyLeanX with Mathlib only.

Source: github.com/openai/math @ 4eaee87, file
lean/OAI/NumberTheory/EgyptianFractions/CeilResidue.lean (imports only Mathlib), part of
the Egyptian-fractions development ("Problem 337"):

    theorem residue_div_eq_fract_neg {u N z h : ℕ} (hh : h < u)
        (heq : u * z = N + h) :
        (h : ℝ) / u = Int.fract (-(N : ℝ) / u)

In words: if a ceiling step writes u·z = N + h with remainder h < u, then the remainder
divided by u is the fractional part of −N/u. The proof below follows the same route as
OAI's (Mathlib's characterisation `Int.fract_eq_iff`, integer witness −z), in PyLeanX's
typed proof steps instead of Lean tactic text.

Run:  python examples/oai_ceil_residue.py
"""

from __future__ import annotations

import pyleanx as pl

M = pl.mathlib  # every Mathlib name, no module paths
R = pl.Real

u, N, z, h = pl.symbols("u N z h", pl.Nat)
uR, NR, zR, hR = (pl.cast(v, R) for v in (u, N, z, h))  # (u : ℝ), …

residue_div_eq_fract_neg = pl.Theorem(
    "residue_div_eq_fract_neg",
    [u, N, z, h],
    assumptions={"hh": h < u, "heq": u * z == N + h},
    conclusion=hR / uR == M.Int.fract(-NR / uR),
    # Instances are not named in the statement, so they cannot be found by name: the
    # instance `FloorRing ℝ` (needed by Int.fract on ℝ) lives in this module.
    imports=["Mathlib.Algebra.Order.Archimedean.Real.Basic"],
    proof=pl.proof(
        # facts over ℝ from the hypotheses over ℕ
        pl.have("hu0", 0 < u, proof=pl.omega()),               # from h < u
        pl.have("hu", 0 < uR, proof=pl.simp(pl.hyp("hu0"))),
        pl.have("heqR", uR * zR == NR + hR,
                proof=pl.rw(pl.rev(M.Nat.cast_mul), pl.rev(M.Nat.cast_add), pl.hyp("heq"))),
        # fract a = b  ↔  0 ≤ b ∧ b < 1 ∧ ∃ m : ℤ, a - b = m
        pl.apply(M.Eq.symm),
        pl.rw(M.Int.fract_eq_iff),
        pl.constructor(),
        pl.positivity(),                                        # 0 ≤ h / u
        pl.constructor(),
        pl.rw(M.div_lt_one(pl.hyp("hu")), M.Nat.cast_lt) >> pl.exact(pl.hyp("hh")),  # h/u < 1
        pl.use(-pl.cast(z, pl.Int)),                            # the integer: −z
        pl.rw(M.Int.cast_neg, M.Int.cast_natCast, pl.rev(M.sub_div),
              M.div_eq_iff(M.Ne.symm(M.ne_of_lt(pl.hyp("hu"))))),   # u ≠ 0
        pl.linarith(pl.hyp("heqR")),                            # −N − h = −z·u
    ),
)

if __name__ == "__main__":
    print(residue_div_eq_fract_neg.to_lean())
    result = residue_div_eq_fract_neg.verify(timeout=1800)
    print(result.summary())
    raise SystemExit(0 if result.verified else 1)
