"""The Hilbert transform on L²(ℝ), as PyLeanX written proofs checked by Lean.

Stein, *Singular Integrals*, ch. II §1, and Tao's notes: for f ∈ L²(ℝ),
Hf = 𝓕⁻(m·𝓕f) with m(ξ) = −i sgn ξ. Then

    10. |m(ξ)| = 1 and m(ξ)² = −1 for ξ ≠ 0;
    11. ‖m·F‖₂ = ‖F‖₂;
    12. m·(m·F) = −F;
    13. ‖Hf‖₂ = ‖f‖₂                    (H is an isometry of L²);
    14. H(Hf) = −f                      (H² = −I).

The definitions (m, the operator F ↦ m·F, H) are in ``pyleanx.hilbert``; every theorem here
is a written proof whose steps cite Mathlib (Plancherel on L², the a.e. calculus of L²) or an
earlier theorem. Run:  python examples/hilbert_transform.py
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import complex_analysis as ca
from pyleanx import hilbert as hil

F, f = pl.symbols("F f", hil.L2)
xi = pl.symbol("ξ", pl.Real)
m = hil.symbol
I_ = ca.I


def sgn(x: object) -> pl.Expr:
    return pl.app(pl.const("Real.sign", imports=("Mathlib.Basic.Real.Sign",),
                           latex=r"\operatorname{sgn}"), x)


def as_c(x: object) -> pl.Expr:
    from pyleanx.terms import ascribe

    return ascribe(x, ca.C)


def _symbol_cases(goal_of: object, final: object, facts: list) -> pl.Tactic:
    """For ξ ≠ 0: the two cases ξ < 0 and ξ > 0 of a statement about m(ξ)."""
    claim, chain, case = pl.claim, pl.chain, pl.case
    unfolded = -I_() * as_c(sgn(xi))

    def branch(cond: object, value: int, fact: object, name: str) -> pl.Case:
        return case(cond,
                    claim(sgn(xi) == pl.real(value), because=[fact, "h"], name="hs"),
                    claim(m(xi) == unfolded, name="hdef", note="definition of m"),
                    chain(goal_of(m(xi)),
                          ("=", goal_of(unfolded), "hdef"),
                          ("=", goal_of(-I_() * as_c(pl.real(value))), "hs"),
                          ("=", final, facts)),
                    name=name)

    return pl.cases_on(branch(xi < 0, -1, hil.sign_neg, "h"),
                       branch(xi > 0, 1, hil.sign_pos, "h"),
                       because=[hil.lt_or_gt, "hξ"])


# -----------------------------------------------------------------------------------------
# 10. The symbol: |m(ξ)| = 1 and m(ξ)² = −1 for ξ ≠ 0
# -----------------------------------------------------------------------------------------

symbol_norm = pl.Theorem(
    "hilbert_symbol_norm", [xi],
    assumptions={"hξ": xi != 0},
    conclusion=pl.norm(m(xi)) == 1,
    proof=pl.proof(_symbol_cases(lambda z: pl.norm(z), 1, [hil.norm_mul, hil.norm_I])),
)

symbol_sq = pl.Theorem(
    "hilbert_symbol_sq", [xi],
    assumptions={"hξ": xi != 0},
    conclusion=m(xi) * m(xi) == -1,
    proof=pl.proof(_symbol_cases(lambda z: z * z, -1, [hil.I_mul_I])),
)


# -----------------------------------------------------------------------------------------
# 11. ‖m·F‖₂ = ‖F‖₂
# -----------------------------------------------------------------------------------------

def _mul_norm_proof() -> pl.Tactic:
    claim, fix, chain = pl.claim, pl.fix, pl.chain
    mF = hil.mul_symbol(F)
    pointwise = pl.fun(lambda s: m(s) * F(s), pl.Real)
    both = lambda s: pl.And(mF(s) == m(s) * F(s), s != 0)  # noqa: E731
    return pl.proof(
        claim(hil.ae_eq(mF, pointwise), because=hil.coe_to_lp, name="hae",
              note="m·F is the L² class of ξ ↦ m(ξ)F(ξ)"),
        claim(hil.ae(lambda s: s != 0), because=hil.ae_ne, name="hne"),
        claim(hil.ae(both), because=[hil.ae_and, "hae", "hne"], name="hboth"),
        claim(pl.Forall(xi, pl.Implies(both(xi), pl.norm(mF(xi)) == pl.norm(F(xi)))),
              name="hpt", note="|m(ξ)F(ξ)| = |m(ξ)||F(ξ)| = |F(ξ)|",
              proof=pl.proof(
                  fix(xi, assume={"h": both(xi)}),
                  claim(mF(xi) == m(xi) * F(xi), because="h", name="hval"),
                  claim(xi != 0, because="h", name="hξ"),
                  claim(pl.norm(m(xi)) == 1, because=[symbol_norm, "hξ"], name="h1"),
                  chain(pl.norm(mF(xi)),
                        ("=", pl.norm(m(xi) * F(xi)), "hval"),
                        ("=", pl.norm(m(xi)) * pl.norm(F(xi)), hil.norm_mul),
                        ("=", 1 * pl.norm(F(xi)), "h1"),
                        ("=", pl.norm(F(xi)), hil.one_mul)),
              )),
        claim(hil.ae(lambda s: pl.norm(mF(s)) == pl.norm(F(s))),
              because=[hil.ae_mono, "hboth", "hpt"], name="hnorm_ae"),
        claim(hil.l2_norm_sq_def(mF) == hil.l2_norm_sq_def(F),
              because=[hil.norm_congr_ae, hil.lp_measurable, "hnorm_ae"], name="heLp"),
        pl.conclude(because=[hil.lp_norm_def, "heLp"]),
    )


mul_symbol_norm = pl.Theorem(
    "hilbert_multiplier_isometry", [F],
    conclusion=pl.norm(hil.mul_symbol(F)) == pl.norm(F),
    proof=_mul_norm_proof(),
)


# -----------------------------------------------------------------------------------------
# 12. m·(m·F) = −F
# -----------------------------------------------------------------------------------------

def _twice_proof() -> pl.Tactic:
    claim, fix, chain = pl.claim, pl.fix, pl.chain
    mF = hil.mul_symbol(F)
    mmF = hil.mul_symbol(mF)
    negF = -F
    all4 = lambda s: pl.And(mmF(s) == m(s) * mF(s), mF(s) == m(s) * F(s),  # noqa: E731
                            negF(s) == -F(s), s != 0)
    return pl.proof(
        claim(hil.ae_eq(mmF, pl.fun(lambda s: m(s) * mF(s), pl.Real)), because=hil.coe_to_lp,
              name="h1"),
        claim(hil.ae_eq(mF, pl.fun(lambda s: m(s) * F(s), pl.Real)), because=hil.coe_to_lp,
              name="h2"),
        claim(hil.ae_eq(negF, hil.neg_fn(F)), because=hil.coe_neg, name="h3"),
        claim(hil.ae(lambda s: s != 0), because=hil.ae_ne, name="h4"),
        claim(hil.ae(lambda s: pl.And(negF(s) == -F(s), s != 0)),
              because=[hil.ae_and, "h3", "h4"], name="h34"),
        claim(hil.ae(lambda s: pl.And(mF(s) == m(s) * F(s), negF(s) == -F(s), s != 0)),
              because=[hil.ae_and, "h2", "h34"], name="h234"),
        claim(hil.ae(all4), because=[hil.ae_and, "h1", "h234"], name="hall"),
        claim(pl.Forall(xi, pl.Implies(all4(xi), mmF(xi) == negF(xi))), name="hpt",
              note="m(ξ)·m(ξ)·F(ξ) = −F(ξ) for ξ ≠ 0",
              proof=pl.proof(
                  fix(xi, assume={"h": all4(xi)}),
                  claim(mmF(xi) == m(xi) * mF(xi), because="h", name="ha"),
                  claim(mF(xi) == m(xi) * F(xi), because="h", name="hb"),
                  claim(negF(xi) == -F(xi), because="h", name="hc"),
                  claim(xi != 0, because="h", name="hξ"),
                  claim(m(xi) * m(xi) == -1, because=[symbol_sq, "hξ"], name="hsq"),
                  chain(mmF(xi),
                        ("=", m(xi) * mF(xi), "ha"),
                        ("=", m(xi) * (m(xi) * F(xi)), "hb"),
                        ("=", m(xi) * m(xi) * F(xi), None, "regroup"),
                        ("=", -1 * F(xi), "hsq"),
                        ("=", -F(xi), None, "−1·a = −a"),
                        ("=", negF(xi), "hc")),
              )),
        claim(hil.ae(lambda s: mmF(s) == negF(s)), because=[hil.ae_mono, "hall", "hpt"],
              name="hae"),
        pl.conclude(because=[hil.lp_ext, "hae"]),
    )


mul_symbol_twice = pl.Theorem(
    "hilbert_multiplier_twice", [F],
    conclusion=hil.mul_symbol(hil.mul_symbol(F)) == -F,
    proof=_twice_proof(),
)


# -----------------------------------------------------------------------------------------
# 13. ‖Hf‖₂ = ‖f‖₂  and  14. H(Hf) = −f
# -----------------------------------------------------------------------------------------

def _isometry_proof() -> pl.Tactic:
    G = hil.mul_symbol(hil.ft(f))
    return pl.proof(
        pl.claim(pl.norm(hil.ft(hil.ift(G))) == pl.norm(hil.ift(G)), because=hil.plancherel,
                 name="hinv", note="Plancherel for 𝓕⁻G"),
        pl.chain(pl.norm(hil.H(f)),
                 ("=", pl.norm(hil.ift(G)), None, "definition of H"),
                 ("=", pl.norm(hil.ft(hil.ift(G))), "hinv"),
                 ("=", pl.norm(G), hil.fourier_fourier_inv),
                 ("=", pl.norm(hil.ft(f)), mul_symbol_norm),
                 ("=", pl.norm(f), hil.plancherel)),
    )


isometry = pl.Theorem(
    "hilbert_isometry", [f],
    conclusion=pl.norm(hil.H(f)) == pl.norm(f),
    proof=_isometry_proof(),
)


def _square_proof() -> pl.Tactic:
    G = hil.mul_symbol(hil.ft(f))
    return pl.proof(
        pl.chain(hil.H(hil.H(f)),
                 ("=", hil.ift(hil.mul_symbol(hil.ft(hil.ift(G)))), None, "definition of H"),
                 ("=", hil.ift(hil.mul_symbol(G)), hil.fourier_fourier_inv),
                 ("=", hil.ift(-hil.ft(f)), mul_symbol_twice),
                 ("=", -hil.ift(hil.ft(f)), hil.fourier_inv_neg),
                 ("=", -f, hil.fourier_inv_fourier)),
    )


square = pl.Theorem(
    "hilbert_square", [f],
    conclusion=hil.H(hil.H(f)) == -f,
    proof=_square_proof(),
)

THEOREMS = [symbol_norm, symbol_sq, mul_symbol_norm, mul_symbol_twice, isometry, square]

if __name__ == "__main__":
    import sys

    results = pl.verify_all(THEOREMS, timeout=3600)
    ok = True
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
        if not res.verified:
            for d in res.errors[:4]:
                print("   ", d.span_label, "|", d.message[:400].replace("\n", " | "))
        ok = ok and res.verified
    sys.exit(0 if ok else 1)
