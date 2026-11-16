"""The Hilbert transform on L²(ℝ) (Stein, *Singular Integrals*, ch. II §1; Tao's notes).

    from pyleanx import hilbert as hil

Hf = 𝓕⁻(m · 𝓕f) with the symbol m(ξ) = −i sgn ξ, for f ∈ L²(ℝ) (Mathlib's Fourier transform
on L² is a linear isometry, Plancherel). This module ships the *definitions* — the symbol,
the multiplication operator F ↦ m·F on L² (its definition contains the one-line proof that
m·F is again in L², because |m| ≤ 1) and H itself — and the vocabulary to write statements.
The theorems about H (‖Hf‖ = ‖f‖, H² = −I, …) are PyLeanX written proofs in
``examples/hilbert_transform.py``, checked by Lean.
"""

from __future__ import annotations

from typing import Any

from ._domain import collect_lemmas, lemma
from .expr import Expr
from .proofs import library_fact
from .types import lean_type

_IMPORTS = ("Mathlib.Analysis.Fourier.LpSpace", "Mathlib.Basic.Real.Sign",
            "Mathlib.MeasureTheory.Function.LpSpace.Basic",
            "Mathlib.MeasureTheory.Function.SpecialFunctions.Basic",
            "Mathlib.MeasureTheory.Constructions.BorelSpace.Order",
            "Mathlib.Tactic.SplitIfs")

#: L²(ℝ) with complex values
L2 = lean_type("MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)",
               _IMPORTS, latex=r"L^2(\mathbb{R})")


def _c(name: str, latex: str) -> Any:
    from .terms import const
    from .types import UNKNOWN

    return const(name, UNKNOWN, imports=_IMPORTS, latex=latex)


def _app(name: str, latex: str, *args: object) -> Expr:
    from .terms import apply

    return apply(_c(name, latex), *args)


def symbol(xi: object) -> Expr:
    """m(ξ) = −i sgn ξ."""
    return _app("PyLeanX.Hilbert.symbol", r"m({0})", xi)


def symbol_fun() -> Expr:
    """The function m."""
    return _c("PyLeanX.Hilbert.symbol", "m")


def mul_symbol(F: object) -> Expr:  # noqa: N803
    """m·F, the multiplication operator on L²."""
    return _app("PyLeanX.Hilbert.mulSymbol", r"m {0}{*}", F)


def H(f: object) -> Expr:  # noqa: N802
    """Hf, the Hilbert transform of f ∈ L²."""
    return _app("PyLeanX.Hilbert.hilbert", r"H{0}{*}", f)


def ft(F: object) -> Expr:  # noqa: N802
    """𝓕F, the Fourier transform on L²."""
    return _app("FourierTransform.fourier", r"\hat{{{0}}}{*}", F)


def ift(F: object) -> Expr:  # noqa: N802
    """𝓕⁻F, the inverse Fourier transform on L²."""
    return _app("FourierTransformInv.fourierInv", r"{0}^{{\vee}}{*}", F)


def ae_eq(F: object, G: object) -> Expr:  # noqa: N803
    """F = G almost everywhere (as functions on ℝ)."""
    from .terms import apply, const

    ae = apply(const("MeasureTheory.ae", imports=_IMPORTS, latex=""),
               const("MeasureTheory.volume", imports=_IMPORTS, latex=""))
    return apply(_c("Filter.EventuallyEq", r"{1} = {2} \text{{ a.e.}}"), ae, F, G)


def ae(body: Any) -> Expr:
    """∀ᵐ ξ, body(ξ): body holds for almost every ξ ∈ ℝ."""
    from .terms import apply, const, fun
    from .types import Real

    ae_ = apply(const("MeasureTheory.ae", imports=_IMPORTS, latex=""),
                const("MeasureTheory.volume", imports=_IMPORTS, latex=""))
    lam = fun(body, Real)
    tex = (r"\text{for a.e. } " + lam.vars[0].name + ": " + lam.body.to_latex())
    tex = tex.replace("{", "{{").replace("}", "}}") + "{0:.0}{1:.0}"
    return apply(_c("Filter.Eventually", tex), lam, ae_)


def l2_norm_sq_def(F: object) -> Expr:
    """eLpNorm F 2 (the L² norm, in [0, ∞])."""
    from .terms import const

    return _app("MeasureTheory.eLpNorm", r"\|{0}\|_2", F, 2,
                const("MeasureTheory.volume", imports=_IMPORTS, latex=""))


def neg_fn(F: object) -> Expr:  # noqa: N803
    """The function ξ ↦ −F(ξ) (pointwise negative of an L² representative)."""
    return _app("Neg.neg", r"-{0}", F)


# =========================================================================================
# Shipped definitions (with the two small facts the definition of m·F needs)
# =========================================================================================

_def_symbol = library_fact("PyLeanX.Hilbert.symbol", r"""
noncomputable def PyLeanX.Hilbert.symbol (ξ : ℝ) : ℂ := -Complex.I * (Real.sign ξ : ℂ)
""", *_IMPORTS, label="definition of the symbol m(ξ) = −i sgn ξ")

_symbol_measurable = library_fact("PyLeanX.Hilbert.symbol_measurable", r"""
theorem PyLeanX.Hilbert.symbol_measurable : Measurable PyLeanX.Hilbert.symbol := by
  have h : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const)
  unfold PyLeanX.Hilbert.symbol
  exact measurable_const.mul (Complex.measurable_ofReal.comp h)
""", *_IMPORTS, label="m is measurable", requires=[_def_symbol])

_norm_symbol_le = library_fact("PyLeanX.Hilbert.norm_symbol_le", r"""
theorem PyLeanX.Hilbert.norm_symbol_le (ξ : ℝ) : ‖PyLeanX.Hilbert.symbol ξ‖ ≤ 1 := by
  unfold PyLeanX.Hilbert.symbol
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold Real.sign; split_ifs <;> simp
""", *_IMPORTS, label="|m| ≤ 1", requires=[_def_symbol])

_def_mul_symbol = library_fact("PyLeanX.Hilbert.mulSymbol", r"""
noncomputable def PyLeanX.Hilbert.mulSymbol
    (F : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  MeasureTheory.MemLp.toLp (fun ξ => PyLeanX.Hilbert.symbol ξ * F ξ)
    ((MeasureTheory.Lp.memLp F).of_le
      (PyLeanX.Hilbert.symbol_measurable.aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable F))
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (PyLeanX.Hilbert.norm_symbol_le ξ)))
""", *_IMPORTS, label="definition of the multiplication operator F ↦ m·F on L²",
    requires=[_def_symbol, _symbol_measurable, _norm_symbol_le])

_def_hilbert = library_fact("PyLeanX.Hilbert.hilbert", r"""
noncomputable def PyLeanX.Hilbert.hilbert
    (f : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  FourierTransformInv.fourierInv (PyLeanX.Hilbert.mulSymbol (FourierTransform.fourier f))
""", *_IMPORTS, label="definition of the Hilbert transform Hf = 𝓕⁻(m·𝓕f)",
    requires=[_def_mul_symbol])


# =========================================================================================
# Mathlib facts used by the proofs
# =========================================================================================

_LP = "Mathlib.MeasureTheory.Function.LpSpace.Basic"
plancherel = lemma("MeasureTheory.Lp.norm_fourier_eq", "Mathlib.Analysis.Fourier.LpSpace",
                   label="Plancherel: ‖𝓕F‖₂ = ‖F‖₂")
fourier_inv_fourier = lemma("fourierInv_fourier_eq", "Mathlib.Analysis.Fourier.LpSpace",
                            label="𝓕⁻(𝓕F) = F")
fourier_fourier_inv = lemma("fourier_fourierInv_eq", "Mathlib.Analysis.Fourier.LpSpace",
                            label="𝓕(𝓕⁻F) = F")
fourier_inv_neg = lemma("fourierInv_neg", "Mathlib.Analysis.Fourier.LpSpace",
                        label="𝓕⁻(−F) = −𝓕⁻F")
coe_to_lp = lemma("MeasureTheory.MemLp.coeFn_toLp", _LP,
                  label="the L² class of a function agrees with it a.e.")
coe_neg = lemma("MeasureTheory.Lp.coeFn_neg", _LP, label="(−F)(ξ) = −F(ξ) a.e.")
lp_ext = lemma("MeasureTheory.Lp.ext", _LP, label="L² elements equal a.e. are equal")
lp_norm_def = lemma("MeasureTheory.Lp.norm_def", _LP, label="the L² norm")
lp_measurable = lemma("MeasureTheory.Lp.aestronglyMeasurable", _LP,
                      label="an L² function is measurable")
norm_congr_ae = lemma("MeasureTheory.eLpNorm_congr_norm_ae",
                      "Mathlib.MeasureTheory.Function.LpSeminorm.Basic",
                      label="functions with equal |·| a.e. have equal norms")
ae_ne = lemma("MeasureTheory.Measure.ae_ne",
              "Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass",
              label="ξ ≠ 0 for almost every ξ")
ae_and = lemma("Filter.Eventually.and", "Mathlib.Order.Filter.Basic",
               label="two a.e. statements hold together a.e.")
ae_mono = lemma("Filter.Eventually.mono", "Mathlib.Order.Filter.Basic",
                label="what follows pointwise from an a.e. statement holds a.e.")
sign_pos = lemma("Real.sign_of_pos", "Mathlib.Basic.Real.Sign", label="sgn ξ = 1 for ξ > 0")
sign_neg = lemma("Real.sign_of_neg", "Mathlib.Basic.Real.Sign", label="sgn ξ = −1 for ξ < 0")
norm_mul = lemma("norm_mul", "Mathlib.Analysis.Normed.Field.Basic", label="|ab| = |a||b|")
norm_I = lemma("Complex.norm_I", "Mathlib.Analysis.Complex.Basic", label="|i| = 1")
I_mul_I = lemma("Complex.I_mul_I", "Mathlib.Analysis.Complex.Basic", label="i² = −1")
one_mul = lemma("one_mul", "Mathlib.Algebra.Group.Defs", label="1·a = a")
lt_or_gt = lemma("lt_or_gt_of_ne", "Mathlib.Order.Basic", label="ξ ≠ 0 means ξ < 0 or ξ > 0")

LEMMAS = collect_lemmas(globals())
