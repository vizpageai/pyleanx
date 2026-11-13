"""Harmonic analysis as written in a textbook: Fourier series and the Fourier transform.

    from pyleanx import harmonic as ha

Conventions (as in Stein–Shakarchi, *Fourier Analysis*, and Tao's harmonic analysis notes):

* Fourier series live on the circle, parametrised by ``[−π, π]``: for ``f : ℝ → ℂ``,
  ``ha.coeff(f, n)`` is f̂(n) = (1/2π) ∫_{−π}^{π} f(x) e^{−inx} dx (``ha.coeff_eq_integral``),
  Mathlib's ``fourierCoeffOn`` on ``[−π, π]``.
* The Fourier transform on ℝ is f̂(ξ) = ∫ f(x) e^{−2πixξ} dx (``ha.ft``; ``ha.ft_eq_integral``),
  Mathlib's ``𝓕``; ``ha.ift`` is the inverse transform ``𝓕⁻``.
* ``L²``, ``L¹`` and the two sides of Parseval are small Lean definitions shipped here
  (``PyLeanX.Harmonic.*``) and emitted, with the facts proved about them, into every Lean file
  that uses them. Each fact is proved from Mathlib in that file; nothing is assumed.

Not available (Mathlib lacks them at the pinned version): Fejér and Dirichlet kernels and
summability methods, the Hardy–Littlewood maximal inequality, interpolation (Riesz–Thorin,
Marcinkiewicz), the Hilbert transform and Calderón–Zygmund theory.
"""

from __future__ import annotations

from typing import Any

from ._domain import collect_lemmas, lemma
from .complex_analysis import C
from .expr import Expr
from .proofs import library_fact
from .types import Fn, Int, Real

_FOURIER = ("Mathlib.Analysis.Fourier.AddCircle",)
_TRANSFORM = ("Mathlib.Analysis.Fourier.FourierTransform",
              "Mathlib.Analysis.Fourier.RiemannLebesgueLemma",
              "Mathlib.Analysis.Fourier.Inversion",
              "Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform")
_ALL = (*_FOURIER, *_TRANSFORM)

#: sorts: functions on the line/circle with complex values, sequences indexed by ℤ
CFun = Fn(Real, C)
ZSeq = Fn(Int, C)
RZSeq = Fn(Int, Real)


def _c(name: str, latex: str, imports: tuple[str, ...] = _ALL) -> Any:
    from .terms import const
    from .types import UNKNOWN

    return const(name, UNKNOWN, imports=imports, latex=latex)


def _app(name: str, latex: str, *args: object) -> Expr:
    from .terms import apply

    return apply(_c(name, latex), *args)


# =========================================================================================
# Vocabulary
# =========================================================================================

def coeff(f: object, n: object) -> Expr:
    """f̂(n), the n-th Fourier coefficient of ``f`` on [−π, π]."""
    return _app("PyLeanX.Harmonic.coeff", r"\hat{{{0}}}({1})", f, n)


def coeff_seq(f: object) -> Expr:
    """The sequence (f̂(n))_{n ∈ ℤ}."""
    return _app("PyLeanX.Harmonic.coeff", r"\hat{{{0}}}", f)


def ft(f: object, xi: object) -> Expr:
    """f̂(ξ) = ∫ f(x) e^{−2πixξ} dx, the Fourier transform of ``f : ℝ → ℂ`` at ``ξ``."""
    return _app("PyLeanX.Harmonic.ft", r"\hat{{{0}}}({1})", f, xi)


def ft_fun(f: object) -> Expr:
    """The function f̂ (to pass to ``ift`` or to state ``f̂ ∈ L¹``)."""
    return _app("PyLeanX.Harmonic.ft", r"\hat{{{0}}}", f)


def ift(F: object, x: object) -> Expr:
    """F^∨(x) = ∫ F(ξ) e^{2πixξ} dξ, the inverse Fourier transform."""
    return _app("PyLeanX.Harmonic.ift", r"\left({0}\right)^{{\vee}}({1})", F, x)


def gauss(x: object) -> Expr:
    """The Gaussian e^{−πx²}."""
    return _app("PyLeanX.Harmonic.gauss", r"e^{{-\pi {0}^2}}", x)


def gauss_fun() -> Expr:
    """The function x ↦ e^{−πx²}."""
    return _c("PyLeanX.Harmonic.gauss", r"e^{-\pi x^2}")


def L2(f: object) -> Expr:  # noqa: N802 - mathematical name
    """f ∈ L²(−π, π)."""
    return _app("PyLeanX.Harmonic.L2", r"{0} \in L^2(-\pi, \pi)", f)


def integrable_on_circle(f: object) -> Expr:
    """f ∈ L¹(−π, π) (integrable on [−π, π])."""
    return _app("PyLeanX.Harmonic.integrable_on_circle", r"{0} \in L^1(-\pi, \pi)", f)


def integrable(f: object) -> Expr:
    """f ∈ L¹(ℝ)."""
    return _app("MeasureTheory.Integrable", r"{0} \in L^1(\mathbb{{R}})", f)


def continuous(f: object) -> Expr:
    """f is continuous on ℝ."""
    return _app("Continuous", r"{0} \text{{ is continuous}}", f)


def coeff_sq_sum(f: object) -> Expr:
    """∑_{n ∈ ℤ} |f̂(n)|²."""
    return _app("PyLeanX.Harmonic.coeff_sq_sum",
                r"\sum_{{n \in \mathbb{{Z}}}} \left|\hat{{{0}}}(n)\right|^2", f)


def mean_square(f: object) -> Expr:
    """(1/2π) ∫_{−π}^{π} |f(x)|² dx."""
    return _app("PyLeanX.Harmonic.mean_square",
                r"\frac{{1}}{{2\pi}} \int_{{-\pi}}^{{\pi}} \left|{0}(x)\right|^2 \, dx", f)


def derivative(f: object, g: object) -> Expr:
    """f′ = g on ℝ: ``∀ x, HasDerivAt f (g x) x``."""
    from .binders import symbol
    from .expr import Forall

    x = symbol("x", Real)
    return Forall(x, _app("HasDerivAt", r"{0}'({2}) = {1}", f, g(x), x))  # type: ignore[operator]


def summable(u: object) -> Expr:
    """∑_n u(n) converges (``Summable u``)."""
    from .analysis import sequence_latex

    body = sequence_latex(u)
    body = body.replace("{0}_n", "{0}(n)") if body.startswith("{0}_n") else body
    return _app("Summable", r"\sum_{{n \in \mathbb{{Z}}}} " + body + r" \text{{ converges}}", u)


def tends_to_zero(u: object) -> Expr:
    """u(n) → 0 as |n| → ∞ (``Tendsto u cofinite (𝓝 0)``), for ``u`` indexed by ℤ."""
    from .analysis import sequence_latex
    from .terms import apply, const

    body = sequence_latex(u)
    body = body.replace("{0}_n", "{0}(n)") if body.startswith("{0}_n") else body
    t = _c("Filter.Tendsto", body + r" \to 0 \text{{ as }} |n| \to \infty")
    return apply(t, u, const("Filter.cofinite", imports=_ALL),
                 apply(const("nhds", imports=_ALL), 0))


def coeffs_tend_to_zero(f: object) -> Expr:
    """f̂(n) → 0 as |n| → ∞."""
    from .terms import apply, const

    t = _c("Filter.Tendsto", r"{0}(n) \to 0 \text{{ as }} |n| \to \infty")
    return apply(t, coeff_seq(f), const("Filter.cofinite", imports=_ALL),
                 apply(const("nhds", imports=_ALL), 0))

# =========================================================================================
# Shipped definitions and facts (Lean, proved from Mathlib in every file that uses them)
# =========================================================================================

_def_coeff = library_fact(
    "PyLeanX.Harmonic.coeff", """
noncomputable def PyLeanX.Harmonic.coeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (neg_lt_self Real.pi_pos) f n
""", *_ALL,
    label="definition of coeff")

_def_L2 = library_fact(
    "PyLeanX.Harmonic.L2", """
def PyLeanX.Harmonic.L2 (f : ℝ → ℂ) : Prop :=
  MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi))
""", *_ALL,
    label="definition of L2")

_def_integrable_on_circle = library_fact(
    "PyLeanX.Harmonic.integrable_on_circle", """
def PyLeanX.Harmonic.integrable_on_circle (f : ℝ → ℂ) : Prop :=
  IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi
""", *_ALL,
    label="definition of integrable_on_circle")

_def_coeff_sq_sum = library_fact(
    "PyLeanX.Harmonic.coeff_sq_sum", """
noncomputable def PyLeanX.Harmonic.coeff_sq_sum (f : ℝ → ℂ) : ℝ :=
  ∑' n : ℤ, ‖PyLeanX.Harmonic.coeff f n‖ ^ 2
""", *_ALL,
    label="definition of coeff_sq_sum",
    requires=[_def_coeff])

_def_mean_square = library_fact(
    "PyLeanX.Harmonic.mean_square", """
noncomputable def PyLeanX.Harmonic.mean_square (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2
""", *_ALL,
    label="definition of mean_square")

_def_ft = library_fact(
    "PyLeanX.Harmonic.ft", """
noncomputable def PyLeanX.Harmonic.ft (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  FourierTransform.fourier f ξ
""", *_ALL,
    label="definition of ft")

_def_ift = library_fact(
    "PyLeanX.Harmonic.ift", """
noncomputable def PyLeanX.Harmonic.ift (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  FourierTransformInv.fourierInv F x
""", *_ALL,
    label="definition of ift")

_def_gauss = library_fact(
    "PyLeanX.Harmonic.gauss", """
noncomputable def PyLeanX.Harmonic.gauss (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * x ^ 2)
""", *_ALL,
    label="definition of gauss")

_DEFS = (
    _def_coeff,
    _def_L2,
    _def_integrable_on_circle,
    _def_coeff_sq_sum,
    _def_mean_square,
    _def_ft,
    _def_ift,
    _def_gauss,
)

coeff_eq_integral = library_fact(
    "PyLeanX.Harmonic.coeff_eq_integral", """
theorem PyLeanX.Harmonic.coeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    PyLeanX.Harmonic.coeff f n =
      (1 / (2 * Real.pi) : ℝ) • ∫ x in (-Real.pi)..Real.pi,
        Complex.exp (-(n : ℂ) * Complex.I * x) * f x := by
  rw [PyLeanX.Harmonic.coeff, fourierCoeffOn_eq_integral]
  have h2 : (1 / (Real.pi - -Real.pi) : ℝ) = 1 / (2 * Real.pi) := by ring
  rw [h2]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [smul_eq_mul]
  rw [fourier_coe_apply]
  congr 2
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  ring
""", *_ALL,
    label="definition of the Fourier coefficient: f̂(n) = (1/2π) ∫ f(x) e^{−inx} dx",
    requires=_DEFS)

coeff_const_mul = library_fact(
    "PyLeanX.Harmonic.coeff_const_mul", """
theorem PyLeanX.Harmonic.coeff_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    PyLeanX.Harmonic.coeff (fun x => c * f x) n = c * PyLeanX.Harmonic.coeff f n :=
  fourierCoeffOn.const_mul f c n _
""", *_ALL,
    label="linearity of Fourier coefficients: (cf)^(n) = c f̂(n)",
    requires=_DEFS)

coeff_add = library_fact(
    "PyLeanX.Harmonic.coeff_add", """
theorem PyLeanX.Harmonic.coeff_add {f g : ℝ → ℂ} (n : ℤ)
    (hf : PyLeanX.Harmonic.integrable_on_circle f) (hg : PyLeanX.Harmonic.integrable_on_circle g) :
    PyLeanX.Harmonic.coeff (fun x => f x + g x) n =
      PyLeanX.Harmonic.coeff f n + PyLeanX.Harmonic.coeff g n := by
  have hc : ContinuousOn (fun x : ℝ => fourier (-n) (x : AddCircle (Real.pi - -Real.pi)))
      (Set.uIcc (-Real.pi) Real.pi) :=
    ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).continuousOn
  have hf' := hf.continuousOn_mul hc
  have hg' := hg.continuousOn_mul hc
  simp only [PyLeanX.Harmonic.coeff, fourierCoeffOn_eq_integral, smul_eq_mul]
  rw [← smul_add, ← intervalIntegral.integral_add hf' hg']
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [mul_add]
""", *_ALL,
    label="linearity of Fourier coefficients: (f + g)^(n) = f̂(n) + ĝ(n)",
    requires=_DEFS)

coeff_derivative = library_fact(
    "PyLeanX.Harmonic.coeff_derivative", """
theorem PyLeanX.Harmonic.coeff_derivative {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hi : PyLeanX.Harmonic.integrable_on_circle f')
    (hper : f (-Real.pi) = f Real.pi) :
    PyLeanX.Harmonic.coeff f' n = Complex.I * n * PyLeanX.Harmonic.coeff f n := by
  have key := fourierCoeffOn_of_hasDerivAt (neg_lt_self Real.pi_pos) hn
    (fun x _ => hd x) hi
  simp only [PyLeanX.Harmonic.coeff] at *
  rw [key, hper, sub_self, mul_zero, zero_sub]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
  push_cast
  field_simp
  ring
""", *_ALL,
    label="integration by parts: (f′)^(n) = in f̂(n) for periodic f",
    requires=_DEFS)

norm_I_mul_int = library_fact(
    "PyLeanX.Harmonic.norm_I_mul_int", """
theorem PyLeanX.Harmonic.norm_I_mul_int (n : ℤ) (z : ℂ) :
    ‖Complex.I * n * z‖ = |(n : ℝ)| * ‖z‖ := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
""", *_ALL,
    label="|i n z| = |n| |z|",
    requires=_DEFS)

abs_int_ne_zero = library_fact(
    "PyLeanX.Harmonic.abs_int_ne_zero", """
theorem PyLeanX.Harmonic.abs_int_ne_zero {n : ℤ} (hn : n ≠ 0) : |(n : ℝ)| ≠ 0 := by
  simpa using hn
""", *_ALL,
    label="|n| ≠ 0 for n ≠ 0",
    requires=_DEFS)

parseval = library_fact(
    "PyLeanX.Harmonic.parseval", """
theorem PyLeanX.Harmonic.parseval {f : ℝ → ℂ} (hf : PyLeanX.Harmonic.L2 f) :
    PyLeanX.Harmonic.coeff_sq_sum f = PyLeanX.Harmonic.mean_square f := by
  have h := tsum_sq_fourierCoeffOn (neg_lt_self Real.pi_pos) hf
  simp only [PyLeanX.Harmonic.coeff_sq_sum, PyLeanX.Harmonic.mean_square,
    PyLeanX.Harmonic.coeff]
  rw [h, smul_eq_mul]
  congr 1
  rw [one_div]
  congr 1
  ring
""", *_ALL,
    label="Parseval's identity",
    requires=_DEFS)

bessel_summable = library_fact(
    "PyLeanX.Harmonic.bessel_summable", """
theorem PyLeanX.Harmonic.bessel_summable {f : ℝ → ℂ} (hf : PyLeanX.Harmonic.L2 f) :
    Summable (fun n : ℤ => ‖PyLeanX.Harmonic.coeff f n‖ ^ 2) :=
  (hasSum_sq_fourierCoeffOn (neg_lt_self Real.pi_pos) hf).summable
""", *_ALL,
    label="Bessel's inequality: ∑ |f̂(n)|² converges for f ∈ L²",
    requires=_DEFS)

terms_tend_to_zero = library_fact(
    "PyLeanX.Harmonic.terms_tend_to_zero", """
theorem PyLeanX.Harmonic.terms_tend_to_zero {u : ℤ → ℝ} (h : Summable u) :
    Filter.Tendsto u Filter.cofinite (nhds 0) :=
  h.tendsto_cofinite_zero
""", *_ALL,
    label="the terms of a convergent series tend to 0",
    requires=_DEFS)

tendsto_zero_of_norm_sq = library_fact(
    "PyLeanX.Harmonic.tendsto_zero_of_norm_sq", """
theorem PyLeanX.Harmonic.tendsto_zero_of_norm_sq {c : ℤ → ℂ}
    (h : Filter.Tendsto (fun n => ‖c n‖ ^ 2) Filter.cofinite (nhds 0)) :
    Filter.Tendsto c Filter.cofinite (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Real.sqrt_zero] at hs
  refine hs.congr fun n => ?_
  simp [Real.sqrt_sq (norm_nonneg _)]
""", *_ALL,
    label="|cₙ|² → 0 implies cₙ → 0",
    requires=_DEFS)

riemann_lebesgue_coeff = library_fact(
    "PyLeanX.Harmonic.riemann_lebesgue_coeff", """
theorem PyLeanX.Harmonic.riemann_lebesgue_coeff {f : ℝ → ℂ} (hf : PyLeanX.Harmonic.L2 f) :
    Filter.Tendsto (PyLeanX.Harmonic.coeff f) Filter.cofinite (nhds 0) :=
  PyLeanX.Harmonic.tendsto_zero_of_norm_sq
    (PyLeanX.Harmonic.terms_tend_to_zero (PyLeanX.Harmonic.bessel_summable hf))
""", *_ALL,
    label="Riemann–Lebesgue lemma: f̂(n) → 0 as |n| → ∞",
    requires=[*_DEFS, bessel_summable, terms_tend_to_zero, tendsto_zero_of_norm_sq])

sum_of_zero_coeffs = library_fact(
    "PyLeanX.Harmonic.sum_of_zero_coeffs", """
theorem PyLeanX.Harmonic.sum_of_zero_coeffs {f : ℝ → ℂ}
    (h : ∀ n : ℤ, PyLeanX.Harmonic.coeff f n = 0) : PyLeanX.Harmonic.coeff_sq_sum f = 0 := by
  simp [PyLeanX.Harmonic.coeff_sq_sum, h]
""", *_ALL,
    label="a sum of zeros is 0",
    requires=_DEFS)

ft_eq_integral = library_fact(
    "PyLeanX.Harmonic.ft_eq_integral", """
theorem PyLeanX.Harmonic.ft_eq_integral (f : ℝ → ℂ) (ξ : ℝ) :
    PyLeanX.Harmonic.ft f ξ =
      ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * f x := by
  simp only [PyLeanX.Harmonic.ft, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
""", *_ALL,
    label="definition of the Fourier transform: f̂(ξ) = ∫ f(x) e^{−2πixξ} dx",
    requires=_DEFS)

riemann_lebesgue = library_fact(
    "PyLeanX.Harmonic.riemann_lebesgue", """
theorem PyLeanX.Harmonic.riemann_lebesgue (f : ℝ → ℂ) :
    Filter.Tendsto (PyLeanX.Harmonic.ft f) (Filter.cocompact ℝ) (nhds 0) :=
  Real.zero_at_infty_fourier f
""", *_ALL,
    label="Riemann–Lebesgue lemma: f̂(ξ) → 0 as |ξ| → ∞",
    requires=_DEFS)

gaussian = library_fact(
    "PyLeanX.Harmonic.gaussian", """
theorem PyLeanX.Harmonic.gaussian (ξ : ℝ) :
    PyLeanX.Harmonic.ft PyLeanX.Harmonic.gauss ξ = PyLeanX.Harmonic.gauss ξ := by
  have hg : PyLeanX.Harmonic.gauss = fun x : ℝ => Complex.exp (-Real.pi * x ^ 2) := rfl
  have h := congrFun (fourier_gaussian_pi (b := 1) (by simp)) ξ
  rw [PyLeanX.Harmonic.ft, hg]
  simpa using h
""", *_ALL,
    label="the Gaussian e^{−πx²} is its own Fourier transform",
    requires=_DEFS)

inversion = library_fact(
    "PyLeanX.Harmonic.inversion", """
theorem PyLeanX.Harmonic.inversion {f : ℝ → ℂ} (hc : Continuous f)
    (hf : MeasureTheory.Integrable f) (hF : MeasureTheory.Integrable (PyLeanX.Harmonic.ft f))
    (x : ℝ) : f x = PyLeanX.Harmonic.ift (PyLeanX.Harmonic.ft f) x := by
  have := hc.fourierInv_fourier_eq hf hF
  exact (congrFun this x).symm
""", *_ALL,
    label="Fourier inversion formula",
    requires=_DEFS)

ift_at_zero = library_fact(
    "PyLeanX.Harmonic.ift_at_zero", """
theorem PyLeanX.Harmonic.ift_at_zero (F : ℝ → ℂ) :
    PyLeanX.Harmonic.ift F 0 = ∫ ξ : ℝ, F ξ := by
  simp [PyLeanX.Harmonic.ift, Real.fourierInv_eq']
""", *_ALL,
    label="F^∨(0) = ∫ F(ξ) dξ",
    requires=_DEFS)

div_of_mul = library_fact(
    "PyLeanX.Harmonic.div_of_mul", """
theorem PyLeanX.Harmonic.div_of_mul {a b c : ℝ} (hc : c ≠ 0) (h : b = c * a) : a = b / c := by
  rw [h, mul_div_cancel_left₀ a hc]
""", *_ALL,
    label="b = ca with c ≠ 0 gives a = b/c",
    requires=_DEFS)

div_div = lemma("div_div", "Mathlib.Algebra.Group.Basic", label="a/b/c = a/(bc)")

LEMMAS = collect_lemmas(globals())
