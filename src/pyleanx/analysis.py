"""Real analysis basics: elementary functions on ℝ and their standard facts.

    from pyleanx import analysis as an
    x = pl.symbol("x", pl.Real)
    pl.Theorem("pythagorean_trig", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
               proof=pl.exact(an.sin_sq_add_cos_sq(x)))

Abstractions and limitations
----------------------------
* Functions are Mathlib's total real functions: ``Real.sqrt x = 0`` for ``x < 0``,
  ``Real.log 0 = 0``, ``Real.log (-x) = Real.log x``. Statements mean exactly that;
  add hypotheses (``pl.Le(0, x)``) where the informal statement assumes a domain.
* Derivatives of real functions: ``deriv(f, x)`` is Mathlib's ``deriv f x`` (which is 0
  where ``f`` is not differentiable), ``differentiable(f)`` is ``Differentiable ℝ f``.
  Functions are symbols of sort ``pl.Fn(pl.Real, pl.Real)`` or ``pl.fun(lambda t: …)``.
* ``LEMMAS`` reference declarations at :data:`VERIFIED_MATHLIB`; Lean checks every use.
"""

from __future__ import annotations

from ._domain import CATALOG_VERSION, VERIFIED_MATHLIB, collect_lemmas, lemma
from .expr import App, Expr, Func, abs_, exp, log, sqrt
from .proofs import library_fact
from .types import Fn, Prop, Real

_TRIG = "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"
_SQRT = "Mathlib.Analysis.Real.Sqrt"
_EXP = "Mathlib.Analysis.SpecialFunctions.Exp"
_LOG = "Mathlib.Analysis.SpecialFunctions.Log.Basic"

_SIN = Func("Real.sin", (Real,), Real, (_TRIG,), latex=r"\sin")
_COS = Func("Real.cos", (Real,), Real, (_TRIG,), latex=r"\cos")
_PI = Func("Real.pi", (), Real, (_TRIG,), latex=r"\pi")


def sin(x: object) -> App:
    """``Real.sin x``, the sine function on ℝ."""
    return _SIN(x)


def cos(x: object) -> App:
    """``Real.cos x``, the cosine function on ℝ."""
    return _COS(x)


def pi() -> App:
    """The constant π (``Real.pi``)."""
    return _PI()


_DERIV_MOD = "Mathlib.Analysis.Calculus.Deriv.Basic"
_MVT = "Mathlib.Analysis.Calculus.MeanValue"
_TRIG_DERIV = "Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv"
_RR = Fn(Real, Real)
_DERIV = Func("deriv", (_RR, Real), Real, (_DERIV_MOD,), latex="{0}'({1})")
_DERIV_LAM = Func("deriv", (_RR, Real), Real, (_DERIV_MOD,),
                  latex=r"\left({0}\right)'({1})")


def deriv(f: object, x: object) -> App:
    """``f′(x)``: the derivative of ``f : ℝ → ℝ`` at ``x`` (Mathlib's ``deriv f x``)."""
    from .terms import Lam

    return (_DERIV_LAM if isinstance(f, Lam) else _DERIV)(f, x)


def differentiable(f: object) -> Expr:
    """``f`` is differentiable on all of ℝ (``Differentiable ℝ f``)."""
    from .terms import apply, const
    from .types import lean_type

    c = const("Differentiable", Fn(lean_type("Type"), _RR, Prop), [_DERIV_MOD],
              latex=r"{1} \text{{ is differentiable}}")
    return apply(c, Real, f)


sqrt_nonneg = lemma("Real.sqrt_nonneg", _SQRT,
                     label="square roots are nonnegative")
sq_sqrt = lemma("Real.sq_sqrt", _SQRT, label="(√a)² = a for a ≥ 0")  # 0 ≤ a → √a ^ 2 = a
sqrt_mul = lemma("Real.sqrt_mul", _SQRT, label="√(ab) = √a·√b for a ≥ 0")
sqrt_sq = lemma("Real.sqrt_sq", _SQRT,
                 label="√(a²) = a for a ≥ 0")          # 0 ≤ a → √(a ^ 2) = a
sqrt_mul_self = lemma("Real.sqrt_mul_self", _SQRT,
                       label="√(a·a) = a for a ≥ 0")
exp_pos = lemma("Real.exp_pos", _EXP,
                 label="eˣ > 0")
exp_nonneg = lemma("Real.exp_nonneg", _EXP,
                    label="eˣ ≥ 0")
add_one_le_exp = lemma("Real.add_one_le_exp", _EXP,
                        label="1 + x ≤ eˣ")
exp_log = lemma("Real.exp_log", _LOG,
                 label="e^(log x) = x for x > 0")           # 0 < x → exp (log x) = x
log_exp = lemma("Real.log_exp", _LOG,
                 label="log(eˣ) = x")
log_le_sub_one_of_pos = lemma("Real.log_le_sub_one_of_pos", _LOG,
                               label="log x ≤ x − 1 for x > 0")
sin_sq_add_cos_sq = lemma("Real.sin_sq_add_cos_sq", _TRIG,
                           label="sin²x + cos²x = 1")
cos_sq_add_sin_sq = lemma("Real.cos_sq_add_sin_sq", _TRIG,
                           label="cos²x + sin²x = 1")
sin_le_one = lemma("Real.sin_le_one", _TRIG,
                    label="sin x ≤ 1")
neg_one_le_sin = lemma("Real.neg_one_le_sin", _TRIG,
                        label="−1 ≤ sin x")
cos_le_one = lemma("Real.cos_le_one", _TRIG,
                    label="cos x ≤ 1")
pi_pos = lemma("Real.pi_pos", _TRIG,
                label="π > 0")
sin_zero = lemma("Real.sin_zero", _TRIG, label="sin 0 = 0")
cos_zero = lemma("Real.cos_zero", _TRIG, label="cos 0 = 1")

# Calculus facts, named as a textbook would cite them.
constant_of_zero_derivative = lemma(
    "is_const_of_deriv_eq_zero", _MVT,
    label="a differentiable function with derivative 0 everywhere is constant")
deriv_sin = lemma("Real.deriv_sin", _TRIG_DERIV, label="sin′ = cos")
deriv_cos = lemma("Real.deriv_cos'", _TRIG_DERIV, label="cos′ = −sin")

# ---------------------------------------------------------------------------------------
# Sequences and limits (ε–N)
# ---------------------------------------------------------------------------------------

_TOPO = "Mathlib.Topology.MetricSpace.Pseudo.Defs"
_ORDER_TOPO = "Mathlib.Topology.Instances.Real.Lemmas"


def sequence_latex(a: object, wrap: bool = False) -> str:
    """How a sequence prints: ``a_n`` for a symbol ``a``, the formula ``1/(n+1)`` (in its own
    variable) for ``pl.fun(lambda n: …)``, ``{0}`` otherwise (a template for ``const``)."""
    from .expr import Var
    from .terms import Lam

    if isinstance(a, Var):
        return "({0}_n)" if wrap else "{0}_n"
    if isinstance(a, Lam) and len(a.vars) == 1:
        body = a.body.to_latex().replace("{", "{{").replace("}", "}}")
        if wrap:
            body = rf"\left({body}\right)_{{{{{a.vars[0].name}}}}}"
        return body + "{0:.0}"  # the sequence itself is not printed again
    return "{0}"


def tendsto(a: object, limit: object) -> Expr:
    """``aₙ → L`` as n → ∞ for a sequence ``a : ℕ → ℝ`` (``Tendsto a atTop (𝓝 L)``)."""
    from .terms import apply, const

    seq = sequence_latex(a)
    t = const("Filter.Tendsto", imports=(_TOPO, _ORDER_TOPO),
              latex=seq + r" \to {2}")
    at_top = const("Filter.atTop", imports=(_TOPO,), latex=r"\infty")
    nhds = const("nhds", imports=(_TOPO,), latex="{0}")
    return apply(t, a, at_top, apply(nhds, limit))


#: aₙ → L  ⟺  ∀ ε > 0, ∃ N, ∀ n ≥ N, |aₙ − L| < ε (the textbook definition).
tendsto_iff = library_fact(
    "PyLeanX.Analysis.tendsto_iff_eps_N", """
    theorem PyLeanX.Analysis.tendsto_iff_eps_N (a : ℕ → ℝ) (L : ℝ) :
        Filter.Tendsto a Filter.atTop (nhds L) ↔
          ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |a n - L| < ε := by
      simp only [Metric.tendsto_atTop, Real.dist_eq, gt_iff_lt, ge_iff_le]
    """, _TOPO, _ORDER_TOPO, label="definition of a limit (ε–N)")
triangle_inequality = lemma("abs_add_le", "Mathlib.Algebra.Order.Group.Unbundled.Abs",
                            label="triangle inequality")

from ._analysis_textbook import *  # noqa: E402, F403 - textbook facts
from ._analysis_textbook import (  # noqa: E402 - textbook vocabulary
    bounded,
    cauchy,
    closed_interval,
    continuous,
    continuous_at,
    continuous_on,
    differentiable_on,
    increasing,
    open_interval,
    strictly_increasing,
    uniformly_continuous_on,
)

LEMMAS = collect_lemmas(globals())

__all__ = ["sin", "cos", "pi", "sqrt", "exp", "log", "abs_", "deriv", "differentiable",
           "tendsto", "closed_interval", "open_interval", "continuous", "continuous_at",
           "continuous_on", "differentiable_on", "uniformly_continuous_on", "cauchy",
           "increasing", "strictly_increasing", "bounded",
           "LEMMAS", "VERIFIED_MATHLIB",
           "CATALOG_VERSION", *LEMMAS]
