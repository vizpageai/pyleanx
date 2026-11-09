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
* No limits, derivatives or integrals yet (they need function-valued sorts and
  filters; planned with typeclass binder support).
* ``LEMMAS`` reference declarations at :data:`VERIFIED_MATHLIB`; Lean checks every use.
"""

from __future__ import annotations

from ._domain import CATALOG_VERSION, VERIFIED_MATHLIB, collect_lemmas, lemma
from .expr import App, Func, abs_, exp, log, sqrt
from .types import Real

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


sqrt_nonneg = lemma("Real.sqrt_nonneg", _SQRT)
sq_sqrt = lemma("Real.sq_sqrt", _SQRT)          # 0 ≤ a → √a ^ 2 = a
sqrt_sq = lemma("Real.sqrt_sq", _SQRT)          # 0 ≤ a → √(a ^ 2) = a
sqrt_mul_self = lemma("Real.sqrt_mul_self", _SQRT)
exp_pos = lemma("Real.exp_pos", _EXP)
exp_nonneg = lemma("Real.exp_nonneg", _EXP)
add_one_le_exp = lemma("Real.add_one_le_exp", _EXP)
exp_log = lemma("Real.exp_log", _LOG)           # 0 < x → exp (log x) = x
log_exp = lemma("Real.log_exp", _LOG)
log_le_sub_one_of_pos = lemma("Real.log_le_sub_one_of_pos", _LOG)
sin_sq_add_cos_sq = lemma("Real.sin_sq_add_cos_sq", _TRIG)
cos_sq_add_sin_sq = lemma("Real.cos_sq_add_sin_sq", _TRIG)
sin_le_one = lemma("Real.sin_le_one", _TRIG)
neg_one_le_sin = lemma("Real.neg_one_le_sin", _TRIG)
cos_le_one = lemma("Real.cos_le_one", _TRIG)
pi_pos = lemma("Real.pi_pos", _TRIG)

LEMMAS = collect_lemmas(globals())

__all__ = ["sin", "cos", "pi", "sqrt", "exp", "log", "abs_", "LEMMAS", "VERIFIED_MATHLIB",
           "CATALOG_VERSION", *LEMMAS]
