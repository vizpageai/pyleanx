"""Real-variable methods on ℝ (Stein, *Singular Integrals*, ch. I; Tao, harmonic analysis notes):
intervals, Lebesgue measure, finite families, covering and maximal averages.

    from pyleanx import realvar as rv

Everything here is *vocabulary* (how statements are written and printed) plus references to
Mathlib theorems. The classical results of the theory (the Vitali covering lemma for finite
families, the Hardy–Littlewood maximal inequality, …) are proved as PyLeanX written proofs in
``examples/singular_integrals.py``, step by step from these facts, and checked by Lean.

Conventions: the measure is Lebesgue measure on ℝ, used through its real-valued form
``|E| = volume.real E`` (Mathlib's ``Measure.real``); the interval with centre ``c`` and
radius ``r`` is the closed ball ``[c − r, c + r]``; families are indexed by a finite set
``s : Finset ℕ`` with centres ``c : ℕ → ℝ`` and radii ``r : ℕ → ℝ``.
"""

from __future__ import annotations

from typing import Any

from ._domain import collect_lemmas, lemma
from .expr import Expr
from .types import Fn, Nat, Real, lean_type

_VITALI = "Mathlib.MeasureTheory.Covering.Vitali"
_SETINT = "Mathlib.MeasureTheory.Integral.Bochner.Set"
_LEB = "Mathlib.MeasureTheory.Measure.Lebesgue.Basic"
_REAL = "Mathlib.MeasureTheory.Measure.Real"
_FINSET = "Mathlib.Algebra.BigOperators.Group.Finset.Basic"
_ALL = (_VITALI, _SETINT, _LEB, "Mathlib.Data.Finset.Basic", "Mathlib.Data.Set.Basic")

#: a finite set of indices, a real function, a family of centres/radii
Indices = lean_type("Finset ℕ", (_FINSET,), latex=r"\text{Finset}(\mathbb{N})")
IndexSet = lean_type("Set ℕ", (_FINSET,), latex=r"\text{Set}(\mathbb{N})")
RFun = Fn(Real, Real)
Family = Fn(Nat, Real)


def finset_of(index: Any) -> Any:
    """The type of finite sets of indices of sort ``index`` (``Finset ℕ``, ``Finset ℝ``)."""
    sym = {"Nat": "ℕ", "Real": "ℝ", "Int": "ℤ"}[index.name]
    bb = {"Nat": "N", "Real": "R", "Int": "Z"}[index.name]
    return lean_type(f"Finset {sym}", (_FINSET,), latex=rf"\text{{Finset}}(\mathbb{{{bb}}})")


def set_of(index: Any) -> Any:
    """The type of sets of indices of sort ``index``."""
    sym = {"Nat": "ℕ", "Real": "ℝ", "Int": "ℤ"}[index.name]
    bb = {"Nat": "N", "Real": "R", "Int": "Z"}[index.name]
    return lean_type(f"Set {sym}", (_FINSET,), latex=rf"\text{{Set}}(\mathbb{{{bb}}})")


def _c(name: str, latex: str, imports: tuple[str, ...] = _ALL) -> Any:
    from .terms import const
    from .types import UNKNOWN

    return const(name, UNKNOWN, imports=imports, latex=latex)


def _app(name: str, latex: str, *args: object) -> Expr:
    from .terms import apply

    return apply(_c(name, latex), *args)


def interval(c: object, r: object) -> Expr:
    """The closed interval [c − r, c + r] (``Metric.closedBall c r``)."""
    return _app("Metric.closedBall", r"[{0} - {1}, {0} + {1}]", c, r)


def ball(c: object, r: object) -> Expr:
    """The open interval (c − r, c + r) (``Metric.ball c r``)."""
    return _app("Metric.ball", r"({0} - {1}, {0} + {1})", c, r)


def is_compact(K: object) -> Expr:  # noqa: N803
    """K is compact."""
    return _app("IsCompact", r"{0} \text{{ is compact}}", K)


def measure(E: object) -> Expr:  # noqa: N803 - mathematical name
    """|E|, the Lebesgue measure of ``E ⊆ ℝ`` (real-valued: ``volume.real E``)."""
    from .terms import apply, const

    vol = const("MeasureTheory.volume", imports=_ALL, latex="")
    return apply(_c("MeasureTheory.Measure.real", r"\left|{1}\right|"), vol, E)


def mem(x: object, S: object) -> Expr:  # noqa: N803
    """x ∈ S (for a set or a finite set)."""
    return _app("Membership.mem", r"{1} \in {0}", S, x)


def subset(A: object, B: object) -> Expr:  # noqa: N803
    """A ⊆ B (sets or finite sets; written with Lean's ``⊆``)."""
    from .expr import Compare, _lift

    return Compare("subset", _lift(A), _lift(B))


def as_set(v: object, index: Any = Nat) -> Expr:
    """A finite set of indices viewed as a set (Lean's coercion ``↑v``)."""
    from .terms import ascribe

    return ascribe(v, IndexSet if index is Nat else set_of(index))


def finite(u: object) -> Expr:
    """u is a finite set."""
    return _app("Set.Finite", r"{0} \text{{ is finite}}", u)


def union(s: object, c: object, r: object, scale: object = 1, index: Any = Nat) -> Expr:
    """⋃_{i ∈ s} [cᵢ − k rᵢ, cᵢ + k rᵢ] (``scale`` = k dilates every interval)."""
    from .terms import union as big_union

    if isinstance(scale, int) and scale == 1:
        return big_union(s, lambda i: interval(c(i), r(i)), sort=index)  # type: ignore[operator]
    return big_union(s, lambda i: interval(c(i), scale * r(i)),  # type: ignore[operator]
                     sort=index)


def disjoint_intervals(v: object, c: object, r: object, index: Any = Nat) -> Expr:
    """The intervals [cⱼ − rⱼ, cⱼ + rⱼ], j ∈ v, are pairwise disjoint."""
    from .terms import fun

    family = fun(lambda j: interval(c(j), r(j)), index)  # type: ignore[operator]
    return _app("Set.PairwiseDisjoint", r"\text{{the intervals indexed by }} {0}"
                r"\text{{ are pairwise disjoint}}", v, family)


def vol(E: object) -> Expr:  # noqa: N803
    """μ(E) ∈ [0, ∞], the Lebesgue measure of E (``volume E``)."""
    from .terms import apply, const

    return apply(const("MeasureTheory.volume", imports=_ALL, latex=r"\mu"), E)


def of_real(a: object) -> Expr:
    """A real number a ≥ 0 viewed in [0, ∞] (``ENNReal.ofReal a``)."""
    return _app("ENNReal.ofReal", "{0}", a)


def measurable(E: object) -> Expr:  # noqa: N803
    """E is (Lebesgue/Borel) measurable."""
    return _app("MeasurableSet", r"{0} \text{{ is measurable}}", E)


def finite_measure_ne(E: object) -> Expr:  # noqa: N803
    """μ(E) ≠ ∞."""
    from .terms import const

    return vol(E) != const("Top.top", latex=r"\infty")  # type: ignore[operator]


def finite_measure(E: object) -> Expr:  # noqa: N803
    """|E| < ∞ (``volume E < ⊤`` for Lebesgue measure, in [0, ∞])."""
    from .terms import apply, const

    vol = const("MeasureTheory.volume", imports=_ALL, latex=r"\mu")
    top = const("Top.top", latex=r"\infty")
    return apply(vol, E) < top  # type: ignore[operator]


def integrable(f: object) -> Expr:
    """f ∈ L¹(ℝ)."""
    return _app("MeasureTheory.Integrable", r"{0} \in L^1(\mathbb{{R}})", f)


def integrable_on(g: object, S: object) -> Expr:  # noqa: N803
    """g is integrable on S."""
    return _app("MeasureTheory.IntegrableOn", r"{0} \text{{ is integrable on }} {1}", g, S)


def ae_nonneg(g: object) -> Expr:
    """0 ≤ g almost everywhere."""
    from .terms import apply, const

    ae = apply(const("MeasureTheory.ae", imports=_ALL, latex=""),
               const("MeasureTheory.volume", imports=_ALL, latex=""))
    return apply(_c("Filter.EventuallyLE", r"0 \le {2} \text{{ a.e.}}"), ae, 0, g)


def abs_fun(f: Any) -> Expr:
    """The function |f| : x ↦ |f(x)|."""
    from .expr import abs_
    from .terms import fun
    from .types import Real as _R

    return fun(lambda t: abs_(f(t)), _R)


def l1_norm(f: Any) -> Expr:
    """‖f‖₁ = ∫ |f(x)| dx."""
    from .expr import abs_
    from .terms import integral

    return integral(lambda x: abs_(f(x)))


def average_exceeds(f: Any, lam: object, c: object, r: object) -> Expr:
    """λ |I| < ∫_I |f| for the interval I = [c − r, c + r] (the average of |f| over I exceeds λ)."""
    from .expr import abs_
    from .terms import integral

    I = interval(c, r)  # noqa: E741
    return lam * measure(I) < integral(lambda w: abs_(f(w)), within=I)  # type: ignore[operator]


# =========================================================================================
# Mathlib facts, by their textbook names
# =========================================================================================

vitali_mathlib = lemma(
    "Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall", _VITALI,
    label="the Vitali covering lemma (Mathlib): a disjoint subfamily whose τ-dilates, τ > 3, "
          "cover the family")
single_le_sum = lemma("Finset.single_le_sum", _FINSET,
                      label="a term of a sum of nonnegative terms is at most the sum")
finite_subset = lemma("Set.Finite.subset", "Mathlib.Data.Set.Finite.Basic",
                      label="a subset of a finite set is finite")
finset_finite = lemma("Finset.finite_toSet", "Mathlib.Data.Set.Finite.Basic",
                      label="a finite set of indices is finite")
finite_as_finset = lemma("Set.Finite.exists_finset_coe", "Mathlib.Data.Set.Finite.Basic",
                         label="a finite set is indexed by a finite set")
coe_subset = lemma("Finset.coe_subset", _FINSET, label="v ⊆ s as sets iff as finite sets")
measure_mono = lemma("MeasureTheory.measureReal_mono", _REAL, label="monotonicity of measure")
measure_union_le = lemma("MeasureTheory.measureReal_biUnion_finset_le", _REAL,
                         label="subadditivity of measure")
measure_interval = lemma("Real.volume_real_closedBall", _LEB,
                         label="|[c − r, c + r]| = 2r")
integral_disjoint_union = lemma("MeasureTheory.integral_biUnion_finset", _SETINT,
                                label="the integral over a disjoint union is the sum")
set_integral_le = lemma("MeasureTheory.setIntegral_le_integral", _SETINT,
                        label="the integral over a set is at most the integral of a "
                              "nonnegative function")
mem_union = lemma("Set.mem_iUnion₂", "Mathlib.Order.SetNotation",
                  label="x ∈ ⋃ᵢ Aᵢ iff x ∈ Aᵢ for some i")
union_finite_measure = lemma("MeasureTheory.measure_biUnion_lt_top",
                             "Mathlib.MeasureTheory.Measure.MeasureSpace",
                             label="a finite union of sets of finite measure has finite measure")
interval_finite_measure = lemma("MeasureTheory.measure_closedBall_lt_top",
                                "Mathlib.MeasureTheory.Measure.Typeclasses.Finite",
                                label="an interval has finite measure")
measure_union_le_ennreal = lemma("MeasureTheory.measure_biUnion_finset_le",
                                 "Mathlib.MeasureTheory.Measure.MeasureSpace",
                                 label="subadditivity of measure")
lt_ne = lemma("LT.lt.ne", "Mathlib.Order.Basic", label="a < b gives a ≠ b")
sum_congr = lemma("Finset.sum_congr", _FINSET, label="sums of equal terms are equal")
integrable_abs = lemma("MeasureTheory.Integrable.abs",
                       "Mathlib.MeasureTheory.Function.L1Space.Integrable",
                       label="|f| is integrable when f is")
integrable_on_of_integrable = lemma("MeasureTheory.Integrable.integrableOn",
                                    "Mathlib.MeasureTheory.Integral.IntegrableOn",
                                    label="an integrable function is integrable on every set")
interval_measurable = lemma("measurableSet_closedBall",
                            "Mathlib.MeasureTheory.Constructions.BorelSpace.Metric",
                            label="intervals are measurable")
everywhere_ae = lemma("Filter.Eventually.of_forall", "Mathlib.Order.Filter.Basic",
                      label="what holds everywhere holds almost everywhere")
abs_nonneg = lemma("abs_nonneg", "Mathlib.Algebra.Order.Group.Unbundled.Abs",
                   label="|x| ≥ 0")
axiom_of_choice = lemma("Classical.axiomOfChoice", "Mathlib.Order.Basic",
                        label="choice: pick one ρ for every x")
compact_finite_subcover = lemma(
    "IsCompact.elim_finite_subcover_image", "Mathlib.Topology.Compactness.Compact",
    label="compactness: finitely many of the open sets already cover")
ball_open = lemma("Metric.isOpen_ball", "Mathlib.Topology.MetricSpace.Pseudo.Defs",
                  label="open intervals are open")
mem_ball_self = lemma("Metric.mem_ball_self", "Mathlib.Topology.MetricSpace.Pseudo.Defs",
                      label="x ∈ (x − ρ, x + ρ) for ρ > 0")
ball_in_interval = lemma("Metric.ball_subset_closedBall",
                         "Mathlib.Topology.MetricSpace.Pseudo.Defs",
                         label="(c − r, c + r) ⊆ [c − r, c + r]")
mem_coe = lemma("Finset.mem_coe", _FINSET, label="membership in a finite set and in its set")
mul_le_mul_left = lemma("mul_le_mul_of_nonneg_left", "Mathlib.Algebra.Order.Ring.Defs",
                        label="multiply an inequality by α ≥ 0")
inner_regular = lemma("MeasurableSet.exists_lt_isCompact_of_ne_top",
                      "Mathlib.MeasureTheory.Measure.Regular",
                      label="inner regularity: a measurable set of finite measure contains "
                            "compact sets of almost the same measure")
subset_finite_measure = lemma("MeasureTheory.measure_ne_top_of_subset",
                              "Mathlib.MeasureTheory.Measure.MeasureSpaceDef",
                              label="a subset of a set of finite measure has finite measure")
of_real_lt = lemma("ENNReal.ofReal_lt_iff_lt_toReal", "Mathlib.Basic.ENNReal.Real",
                   label="comparing a real number with a finite measure")
integral_nonneg_ae = lemma("MeasureTheory.integral_nonneg_of_ae",
                           "Mathlib.MeasureTheory.Integral.Bochner.Basic",
                           label="the integral of a nonnegative function is nonnegative")
div_lt_iff = lemma("div_lt_iff₀'", "Mathlib.Algebra.Order.GroupWithZero.Basic",
                   label="b/c < a iff b < ca for c > 0")
mul_div_cancel = lemma("mul_div_cancel₀", "Mathlib.Algebra.Group.Basic",
                       label="c · (b/c) = b for c ≠ 0")
measure_real_def = lemma("MeasureTheory.measureReal_def",
                         "Mathlib.MeasureTheory.Measure.MeasureSpaceDef",
                         label="|E| is μ(E) as a real number")
div_nonneg = lemma("div_nonneg", "Mathlib.Algebra.Order.GroupWithZero.Basic",
                   label="a quotient of nonnegative numbers is nonnegative")
mul_lt_mul_left = lemma("mul_lt_mul_of_pos_left", "Mathlib.Algebra.Order.GroupWithZero.Defs",
                        label="multiply a strict inequality by α > 0")
ne_of_gt = lemma("ne_of_gt", "Mathlib.Order.Basic", label="α > 0 gives α ≠ 0")
mul_nonneg = lemma("mul_nonneg", "Mathlib.Algebra.Order.Ring.Defs",
                   label="a product of nonnegative numbers is nonnegative")
sum_le_sum = lemma("Finset.sum_le_sum", _FINSET, label="termwise comparison of sums")
mul_sum = lemma("Finset.mul_sum", _FINSET, label="a constant factor comes out of a sum")

LEMMAS = collect_lemmas(globals())
