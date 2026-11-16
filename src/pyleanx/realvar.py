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

    return fun(lambda ζ: abs_(f(ζ)), _R)


def above(f: Any, beta: object) -> Expr:
    """The set {x : |f(x)| > β} (``setOf fun x => β < |f x|``)."""
    from .expr import _lift, abs_
    from .terms import apply, fun
    from .types import Real as _R

    tex = (r"\{" + "|" + f.to_latex() + r"| > " + _lift(beta).to_latex() + r"\}")
    tex = tex.replace("{", "{{").replace("}", "}}") + "{0:.0}"
    return apply(_c("setOf", tex), fun(lambda ζ: beta < abs_(f(ζ)), _R))  # type: ignore[operator]


def cut(f: Any, beta: object) -> Expr:
    """The function f·1{|f|>β}: f where |f| > β, 0 elsewhere (``Set.indicator``)."""
    from .terms import apply

    return apply(_c("Set.indicator", r"{1} \mathbf{{1}}_{{{0}}}{*}",
                    (*_ALL, "Mathlib.Algebra.Notation.Indicator")), above(f, beta), f)


def level_set(f: Any, lam: object) -> Expr:
    """{Mf > α}: the points x having an interval [x − ρ, x + ρ] on which the average of |f|
    exceeds α (``setOf fun x => ∃ ρ, 0 < ρ ∧ α |[x−ρ, x+ρ]| < ∫ |f|``)."""
    from .binders import symbol
    from .expr import And, Exists, _lift
    from .terms import apply, fun
    from .types import Real as _R

    tex = r"\{M" + f.to_latex() + " > " + _lift(lam).to_latex() + r"\}"
    tex = tex.replace("{", "{{").replace("}", "}}") + "{0:.0}"
    rho = symbol("ρ", _R)
    return apply(_c("setOf", tex), fun(lambda ζ: Exists(rho, And(
        0 < rho, average_exceeds(f, lam, ζ, rho))), _R))  # type: ignore[operator]


def rpow(x: object, y: object) -> Expr:
    """x^y with a real exponent (``Real.rpow``, written ``x ^ y``)."""
    from .expr import BinOp, _lift

    return BinOp("pow", _lift(x), _lift(y), Real)


def ennreal(a: object) -> Expr:
    """A real number a ≥ 0 as an element of [0, ∞] (``ENNReal.ofReal a``)."""
    return of_real(a)


def _lint_latex(lam: Any, dom: Any = None) -> str:
    """The display of ∫ body dx (over ``dom``) as a format template with hidden slots."""
    from .render.latex import latex_name

    var = latex_name(lam.vars[0].name)
    body = lam.body.to_latex()
    sub = "_{" + dom.to_latex() + "}" if dom is not None else ""
    tex = chr(92) + "int" + sub + " " + body + " " + chr(92) + ", d" + var
    return tex.replace("{", "{{").replace("}", "}}") + "{0:.0}{1:.0}"


def lintegral(body: Any, within: object = None) -> Expr:
    """∫ body(x) dx over ℝ or over a set, for a [0, ∞]-valued function (``∫⁻``)."""
    from .terms import apply, const, fun

    lam = fun(body, Real)
    vol = const("MeasureTheory.volume", imports=_ALL, latex="")
    if within is None:
        return apply(const("MeasureTheory.lintegral", imports=_ALL, latex=_lint_latex(lam)),
                     vol, lam)
    restrict = apply(const("MeasureTheory.Measure.restrict", imports=_ALL, latex=""),
                     vol, within)
    return apply(const("MeasureTheory.lintegral", imports=_ALL,
                       latex=_lint_latex(lam, within)), restrict, lam)


def Ioi(a: object) -> Expr:  # noqa: N802 - Mathlib's name
    """(a, ∞)."""
    return _app("Set.Ioi", r"({0}, \infty)", a)


def Iio(b: object) -> Expr:  # noqa: N802
    """(−∞, b)."""
    return _app("Set.Iio", r"(-\infty, {0})", b)


def Ioo(a: object, b: object) -> Expr:  # noqa: N802
    """(a, b)."""
    return _app("Set.Ioo", "({0}, {1})", a, b)


def Ioc(a: object, b: object) -> Expr:  # noqa: N802
    """(a, b]."""
    return _app("Set.Ioc", "({0}, {1}]", a, b)


def indicator(S: object, g: object) -> Expr:  # noqa: N803
    """g·1_S, the function equal to g on S and 0 elsewhere."""
    return _app("Set.indicator", r"{1} \mathbf{{1}}_{{{0}}}{*}", S, g)


def interval_integrable(g: object, a: object, b: object) -> Expr:
    """g is integrable on [a, b]."""
    from .terms import const

    return _app("IntervalIntegrable", r"{0} \text{{ is integrable on }} [{2}, {3}]", g,
                const("MeasureTheory.volume", imports=_ALL, latex=""), a, b)


def lintegral_nested(body: Any, within: object, inside: object) -> Expr:
    """∫ over ``within`` for Lebesgue measure restricted to ``inside`` (∫⁻)."""
    from .terms import apply, const, fun

    lam = fun(body, Real)
    vol = const("MeasureTheory.volume", imports=_ALL, latex="")
    restrict = const("MeasureTheory.Measure.restrict", imports=_ALL, latex="")
    mu = apply(restrict, apply(restrict, vol, inside), within)
    dom = _app("Inter.inter", r"{0} \cap {1}", within, inside)
    return apply(const("MeasureTheory.lintegral", imports=_ALL, latex=_lint_latex(lam, dom)),
                 mu, lam)


def measurable_fn(g: object) -> Expr:
    """g is measurable."""
    return _app("Measurable", r"{0} \text{{ is measurable}}", g)


def pred_set(body: Any, sort: Any) -> Expr:
    """{q : sort | body(q)} (a set given by a property)."""
    from .terms import apply, fun

    return apply(_c("setOf", r"\{{ {0} \}}"), fun(body, sort))


def volume_on_half_line_times_line() -> Expr:
    """Lebesgue measure on (0, ∞) × ℝ (the product of the restriction and Lebesgue measure)."""
    from .terms import apply, const

    vol = const("MeasureTheory.volume", imports=_ALL, latex="")
    restrict = apply(const("MeasureTheory.Measure.restrict", imports=_ALL, latex=""), vol,
                     Ioi(0))
    return apply(const("MeasureTheory.Measure.prod",
                       imports=(*_ALL, "Mathlib.MeasureTheory.Measure.Prod"),
                       latex=r"dt\,dx \text{{ on }} (0, \infty) \times \mathbb{{R}}{0:.0}{1:.0}"),
                 restrict, vol)


def ae_measurable(g: object, mu: object) -> Expr:
    """g is almost-everywhere measurable for the measure mu."""
    return _app("AEMeasurable", r"{0} \text{{ is measurable for }} {1}", g, mu)


def uncurry(F: object) -> Expr:  # noqa: N803
    """(t, x) ↦ F(t, x) as a function on pairs."""
    return _app("Function.uncurry", r"{0}", F)


def dist(a: object, b: object) -> Expr:
    """|a − b|, the distance on ℝ (``dist a b``)."""
    return _app("dist", "|{0} - {1}|", a, b)


def is_open(S: object) -> Expr:  # noqa: N803
    """S is open."""
    return _app("IsOpen", r"{0} \text{{ is open}}", S)


def ae_nonneg_on(g: object, S: object) -> Expr:  # noqa: N803
    """0 ≤ g almost everywhere on S."""
    from .terms import apply, const

    vol = const("MeasureTheory.volume", imports=_ALL, latex="")
    ae = apply(const("MeasureTheory.ae", imports=_ALL, latex=""),
               apply(const("MeasureTheory.Measure.restrict", imports=_ALL, latex=""), vol, S))
    return apply(_c("Filter.EventuallyLE", r"0 \le {2} \text{{ a.e. on }} S"), ae, 0, g)


def ae_subset(A: object, B: object) -> Expr:  # noqa: N803
    """A ⊆ B up to a null set."""
    from .terms import apply, const

    ae = apply(const("MeasureTheory.ae", imports=_ALL, latex=""),
               const("MeasureTheory.volume", imports=_ALL, latex=""))
    return apply(_c("Filter.EventuallyLE", r"{1} \subseteq {2} \text{{ a.e.}}"), ae, A, B)


def locally_integrable(f: object) -> Expr:
    """f is locally integrable (integrable on every compact set)."""
    return _app("MeasureTheory.LocallyIntegrable", r"{0} \in L^1_{{\mathrm{{loc}}}}", f)


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
_IND = "Mathlib.Algebra.Notation.Indicator"
indicator_of_mem = lemma("Set.indicator_of_mem", _IND,
                         label="f·1_S = f on S")
indicator_of_not_mem = lemma("Set.indicator_of_notMem", _IND,
                             label="f·1_S = 0 off S")
abs_zero = lemma("abs_zero", "Mathlib.Algebra.Order.Group.Unbundled.Abs", label="|0| = 0")
integrable_on_compact = lemma("MeasureTheory.LocallyIntegrable.integrableOn_isCompact",
                              "Mathlib.MeasureTheory.Function.LocallyIntegrable",
                              label="a locally integrable function is integrable on compact sets")
interval_compact = lemma("isCompact_closedBall", "Mathlib.Topology.MetricSpace.ProperSpace",
                         label="closed intervals are compact")
integrable_const_on = lemma("MeasureTheory.integrableOn_const",
                            "Mathlib.MeasureTheory.Integral.IntegrableOn",
                            label="a constant is integrable on a set of finite measure")
integrable_add = lemma("MeasureTheory.Integrable.add",
                       "Mathlib.MeasureTheory.Function.L1Space.Integrable",
                       label="a sum of integrable functions is integrable")
integral_add = lemma("MeasureTheory.integral_add", "Mathlib.MeasureTheory.Integral.Bochner.Basic",
                     label="the integral of a sum is the sum of the integrals")
set_integral_const = lemma("MeasureTheory.setIntegral_const",
                           "Mathlib.MeasureTheory.Integral.Bochner.Set",
                           label="∫_E c = c|E|")
set_integral_mono = lemma("MeasureTheory.setIntegral_mono",
                          "Mathlib.MeasureTheory.Integral.Bochner.Set",
                          label="monotonicity of the integral")
smul_eq_mul = lemma("smul_eq_mul", "Mathlib.Algebra.Group.Defs", label="a • b = ab")
is_open_iff = lemma("Metric.isOpen_iff", "Mathlib.Topology.MetricSpace.Pseudo.Defs",
                    label="a set is open iff it contains an interval around each point")
mem_set_of = lemma("Set.mem_setOf_eq", "Mathlib.Data.Set.Defs", label="definition of the set")
mem_ball = lemma("Metric.mem_ball'", "Mathlib.Topology.MetricSpace.Pseudo.Defs",
                 label="y ∈ (x − δ, x + δ) iff |x − y| < δ")
dist_comm = lemma("dist_comm", "Mathlib.Topology.MetricSpace.Pseudo.Defs",
                  label="|x − y| = |y − x|")
interval_in_interval = lemma("Metric.closedBall_subset_closedBall'",
                             "Mathlib.Topology.MetricSpace.Pseudo.Defs",
                             label="[x − ρ, x + ρ] ⊆ [y − ρ', y + ρ'] when ρ + |x − y| ≤ ρ'")
subset_ae = lemma("HasSubset.Subset.eventuallyLE", "Mathlib.MeasureTheory.Measure.MeasureSpace",
                  label="a subset is a subset almost everywhere")
set_integral_mono_set = lemma("MeasureTheory.setIntegral_mono_set",
                              "Mathlib.MeasureTheory.Integral.Bochner.Set",
                              label="a larger set has a larger integral of a nonnegative function")
div_pos = lemma("div_pos", "Mathlib.Algebra.Order.GroupWithZero.Basic",
                label="a quotient of positive numbers is positive")
open_inner_regular = lemma("IsOpen.exists_lt_isCompact", "Mathlib.MeasureTheory.Measure.Regular",
                           label="inner regularity: an open set contains compact sets of almost "
                                 "its measure")
compact_finite_measure = lemma("IsCompact.measure_lt_top",
                               "Mathlib.MeasureTheory.Measure.Typeclasses.Finite",
                               label="a compact set has finite measure")
not_le = lemma("not_le", "Mathlib.Order.Defs.LinearOrder", label="¬(a ≤ b) iff b < a")
_POW = "Mathlib.Analysis.SpecialFunctions.Pow.Real"
_INTS = "Mathlib.Analysis.SpecialFunctions.Integrals.Basic"
integral_rpow = lemma("integral_rpow", _INTS, label="∫_a^b t^r dt = (b^{r+1} − a^{r+1})/(r+1)")
or_inl = lemma("Or.inl", "Mathlib.Order.Basic", label="the first alternative")
zero_rpow = lemma("Real.zero_rpow", _POW, label="0^r = 0 for r ≠ 0")
rpow_add_one = lemma("Real.rpow_add_one", _POW, label="t^{r+1} = t^r·t for t ≠ 0")
mul_rpow = lemma("Real.mul_rpow", _POW, label="(ab)^r = a^r b^r for a, b ≥ 0")
rpow_nonneg = lemma("Real.rpow_nonneg", _POW, label="t^r ≥ 0 for t ≥ 0")
sub_zero = lemma("sub_zero", "Mathlib.Algebra.Group.Basic", label="a − 0 = a")
of_real_mul = lemma("ENNReal.ofReal_mul", "Mathlib.Basic.ENNReal.Real",
                    label="ab as an element of [0, ∞] is a·b for a ≥ 0")
_ORD = "Mathlib.Order.Interval.Set.Basic"
set_lintegral_congr = lemma("MeasureTheory.setLIntegral_congr_fun",
                            "Mathlib.MeasureTheory.Integral.Lebesgue.Basic",
                            label="integrals of functions equal on the set are equal")
set_lintegral_mono = lemma("MeasureTheory.setLIntegral_mono'",
                           "Mathlib.MeasureTheory.Integral.Lebesgue.Basic",
                           label="monotonicity of the integral on a set")
lintegral_indicator = lemma("MeasureTheory.lintegral_indicator",
                            "Mathlib.MeasureTheory.Integral.Lebesgue.Basic",
                            label="the integral of g·1_S is the integral of g over S")
restrict_restrict = lemma("MeasureTheory.Measure.restrict_restrict",
                          "Mathlib.MeasureTheory.Measure.Restrict",
                          label="restricting twice restricts to the intersection")
measurable_Ioi = lemma("measurableSet_Ioi", "Mathlib.MeasureTheory.Constructions.BorelSpace.Order",
                       label="(a, ∞) is measurable")
measurable_Iio = lemma("measurableSet_Iio", "Mathlib.MeasureTheory.Constructions.BorelSpace.Order",
                       label="(−∞, b) is measurable")
measurable_Ioo = lemma("measurableSet_Ioo", "Mathlib.MeasureTheory.Constructions.BorelSpace.Order",
                       label="(a, b) is measurable")
iio_inter_ioi = lemma("Set.Iio_inter_Ioi", _ORD, label="(−∞, b) ∩ (a, ∞) = (a, b)")
ioo_sub_ioc = lemma("Set.Ioo_subset_Ioc_self", _ORD, label="(a, b) ⊆ (a, b]")
mem_Ioi = lemma("Set.mem_Ioi", _ORD, label="t ∈ (a, ∞) iff a < t")
mem_Iio = lemma("Set.mem_Iio", _ORD, label="t ∈ (−∞, b) iff t < b")
of_real_integral = lemma("MeasureTheory.ofReal_integral_eq_lintegral_ofReal",
                         "Mathlib.MeasureTheory.Integral.Bochner.Basic",
                         label="for g ≥ 0 integrable, ∫g in [0, ∞] is ∫ of g in [0, ∞]")
rpow_interval_integrable = lemma("intervalIntegral.intervalIntegrable_rpow'",
                                 "Mathlib.Analysis.SpecialFunctions.Integrability.Basic",
                                 label="t^r is integrable on bounded intervals for r > −1")
interval_integrable_Ioc = lemma("intervalIntegrable_iff_integrableOn_Ioc_of_le",
                                "Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic",
                                label="integrable on [a, b] means integrable on (a, b]")
integrable_on_mono = lemma("MeasureTheory.IntegrableOn.mono_set",
                           "Mathlib.MeasureTheory.Integral.IntegrableOn",
                           label="integrable on a set, so on a subset")
integrable_const_mul = lemma("MeasureTheory.Integrable.const_mul",
                             "Mathlib.MeasureTheory.Function.L1Space.Integrable",
                             label="a constant multiple of an integrable function is integrable")
ae_on_set = lemma("MeasureTheory.ae_restrict_of_forall_mem",
                  "Mathlib.MeasureTheory.Measure.Restrict",
                  label="what holds on all of S holds a.e. on S")
integral_ioc_ioo = lemma("MeasureTheory.integral_Ioc_eq_integral_Ioo",
                         "Mathlib.MeasureTheory.Integral.Bochner.Set",
                         label="endpoints do not matter")
interval_integral_ioc = lemma("intervalIntegral.integral_of_le",
                              "Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic",
                              label="∫_a^b = ∫ over (a, b] for a ≤ b")
interval_const_mul = lemma("intervalIntegral.integral_const_mul",
                           "Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic",
                           label="a constant comes out of the integral")
mul_zero = lemma("mul_zero", "Mathlib.Algebra.GroupWithZero.Defs", label="a·0 = 0")
of_real_zero = lemma("ENNReal.ofReal_zero", "Mathlib.Basic.ENNReal.Real", label="0 in [0, ∞]")
integral_const_mul = lemma("MeasureTheory.integral_const_mul",
                           "Mathlib.MeasureTheory.Integral.Bochner.Basic",
                           label="a constant comes out of the integral")
mul_le_mul_left_ennreal = lemma("mul_le_mul'", "Mathlib.Algebra.Order.Monoid.Unbundled.Basic",
                                label="multiply both sides of an inequality by w ≥ 0")
_PROD = "Mathlib.MeasureTheory.Measure.Prod"
_MEAS = "Mathlib.MeasureTheory.Measure.MeasureSpace"
tonelli = lemma("MeasureTheory.lintegral_lintegral_swap", _PROD,
                label="Tonelli: the order of integration can be swapped")
lintegral_congr = lemma("MeasureTheory.lintegral_congr",
                        "Mathlib.MeasureTheory.Integral.Lebesgue.Basic",
                        label="integrals of equal functions are equal")
lintegral_const_mul = lemma("MeasureTheory.lintegral_const_mul'",
                            "Mathlib.MeasureTheory.Integral.Lebesgue.Basic",
                            label="a finite constant comes out of the integral")
of_real_ne_top = lemma("ENNReal.ofReal_ne_top", "Mathlib.Basic.ENNReal.Real",
                       label="a real number is finite in [0, ∞]")
fun_ext = lemma("funext", "Mathlib.Order.Basic", label="functions equal at every point are equal")
measurable_set_lt = lemma("measurableSet_lt",
                          "Mathlib.MeasureTheory.Constructions.BorelSpace.Order",
                          label="{a | g a < h a} is measurable for measurable g, h")
measurable_indicator = lemma("Measurable.indicator",
                             "Mathlib.MeasureTheory.MeasurableSpace.Basic",
                             label="g·1_S is measurable for measurable g and S")
measurable_mul = lemma("Measurable.mul", "Mathlib.MeasureTheory.Group.Arithmetic",
                       label="a product of measurable functions is measurable")
measurable_of_real = lemma("Measurable.ennreal_ofReal",
                           "Mathlib.MeasureTheory.Function.SpecialFunctions.Basic",
                           label="a measurable real function is measurable in [0, ∞]")
measurable_ae = lemma("Measurable.aemeasurable", _MEAS,
                      label="measurable implies almost-everywhere measurable")
rpow_pos_two = lemma("Real.rpow_pos_of_pos", "Mathlib.Analysis.SpecialFunctions.Pow.Real",
                     label="a positive number to any power is positive")
mul_nonneg = lemma("mul_nonneg", "Mathlib.Algebra.Order.Ring.Defs",
                   label="a product of nonnegative numbers is nonnegative")
sum_le_sum = lemma("Finset.sum_le_sum", _FINSET, label="termwise comparison of sums")
mul_sum = lemma("Finset.mul_sum", _FINSET, label="a constant factor comes out of a sum")

LEMMAS = collect_lemmas(globals())
