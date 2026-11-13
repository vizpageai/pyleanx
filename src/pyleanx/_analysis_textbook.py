"""Real analysis as written in a textbook or paper: vocabulary and citable theorems.

Imported into :mod:`pyleanx.analysis` (``an``). Every fact prints as the reason a book gives
("the squeeze theorem", "Bolzano–Weierstrass", "the mean value theorem"). Definitions come
with their ε–N / ε–δ unfoldings (``an.continuous_at_iff``, ``an.cauchy_iff``, …), so a proof
can work from the definition exactly as a book does.

Conventions: sequences are functions ``ℕ → ℝ`` (indexed from 0, so "1/n" is written
``1/(n+1)``); intervals are closed ``[a, b]`` for continuity and open ``(a, b)`` for
differentiability, as in Rolle and the mean value theorem; ``deriv f c`` is ``f′(c)``.
"""

from __future__ import annotations

from typing import Any

from ._domain import lemma
from .expr import Expr
from .proofs import library_fact

_PSEUDO = "Mathlib.Topology.MetricSpace.Pseudo.Defs"
_REAL_TOP = "Mathlib.Topology.Instances.Real.Lemmas"
_IVT = "Mathlib.Topology.Order.IntermediateValue"
_COMPACT = "Mathlib.Topology.Order.Compact"
_MONO = "Mathlib.Topology.Order.MonotoneConvergence"
_SEQ = "Mathlib.Topology.MetricSpace.Sequences"
_HEINE = "Mathlib.Topology.UniformSpace.HeineCantor"
_ROLLE = "Mathlib.Analysis.Calculus.LocalExtr.Rolle"
_MVT = "Mathlib.Analysis.Calculus.Deriv.MeanValue"
_LIMITS = "Mathlib.Analysis.SpecificLimits.Basic"
_ARCH = "Mathlib.Algebra.Order.Archimedean.Basic"
_ABS = "Mathlib.Algebra.Order.Group.Unbundled.Abs"
_ABS_RING = "Mathlib.Algebra.Order.Ring.Abs"
_ABS_GROUP = "Mathlib.Algebra.Order.Group.Abs"
_BASE = (_PSEUDO, _REAL_TOP)


def _c(name: str, imports: tuple[str, ...], latex: str) -> Any:
    from .terms import const
    from .types import UNKNOWN

    return const(name, UNKNOWN, imports=imports, latex=latex)


def _app(name: str, imports: tuple[str, ...], latex: str, *args: object) -> Expr:
    from .terms import apply

    return apply(_c(name, imports, latex), *args)


# =========================================================================================
# Vocabulary
# =========================================================================================

def closed_interval(a: object, b: object) -> Expr:
    """``[a, b]`` (``Set.Icc a b``)."""
    return _app("Set.Icc", ("Mathlib.Order.Interval.Set.Defs",), "[{0}, {1}]", a, b)


def open_interval(a: object, b: object) -> Expr:
    """``(a, b)`` (``Set.Ioo a b``)."""
    return _app("Set.Ioo", ("Mathlib.Order.Interval.Set.Defs",), "({0}, {1})", a, b)


def continuous(f: object) -> Expr:
    """``f`` is continuous on ℝ (``Continuous f``)."""
    return _app("Continuous", _BASE, r"{0} \text{{ is continuous}}", f)


def continuous_at(f: object, x: object) -> Expr:
    """``f`` is continuous at ``x`` (``ContinuousAt f x``); unfold with ``continuous_at_iff``."""
    return _app("ContinuousAt", _BASE, r"{0} \text{{ is continuous at }} {1}", f, x)


def continuous_on(f: object, a: object, b: object) -> Expr:
    """``f`` is continuous on ``[a, b]`` (``ContinuousOn f (Set.Icc a b)``)."""
    return _app("ContinuousOn", _BASE, r"{0} \text{{ is continuous on }} {1}", f,
                closed_interval(a, b))


def differentiable_on(f: object, a: object, b: object) -> Expr:
    """``f`` is differentiable on ``(a, b)`` (``DifferentiableOn ℝ f (Set.Ioo a b)``)."""
    from .types import Real

    return _app("DifferentiableOn", (_MVT,), r"{1} \text{{ is differentiable on }} {2}", Real,
                f, open_interval(a, b))


def uniformly_continuous_on(f: object, a: object, b: object) -> Expr:
    """``f`` is uniformly continuous on ``[a, b]``; unfold with ``uniformly_continuous_iff``."""
    return _app("UniformContinuousOn", _BASE,
                r"{0} \text{{ is uniformly continuous on }} {1}", f, closed_interval(a, b))


def cauchy(a: object) -> Expr:
    """``(aₙ)`` is a Cauchy sequence (``CauchySeq a``); unfold with ``cauchy_iff``."""
    from .analysis import sequence_latex

    return _app("CauchySeq", _BASE, sequence_latex(a, wrap=True) + r" \text{{ is Cauchy}}", a)


def increasing(a: object) -> Expr:
    """``(aₙ)`` is increasing: ``m ≤ n → aₘ ≤ aₙ`` (``Monotone a``)."""
    from .analysis import sequence_latex

    return _app("Monotone", _BASE, sequence_latex(a, wrap=True) + r" \text{{ is increasing}}",
                a)


def strictly_increasing(phi: object) -> Expr:
    """``φ`` is strictly increasing (``StrictMono φ``), e.g. the indices of a subsequence."""
    return _app("StrictMono", _BASE, r"{0} \text{{ is strictly increasing}}", phi)


def bounded(a: object) -> Expr:
    """``(aₙ)`` is bounded: ``∃ M, ∀ n, |aₙ| ≤ M`` (written out, as in a book)."""
    from .binders import symbol
    from .expr import Exists, Forall, abs_
    from .types import Nat, Real

    M = symbol("M", Real)
    n = symbol("n", Nat)
    return Exists(M, Forall(n, abs_(a(n)) <= M))  # type: ignore[operator]


# =========================================================================================
# Facts from Mathlib, cited by their textbook names
# =========================================================================================

abs_lt = lemma("abs_lt", _ABS, label="|x| < r ⟺ −r < x < r")
abs_le = lemma("abs_le", _ABS_GROUP, label="|x| ≤ r ⟺ −r ≤ x ≤ r")
abs_sub_comm = lemma("abs_sub_comm", _ABS, label="|x − y| = |y − x|")
abs_mul = lemma("abs_mul", _ABS_RING, label="|xy| = |x||y|")
abs_nonneg = lemma("abs_nonneg", _ABS, label="|x| ≥ 0")
reverse_triangle = lemma("abs_sub_abs_le_abs_sub", _ABS_GROUP,
                         label="reverse triangle inequality")
le_max_left = lemma("le_max_left", "Mathlib.Order.Defs.LinearOrder", label="max(a, b) ≥ a")
le_max_right = lemma("le_max_right", "Mathlib.Order.Defs.LinearOrder", label="max(a, b) ≥ b")
abs_of_pos = lemma("abs_of_pos", _ABS, label="|x| = x for x > 0")
abs_of_nonneg = lemma("abs_of_nonneg", _ABS, label="|x| = x for x ≥ 0")
abs_pos = lemma("abs_pos", _ABS, label="|x| > 0 for x ≠ 0")

# =========================================================================================
# Shipped facts (Lean theorems with proofs, stated as in a textbook)
# =========================================================================================

continuous_at_iff = library_fact(
    "PyLeanX.Analysis.continuousAt_iff_eps_delta", """
theorem PyLeanX.Analysis.continuousAt_iff_eps_delta (f : ℝ → ℝ) (x₀ : ℝ) :
    ContinuousAt f x₀ ↔
      ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, |x - x₀| < δ → |f x - f x₀| < ε := by
  simp only [Metric.continuousAt_iff, Real.dist_eq, gt_iff_lt]
""", *_BASE,
    label="definition of continuity (ε–δ)")

cauchy_iff = library_fact(
    "PyLeanX.Analysis.cauchy_iff_eps_N", """
theorem PyLeanX.Analysis.cauchy_iff_eps_N (a : ℕ → ℝ) :
    CauchySeq a ↔
      ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ m : ℕ, m ≥ N → ∀ n : ℕ, n ≥ N → |a m - a n| < ε := by
  rw [Metric.cauchySeq_iff]
  simp only [Real.dist_eq, gt_iff_lt, ge_iff_le]
""", *_BASE,
    label="definition of a Cauchy sequence")

uniformly_continuous_iff = library_fact(
    "PyLeanX.Analysis.uniformContinuousOn_iff_eps_delta", """
theorem PyLeanX.Analysis.uniformContinuousOn_iff_eps_delta (f : ℝ → ℝ) (a b : ℝ) :
    UniformContinuousOn f (Set.Icc a b) ↔
      ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Icc a b → ∀ y : ℝ, y ∈ Set.Icc a b →
        |x - y| < δ → |f x - f y| < ε := by
  simp only [Metric.uniformContinuousOn_iff, Real.dist_eq, gt_iff_lt]
""", *_BASE,
    label="definition of uniform continuity")

limit_unique = library_fact(
    "PyLeanX.Analysis.limit_unique", """
theorem PyLeanX.Analysis.limit_unique {a : ℕ → ℝ} {L L' : ℝ}
    (h : Filter.Tendsto a Filter.atTop (nhds L)) (h' : Filter.Tendsto a Filter.atTop (nhds L')) :
    L = L' :=
  tendsto_nhds_unique h h'
""", *_BASE,
    label="limits are unique")

limit_add = library_fact(
    "PyLeanX.Analysis.limit_add", """
theorem PyLeanX.Analysis.limit_add {a b : ℕ → ℝ} {A B : ℝ}
    (ha : Filter.Tendsto a Filter.atTop (nhds A)) (hb : Filter.Tendsto b Filter.atTop (nhds B)) :
    Filter.Tendsto (fun n => a n + b n) Filter.atTop (nhds (A + B)) :=
  ha.add hb
""", *_BASE,
    label="the limit of a sum is the sum of the limits")

limit_sub = library_fact(
    "PyLeanX.Analysis.limit_sub", """
theorem PyLeanX.Analysis.limit_sub {a b : ℕ → ℝ} {A B : ℝ}
    (ha : Filter.Tendsto a Filter.atTop (nhds A)) (hb : Filter.Tendsto b Filter.atTop (nhds B)) :
    Filter.Tendsto (fun n => a n - b n) Filter.atTop (nhds (A - B)) :=
  ha.sub hb
""", *_BASE,
    label="the limit of a difference is the difference of the limits")

limit_mul = library_fact(
    "PyLeanX.Analysis.limit_mul", """
theorem PyLeanX.Analysis.limit_mul {a b : ℕ → ℝ} {A B : ℝ}
    (ha : Filter.Tendsto a Filter.atTop (nhds A)) (hb : Filter.Tendsto b Filter.atTop (nhds B)) :
    Filter.Tendsto (fun n => a n * b n) Filter.atTop (nhds (A * B)) :=
  ha.mul hb
""", *_BASE,
    label="the limit of a product is the product of the limits")

limit_const_mul = library_fact(
    "PyLeanX.Analysis.limit_const_mul", """
theorem PyLeanX.Analysis.limit_const_mul {c : ℝ} {a : ℕ → ℝ} {A : ℝ}
    (ha : Filter.Tendsto a Filter.atTop (nhds A)) :
    Filter.Tendsto (fun n => c * a n) Filter.atTop (nhds (c * A)) :=
  ha.const_mul c
""", *_BASE,
    label="constant multiples of limits")

limit_const = library_fact(
    "PyLeanX.Analysis.limit_const", """
theorem PyLeanX.Analysis.limit_const (c : ℝ) :
    Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) :=
  tendsto_const_nhds
""", *_BASE,
    label="a constant sequence converges to its value")

squeeze = library_fact(
    "PyLeanX.Analysis.squeeze", """
theorem PyLeanX.Analysis.squeeze {a b c : ℕ → ℝ} {L : ℝ}
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : Filter.Tendsto a Filter.atTop (nhds L)) (hc : Filter.Tendsto c Filter.atTop (nhds L)) :
    Filter.Tendsto b Filter.atTop (nhds L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hc hab hbc
""", *_BASE,
    label="the squeeze theorem")

one_over_n = library_fact(
    "PyLeanX.Analysis.one_over_n", """
theorem PyLeanX.Analysis.one_over_n :
    Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
""", *_BASE, _LIMITS,
    label="1/(n+1) → 0")

archimedean = library_fact(
    "PyLeanX.Analysis.archimedean", """
theorem PyLeanX.Analysis.archimedean (x : ℝ) : ∃ N : ℕ, x < N :=
  exists_nat_gt x
""", *_BASE, _ARCH,
    label="the Archimedean property")

reciprocal_lt = library_fact(
    "PyLeanX.Analysis.reciprocal_lt", """
theorem PyLeanX.Analysis.reciprocal_lt {x ε : ℝ} (hε : 0 < ε) (h : 1 / ε < x) : 1 / x < ε := by
  have hx : 0 < x := lt_trans (by positivity) h
  exact (one_div_lt hx hε).2 h
""", *_BASE,
    label="taking reciprocals: 1/ε < x gives 1/x < ε")

convergent_bounded = library_fact(
    "PyLeanX.Analysis.convergent_bounded", """
theorem PyLeanX.Analysis.convergent_bounded {a : ℕ → ℝ} {L : ℝ}
    (h : Filter.Tendsto a Filter.atTop (nhds L)) : ∃ M : ℝ, ∀ n : ℕ, |a n| ≤ M := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
    (Metric.isBounded_range_of_tendsto a h)
  exact ⟨M, fun n => by simpa [Metric.mem_closedBall, Real.dist_eq] using hM ⟨n, rfl⟩⟩
""", *_BASE, "Mathlib.Topology.MetricSpace.Bounded",
    label="a convergent sequence is bounded")

convergent_cauchy = library_fact(
    "PyLeanX.Analysis.convergent_cauchy", """
theorem PyLeanX.Analysis.convergent_cauchy {a : ℕ → ℝ} {L : ℝ}
    (h : Filter.Tendsto a Filter.atTop (nhds L)) : CauchySeq a :=
  h.cauchySeq
""", *_BASE, "Mathlib.Topology.UniformSpace.Cauchy",
    label="a convergent sequence is Cauchy")

cauchy_convergent = library_fact(
    "PyLeanX.Analysis.cauchy_convergent", """
theorem PyLeanX.Analysis.cauchy_convergent {a : ℕ → ℝ} (h : CauchySeq a) :
    ∃ L : ℝ, Filter.Tendsto a Filter.atTop (nhds L) :=
  cauchySeq_tendsto_of_complete h
""", *_BASE,
    label="ℝ is complete: every Cauchy sequence converges")

monotone_convergence = library_fact(
    "PyLeanX.Analysis.monotone_convergence", """
theorem PyLeanX.Analysis.monotone_convergence {a : ℕ → ℝ} {M : ℝ} (h : Monotone a)
    (hM : ∀ n, a n ≤ M) : ∃ L : ℝ, Filter.Tendsto a Filter.atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciSup h ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩⟩
""", *_BASE, _MONO,
    label="monotone convergence theorem: a bounded increasing sequence converges")

increasing_of_step = library_fact(
    "PyLeanX.Analysis.increasing_of_step", """
theorem PyLeanX.Analysis.increasing_of_step {a : ℕ → ℝ} (h : ∀ n, a n ≤ a (n + 1)) :
    Monotone a :=
  monotone_nat_of_le_succ h
""", *_BASE,
    label="aₙ ≤ aₙ₊₁ for every n, so (aₙ) is increasing")

bolzano_weierstrass = library_fact(
    "PyLeanX.Analysis.bolzano_weierstrass", """
theorem PyLeanX.Analysis.bolzano_weierstrass {a : ℕ → ℝ} {M : ℝ} (h : ∀ n, |a n| ≤ M) :
    ∃ φ : ℕ → ℕ, ∃ L : ℝ,
      StrictMono φ ∧ Filter.Tendsto (fun n => a (φ n)) Filter.atTop (nhds L) := by
  obtain ⟨L, -, φ, hφ, hL⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := M))
    (x := a) (fun n => by simpa [Metric.mem_closedBall, Real.dist_eq] using h n)
  exact ⟨φ, L, hφ, hL⟩
""", *_BASE, _SEQ,
    label="Bolzano–Weierstrass: a bounded sequence has a convergent subsequence")

sequential_continuity = library_fact(
    "PyLeanX.Analysis.sequential_continuity", """
theorem PyLeanX.Analysis.sequential_continuity {f : ℝ → ℝ} {a : ℕ → ℝ} {x : ℝ}
    (hf : ContinuousAt f x) (ha : Filter.Tendsto a Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => f (a n)) Filter.atTop (nhds (f x)) :=
  hf.tendsto.comp ha
""", *_BASE,
    label="a function continuous at x preserves limits of sequences converging to x")

ivt = library_fact(
    "PyLeanX.Analysis.ivt", """
theorem PyLeanX.Analysis.ivt {f : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ y) (hb : y ≤ f b) :
    ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ f c = y := by
  obtain ⟨c, ⟨h1, h2⟩, hc⟩ := intermediate_value_Icc hab hf ⟨ha, hb⟩
  exact ⟨c, h1, h2, hc⟩
""", *_BASE, _IVT,
    label="the intermediate value theorem")

evt_max = library_fact(
    "PyLeanX.Analysis.evt_max", """
theorem PyLeanX.Analysis.evt_max {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ ∀ x : ℝ, a ≤ x → x ≤ b → f x ≤ f c := by
  obtain ⟨c, ⟨h1, h2⟩, hc⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab) hf
  exact ⟨c, h1, h2, fun x hx1 hx2 => hc ⟨hx1, hx2⟩⟩
""", *_BASE, _COMPACT,
    label="the extreme value theorem (maximum)")

evt_min = library_fact(
    "PyLeanX.Analysis.evt_min", """
theorem PyLeanX.Analysis.evt_min {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ ∀ x : ℝ, a ≤ x → x ≤ b → f c ≤ f x := by
  obtain ⟨c, ⟨h1, h2⟩, hc⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab) hf
  exact ⟨c, h1, h2, fun x hx1 hx2 => hc ⟨hx1, hx2⟩⟩
""", *_BASE, _COMPACT,
    label="the extreme value theorem (minimum)")

rolle = library_fact(
    "PyLeanX.Analysis.rolle", """
theorem PyLeanX.Analysis.rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hfab : f a = f b) : ∃ c : ℝ, a < c ∧ c < b ∧ deriv f c = 0 := by
  obtain ⟨c, ⟨h1, h2⟩, hc⟩ := exists_deriv_eq_zero hab hf hfab
  exact ⟨c, h1, h2, hc⟩
""", *_BASE, _ROLLE,
    label="Rolle's theorem")

mvt = library_fact(
    "PyLeanX.Analysis.mvt", """
theorem PyLeanX.Analysis.mvt {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hd : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c : ℝ, a < c ∧ c < b ∧ deriv f c = (f b - f a) / (b - a) := by
  obtain ⟨c, ⟨h1, h2⟩, hc⟩ := exists_deriv_eq_slope f hab hf hd
  exact ⟨c, h1, h2, hc⟩
""", *_BASE, _MVT,
    label="the mean value theorem")

heine_cantor = library_fact(
    "PyLeanX.Analysis.heine_cantor", """
theorem PyLeanX.Analysis.heine_cantor {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) : UniformContinuousOn f (Set.Icc a b) :=
  isCompact_Icc.uniformContinuousOn_of_continuous hf
""", *_BASE, _HEINE,
    label="Heine–Cantor: a continuous function on [a, b] is uniformly continuous")

continuous_on_of_continuous = library_fact(
    "PyLeanX.Analysis.continuous_on_of_continuous", """
theorem PyLeanX.Analysis.continuous_on_of_continuous {f : ℝ → ℝ} (a b : ℝ)
    (hf : Continuous f) : ContinuousOn f (Set.Icc a b) :=
  hf.continuousOn
""", *_BASE,
    label="a continuous function is continuous on every interval")

continuous_at_of_continuous = library_fact(
    "PyLeanX.Analysis.continuous_at_of_continuous", """
theorem PyLeanX.Analysis.continuous_at_of_continuous {f : ℝ → ℝ} (x : ℝ)
    (hf : Continuous f) : ContinuousAt f x :=
  hf.continuousAt
""", *_BASE,
    label="a continuous function is continuous at every point")

differentiable_on_of_differentiable = library_fact(
    "PyLeanX.Analysis.differentiable_on_of_differentiable", """
theorem PyLeanX.Analysis.differentiable_on_of_differentiable {f : ℝ → ℝ} (a b : ℝ)
    (hf : Differentiable ℝ f) : DifferentiableOn ℝ f (Set.Ioo a b) :=
  hf.differentiableOn
""", *_BASE, _MVT,
    label="a differentiable function is differentiable on every interval")
