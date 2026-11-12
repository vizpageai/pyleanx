"""Complex analysis: ℂ, discs and circles, holomorphy, circle integrals (Mathlib's notions).

    import pyleanx as pl
    from pyleanx import complex_analysis as ca

    f = pl.symbol("f", pl.Fn(ca.C, ca.C))
    c, w = pl.symbols("c w", ca.C)
    R = pl.symbol("R", pl.Real)
    ca.circle_integral(lambda z: pl.smul(ca.inv(z - w), f(z)), c, R)   # ∮_{|z−c|=R} f(z)/(z−w) dz

Abstractions and limitations
----------------------------
* ``circle_integral(g, c, R)`` is Mathlib's ``∮ z in C(c, R), g z``: the integral over the
  circle traversed once counterclockwise, ``∫₀^{2π} g(c + R e^{iθ}) · iRe^{iθ} dθ``. It is
  defined for every ``g`` (0 when ``g`` is not integrable on the circle), so statements carry
  the hypotheses that make it meaningful.
* "Holomorphic on S" is Mathlib's ``DifferentiableOn ℂ f S`` (complex-differentiable at
  every point of S within S). ``ball``/``closed_ball``/``sphere`` are the open disc, closed
  disc and circle ``|z − c| = R``.
* Facts marked *shipped* are Lean theorems with proofs that PyLeanX emits into every file
  citing them; the others reference declarations at :data:`VERIFIED_MATHLIB`.
"""

from __future__ import annotations

from typing import Any

from ._domain import CATALOG_VERSION, VERIFIED_MATHLIB, collect_lemmas, lemma
from .expr import Expr
from .proofs import library_fact
from .types import lean_type

_COMPLEX = "Mathlib.Analysis.Complex.Basic"
_CIRCLE = "Mathlib.MeasureTheory.Integral.CircleIntegral"
_CAUCHY = "Mathlib.Analysis.Complex.CauchyIntegral"
_DSLOPE = "Mathlib.Analysis.Calculus.DSlope"
_METRIC = "Mathlib.Topology.MetricSpace.Pseudo.Defs"
_TRIG = "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"

#: The complex numbers.
C = lean_type("ℂ", (_COMPLEX,), latex=r"\mathbb{C}")


def _c(name: str, imports: tuple[str, ...], latex: str, sort: Any = None) -> Any:
    from .terms import const
    from .types import UNKNOWN

    return const(name, sort if sort is not None else UNKNOWN, imports=imports, latex=latex)


def _app(name: str, imports: tuple[str, ...], latex: str, *args: object) -> Expr:
    from .terms import apply

    return apply(_c(name, imports, latex), *args)


def I() -> Expr:  # noqa: N802, E743 - mathematical name
    """The imaginary unit ``i`` (``Complex.I``)."""
    return _c("Complex.I", (_COMPLEX,), "i", C)


def pi() -> Expr:
    """π as a complex number (``(Real.pi : ℂ)``)."""
    from .terms import ascribe

    return ascribe(_c("Real.pi", (_TRIG,), r"\pi", lean_type("ℝ")), C)


def two_pi_i() -> Expr:
    """``2πi``."""
    return 2 * pi() * I()


def inv(z: object) -> Expr:
    """``z⁻¹``."""
    from .algebra import inv as _inv

    return _inv(z)


def ball(c: object, r: object) -> Expr:
    """The open disc ``{z : |z − c| < r}`` (``Metric.ball c r``)."""
    return _app("Metric.ball", (_METRIC,), r"D({0}, {1})", c, r)


def closed_ball(c: object, r: object) -> Expr:
    """The closed disc ``{z : |z − c| ≤ r}`` (``Metric.closedBall c r``)."""
    return _app("Metric.closedBall", (_METRIC,), r"\bar{{D}}({0}, {1})", c, r)


def sphere(c: object, r: object) -> Expr:
    """The circle ``{z : |z − c| = r}`` (``Metric.sphere c r``)."""
    return _app("Metric.sphere", (_METRIC,), r"\partial D({0}, {1})", c, r)


def mem(z: object, s: object) -> Expr:
    """``z ∈ s``."""
    return _app("Membership.mem", (), r"{1} \in {0}", s, z)


def minus_point(s: object, w: object) -> Expr:
    """``s \\ {w}``: the set with the point ``w`` removed."""
    single = _app("singleton", (), r"\{{{0}\}}", w)
    return _app("SDiff.sdiff", (), r"{0} \setminus {1}", s, single)


def holomorphic_on(f: object, s: object) -> Expr:
    """``f`` is holomorphic on ``s`` (``DifferentiableOn ℂ f s``)."""
    return _app("DifferentiableOn", (_CAUCHY,), r"{1} \text{{ is holomorphic on }} {2}", C, f, s)


def differentiable_at(f: object, z: object) -> Expr:
    """``f`` is complex-differentiable at ``z`` (``DifferentiableAt ℂ f z``)."""
    return _app("DifferentiableAt", (_CAUCHY,),
                r"{1} \text{{ is complex-differentiable at }} {2}", C, f, z)


def continuous_on(f: object, s: object) -> Expr:
    """``f`` is continuous on ``s`` (``ContinuousOn f s``)."""
    return _app("ContinuousOn", (_CAUCHY,), r"{0} \text{{ is continuous on }} {1}", f, s)


def difference_quotient(f: object, w: object) -> Expr:
    """``z ↦ (f(z) − f(w))/(z − w)``, extended by ``f′(w)`` at ``w`` (Mathlib's ``dslope f w``)."""
    return _app("dslope", (_DSLOPE,), r"\frac{{{0}(z) - {0}({1})}}{{z - {1}}}", f, w)


def circle_integral(body: Any, c: object, r: object) -> Expr:
    """``∮_{|z − c| = r} body(z) dz`` (Mathlib's ``∮ z in C(c, r), body z``)."""
    from .terms import Lam, apply, fun

    lam = body if isinstance(body, Lam) else fun(body, C)
    v = lam.vars[0].name
    tex = lam.body.to_latex().replace("{", "{{").replace("}", "}}")
    template = r"\oint_{{|" + v + r" - {1}| = {2}}} " + tex + r" \, d" + v
    return apply(_c("circleIntegral", (_CIRCLE,), template), lam, c, r)


# ---------------------------------------------------------------------------------------
# Facts
# ---------------------------------------------------------------------------------------

_FACT_IMPORTS = (_CAUCHY, _DSLOPE, _CIRCLE)

#: Cauchy's theorem for a disc, allowing one exceptional point (Mathlib's Goursat-type
#: theorem with a countable exceptional set, for the set {w}).
cauchy_theorem = library_fact("PyLeanX.Complex.cauchy_theorem_disc", """
    theorem PyLeanX.Complex.cauchy_theorem_disc {g : ℂ → ℂ} {c w : ℂ} {R : ℝ} (h0 : 0 ≤ R)
        (hc : ContinuousOn g (Metric.closedBall c R))
        (hd : ∀ z ∈ Metric.ball c R \\ {w}, DifferentiableAt ℂ g z) :
        (∮ z in C(c, R), g z) = 0 :=
      Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable h0
        (Set.countable_singleton w) hc hd
    """, *_FACT_IMPORTS,
    label="Cauchy's theorem (g is continuous on the closed disc and holomorphic except at w)")

#: The difference quotient of a holomorphic function is continuous, also at w.
quotient_continuous = library_fact("PyLeanX.Complex.dslope_continuousOn", """
    theorem PyLeanX.Complex.dslope_continuousOn {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
        (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hw : w ∈ Metric.ball c R) :
        ContinuousOn (dslope f w) (Metric.closedBall c R) := by
      have hn : Metric.closedBall c R ∈ nhds w :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hw) Metric.ball_subset_closedBall
      exact (continuousOn_dslope hn).2 ⟨hf.continuousOn, hf.differentiableAt hn⟩
    """, *_FACT_IMPORTS,
    label="g → f′(w) as z → w, so g is continuous; elsewhere it is a quotient of "
          "continuous functions")

#: Away from w, the difference quotient is complex-differentiable.
quotient_differentiable = library_fact("PyLeanX.Complex.dslope_differentiableAt", """
    theorem PyLeanX.Complex.dslope_differentiableAt {f : ℂ → ℂ} {c w z : ℂ} {R : ℝ}
        (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hz : z ∈ Metric.ball c R \\ {w}) :
        DifferentiableAt ℂ (dslope f w) z := by
      have hn : Metric.closedBall c R ∈ nhds z :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz.1) Metric.ball_subset_closedBall
      have hne : z ≠ w := fun h => hz.2 (by simp [h])
      exact (differentiableAt_dslope_of_ne hne).2 (hf.differentiableAt hn)
    """, *_FACT_IMPORTS,
    label="for z ≠ w, g is a quotient of holomorphic functions")

#: On the circle z ≠ w, so (z − w)⁻¹ f(z) = g(z) + (z − w)⁻¹ f(w); integrate term by term.
integrate_termwise = library_fact("PyLeanX.Complex.circleIntegral_split", """
    theorem PyLeanX.Complex.circleIntegral_split {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
        (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hw : w ∈ Metric.ball c R) :
        (∮ z in C(c, R), (z - w)⁻¹ • f z) =
          (∮ z in C(c, R), dslope f w z) + ∮ z in C(c, R), (z - w)⁻¹ • f w := by
      have hR : 0 < R := Metric.pos_of_mem_ball hw
      have hne : ∀ z ∈ Metric.sphere c R, z - w ≠ 0 := by
        intro z hz h
        rw [sub_eq_zero] at h
        subst h
        rw [Metric.mem_sphere] at hz
        rw [Metric.mem_ball] at hw
        linarith
      have h1 : Set.EqOn (fun z => dslope f w z)
          (fun z => (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (Metric.sphere c R) := by
        intro z hz
        simp only
        rw [dslope_of_ne _ (sub_ne_zero.mp (hne z hz)), slope_def_module, smul_sub]
      have hk : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (Metric.sphere c R) :=
        (continuousOn_id.sub continuousOn_const).inv₀ hne
      have hc1 : ContinuousOn (fun z => (z - w)⁻¹ • f z) (Metric.sphere c R) :=
        hk.smul (hf.continuousOn.mono Metric.sphere_subset_closedBall)
      have hc2 : ContinuousOn (fun z => (z - w)⁻¹ • f w) (Metric.sphere c R) :=
        hk.smul continuousOn_const
      rw [circleIntegral.integral_congr hR.le h1,
        circleIntegral.integral_sub (hc1.circleIntegrable hR.le) (hc2.circleIntegrable hR.le)]
      abel
    """, *_FACT_IMPORTS,
    label="on the circle z ≠ w, so (z − w)⁻¹f(z) = g(z) + (z − w)⁻¹f(w); integrate termwise")

kernel_integral = lemma("circleIntegral.integral_sub_inv_of_mem_ball", _CIRCLE,
                        label="∮ dz/(z − w) = 2πi for w inside the circle")
integral_smul_const = lemma("circleIntegral.integral_smul_const", _CIRCLE,
                            label="a constant factor comes out of the integral")
radius_pos = lemma("Metric.pos_of_mem_ball", _METRIC,
                   label="a disc containing a point has positive radius")

#: Mathlib's statements of Cauchy's integral formula, and its removable-singularity theorem
#: (which Mathlib derives from the formula): pass as ``avoid=`` in a proof of the formula.
INTEGRAL_FORMULA = (
    lemma("Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable", _CAUCHY),
    lemma("Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux", _CAUCHY),
    lemma("Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable",
          _CAUCHY),
    lemma("DiffContOnCl.circleIntegral_sub_inv_smul", _CAUCHY),
    lemma("DifferentiableOn.circleIntegral_sub_inv_smul", _CAUCHY),
    lemma("Complex.differentiableOn_dslope", "Mathlib.Analysis.Complex.RemovableSingularity"),
)

LEMMAS = collect_lemmas(globals())

__all__ = ["C", "I", "pi", "two_pi_i", "inv", "ball", "closed_ball", "sphere", "mem",
           "minus_point", "holomorphic_on", "differentiable_at", "continuous_on",
           "difference_quotient", "circle_integral", "INTEGRAL_FORMULA", "LEMMAS",
           "VERIFIED_MATHLIB", "CATALOG_VERSION", *LEMMAS]
