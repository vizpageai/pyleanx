"""LaTeX display, the @pl.theorem decorator, Greek/subscript names, Unicode type names."""

import pytest

import pyleanx as pl
from pyleanx.render.latex import latex_name


@pytest.mark.parametrize(
    "name, expected",
    [("x", "x"), ("α", r"\alpha"), ("ε", r"\varepsilon"), ("Ω", r"\Omega"), ("Α", "A"),
     ("x₁", "x_{1}"), ("x1", "x_{1}"), ("θ₁₂", r"\theta_{12}"), ("x_1", "x_{1}"),
     ("x_max", r"x_{\mathit{max}}"), ("abc", r"\mathit{abc}"), ("x'", "x'"),
     ("αβ", r"\alpha \beta"), ("h_α", r"h_{\alpha}")],
)
def test_latex_names(name, expected):
    assert latex_name(name) == expected


def test_expression_latex():
    x, y = pl.symbols("x y", pl.Real)
    θ, ε = pl.symbols("θ ε", pl.Real)
    n = pl.symbol("n", pl.Nat)
    P, Q = pl.prop_symbol("P"), pl.prop_symbol("Q")
    cases = [
        ((x + y) ** 2 == x**2 + 2 * x * y + y**2,
         r"\left(x + y\right)^{2} = x^{2} + 2 x y + y^{2}"),
        (x * 2, r"x \cdot 2"),
        (pl.integer(2) * 3 == 6, r"2 \cdot 3 = 6"),
        (x / (y + 1), r"\frac{x}{y + 1}"),
        (pl.rat(1, 2) * θ, r"\frac{1}{2} \theta"),
        (pl.real("-0.25") + x, r"-\frac{1}{4} + x"),
        (pl.sqrt(x) ** 2, r"\left(\sqrt{x}\right)^{2}"),
        (abs(θ - 1) <= ε, r"\left|\theta - 1\right| \leq \varepsilon"),
        (pl.exp(x) > 0, r"\exp\left(x\right) > 0"),
        (pl.max(x, y) >= x, r"\max\left(x, y\right) \geq x"),
        (-(x + y), r"-\left(x + y\right)"),
        ((-x) ** 2, r"\left(-x\right)^{2}"),
        (x != y, r"x \neq y"),
        (pl.cast(n, pl.Real) + x, r"\left(n : \mathbb{R}\right) + x"),
        (n % 2 == 0, r"n \bmod 2 = 0"),
        (pl.Implies(P, Q), r"P \to Q"),
        (pl.Iff(P, ~Q), r"P \leftrightarrow \neg Q"),
        (pl.And(P | Q, P), r"\left(P \lor Q\right) \land P"),
        (pl.Forall([x], pl.Exists([y], y > x)),
         r"\forall x \in \mathbb{R},\ \exists y \in \mathbb{R},\ y > x"),
        (pl.TRUE, r"\top"),
    ]
    for e, expected in cases:
        assert e.to_latex() == expected, (e.to_latex(), expected)
        assert e._repr_latex_() == f"${expected}$"


def test_mixed_binders_latex():
    x = pl.symbol("x", pl.Real)
    n = pl.symbol("n", pl.Nat)
    P = pl.prop_symbol("P")
    q = pl.Forall([x, n, P], pl.Implies(P, pl.cast(n, pl.Real) * x == x * pl.cast(n, pl.Real)))
    assert q.to_latex().startswith(
        r"\forall x \in \mathbb{R},\ n \in \mathbb{N},\ P : \mathrm{Prop},\ ")


def test_theorem_latex_and_markdown():
    a, b = pl.symbols("a b", pl.Real)
    thm = pl.Theorem("sum_pos", [a, b], assumptions={"ha": a > 0, "hb": b > 0},
                     conclusion=a + b > 0, proof=pl.linarith())
    assert thm.to_latex() == (r"\forall a, b \in \mathbb{R},\quad a > 0,\ b > 0 "
                              r"\;\Longrightarrow\; a + b > 0")
    md = thm._repr_markdown_()
    assert "$$" in md and "```lean" in md and "theorem sum_pos" in md
    assert "not yet verified" in md
    assert pl.latex(thm) == thm.to_latex() and pl.latex(a + b) == "a + b"


def test_decorator_builds_theorem():
    @pl.theorem(proof=pl.ring())
    def square_identity(x: pl.Real, y: pl.Real):
        """The binomial square."""
        return (x + y) ** 2 == x**2 + 2 * x * y + y**2

    assert isinstance(square_identity, pl.Theorem)
    assert square_identity.name == "square_identity"
    assert [v.name for v in square_identity.variables] == ["x", "y"]
    assert "theorem square_identity (x y : Real) :" in square_identity.to_lean()
    assert square_identity.__doc__ == "The binomial square."
    assert square_identity.origin.filename.endswith("test_latex.py")


def test_decorator_options_and_greek():
    @pl.theorem(name="scaled", proof=pl.positivity(),
                assumptions=lambda α, x: {"hα": α > 0})
    def _ignored_name(α: pl.Real, x: pl.Real):
        return α * x**2 + α >= 0

    src = _ignored_name.to_lean()
    assert "theorem scaled (α x : Real) (hα : α > 0) :" in src

    @pl.theorem
    def no_proof_yet(n: pl.Nat):
        return n + 0 == n

    assert no_proof_yet.proof is None
    no_proof_yet.prove(pl.simp())
    assert "  simp" in no_proof_yet.to_lean()


def test_decorator_errors():
    with pytest.raises(pl.SortError, match="sort annotation"):
        @pl.theorem
        def missing(x):
            return x == x

    with pytest.raises(pl.SortError, match="args"):
        @pl.theorem
        def star(*xs: pl.Real):
            return pl.TRUE

    with pytest.raises(pl.SymbolicTruthValueError):
        @pl.theorem
        def uses_if(x: pl.Real):
            return x > 0 if x else x < 0

    with pytest.raises(pl.IdentifierError):
        @pl.theorem
        def λ_bad(λ: pl.Real):  # λ is Lean syntax
            return λ == λ


def test_greek_and_subscript_symbols():
    θ = pl.symbol("θ", pl.Real)
    x1 = pl.symbol("x₁", pl.Real)
    thm = pl.Theorem("greek_ok", [θ, x1], conclusion=θ + x1 == x1 + θ, proof=pl.ring())
    assert "theorem greek_ok (θ x₁ : Real) :" in thm.to_lean()
    for bad in ["λ", "Π", "Σ", "₁x", "ℝ"]:
        with pytest.raises(pl.IdentifierError):
            pl.symbol(bad, pl.Real)


def test_unicode_type_names():
    x = pl.symbol("x", pl.Real)
    n = pl.symbol("n", pl.Nat)
    k = pl.symbol("k", pl.Int)
    q = pl.symbol("q", pl.Rat)
    y = pl.symbol("y", pl.Real)
    thm = pl.Theorem("u", [x, n, k, q],
                     conclusion=pl.And(pl.cast(n, pl.Real) + x == x + pl.cast(n, pl.Real),
                                       k == k, q == q, pl.Forall([y], y == y)),
                     proof=pl.simp())
    proj = pl.LeanProject.at(".").with_(unicode_types=True)
    src = thm.to_lean(proj)
    assert "theorem u (x : ℝ) (n : ℕ) (k : ℤ) (q : ℚ) :" in src
    assert "(↑n : ℝ)" in src and "∀ (y : ℝ), y = y" in src
    for mod in ("Mathlib.Data.Nat.Notation", "Mathlib.Data.Int.Notation",
                "Mathlib.Data.Rat.Init"):
        assert f"import {mod}" in src
    plain = thm.to_lean()
    assert "ℝ" not in plain and "Mathlib.Data.Nat.Notation" not in plain
    # a Nat exponent alone does not pull in the ℕ notation module
    t2 = pl.Theorem("v", [x], conclusion=x**2 >= 0, proof=pl.positivity())
    assert "Nat.Notation" not in t2.to_lean(proj)


def test_result_markdown():
    r = pl.VerificationResult(theorem="t", status=pl.Status.VERIFIED, axioms=("propext",))
    assert "✅" in r._repr_markdown_() and "propext" in r._repr_markdown_()
    bad = pl.VerificationResult(theorem="t", status=pl.Status.REJECTED,
                                diagnostics=[pl.Diagnostic("error", "boom\nmore", 3, 2)])
    assert "❌" in bad._repr_markdown_() and "boom" in bad._repr_markdown_()
