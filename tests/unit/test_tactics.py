import pytest

import pyleanx as pl
from pyleanx.proofs import Name, contains_raw, screen_raw_tactic
from pyleanx.render.lean import render_tactic_lines as lines


def test_basic_tactics():
    assert lines(pl.ring()) == ["ring"]
    assert lines(pl.omega()) == ["omega"]
    assert lines(pl.positivity()) == ["positivity"]
    assert lines(pl.simp()) == ["simp"]
    assert lines(pl.simp("h", only=True, at="h2")) == ["simp only [h] at h2"]
    assert lines(pl.simp(only=True)) == ["simp only []"]
    assert lines(pl.linarith()) == ["linarith"]
    assert lines(pl.nlinarith(pl.mathlib.sq_nonneg)) == ["nlinarith [sq_nonneg]"]
    assert lines(pl.norm_num()) == ["norm_num"]
    assert lines(pl.rfl()) == ["rfl"] and lines(pl.decide()) == ["decide"]


def test_intro_exact_apply_rw():
    assert lines(pl.intro("h", "h2")) == ["intro h h2"]
    assert lines(pl.exact("h")) == ["exact h"]
    assert lines(pl.apply(pl.ref("le_of_lt"))) == ["apply le_of_lt"]
    assert lines(pl.rw("h", pl.rev("add_comm"), at="h3")) == ["rw [h, ← add_comm] at h3"]


def test_term_application_with_expressions():
    x = pl.symbol("x", pl.Real)
    assert lines(pl.exact(pl.mathlib.sq_nonneg(x - 1))) == ["exact sq_nonneg (x - 1)"]
    assert lines(pl.exact(pl.ref("mul_pos")("ha", "hb"))) == ["exact mul_pos ha hb"]


def test_ref_to_theorem():
    x = pl.symbol("x", pl.Real)
    t = pl.Theorem("helper", [x], conclusion=x == x, proof=pl.rfl())
    assert lines(pl.exact(pl.ref(t)(x))) == ["exact helper x"]


def test_steps_and_branches():
    t = pl.constructor() >> pl.branches(pl.positivity(), pl.intro("h") >> pl.exact("h"))
    assert lines(t) == ["constructor", "· positivity", "· intro h", "  exact h"]
    assert len(t.flat()) == 2


def test_use():
    x = pl.symbol("x", pl.Real)
    assert lines(pl.use(x + 1)) == ["use x + 1"]
    assert lines(pl.use(pl.real(2))) == ["use (2 : Real)"]


def test_tactic_validation():
    with pytest.raises(pl.IdentifierError):
        pl.exact("h; sorry")
    with pytest.raises(pl.IdentifierError):
        pl.intro("bad name")
    with pytest.raises(pl.TacticError):
        pl.intro()
    with pytest.raises(pl.TacticError):
        pl.steps()
    with pytest.raises(pl.TacticError):
        pl.steps("ring")  # type: ignore[arg-type]
    with pytest.raises(pl.TacticError):
        pl.Theorem("t", [], conclusion=pl.TRUE).prove("ring")  # type: ignore[arg-type]
    with pytest.raises(pl.IdentifierError):
        Name("Nat.add zero")
    with pytest.raises(pl.TacticError):
        pl.exact(3.5)  # type: ignore[arg-type]


def test_tactic_imports():
    assert "Mathlib.Tactic.Ring" in pl.ring().imports()
    assert pl.omega().imports() == ()
    assert "Mathlib.Algebra.Order.Ring.Unbundled.Basic" in pl.exact(pl.mathlib.sq_nonneg).imports()


@pytest.mark.parametrize(
    "text",
    [
        "sorry\naxiom bogus : False",
        "set_option debug.skipKernelTC true in rfl",
        "#print axioms foo",
        "exact (by run_tac pure ())",
        "/- comment -/ rfl",
        "rfl\ntheorem other : True := trivial",
        "exact Lean.Elab.foo",
    ],
)
def test_raw_tactic_screening_rejects(text):
    assert screen_raw_tactic(text)


@pytest.mark.parametrize(
    "text", ["nlinarith [sq_nonneg (x - 1)]", "intro h\nexact h", "simp [Nat.add_comm]",
             "exact h.le"]
)
def test_raw_tactic_screening_accepts(text):
    assert screen_raw_tactic(text) == []


def test_raw_tactic_marked():
    t = pl.intro("h") >> pl.raw_tactic("  exact h  ")
    assert contains_raw(t)
    assert lines(t) == ["intro h", "exact h"]
    with pytest.raises(pl.TacticError):
        pl.raw_tactic("   ")
