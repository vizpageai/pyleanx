"""Golden tests for deterministic Lean rendering."""

import pyleanx as pl
from pyleanx.render.lean import render_module

SQUARE_IDENTITY = """\
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem square_identity (x y : Real) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

#print axioms square_identity
"""

NAT_ADD_ZERO = """\
set_option autoImplicit false

theorem nat_add_zero (n : Nat) :
    n + 0 = n := by
  simp

#print axioms nat_add_zero
"""

IDENTITY_IMP = """\
set_option autoImplicit false

theorem identity_imp (P : Prop) :
    P → P := by
  intro h
  exact h

#print axioms identity_imp
"""


def test_square_identity_golden():
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("square_identity", variables=[x, y],
                     conclusion=(x + y) ** 2 == x**2 + 2 * x * y + y**2)
    thm.prove(pl.ring())
    assert thm.to_lean() == SQUARE_IDENTITY


def test_nat_add_zero_golden():
    n = pl.symbol("n", pl.Nat)
    assert pl.Theorem("nat_add_zero", [n], conclusion=n + 0 == n,
                      proof=pl.simp()).to_lean() == NAT_ADD_ZERO


def test_identity_imp_golden():
    P = pl.prop_symbol("P")
    thm = pl.Theorem("identity_imp", [P], conclusion=pl.Implies(P, P))
    thm.prove(pl.steps(pl.intro("h"), pl.exact("h")))
    assert thm.to_lean() == IDENTITY_IMP


def test_to_lean_is_deterministic_and_pure():
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("t", [x, y], conclusion=x * y == y * x, proof=pl.ring())
    first = thm.to_lean()
    assert thm.to_lean() == first
    x2, y2 = pl.symbols("x y", pl.Real)
    other = pl.Theorem("t", [x2, y2], conclusion=x2 * y2 == y2 * x2, proof=pl.ring())
    assert other.to_lean() == first  # independent of variable uids


def test_hypotheses_and_mixed_binders():
    x = pl.symbol("x", pl.Real)
    n = pl.symbol("n", pl.Nat)
    P = pl.prop_symbol("P")
    thm = pl.Theorem("t", [x, n, P], assumptions=[("hx", 0 < x), ("hP", P)],
                     conclusion=pl.And(P, pl.cast(n, pl.Real) + x > 0), proof=pl.omega())
    src = thm.to_lean()
    assert "theorem t (x : Real) (n : Nat) (P : Prop) (hx : x > 0) (hP : P) :" in src
    assert "    P ∧ (↑n : Real) + x > 0 := by" in src


def test_precedence_and_parentheses():
    x, y = pl.symbols("x y", pl.Real)
    P, Q, R = (pl.prop_symbol(n) for n in "PQR")
    cases = [
        ((-x) ** 2, "(-x) ^ 2"),
        (-(x**2), "-(x ^ 2)"),
        (x - (y - 1), "x - (y - 1)"),
        ((x - y) - 1, "x - y - 1"),
        (x / (y * 2), "x / (y * 2)"),
        ((x**2) ** 3, "(x ^ 2) ^ 3"),
        (x ** (pl.nat(2) ** 3), "x ^ 2 ^ 3"),
        (x * (y + 1) / 2 - pl.rat(1, 2), "x * (y + 1) / 2 - 1 / 2"),
        (x * pl.rat(1, 2), "x * (1 / 2)"),
        (pl.Implies(pl.Implies(P, Q), R), "(P → Q) → R"),
        (pl.Implies(P, Q, R), "P → Q → R"),
        (pl.Not(P & Q) | ~P, "¬(P ∧ Q) ∨ ¬P"),
        (pl.And(P | Q, R), "(P ∨ Q) ∧ R"),
        (pl.Iff(P, pl.Implies(Q, P)), "P ↔ Q → P"),
        (pl.And(pl.Forall([x], x == x), P), "(∀ (x : Real), x = x) ∧ P"),
        (pl.Not(x == y), "¬x = y"),
        (pl.sqrt(x + 1) ** 2, "Real.sqrt (x + 1) ^ 2"),
        (abs(x - 1) <= 3, "abs (x - 1) ≤ 3"),
        (pl.integer(-3) ** 2 == 9, "(-3 : Int) ^ 2 = (9 : Int)"),
        (pl.real(2) + 2 == 4, "(2 : Real) + (2 : Real) = (4 : Real)"),
        (pl.nat(2) + 2 == 4, "2 + 2 = 4"),
        (pl.cast(pl.symbol("m", pl.Nat) + 1, pl.Real), "(↑(m + 1) : Real)"),
        (x + -1, "x + -1"),
        (pl.real("-0.5") * x, "-1 / 2 * x"),
    ]
    for expr, expected in cases:
        assert expr.to_lean() == expected, (expr.to_lean(), expected)


def test_quantifier_binders_grouped():
    x, y = pl.symbols("x y", pl.Real)
    n = pl.symbol("n", pl.Nat)
    q = pl.Forall([x, y], pl.Exists([n], pl.cast(n, pl.Real) > x + y))
    assert q.to_lean() == "∀ (x y : Real), ∃ (n : Nat), (↑n : Real) > x + y"


def test_source_map_spans():
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("t", [x], conclusion=x**2 >= 0,
                     proof=pl.steps(pl.positivity()))
    mod = render_module([thm])
    lines = mod.source.splitlines()
    sm = mod.source_map
    audit = sm.audit_line("t")
    assert lines[audit - 1] == "#print axioms t"
    tactic_spans = [s for s in sm.spans if s.kind == "tactic"]
    assert len(tactic_spans) == 1
    assert lines[tactic_spans[0].start_line - 1] == "  positivity"
    assert tactic_spans[0].origin is not None and tactic_spans[0].origin.filename.endswith(
        "test_render.py")
    span = sm.innermost(tactic_spans[0].start_line)
    assert span.kind == "tactic"
    thm_span = sm.theorem_span("t")
    assert thm_span.contains(tactic_spans[0].start_line) and not thm_span.contains(audit)


def test_module_with_multiple_theorems_and_imports():
    x = pl.symbol("x", pl.Real)
    n = pl.symbol("n", pl.Nat)
    a = pl.Theorem("a", [x], conclusion=x**2 >= 0, proof=pl.positivity())
    b = pl.Theorem("b", [n], conclusion=n + 0 == n, proof=pl.simp())
    mod = render_module([a, b])
    assert mod.imports == ("Mathlib.Basic.Real.Basic", "Mathlib.Tactic.Positivity")
    assert mod.source.count("#print axioms") == 2
    assert render_module([a, b], import_mode="mathlib").imports == ("Mathlib",)


def test_statement_only_rendering_has_failing_placeholder():
    x = pl.symbol("x", pl.Real)
    src = pl.Theorem("t", [x], conclusion=x == x).to_lean()
    assert 'fail "pyleanx: no proof supplied"' in src
    assert "sorry" not in src
