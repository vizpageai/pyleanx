"""Written proofs across domains: fix/take/choose/contradiction/cases/induction/chain/
suffices, abstract structures, and the number-theory/analysis/algebra vocabularies (no Lean).
"""

from __future__ import annotations

import runpy
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import algebra as alg
from pyleanx import numbers as nt
from pyleanx.binders import substitute
from pyleanx.errors import TacticError
from pyleanx.proofs import CaseSplit, chain_relation
from pyleanx.serialize import theorem_from_canonical

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"
READABLE = ["infinite_primes", "consecutive_even", "limit_sum", "group_abelian", "bernoulli",
            "trig", "side_splitter", "am_gm", "cauchy_integral"]


def example(name: str) -> pl.Theorem:
    ns = runpy.run_path(str(EXAMPLES / f"readable_{name}.py"))
    return next(v for v in ns.values() if isinstance(v, pl.Theorem))


def _body(src: str) -> str:
    return "\n".join(ln for ln in src.splitlines() if not ln.startswith("import "))


@pytest.mark.parametrize("name", READABLE)
def test_examples_round_trip_and_have_no_sorry(name: str) -> None:
    thm = example(name)
    src = thm.to_lean()
    assert "sorry" not in src and "admit" not in src
    again = theorem_from_canonical(thm.canonical())
    assert _body(again.to_lean()) == _body(src)


def test_epsilon_N_proof_renders_the_textbook_moves() -> None:
    src = example("limit_sum").to_lean()
    assert "suffices h : ∀ (ε : Real), ε > 0 →" in src
    assert "intro ε (hε : ε > 0)" in src
    assert "obtain ⟨N₁, hN₁⟩ : ∃ (N₁ : Nat), ∀ (n : Nat), n ≥ N₁ →" in src
    assert "refine ⟨max N₁ N₂, ?_⟩" in src
    assert "intro n (hn : n ≥ max N₁ N₂)" in src
    assert "calc abs (a n + b n - (A + B))" in src
    assert "theorem PyLeanX.Analysis.tendsto_iff_eps_N" in src  # shipped with its proof


def test_contradiction_and_choose() -> None:
    src = example("infinite_primes").to_lean()
    assert "set N : Nat := Nat.factorial n + 1 with N_def" in src
    assert "obtain ⟨p, hp, hpN⟩ : ∃ (p : Nat), Nat.Prime p ∧ Dvd.dvd p N :=" in src
    assert "refine ⟨p, ?_⟩" in src
    assert "by_contra hle_neg" in src and "have hle : p ≤ n := by" in src
    assert "have step6_2 : Dvd.dvd p (Nat.factorial n) := by" in src  # nested names


def test_cases_and_induction() -> None:
    src = example("consecutive_even").to_lean()
    assert "have step1 : Even n ∨ Odd n :=" in src
    assert "rcases step1 with h | h" in src
    assert src.count("· obtain ⟨k, hk⟩") == 2
    src = example("bernoulli").to_lean()
    assert "induction n with" in src and "| succ k ih =>" in src


def test_type_parameter_binders_and_round_trip() -> None:
    thm = example("group_abelian")
    src = thm.to_lean()
    assert "theorem abelian_of_sq_eq_one {G : Type*} [Group G] (a b : G)" in src
    assert "import Mathlib.Tactic.TypeStar" in src
    G = alg.group("G")
    assert G is alg.group("G")  # interned
    data = thm.canonical()
    assert data["variables"][0][2] == ["param", "G", ["Group"],
                                       ["Mathlib.Tactic.TypeStar", "Mathlib.Algebra.Group.Defs"],
                                       "group"]


def test_prose_across_domains() -> None:
    text = str(example("infinite_primes").prose())
    assert "3. N ≠ 1.  (n! > 0, so N ≥ 2)" in text
    assert "4. Choose p such that p is prime ∧ p ∣ N.  (every n ≠ 1 has a prime factor)" in text
    assert "5. Take p." in text
    assert "6.1. Suppose, for contradiction, that p ≤ n." in text
    assert "This is a contradiction (a prime does not divide 1)." in text
    assert text.rstrip().splitlines()[-2] == "  Hence n < p ∧ p is prime. ∎"

    text = str(example("consecutive_even").prose())
    assert "Case 1: n is even." in text and "Case 2: n is odd." in text
    assert "1.3. Choose k such that n = 2k + 1." in text  # numbering continues across cases

    text = str(example("bernoulli").prose())
    assert "Base case: (1 + x)⁰ ≥ 1 + 0x." in text
    assert ("Inductive step: assume (1 + x)^k ≥ 1 + kx (ih); "
            "we show (1 + x)^(k + 1) ≥ 1 + (k + 1)x.") in text

    text = str(example("group_abelian").prose())
    assert text.startswith("Theorem (abelian_of_sq_eq_one). For every group G and all a, b ∈ G:")
    assert "ab = (ab)⁻¹ (by step 1)" in text

    text = str(example("limit_sum").prose())
    assert "4. Let ε ∈ ℝ with ε > 0." in text
    assert "7. Take N = max(N₁, N₂)." in text
    md = example("limit_sum").prose().to_markdown()
    assert r"\le" in md and "$" in md


def test_one_fact_for_both_corresponding_angles() -> None:
    src = example("side_splitter").to_lean()
    assert "corresponding_angles_2" not in src
    assert "with_reducible_and_instances apply And.right" in src


def test_chain_relation() -> None:
    assert chain_relation(["=", "≤", "="]) == "≤"
    assert chain_relation(["≤", "<"]) == "<"
    assert chain_relation(["≥", "=", ">"]) == ">"
    with pytest.raises(TacticError):
        chain_relation(["≤", "≥"])
    a = pl.symbol("a", pl.Real)
    with pytest.raises(TacticError):
        pl.chain(a, ("<=", a), (">=", a))
    with pytest.raises(TacticError):
        pl.chain(a, ("!=", a))


def test_validation_messages() -> None:
    a = pl.symbol("a", pl.Real)
    with pytest.raises(TacticError, match="at least two"):
        pl.cases_on(pl.case(a > 0, pl.conclude()))
    with pytest.raises(TacticError, match="variables or assume"):
        pl.fix()
    with pytest.raises(TacticError, match="witness"):
        pl.take()
    with pytest.raises(TacticError, match="symbols"):
        pl.choose(a + 1, such_that=a > 0)  # type: ignore[arg-type]
    with pytest.raises(TacticError, match="proof steps"):
        pl.case(a > 0)


def test_cases_on_p_or_not_p_needs_no_reason() -> None:
    a = pl.symbol("a", pl.Real)
    split = pl.cases_on(pl.case(a >= 0, pl.conclude()), pl.case(pl.Not(a >= 0), pl.conclude()))
    assert isinstance(split, CaseSplit)
    assert [f.name for f in split.facts] == ["Classical.em"]


def test_substitute_respects_binders() -> None:
    n, k = pl.symbols("n k", pl.Nat)
    x = pl.symbol("x", pl.Real)
    p = pl.Forall(x, (1 + x)**n >= 1)
    assert substitute(p, {n.uid: k + 1}).to_lean() == "∀ (x : Real), (1 + x) ^ (k + 1) ≥ 1"
    assert substitute(p, {x.uid: pl.real(0)}) .to_lean() == p.to_lean()  # x is bound


def test_number_theory_vocabulary() -> None:
    n = pl.symbol("n", pl.Nat)
    assert nt.divides(3, n).to_lean() == "Dvd.dvd 3 n"
    assert nt.even(n).to_latex() == r"n \text{ is even}"
    assert (nt.factorial(n) + 1).to_lean() == "Nat.factorial n + 1"
    assert {"even_or_odd", "exists_prime_dvd", "dvd_factorial"} <= set(nt.LEMMAS)


def test_cauchy_integral_formula_from_cauchys_theorem() -> None:
    thm = example("cauchy_integral")
    src = thm.to_lean()
    assert "set g : ℂ → ℂ := dslope f w with g_def" in src
    assert "theorem PyLeanX.Complex.cauchy_theorem_disc" in src
    # the forbidden lemmas' modules are imported, so `simp [-lemma]` can name them
    assert "import Mathlib.Analysis.Complex.RemovableSingularity" in src
    # the avoid check also looks inside the PyLeanX facts the proof cites
    assert "(`PyLeanX).isPrefixOf u" in src
    assert "exact Metric.pos_of_mem_ball hw" in src
    text = str(thm.prose())
    assert "5. ∮_(|z - c| = R)g(z) dz = 0.  (Cauchy's theorem" in text
    assert "if f is holomorphic on D̄(c, R), w ∈ D(c, R)" in text


def test_gap_filler_rewrites_and_applies_to_hypotheses() -> None:
    from pyleanx.proofs import Justify, Name

    alts = Justify((Name("L"), Name("h"))).alternatives()
    assert "exact L h" in alts and "(rw [L]; done)" in alts
