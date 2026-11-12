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
    assert "(env.getModuleIdxFor? u).isNone" in src
    assert "exact Metric.pos_of_mem_ball hw" in src
    text = str(thm.prose())
    assert "5. ∮_(|z - c| = R)g(z) dz = 0.  (Cauchy's theorem" in text
    assert "if f is holomorphic on D̄(c, R), w ∈ D(c, R)" in text


def test_gap_filler_rewrites_and_applies_to_hypotheses() -> None:
    from pyleanx.proofs import Justify, Name

    alts = Justify((Name("L"), Name("h"))).alternatives()
    assert "exact L h" in alts and "(rw [L]; done)" in alts


# --------------------------------------------------------------------------- citing theorems


def _lemma_and_user() -> tuple[pl.Theorem, pl.Theorem]:
    a = pl.symbol("a", pl.Real)
    lemma_ = pl.Theorem("sq_nonneg_lemma", [a], conclusion=a**2 >= 0, proof=pl.positivity())
    b = pl.symbol("b", pl.Real)
    user = pl.Theorem("uses_lemma", [b], conclusion=b**2 + 1 > 0,
                      proof=pl.proof(pl.claim(b**2 >= 0, because=lemma_), pl.conclude()))
    return lemma_, user


def test_citing_a_theorem_emits_its_proof_first() -> None:
    lemma_, user = _lemma_and_user()
    src = user.to_lean()
    assert "-- PyLeanX: theorem sq_nonneg_lemma, cited by a proof below" in src
    assert src.index("theorem sq_nonneg_lemma") < src.index("theorem uses_lemma")
    assert "#print axioms sq_nonneg_lemma" in src  # the cited proof is audited too
    # in one batch the cited theorem is emitted once, before its citer, whatever the order
    from pyleanx.render.lean import render_module

    mod = render_module([user, lemma_])
    assert mod.source.count("theorem sq_nonneg_lemma") == 1
    assert mod.source.index("theorem sq_nonneg_lemma") < mod.source.index("theorem uses_lemma")
    assert mod.theorem_names == ("uses_lemma", "sq_nonneg_lemma")
    kinds = {s.kind for s in render_module([user]).source_map.spans}
    assert "cited_theorem" in kinds


def test_only_proved_theorems_can_be_cited() -> None:
    draft = pl.Theorem("draft", [], conclusion=pl.TRUE)
    user = pl.Theorem("uses_draft", [], conclusion=pl.TRUE,
                      proof=pl.proof(pl.conclude(because=draft)))
    with pytest.raises(TacticError, match="has no proof"):
        user.to_lean()
    draft.prove(pl.rfl())
    assert "theorem draft" in user.to_lean()  # proved now: cited with its proof


def test_citation_cycles_are_rejected() -> None:
    p_ = pl.Theorem("p_thm", [], conclusion=pl.TRUE, proof=pl.rfl())
    q_ = pl.Theorem("q_thm", [], conclusion=pl.TRUE, proof=pl.proof(pl.conclude(because=p_)))
    p_.prove(pl.proof(pl.conclude(because=q_)))
    with pytest.raises(TacticError, match="cycle"):
        q_.to_lean()


def test_citations_round_trip_and_bank_records_them(tmp_path) -> None:
    from pyleanx.backend.interface import Status, VerificationResult
    from pyleanx.proofs import CITED_THEOREMS
    from pyleanx.render.lean import render_statement

    lemma_, user = _lemma_and_user()
    data = user.canonical()
    assert ["theorem_ref", "sq_nonneg_lemma"] in data["proof"][1][0][3]
    assert _body(theorem_from_canonical(data).to_lean()) == _body(user.to_lean())
    saved = CITED_THEOREMS.pop("sq_nonneg_lemma")
    try:
        with pytest.raises(Exception, match="not loaded"):
            theorem_from_canonical(data)
    finally:
        CITED_THEOREMS["sq_nonneg_lemma"] = saved

    proj = pl.find_project(None)

    def ok(t: pl.Theorem) -> VerificationResult:
        return VerificationResult(theorem=t.name, status=Status.VERIFIED,
                                  lean_source=render_statement(t), axioms=("propext",),
                                  toolchain=proj.toolchain,
                                  mathlib_revision=proj.mathlib_revision)

    bank = pl.TheoremBank(tmp_path / "bank.json")
    bank.add_theorem(lemma_, ok(lemma_), id="lemma")
    entry = bank.add_theorem(user, ok(user), id="user")
    assert entry.dependencies == ("lemma",)  # recorded from the citation
    names = [t.name for t in bank.load_with_dependencies("user")]
    assert names == ["sq_nonneg_lemma", "uses_lemma"]


def test_a_broken_cited_theorem_rejects_only_its_citers() -> None:
    import json

    from pyleanx.backend.interface import Status
    from pyleanx.backend.subprocess_backend import LeanRun, classify, parse_json_messages
    from pyleanx.project import LeanProject
    from pyleanx.render.lean import render_module

    _, user = _lemma_and_user()
    c = pl.symbol("c", pl.Real)
    other = pl.Theorem("unrelated", [c], conclusion=c**2 >= 0, proof=pl.positivity())
    mod = render_module([user, other])
    sm = mod.source_map
    dep = next(s for s in sm.spans if s.kind == "cited_theorem")
    assert dep.theorem == "uses_lemma"

    def msg(sev: str, line: int, data: str) -> str:
        return json.dumps({"severity": sev, "pos": {"line": line, "column": 0},
                           "endPos": None, "data": data, "fileName": "f.lean"})

    ax = "depends on axioms: [propext]"
    out = "\n".join([msg("error", dep.start_line + 1, "positivity failed"),
                     msg("information", sm.audit_line("uses_lemma"), f"'uses_lemma' {ax}"),
                     msg("information", sm.audit_line("unrelated"), f"'unrelated' {ax}")])
    msgs, _ = parse_json_messages(out)
    run = LeanRun(returncode=1, messages=msgs, other_output="", timed_out=False, duration_ms=1)
    v = classify(run, mod, LeanProject.at("."))
    assert v["unrelated"][0] is Status.VERIFIED
    assert v["uses_lemma"][0] is Status.REJECTED
    assert any("cited theorem sq_nonneg_lemma" in d.message for d in v["uses_lemma"][1])
