"""Written proofs: pl.claim / pl.conclude / pl.let, avoid=, library facts, prose (no Lean)."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import analysis as an
from pyleanx import geometry as geo
from pyleanx.errors import TacticError
from pyleanx.proofs import Claim, Justify, library_facts
from pyleanx.prose import latex_text
from pyleanx.serialize import theorem_from_canonical

x, t, a, b = pl.symbols("x t a b", pl.Real)
f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))


def trig() -> pl.Theorem:
    return pl.Theorem(
        "trig_by_derivative", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
        avoid=[an.sin_sq_add_cos_sq],
        proof=pl.proof(
            pl.let(f, lambda t: an.sin(t)**2 + an.cos(t)**2),
            pl.claim(an.differentiable(f)),
            pl.claim(pl.Forall(t, an.deriv(f, t) == 0), note="chain rule"),
            pl.claim(f(x) == f(0), because=an.constant_of_zero_derivative),
            pl.claim(f(0) == 1, because=[an.sin_zero, an.cos_zero], name="at_zero"),
            pl.conclude(),
        ))


def _body(src: str) -> str:
    return "\n".join(ln for ln in src.splitlines() if not ln.startswith("import "))


def test_claims_are_named_by_position_and_render_as_have() -> None:
    src = trig().to_lean()
    assert "set f : Real → Real := fun (t : Real) => " in src and "with f_def" in src
    assert "have step2 : Differentiable Real f := by" in src  # named by position
    assert "have step4 : f x = f 0 := by" in src
    assert "have at_zero : f 0 = 1 := by" in src  # explicit names are kept
    assert "(apply is_const_of_deriv_eq_zero; all_goals (" in src
    assert "(intros; simp only [f_def] at *; first |" in src


def test_avoid_reaches_simp_and_adds_a_lean_check() -> None:
    src = trig().to_lean()
    assert "-Real.sin_sq_add_cos_sq" in src
    assert "(aesop; done)" not in src  # aesop's simp set cannot be restricted
    assert "#eval show MetaM Unit from do" in src
    assert "let avoid : Array Name := #[`Real.sin_sq_add_cos_sq]" in src
    assert "throwError" in src
    assert src.index("#eval show MetaM") < src.index("#print axioms trig_by_derivative")


def test_no_avoid_check_without_avoid() -> None:
    thm = pl.Theorem("plain_claims", [a], conclusion=a**2 >= 0,
                     proof=pl.proof(pl.claim(a**2 >= 0), pl.conclude()))
    src = thm.to_lean()
    assert "#eval" not in src and "(aesop; done)" in src


def test_avoid_is_part_of_the_statement_record_and_round_trips() -> None:
    thm = trig()
    data = thm.canonical()
    assert data["avoid"] == ["Real.sin_sq_add_cos_sq"]
    again = theorem_from_canonical(data)
    assert again.avoid == thm.avoid
    assert _body(again.to_lean()) == _body(thm.to_lean())  # lemma imports live elsewhere


def test_plain_theorem_canonical_has_no_avoid_key() -> None:
    thm = pl.Theorem("t0", [a], conclusion=a == a, proof=pl.rfl())
    assert "avoid" not in thm.canonical()


def test_claim_validation() -> None:
    with pytest.raises(TacticError):
        pl.claim(a == a, proof="ring")  # type: ignore[arg-type]
    with pytest.raises(TacticError, match="give it a name"):
        pl.claim(a == a, because=pl.claim(a == a))
    named = pl.claim(a == a, name="h")
    assert pl.claim(a == a, because=named).facts[0].name == "h"


def test_justify_alternatives_close_or_fail() -> None:
    j = Justify((pl.hyp("h"),), ("f_def",))
    alts = j.alternatives()
    assert alts[0] == "assumption" and "exact h" in alts
    assert all("sorry" not in a for a in alts)
    assert any(a.startswith("(intros; simp only [f_def] at *;") for a in alts)


def test_let_needs_a_function_symbol_for_lambda() -> None:
    with pytest.raises(TacticError):
        pl.let(a, lambda s: s)


def test_library_facts_are_emitted_once_with_their_requirements() -> None:
    A, B, C, D, E = geo.points("A B C D E")
    thm = pl.Theorem(
        "ss", [A, B, C, D, E],
        assumptions={"hABC": geo.triangle(A, B, C), "hD": geo.on_segment(D, A, B),
                     "hE": geo.on_segment(E, A, C),
                     "hP": geo.parallel(geo.line(D, E), geo.line(B, C))},
        conclusion=geo.dist(A, D) / geo.dist(A, B) == geo.dist(A, E) / geo.dist(A, C),
        proof=pl.proof(
            pl.claim(geo.angle(A, B, C) == geo.angle(A, D, E),
                     because=geo.corresponding_angles),
            pl.claim(geo.angle(B, C, A) == geo.angle(D, E, A),
                     because=geo.corresponding_angles),
            pl.claim(geo.similar((A, B, C), (A, D, E)), because=geo.similar_AA),
            pl.conclude(because=geo.similar_sides)))
    names = [f.name for f in library_facts([thm])]
    assert names == ["PyLeanX.Geometry.corresponding_angles",
                     "PyLeanX.Geometry.similar_sides"]
    src = thm.to_lean()
    assert src.count("theorem PyLeanX.Geometry.corresponding_angles") == 1
    # one fact for both pairs of angles: the gap filler takes the half each claim needs
    assert "apply And.right; with_reducible_and_instances apply PyLeanX.Geometry.corresponding_angles;" in src
    assert "sorry" not in src
    assert src.index("theorem PyLeanX.Geometry.similar_sides") < src.index("theorem ss ")
    assert "import Mathlib.Geometry.Euclidean.Similarity" in src
    # rebuilt from its record, the proof still cites the shipped facts
    assert _body(theorem_from_canonical(thm.canonical()).to_lean()) == _body(src)
    text = str(thm.prose())
    assert "ABC is a triangle" in text and "DE ∥ BC" in text
    assert "△ABC ∼ △ADE.  (AA similarity)" in text
    assert "Hence |AD|/|AB| = |AE|/|AC| (similar triangles have proportional sides). ∎" in text


def test_prose_reads_like_a_proof() -> None:
    p = trig().prose()
    text = str(p)
    assert text.splitlines()[0] == ("Theorem (trig_by_derivative). "
                                    "For all x ∈ ℝ: sin² x + cos² x = 1.")
    assert "1. Let f(t) = sin² t + cos² t." in text
    assert "2. f is differentiable." in text
    assert "3. ∀ t ∈ ℝ, f′(t) = 0.  (chain rule)" in text
    assert "4. f(x) = f(0).  (a differentiable function with derivative 0" in text
    assert "5. f(0) = 1.  (sin 0 = 0, cos 0 = 1)" in text
    assert "Hence sin² x + cos² x = 1. ∎" in text
    assert "Without using: Real.sin_sq_add_cos_sq." in text
    assert "not yet checked by Lean" in text
    md = p.to_markdown()
    assert r"$f \text{ is differentiable}$" in md


def test_prose_reports_only_verified_results_as_checked() -> None:
    class R:
        verified = False
        status = pl.Status.REJECTED
        axioms = ()

    assert "did not accept" in trig().prose(R()).status  # type: ignore[arg-type]

    class V:
        verified = True
        status = pl.Status.VERIFIED
        axioms = ("propext",)

    assert "Checked by Lean (axioms: propext)" in trig().prose(V()).status  # type: ignore


def test_latex_text() -> None:
    assert latex_text(r"\frac{\lvert AD \rvert}{\lvert AB \rvert}") == "|AD|/|AB|"
    assert latex_text(r"\sqrt{a b} \le \frac{a + b}{2}") == "√(ab) ≤ (a + b)/2"
    assert latex_text(r"\left(\cos x\right)^{2}") == "cos² x"
    assert latex_text(r"\forall t \in \mathbb{R},\ f'(t) = 0") == "∀ t ∈ ℝ, f′(t) = 0"


def test_claim_is_exported() -> None:
    assert pl.claim is not None and isinstance(pl.claim(a == a), Claim)
    assert {"claim", "conclude", "let", "prose"} <= set(pl.__all__)


def test_avoid_check_error_rejects_only_its_theorem() -> None:
    import json

    from pyleanx.backend.interface import Status
    from pyleanx.backend.subprocess_backend import LeanRun, classify, parse_json_messages
    from pyleanx.project import LeanProject
    from pyleanx.render.lean import render_module

    def msg(sev: str, line: int, data: str) -> str:
        return json.dumps({"severity": sev, "pos": {"line": line, "column": 0},
                           "endPos": None, "data": data, "fileName": "f.lean"})

    good = pl.Theorem("good", [a], conclusion=a**2 >= 0, proof=pl.positivity())
    cheat = pl.Theorem("cheat", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
                       avoid=[an.sin_sq_add_cos_sq], proof=pl.simp())
    mod = render_module([good, cheat])
    sm = mod.source_map
    check = next(s for s in sm.spans if s.kind == "avoid_check")
    assert check.theorem == "cheat"
    axioms = "depends on axioms: [propext, Classical.choice, Quot.sound]"
    out = "\n".join([
        msg("information", sm.audit_line("good"), f"'good' {axioms}"),
        msg("error", check.start_line + 1, "the proof of cheat uses [Real.sin_sq_add_cos_sq]"),
        msg("information", sm.audit_line("cheat"), f"'cheat' {axioms}"),
    ])
    msgs, _ = parse_json_messages(out)
    run = LeanRun(returncode=1, messages=msgs, other_output="", timed_out=False, duration_ms=1)
    v = classify(run, mod, LeanProject.at("."))
    assert v["good"][0] is Status.VERIFIED
    assert v["cheat"][0] is Status.REJECTED
    err = next(d for d in v["cheat"][1] if d.severity == "error")
    assert err.span_kind == "avoid_check" and "sin_sq_add_cos_sq" in err.message
