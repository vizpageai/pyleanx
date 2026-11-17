"""Real Lean: written proofs across domains, avoid=, shipped library facts, and rejection of
a circular proof and of a false step."""

from __future__ import annotations

import runpy
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import analysis as an
from pyleanx import numbers as nt

pytestmark = pytest.mark.lean

EXAMPLES = Path(__file__).resolve().parents[2] / "examples"
READABLE = ["trig", "side_splitter", "am_gm", "infinite_primes", "consecutive_even",
            "limit_sum", "group_abelian", "bernoulli", "cauchy_integral"]


def _thm(name: str) -> pl.Theorem:
    ns = runpy.run_path(str(EXAMPLES / f"readable_{name}.py"))
    return next(v for v in ns.values() if isinstance(v, pl.Theorem))


def test_written_proofs_verify_and_bad_ones_are_rejected(lean_project):
    good = [_thm(n) for n in READABLE]
    x = pl.symbol("x", pl.Real)
    circular = pl.Theorem("circular_trig", [x], conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
                          avoid=[an.sin_sq_add_cos_sq], proof=pl.simp())
    n, p = pl.symbols("n p", pl.Nat)
    false_step = pl.Theorem(
        "false_step", [n], assumptions={"h": nt.even(n)}, conclusion=nt.even(n * n),
        proof=pl.proof(pl.claim(nt.odd(n), because="h"), pl.conclude()))
    from pyleanx import complex_analysis as ca

    cif = good[-1]
    cif_cheat = pl.Theorem(
        "cif_cheat", cif.variables, [(h.name, h.prop) for h in cif.assumptions], cif.conclusion,
        avoid=ca.INTEGRAL_FORMULA,
        proof=pl.exact(pl.ref("DifferentiableOn.circleIntegral_sub_inv_smul")("hf", "hw")))
    # citing proved theorems: a computation that cites the formula (same batch), and a
    # theorem citing a lemma whose proof is wrong
    import sys

    sys.path.insert(0, str(EXAMPLES))
    try:
        contour = runpy.run_path(str(EXAMPLES / "using_cauchy_integral.py"))["contour_integral"]
        bisector = runpy.run_path(str(EXAMPLES / "readable_angle_bisector.py"))["angle_bisector"]
    finally:
        sys.path.remove(str(EXAMPLES))
    a = pl.symbol("a", pl.Real)
    broken = pl.Theorem("broken_lemma", [a], conclusion=a + 1 <= a, proof=pl.linarith())
    uses_broken = pl.Theorem("uses_broken", [a], conclusion=a + 1 <= a + 0,
                             proof=pl.proof(pl.conclude(because=broken)))
    results = pl.verify_all([*good, circular, false_step, cif_cheat, contour, uses_broken,
                             bisector],
                            project=lean_project, use_cache=False, timeout=3600)
    for t, r in zip(good, results, strict=False):
        assert r.verified, (t.name, [d.message for d in r.diagnostics])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}
        assert "Checked by Lean" in str(t.prose(r))
    bad = results[len(good)]
    assert bad.status is pl.Status.REJECTED
    assert any("Real.sin_sq_add_cos_sq" in d.message and d.span_kind == "avoid_check"
               for d in bad.diagnostics)
    wrong = results[len(good) + 1]
    assert wrong.status is pl.Status.REJECTED and not wrong.verified
    assert "did not accept" in str(false_step.prose(wrong))
    cheat = results[len(good) + 2]
    assert cheat.status is pl.Status.REJECTED
    assert any("DifferentiableOn.circleIntegral_sub_inv_smul" in d.message
               for d in cheat.diagnostics)
    used = results[len(good) + 3]
    assert used.verified, [d.message for d in used.diagnostics]
    assert "theorem cauchy_integral_formula" in str(contour.prose(used))
    citing_broken = results[len(good) + 4]
    assert citing_broken.status is pl.Status.REJECTED and not citing_broken.verified
    assert any("cited" in d.message for d in citing_broken.diagnostics)
    bis = results[-1]
    assert bis.verified, [d.message for d in bis.diagnostics]
    assert set(bis.axioms) <= {"propext", "Classical.choice", "Quot.sound"}


def test_textbook_geometry_and_every_shipped_geometry_fact(lean_project):
    from pyleanx import geometry as geo
    from pyleanx.proofs import LibraryFact

    textbook = runpy.run_path(str(EXAMPLES / "textbook_geometry.py"))["THEOREMS"]
    shipped = [f for f in geo.LEMMAS.values() if isinstance(f, LibraryFact)]
    # a theorem whose Lean file contains every shipped geometry fact with its proof
    all_facts = pl.Theorem("all_geometry_facts_check", [], conclusion=pl.TRUE,
                           proof=pl.proof(pl.conclude(because=shipped)))
    results = pl.verify_all([*textbook, all_facts], project=lean_project, use_cache=False,
                            timeout=3600)
    for t, r in zip([*textbook, all_facts], results, strict=True):
        assert r.verified, (t.name, [d.message for d in r.diagnostics if d.severity == "error"])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}
    src = results[-1].lean_source
    assert all(f"theorem {f.name} " in src for f in shipped)


def test_analysis_catalogue_and_lecture_solutions(lean_project):
    import sys

    from pyleanx import analysis as an
    from pyleanx.proofs import LibraryFact

    shipped = [f for f in an.LEMMAS.values() if isinstance(f, LibraryFact)]
    all_facts = pl.Theorem("all_analysis_facts_check", [], conclusion=pl.TRUE,
                           proof=pl.proof(pl.conclude(because=shipped)))
    # facts first, on their own: a broken shipped fact would reject the whole Lean file
    (facts,) = pl.verify_all([all_facts], project=lean_project, use_cache=False, timeout=3600)
    assert facts.verified, [d.message for d in facts.diagnostics if d.severity == "error"]
    assert all(f"theorem {f.name} " in facts.lean_source for f in shipped)
    sys.path.insert(0, str(EXAMPLES))
    try:
        lecture = runpy.run_path(str(EXAMPLES / "analysis_lecture.py"))
    finally:
        sys.path.remove(str(EXAMPLES))
    sols = lecture["all_solutions"]()
    results = pl.verify_all(sols, project=lean_project, use_cache=False, timeout=3600)
    for t, r in zip(sols, results, strict=True):
        assert r.verified, (t.name, [d.message for d in r.diagnostics if d.severity == "error"])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}


def test_harmonic_catalogue_and_lecture_solutions(lean_project):
    import sys

    from pyleanx import harmonic as ha
    from pyleanx.proofs import LibraryFact

    shipped = [f for f in ha.LEMMAS.values() if isinstance(f, LibraryFact)]
    all_facts = pl.Theorem("all_harmonic_facts_check", [], conclusion=pl.TRUE,
                           proof=pl.proof(pl.conclude(because=shipped)))
    (facts,) = pl.verify_all([all_facts], project=lean_project, use_cache=False, timeout=3600)
    assert facts.verified, [d.message for d in facts.diagnostics if d.severity == "error"]
    sys.path.insert(0, str(EXAMPLES))
    try:
        lecture = runpy.run_path(str(EXAMPLES / "harmonic_lecture.py"))
    finally:
        sys.path.remove(str(EXAMPLES))
    sols = lecture["all_solutions"]()
    results = pl.verify_all(sols, project=lean_project, use_cache=False, timeout=3600)
    for t, r in zip(sols, results, strict=True):
        assert r.verified, (t.name, [d.message for d in r.diagnostics if d.severity == "error"])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}


def test_hilbert_transform_written_proofs(lean_project):
    ns = runpy.run_path(str(EXAMPLES / "hilbert_transform.py"))
    thms = ns["THEOREMS"]
    results = pl.verify_all(thms, project=lean_project, use_cache=False, timeout=3600)
    for t, r in zip(thms, results, strict=True):
        assert r.verified, (t.name, [d.message for d in r.diagnostics if d.severity == "error"])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}


def test_calderon_zygmund_written_proofs(lean_project):
    ns = runpy.run_path(str(EXAMPLES / "calderon_zygmund.py"))
    thms = ns["THEOREMS"]
    results = pl.verify_all(thms, project=lean_project, use_cache=False, timeout=3600)
    for t, r in zip(thms, results, strict=True):
        assert r.verified, (t.name, [d.message for d in r.diagnostics if d.severity == "error"])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}


def test_hilbert_kernel_written_proofs(lean_project):
    ns = runpy.run_path(str(EXAMPLES / "hilbert_kernel.py"))
    thms = ns["THEOREMS"]
    results = pl.verify_all(thms, project=lean_project, use_cache=False, timeout=3600)
    for t, r in zip(thms, results, strict=True):
        assert r.verified, (t.name, [d.message for d in r.diagnostics if d.severity == "error"])
        assert set(r.axioms) <= {"propext", "Classical.choice", "Quot.sound"}
