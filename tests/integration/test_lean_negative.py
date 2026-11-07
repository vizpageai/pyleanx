"""Real Lean integration tests: things that must NEVER be reported as verified."""

import pytest

import pyleanx as pl

pytestmark = pytest.mark.lean


def test_false_claim_rejected(lean_project):
    x = pl.symbol("x", pl.Real)
    r = pl.Theorem("false_claim", [x], conclusion=x**2 < 0, proof=pl.positivity()).verify(
        lean_project)
    assert not r.verified and r.status is pl.Status.REJECTED
    assert r.errors


def test_wrong_tactic_rejected_with_source_mapping(lean_project):
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("wrong_tactic", [x, y], conclusion=x * y >= 0)
    thm.prove(pl.ring())  # this line is the Python origin of the failing step
    r = thm.verify(lean_project)
    assert r.status is pl.Status.REJECTED and not r.verified
    err = r.errors[0]
    assert err.line is not None
    assert err.span_kind in ("tactic", "statement", "theorem")
    origins = [d.python_origin for d in r.errors if d.python_origin]
    assert origins and "test_lean_negative.py" in origins[0]


def test_wrong_tactic_on_nat_rejected(lean_project):
    n = pl.symbol("n", pl.Nat)
    r = pl.Theorem("nat_wrong", [n], conclusion=n - 1 + 1 == n, proof=pl.omega()).verify(
        lean_project)  # false for n = 0 (truncated subtraction)
    assert r.status is pl.Status.REJECTED


def test_missing_proof_never_verified(lean_project):
    x = pl.symbol("x", pl.Real)
    r = pl.Theorem("no_proof", [x], conclusion=x == x).verify(lean_project)
    assert r.status is pl.Status.REJECTED and not r.verified


def test_batch_mixed_results_are_independent(lean_project):
    x = pl.symbol("x", pl.Real)
    good = pl.Theorem("batch_good", [x], conclusion=x**2 >= 0, proof=pl.positivity())
    bad = pl.Theorem("batch_bad", [x], conclusion=x**2 < 0, proof=pl.positivity())
    good2 = pl.Theorem("batch_good2", [x], conclusion=(x + 1) ** 2 == x**2 + 2 * x + 1,
                       proof=pl.ring())
    r1, r2, r3 = pl.verify_all([good, bad, good2], project=lean_project)
    assert r1.verified and r3.verified
    assert r2.status is pl.Status.REJECTED


def test_examples_bad_proof_all_rejected(lean_project):
    from pyleanx.cli import load_theorems

    results = pl.verify_all(load_theorems("examples/bad_proof.py"), project=lean_project)
    assert results and not any(r.verified for r in results)


def test_timeout_is_never_verified(lean_project):
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("slow", [x], conclusion=x**2 >= 0, proof=pl.positivity())
    r = thm.verify(lean_project, timeout=0.05, use_cache=False)
    assert r.status is pl.Status.TIMEOUT and not r.verified


def test_bad_import_is_environment_error(lean_project):
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("bad_import", [x], conclusion=x == x, proof=pl.rfl(),
                     imports=["Mathlib.Does.Not.Exist"])
    r = thm.verify(lean_project)
    assert r.status is pl.Status.ENVIRONMENT_ERROR and not r.verified


def test_unknown_lemma_rejected(lean_project):
    x = pl.symbol("x", pl.Real)
    r = pl.Theorem("unknown_lemma", [x], conclusion=x == x,
                   proof=pl.exact(pl.ref("this_lemma_does_not_exist"))).verify(lean_project)
    assert r.status is pl.Status.REJECTED
