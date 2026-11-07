"""Real Lean integration tests: positive cases. Skipped only if Lean/Mathlib is absent."""

import json
import os
import uuid

import pytest

import pyleanx as pl
from pyleanx.backend.subprocess_backend import run_lean

pytestmark = pytest.mark.lean


def _direct(project, source):
    """M0 baseline: run hand-written Lean directly through the pinned project."""
    work = project.path / ".pyleanx" / "direct"
    work.mkdir(parents=True, exist_ok=True)
    f = work / f"Direct_{uuid.uuid4().hex}.lean"
    f.write_text(source, encoding="utf-8", newline="\n")
    try:
        return run_lean(project, f, timeout=600)
    finally:
        f.unlink(missing_ok=True)


def test_m0_direct_lean_ring_and_axioms(lean_project):
    run = _direct(lean_project, (
        "import Mathlib.Tactic.Ring\nimport Mathlib.Basic.Real.Basic\n\n"
        "theorem sq_id (x y : Real) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by\n"
        "  ring\n\n#print axioms sq_id\n"))
    assert run.returncode == 0, run.other_output
    assert not [m for m in run.messages if m.severity == "error"]
    reports = [m.text for m in run.messages if "depends on axioms" in m.text]
    assert reports and "sq_id" in reports[0]


def test_m0_direct_lean_wrong_statement_fails(lean_project):
    run = _direct(lean_project, (
        "import Mathlib.Tactic.Ring\nimport Mathlib.Basic.Real.Basic\n\n"
        "theorem bad (x y : Real) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by\n  ring\n"))
    assert run.returncode != 0 or any(m.severity == "error" for m in run.messages)


def test_square_identity(lean_project):
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("square_identity", variables=[x, y],
                     conclusion=(x + y) ** 2 == x**2 + 2 * x * y + y**2)
    thm.prove(pl.ring())
    r = thm.verify(lean_project)
    assert r.verified, r.summary()
    assert r.status is pl.Status.VERIFIED
    assert set(r.axioms) <= set(pl.STANDARD_AXIOMS)
    assert r.toolchain == "leanprover/lean4:v4.34.1"
    assert r.mathlib_revision == "d13f23b723b8a846827a245b89c10fc7d3f11612"
    assert len(r.fingerprint) == 64 and r.lean_source == thm.to_lean()
    assert json.loads(r.to_json())["verified"] is True


def test_square_nonnegative_positivity(lean_project):
    x = pl.symbol("x", pl.Real)
    r = pl.Theorem("sq_nonneg_pos", [x], conclusion=x**2 >= 0,
                   proof=pl.positivity()).verify(lean_project)
    assert r.verified, r.summary()


def test_nat_add_zero_simp(lean_project):
    n = pl.symbol("n", pl.Nat)
    r = pl.Theorem("nat_add_zero", [n], conclusion=n + 0 == n, proof=pl.simp()).verify(
        lean_project)
    assert r.verified, r.summary()


def test_identity_implication(lean_project):
    P = pl.prop_symbol("P")
    lemma = pl.Theorem("identity_imp", variables=[P], conclusion=pl.Implies(P, P))
    lemma.prove(pl.steps(pl.intro("h"), pl.exact("h")))
    r = lemma.verify(lean_project)
    assert r.verified, r.summary()
    assert r.axioms == ()  # pure logic needs no axioms


def test_examples_scripts_batch(lean_project):
    """All positive example theorems, in one batch."""
    from pyleanx.cli import load_theorems

    thms = []
    for script in ("square_identity", "square_nonnegative", "nat_add_zero", "implication"):
        thms.extend(load_theorems(f"examples/{script}.py"))
    results = pl.verify_all(thms, project=lean_project)
    bad = [r.summary() for r in results if not r.verified]
    assert not bad, "\n".join(bad)


def test_richer_constructs(lean_project):
    """Hypotheses, quantifiers, casts, functions, branches, use, rw, lemma reuse."""
    x, y = pl.symbols("x y", pl.Real)
    a, b = pl.symbols("a b", pl.Real)
    n, m = pl.symbols("n m", pl.Nat)
    k = pl.symbol("k", pl.Int)
    P, Q = pl.prop_symbol("P"), pl.prop_symbol("Q")
    helper = pl.Theorem("helper_sq", [x], conclusion=0 <= x * x,
                        proof=pl.exact(pl.mathlib.mul_self_nonneg(x)))
    thms = [
        helper,
        pl.Theorem("uses_helper", [y], conclusion=y * y >= 0,
                   proof=pl.exact(pl.ref(helper)(y))),
        pl.Theorem("hyp_linarith", [a, b], assumptions={"ha": a > 0, "hb": b > 0},
                   conclusion=a + b > 0, proof=pl.linarith()),
        pl.Theorem("and_intro", [P, Q], assumptions=[("hp", P), ("hq", Q)],
                   conclusion=P & Q,
                   proof=pl.constructor() >> pl.branches(pl.exact("hp"), pl.exact("hq"))),
        pl.Theorem("exists_bigger", conclusion=pl.Forall([x], pl.Exists([y], y > x)),
                   proof=pl.intro("x") >> pl.use(x + 1) >> pl.linarith()),
        pl.Theorem("ex_cast_nonneg", [n], conclusion=pl.cast(n, pl.Real) >= 0,
                   proof=pl.positivity()),
        pl.Theorem("nat_omega", [n, m], assumptions=[n < m], conclusion=n + 1 <= m,
                   proof=pl.omega()),
        pl.Theorem("int_sq", [k], conclusion=k**2 >= 0, proof=pl.positivity()),
        pl.Theorem("ex_sqrt_nonneg", [x], conclusion=pl.sqrt(x) >= 0, proof=pl.positivity()),
        pl.Theorem("ex_exp_pos", [x], conclusion=pl.exp(x) > 0, proof=pl.positivity()),
        pl.Theorem("ex_abs_nonneg", [x], conclusion=abs(x - 1) >= 0, proof=pl.positivity()),
        pl.Theorem("ex_max_ge", [x, y], conclusion=pl.max(x, y) >= x,
                   proof=pl.exact(pl.ref("le_max_left")(x, y))),
        pl.Theorem("rw_example", [a, b], assumptions={"h": a == b},
                   conclusion=a + 1 == b + 1, proof=pl.rw("h")),
        pl.Theorem("half_plus_half", conclusion=pl.real(1) / 2 + pl.rat(1, 2) == 1,
                   proof=pl.norm_num()),
        pl.Theorem("nlin", [x], conclusion=(x - 1) ** 2 >= 0,
                   proof=pl.nlinarith(pl.mathlib.sq_nonneg(x - 1))),
        pl.Theorem("nat_decide", conclusion=pl.nat(2) + 2 == 4, proof=pl.decide()),
    ]
    results = pl.verify_all(thms, project=lean_project)
    bad = [r.summary() for r in results if not r.verified]
    assert not bad, "\n".join(bad)


@pytest.mark.skipif(os.environ.get("PYLEANX_SLOW_TESTS") != "1",
                    reason="`import Mathlib` loads ~8900 modules; set PYLEANX_SLOW_TESTS=1")
def test_mathlib_import_mode(lean_project):
    x = pl.symbol("x", pl.Real)
    proj = lean_project.with_(import_mode="mathlib")
    thm = pl.Theorem("full_import", [x], conclusion=x**2 + 1 > 0, proof=pl.positivity())
    r = thm.verify(proj)
    assert r.verified, r.summary()
    assert r.lean_source.startswith("import Mathlib\n")


def test_unicode_types_greek_names_and_decorator(lean_project):
    """Lean accepts ℝ ℕ ℤ ℚ, Greek/subscript names, and @pl.theorem-built statements."""
    proj = lean_project.with_(unicode_types=True)

    @pl.theorem(proof=pl.positivity(), assumptions=lambda α, x: {"hα": α > 0})
    def uni_greek(α: pl.Real, x: pl.Real):
        return α * x**2 + α > 0

    x1 = pl.symbol("x₁", pl.Real)
    n = pl.symbol("n", pl.Nat)
    k = pl.symbol("k", pl.Int)
    q = pl.symbol("q", pl.Rat)
    thms = [
        uni_greek,
        pl.Theorem("uni_sub", [x1], conclusion=(x1 + 1) ** 2 == x1**2 + 2 * x1 + 1,
                   proof=pl.ring()),
        pl.Theorem("uni_nat_int_rat", [n, k, q],
                   conclusion=pl.And(n + 0 == n, k + 0 == k, q + 0 == q), proof=pl.simp()),
        pl.Theorem("uni_cast", [n], conclusion=pl.cast(n, pl.Real) >= 0, proof=pl.positivity()),
    ]
    results = pl.verify_all(thms, project=proj)
    bad = [r.summary() for r in results if not r.verified]
    assert not bad, "\n".join(bad)
    src = results[0].lean_source
    assert "(α x : ℝ)" in src and "(x₁ : ℝ)" in src and "(n : ℕ) (k : ℤ) (q : ℚ)" in src
