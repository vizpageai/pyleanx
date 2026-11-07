"""Real Lean integration tests for the axiom audit.

These fixtures deliberately contain `sorry`, a user axiom and native_decide, to
prove that such proofs are policy_rejected. They are negative tests only.
"""

import dataclasses

import pytest

import pyleanx as pl
from pyleanx.backend.subprocess_backend import classify, run_lean
from pyleanx.render.lean import render_module

pytestmark = pytest.mark.lean


def _allow_raw(project, **kw):
    return project.with_(policy=dataclasses.replace(project.policy, allow_raw_tactics=True, **kw))


def test_sorry_is_policy_rejected(lean_project):
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("uses_sorry", [x], conclusion=x**2 < 0, proof=pl.raw_tactic("sorry"))
    r = thm.verify(_allow_raw(lean_project))
    assert r.status is pl.Status.POLICY_REJECTED and not r.verified
    assert r.axioms is not None and "sorryAx" in r.axioms
    assert r.raw_tactics_used


def test_transitive_sorry_is_policy_rejected(lean_project):
    """A proof that only cites a sorry'd lemma: no `sorry` token in its own text."""
    x = pl.symbol("x", pl.Real)
    lemma = pl.Theorem("sorry_lemma", [x], conclusion=x**2 < 0, proof=pl.raw_tactic("sorry"))
    user = pl.Theorem("innocent_looking", [x], conclusion=x**2 < 0,
                      proof=pl.exact(pl.ref(lemma)(x)))
    r_lemma, r_user = pl.verify_all([lemma, user], project=_allow_raw(lean_project))
    assert r_lemma.status is pl.Status.POLICY_REJECTED
    assert r_user.status is pl.Status.POLICY_REJECTED and not r_user.verified
    assert not r_user.raw_tactics_used and "sorryAx" in r_user.axioms


def test_raw_tactic_needs_policy(lean_project):
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("raw_default", [x], conclusion=x**2 >= 0,
                     proof=pl.raw_tactic("positivity", imports=["Mathlib.Tactic.Positivity"]))
    assert thm.verify(lean_project).status is pl.Status.POLICY_REJECTED
    r = thm.verify(_allow_raw(lean_project))
    assert r.verified and r.raw_tactics_used, r.summary()


def test_spoofed_audit_message_does_not_help(lean_project):
    """`trace` prints a fake clean audit line from inside the proof; it must be ignored."""
    x = pl.symbol("x", pl.Real)
    fake = "trace \"'spoof' does not depend on any axioms\"\nsorry"
    thm = pl.Theorem("spoof", [x], conclusion=x**2 < 0, proof=pl.raw_tactic(fake))
    r = thm.verify(_allow_raw(lean_project))
    assert r.status is pl.Status.POLICY_REJECTED and not r.verified
    assert any("does not depend on any axioms" in d.message for d in r.diagnostics)


def test_foreign_axiom_is_policy_rejected(lean_project):
    """A user `axiom bogus : False` (inserted as a test fixture) must be caught."""
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("uses_bogus", [x], conclusion=x**2 < 0,
                     proof=pl.raw_tactic("exact bogus.elim"))
    module = render_module([thm])
    lines = module.source.splitlines()
    blank = lines.index("")  # blank line between imports and set_option (same line count)
    assert blank < module.source_map.spans[0].end_line
    lines[blank] = "axiom bogus : False"
    work = lean_project.path / ".pyleanx" / "fixtures"
    work.mkdir(parents=True, exist_ok=True)
    f = work / "ForeignAxiom.lean"
    f.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    try:
        run = run_lean(lean_project, f, timeout=600)
    finally:
        f.unlink(missing_ok=True)
    status, diags, axioms = classify(run, module, lean_project)["uses_bogus"]
    assert status is pl.Status.POLICY_REJECTED
    assert axioms is not None and "bogus" in axioms
    assert any("non-standard axiom bogus" in d.message for d in diags)
    # ... and it would be accepted only if explicitly allowed:
    allowed = lean_project.with_(policy=dataclasses.replace(
        lean_project.policy, extra_allowed=frozenset({"bogus"})))
    assert classify(run, module, allowed)["uses_bogus"][0] is pl.Status.VERIFIED


def test_native_decide_is_policy_rejected_by_default(lean_project):
    thm = pl.Theorem("native_two", conclusion=pl.nat(2) + 2 == 4,
                     proof=pl.raw_tactic("native_decide"))
    r = thm.verify(_allow_raw(lean_project))
    assert r.status is pl.Status.POLICY_REJECTED, r.summary()
    # Lean >= 4.2x names these `<decl>._native.native_decide.ax_*`; older ones Lean.ofReduceBool
    assert any(a.startswith("Lean.ofReduce") or "_native" in a for a in r.axioms), r.axioms
    r2 = thm.verify(_allow_raw(lean_project, allow_native=True))
    assert r2.verified, r2.summary()


def test_cache_reproducibility_and_invalidation(lean_project):
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("cached_ring", [x, y], conclusion=(x - y) * (x + y) == x**2 - y**2,
                     proof=pl.ring())
    r1 = thm.verify(lean_project)
    r2 = thm.verify(lean_project)
    assert r1.verified and not r1.cache_hit
    assert r2.verified and r2.cache_hit and r2.fingerprint == r1.fingerprint
    # policy change -> new fingerprint, no cache hit
    stricter = lean_project.with_(policy=dataclasses.replace(
        lean_project.policy, allowed=frozenset({"propext", "Classical.choice", "Quot.sound"}),
        extra_allowed=frozenset({"something"})))
    r3 = thm.verify(stricter)
    assert r3.fingerprint != r1.fingerprint and not r3.cache_hit and r3.verified
    # proof change -> new fingerprint
    thm.prove(pl.nlinarith())
    r4 = thm.verify(lean_project)
    assert r4.fingerprint != r1.fingerprint and not r4.cache_hit
    # --no-cache path always runs Lean
    thm.prove(pl.ring())
    r5 = thm.verify(lean_project, use_cache=False)
    assert r5.verified and not r5.cache_hit and r5.fingerprint == r1.fingerprint


def test_mathlib_revision_change_invalidates(lean_project, tmp_path):
    """A different manifest (= Mathlib revision) yields a different fingerprint."""
    from pyleanx.backend.subprocess_backend import fingerprint

    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("fp", [x], conclusion=x == x, proof=pl.rfl())
    mod = render_module([thm])
    other = tmp_path / "proj"
    other.mkdir()
    for name in ("lean-toolchain", "lakefile.toml"):
        (other / name).write_bytes((lean_project.path / name).read_bytes())
    manifest = (lean_project.path / "lake-manifest.json").read_text(encoding="utf-8")
    (other / "lake-manifest.json").write_text(
        manifest.replace("d13f23b723b8a846827a245b89c10fc7d3f11612", "0" * 40), encoding="utf-8")
    other_proj = pl.LeanProject.at(other)
    assert fingerprint(thm.canonical(), mod, lean_project) != fingerprint(
        thm.canonical(), mod, other_proj)
