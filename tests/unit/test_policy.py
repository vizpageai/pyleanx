"""Axiom-audit parsing, policy decisions and attribution logic.

These tests exercise the *decision procedure* on recorded Lean message shapes.
They never stand in for the real-Lean integration tests in tests/integration.
"""

import dataclasses
import json

import pytest

import pyleanx as pl
from pyleanx.backend.audit import AxiomPolicy, parse_axiom_report
from pyleanx.backend.cache import ResultCache
from pyleanx.backend.interface import Status, VerificationResult
from pyleanx.backend.subprocess_backend import LeanRun, classify, parse_json_messages
from pyleanx.project import LeanProject
from pyleanx.render.lean import render_module


def test_parse_axiom_reports():
    r = parse_axiom_report("'foo' depends on axioms: [propext, Classical.choice, Quot.sound]")
    assert r.theorem == "foo" and r.axioms == ("propext", "Classical.choice", "Quot.sound")
    r = parse_axiom_report("'bar' does not depend on any axioms")
    assert r.theorem == "bar" and r.axioms == ()
    r = parse_axiom_report("'baz' depends on axioms: [propext,\n sorryAx]\n")
    assert r.axioms == ("propext", "sorryAx")
    assert parse_axiom_report("unrelated text") is None


def test_default_policy():
    p = pl.DEFAULT_POLICY
    assert p.check(["propext", "Classical.choice", "Quot.sound"]) == []
    assert p.check([]) == []
    assert any("sorryAx" in m for m in p.check(["sorryAx"]))
    assert p.check(["bogus"])
    assert p.check(["Lean.ofReduceBool"])
    assert p.check(["foo._native.bar"])


def test_policy_options_and_fingerprint():
    native = AxiomPolicy(allow_native=True)
    assert native.check(["Lean.ofReduceBool"]) == []
    assert native.check(["sorryAx"])  # sorry is never allowed
    extra = AxiomPolicy(extra_allowed=frozenset({"my_axiom"}))
    assert extra.check(["my_axiom"]) == []
    fps = {pl.DEFAULT_POLICY.fingerprint(), native.fingerprint(), extra.fingerprint()}
    assert len(fps) == 3


def _module():
    x = pl.symbol("x", pl.Real)
    a = pl.Theorem("good", [x], conclusion=x**2 >= 0, proof=pl.positivity())
    b = pl.Theorem("bad", [x], conclusion=x**2 < 0, proof=pl.positivity())
    return render_module([a, b])


def _msg(sev, line, data, col=0):
    return json.dumps({"severity": sev, "pos": {"line": line, "column": col}, "endPos": None,
                       "data": data, "fileName": "f.lean"})


PROJ = LeanProject.at(".")


def test_classify_attributes_by_position():
    mod = _module()
    sm = mod.source_map
    bad_tactic = next(s for s in sm.spans if s.theorem == "bad" and s.kind == "tactic")
    out = "\n".join([
        _msg("information", sm.audit_line("good"),
             "'good' depends on axioms: [propext, Classical.choice, Quot.sound]"),
        _msg("error", bad_tactic.start_line, "failed to prove positivity", 2),
        _msg("information", sm.audit_line("bad"), "'bad' depends on axioms: [sorryAx]"),
    ])
    msgs, _ = parse_json_messages(out)
    run = LeanRun(returncode=1, messages=msgs, other_output="", timed_out=False, duration_ms=1)
    v = classify(run, mod, PROJ)
    assert v["good"][0] is Status.VERIFIED
    assert v["bad"][0] is Status.REJECTED
    err = next(d for d in v["bad"][1] if d.severity == "error")
    assert err.span_kind == "tactic" and err.python_origin and "test_policy" in err.python_origin


def test_spoofed_audit_text_is_ignored():
    mod = _module()
    sm = mod.source_map
    stmt = next(s for s in sm.spans if s.theorem == "good" and s.kind == "tactic")
    out = "\n".join([
        # fake "clean" report printed from inside the proof, not at the audit line
        _msg("information", stmt.start_line, "'good' does not depend on any axioms"),
        _msg("information", sm.audit_line("good"), "'good' depends on axioms: [sorryAx]"),
        _msg("information", sm.audit_line("bad"), "'good' does not depend on any axioms"),
    ])
    msgs, _ = parse_json_messages(out)
    run = LeanRun(returncode=0, messages=msgs, other_output="", timed_out=False, duration_ms=1)
    v = classify(run, mod, PROJ)
    assert v["good"][0] is Status.POLICY_REJECTED  # real report has sorryAx
    assert v["bad"][0] is Status.POLICY_REJECTED  # report names the wrong theorem


def test_missing_audit_is_never_verified():
    mod = _module()
    run = LeanRun(returncode=0, messages=[], other_output="", timed_out=False, duration_ms=1)
    v = classify(run, mod, PROJ)
    assert all(st is Status.POLICY_REJECTED for st, _, _ in v.values())


def test_duplicate_audit_is_never_verified():
    mod = _module()
    line = mod.source_map.audit_line("good")
    rep = "'good' does not depend on any axioms"
    msgs, _ = parse_json_messages(_msg("information", line, rep) + "\n"
                                  + _msg("information", line, rep))
    run = LeanRun(returncode=0, messages=msgs, other_output="", timed_out=False, duration_ms=1)
    assert classify(run, mod, PROJ)["good"][0] is Status.POLICY_REJECTED


def test_timeout_and_environment_errors():
    mod = _module()
    run = LeanRun(returncode=None, messages=[], other_output="", timed_out=True, duration_ms=5)
    assert all(st is Status.TIMEOUT for st, _, _ in classify(run, mod, PROJ).values())
    msgs, _ = parse_json_messages(_msg("error", 1, "unknown module prefix 'Mathlib'"))
    run = LeanRun(returncode=1, messages=msgs, other_output="", timed_out=False, duration_ms=5)
    assert all(st is Status.ENVIRONMENT_ERROR for st, _, _ in classify(run, mod, PROJ).values())
    # nonzero exit without any attributable error: distrust everything
    sm = mod.source_map
    ok = "\n".join(_msg("information", sm.audit_line(n), f"'{n}' does not depend on any axioms")
                   for n in ("good", "bad"))
    msgs, _ = parse_json_messages(ok)
    run = LeanRun(returncode=3, messages=msgs, other_output="crash", timed_out=False,
                  duration_ms=5)
    assert all(st is Status.ENVIRONMENT_ERROR for st, _, _ in classify(run, mod, PROJ).values())


def test_non_json_output_collected():
    msgs, other = parse_json_messages('garbage\n{"x": 1}\n')
    assert msgs == [] and "garbage" in other


def test_raw_tactic_rejected_by_default_policy_without_lean(tmp_path):
    x = pl.symbol("x", pl.Real)
    thm = pl.Theorem("t", [x], conclusion=x**2 >= 0, proof=pl.raw_tactic("positivity"))
    proj = LeanProject.at(tmp_path / "nonexistent")
    (r,) = pl.verify_all([thm], project=proj, cache=ResultCache(tmp_path))
    assert r.status is Status.POLICY_REJECTED and not r.verified and r.raw_tactics_used
    allowed = proj.with_(policy=dataclasses.replace(proj.policy, allow_raw_tactics=True))
    bad = pl.Theorem("t2", [x], conclusion=x**2 >= 0,
                     proof=pl.raw_tactic("sorry\naxiom bogus : False"))
    (r2,) = pl.verify_all([bad], project=allowed, cache=ResultCache(tmp_path))
    assert r2.status is Status.POLICY_REJECTED


def test_missing_proof_and_missing_project(tmp_path):
    x = pl.symbol("x", pl.Real)
    no_proof = pl.Theorem("np", [x], conclusion=x == x)
    with_proof = pl.Theorem("wp", [x], conclusion=x == x, proof=pl.rfl())
    proj = LeanProject.at(tmp_path / "nonexistent")
    r1, r2 = pl.verify_all([no_proof, with_proof], project=proj, cache=ResultCache(tmp_path))
    assert r1.status is Status.REJECTED
    assert r2.status is Status.ENVIRONMENT_ERROR and not r2.verified


def test_cache_only_stores_verified(tmp_path):
    cache = ResultCache(tmp_path)
    bad = VerificationResult(theorem="t", status=Status.REJECTED, fingerprint="abc")
    cache.put(bad)
    assert cache.get("abc") is None
    good = VerificationResult(theorem="t", status=Status.VERIFIED, fingerprint="def",
                              axioms=("propext",))
    cache.put(good)
    hit = cache.get("def")
    assert hit is not None and hit.cache_hit and hit.verified and hit.axioms == ("propext",)
    assert cache.stats()["entries"] == 1
    assert cache.clear() == 1 and cache.get("def") is None


def test_result_json_roundtrip():
    r = VerificationResult(theorem="t", status=Status.VERIFIED, axioms=(), fingerprint="f",
                           diagnostics=[pl.Diagnostic("information", "hi", 1, 0)])
    d = json.loads(r.to_json())
    assert d["verified"] is True and d["status"] == "verified" and d["schema_version"] == 1
    back = VerificationResult.from_dict(d)
    assert back.verified and back.diagnostics[0].message == "hi"
    assert "verified" in r.summary()


@pytest.mark.parametrize("opt", [("debug.skipKernelTC", "true"), ("x; rm", "1")])
def test_unsafe_lean_options_rejected(tmp_path, opt):
    from pyleanx.backend.subprocess_backend import run_lean
    from pyleanx.errors import ProjectError

    proj = LeanProject.at(tmp_path, lean_options=(opt,))
    with pytest.raises(ProjectError):
        run_lean(proj, tmp_path / "x.lean", 1)


def test_name_clash_gets_a_hint():
    mod = _module()
    sm = mod.source_map
    head = next(s for s in sm.spans if s.theorem == "good")
    out = "\n".join([
        _msg("error", head.start_line, "`good` has already been declared"),
        _msg("information", sm.audit_line("bad"), "'bad' depends on axioms: [propext]"),
    ])
    msgs, _ = parse_json_messages(out)
    run = LeanRun(returncode=1, messages=msgs, other_output="", timed_out=False, duration_ms=1)
    v = classify(run, mod, PROJ)
    assert v["good"][0] is Status.REJECTED
    assert "distinctive name" in v["good"][1][0].message
