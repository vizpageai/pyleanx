"""The fast REPL checker against a fake REPL: line mapping, audit, caching, fallbacks."""

from __future__ import annotations

import re
from types import SimpleNamespace

import pytest

import pyleanx as pl
from pyleanx.backend import leaninteract, repl_check
from pyleanx.backend.interface import Status, VerificationResult

x = pl.symbol("x", pl.Real)


class FakeRepl:
    """Answers like the Lean REPL: an axiom report for each ``#print axioms`` line, and an
    error on any line containing ``FAIL``."""

    class _LeanError(Exception):
        pass

    class _li:  # noqa: N801
        @staticmethod
        def Command(cmd: str, env: int | None = None) -> SimpleNamespace:  # noqa: N802
            return SimpleNamespace(cmd=cmd, env=env)

    def __init__(self, axioms: str = "propext") -> None:
        self._envs: dict = {}
        self.commands: list[str] = []
        self.axioms = axioms

    def import_env(self, imports: tuple[str, ...], timeout: float) -> int:
        self._envs.setdefault(tuple(sorted(imports)), 1)
        return 1

    def _run(self, request: SimpleNamespace, timeout: float) -> SimpleNamespace:
        self.commands.append(request.cmd)
        msgs = []
        for i, line in enumerate(request.cmd.splitlines(), start=1):
            m = re.match(r"#print axioms (\S+)", line)
            if m:
                msgs.append(SimpleNamespace(
                    severity="info", data=f"'{m.group(1)}' depends on axioms: [{self.axioms}]",
                    start_pos=SimpleNamespace(line=i, column=0), end_pos=None))
            if "FAIL" in line:
                msgs.append(SimpleNamespace(
                    severity="error", data="unsolved goals\n⊢ False",
                    start_pos=SimpleNamespace(line=i, column=2), end_pos=None))
        return SimpleNamespace(messages=msgs, env=len(self.commands) + 1)


@pytest.fixture
def fake(monkeypatch: pytest.MonkeyPatch) -> FakeRepl:
    repl = FakeRepl()
    monkeypatch.setattr(leaninteract, "get_repl", lambda proj, launch="auto": repl)
    monkeypatch.setattr(leaninteract, "shutdown_repls", lambda: 0)
    repl_check.clear_preamble_cache()
    return repl


def _thm(name: str = "fast_ok") -> pl.Theorem:
    return pl.Theorem(name, [x], assumptions={"hx": x > 0}, conclusion=x ** 2 > 0,
                      proof=pl.proof(pl.conclude(because="hx")))


def test_a_clean_check_is_verified_with_the_audited_axioms(fake: FakeRepl):
    (res,) = pl.check_all([_thm()])
    assert res.verified and res.backend == "repl" and res.axioms == ("propext",)
    assert res.fingerprint == "" and not res.cache_hit  # never archived


def test_an_error_line_rejects_the_theorem_and_names_the_step(fake: FakeRepl,
                                                              monkeypatch: pytest.MonkeyPatch):
    thm = pl.Theorem("fast_bad", [x], conclusion=x ** 2 >= 0,
                     proof=pl.proof(pl.claim(x ** 2 >= 0, note="FAIL", name="h1"),
                                    pl.conclude(because="h1")))
    # put the FAIL marker into the Lean text of step 1
    orig = repl_check.render_module

    def render(*a, **k):
        m = orig(*a, **k)
        src = m.source.replace("have h1", "have h1 -- FAIL", 1)
        return type(m)(src, m.source_map, m.imports, m.theorem_names)

    monkeypatch.setattr(repl_check, "render_module", render)
    (res,) = pl.check_all([thm])
    assert res.status is Status.REJECTED
    assert any((d.span_label or "").startswith("step 1") for d in res.errors)


def test_a_non_standard_axiom_is_refused_by_the_policy(fake: FakeRepl):
    fake.axioms = "propext, sorryAx"
    (res,) = pl.check_all([_thm("fast_sorry")])
    assert res.status is Status.POLICY_REJECTED


def test_the_preamble_is_elaborated_once(fake: FakeRepl):
    from pyleanx import geometry as geo

    A, B, C = geo.points("A B C")
    thm = pl.Theorem("fast_geo", [A, B, C], assumptions={"h": geo.triangle(A, B, C)},
                     conclusion=geo.dist(A, B) > 0,
                     proof=pl.proof(pl.conclude(because=[geo.triangle_sides_pos, "h"])))
    pl.check_all([thm])
    pl.check_all([thm])
    preambles = [c for c in fake.commands if "theorem PyLeanX.Geometry.triangle_sides_pos" in c]
    mains = [c for c in fake.commands if "theorem fast_geo" in c]
    assert len(preambles) == 1 and len(mains) == 2


def test_a_failing_repl_is_restarted_then_the_batch_backend_checks(
        monkeypatch: pytest.MonkeyPatch):
    calls = {"repl": 0, "batch": 0}

    def broken(proj, launch="auto"):
        calls["repl"] += 1
        raise leaninteract.ReplError("refused memory")

    def batch(theorems, **kw):
        calls["batch"] += 1
        return [VerificationResult(theorem=t.name, status=Status.VERIFIED, axioms=())
                for t in theorems]

    monkeypatch.setattr(leaninteract, "get_repl", broken)
    monkeypatch.setattr(leaninteract, "shutdown_repls", lambda: 0)
    monkeypatch.setattr(repl_check, "verify_all", batch)
    (res,) = pl.check_all([_thm("fast_fallback")])
    assert calls == {"repl": 2, "batch": 1}  # one restart, then the batch backend
    assert any("fast REPL check was unavailable" in d.message for d in res.diagnostics)


def test_numeric_check_samples_points_of_the_plane():
    from pyleanx import geometry as geo

    A, B, C = geo.points("A B C")
    thm = pl.Theorem("iso", [A, B, C], assumptions={"h": geo.triangle(A, B, C)},
                     conclusion=geo.dist(A, B) == geo.dist(A, C),
                     proof=pl.proof(pl.conclude()))
    rep = thm.sanity_check()
    assert "The statement looks false" in str(rep) and "A = (" in str(rep)


def test_numeric_check_says_when_nothing_was_checked():
    from pyleanx import geometry as geo

    A, B, C = geo.points("A B C")
    right = pl.Theorem("r", [A, B, C], assumptions={"h": geo.right_angle(A, C, B)},
                       conclusion=geo.dist(A, B) > 0, proof=pl.proof(pl.conclude()))
    assert "no random sample satisfies the hypotheses" in str(right.sanity_check())
    f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))
    fun = pl.Theorem("fn", [f], conclusion=f(1) == f(1), proof=pl.proof(pl.conclude()))
    assert "cannot be sampled" in str(fun.sanity_check())


def test_explain_failure_handles_facts_cited_theorems_and_pyleanx_messages():
    from pyleanx.backend.interface import Diagnostic

    thm = _thm("explain_more")
    res = VerificationResult(theorem=thm.name, status=Status.REJECTED, diagnostics=[
        Diagnostic("error", "type mismatch", span_kind="library_fact",
                   span_label="library fact PyLeanX.X"),
        Diagnostic("error", "x", span_kind="cited_theorem", span_label="cited theorem lemma1"),
        Diagnostic("error", "expected exactly one axiom report", source="pyleanx"),
        Diagnostic("error", "Unknown identifier `foo`", span_kind="tactic",
                   span_label="step 1: exact foo"),
    ])
    why = pl.explain_failure(thm, res, sanity=False)
    assert any("PyLeanX bug" in w for w in why)
    assert any("cited theorem lemma1" in w for w in why)
    assert any("expected exactly one axiom report" in w for w in why)
    assert any("a cited name is not known" in w for w in why)
    assert pl.explain_failure(thm, VerificationResult(theorem="t", status=Status.VERIFIED)) == []
