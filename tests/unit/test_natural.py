"""Natural proof moves: similarly, descriptions, the benchmark heuristics (no Lean)."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import geometry as geo

ROOT = Path(__file__).resolve().parents[2]
A, B, C, D = geo.points("A B C D")


def _pyth(step3: object) -> pl.Theorem:
    AB, AC, AD = geo.dist(A, B), geo.dist(A, C), geo.dist(A, D)
    return pl.Theorem(
        "p", [A, B, C], assumptions={"hABC": geo.triangle(A, B, C),
                                      "hC": geo.right_angle(A, C, B)},
        conclusion=AC ** 2 + geo.dist(B, C) ** 2 == AB ** 2,
        proof=pl.proof(
            pl.choose(D, such_that=pl.And(geo.strictly_between(D, A, B),
                                          geo.right_angle(A, D, C), geo.right_angle(B, D, C)),
                      because=["drop the altitude to the hypotenuse", "hABC", "hC"],
                      names="hD hAD hBD"),
            pl.claim(AC ** 2 == AD * AB, because=["hABC", "hC", "hD", "hAD"], name="h1"),
            step3,
            pl.conclude(because=["h1", "h2"])))


def test_similarly_exchanges_variables_and_renames_hypotheses():
    thm = _pyth(pl.similarly("h1", exchange=(A, B), name="h2"))
    src = thm.to_lean()
    assert "have h2 : dist B C ^ 2 = dist B D * dist B A" in src  # BC² = BD·BA
    h2 = next(s for s in thm.proof.flat() if getattr(s, "name", "") == "h2")
    # justified by the hypothesis about D and B (hBD) in place of hAD
    assert [f.name for f in h2.facts] == ["hABC", "hC", "hD", "hBD"]
    assert "similarly, with A and B exchanged" in str(thm.prose())


def test_similarly_needs_an_earlier_named_step():
    with pytest.raises(pl.TacticError, match="no earlier step named"):
        _pyth(pl.similarly("nope", exchange=(A, B), name="h2"))
    with pytest.raises(pl.TacticError, match="exchange"):
        pl.similarly("h1")


def test_a_description_equal_to_a_label_or_name_is_exact():
    assert pl.fact("the base angles of an isosceles triangle are equal").name == \
        "EuclideanGeometry.angle_eq_angle_of_dist_eq"
    assert pl.fact("straight angle").name == "Sbtw.angle₁₂₃_eq_pi"


def test_repl_messages_use_the_batch_severity_names():
    from types import SimpleNamespace

    from pyleanx.backend.repl_check import _run_chunk

    msg = SimpleNamespace(severity="info", data="'t' depends on axioms: [propext]",
                          start_pos=SimpleNamespace(line=3, column=0), end_pos=None)
    resp = SimpleNamespace(messages=[msg], env=7)

    class FakeRepl:
        class _LeanError(Exception):
            pass

        class _li:  # noqa: N801
            @staticmethod
            def Command(cmd: str, env: int) -> tuple:  # noqa: N802
                return (cmd, env)

        def _run(self, req: object, timeout: float) -> object:
            return resp

    env, msgs, failed = _run_chunk(FakeRepl(), "x", 0, first_line=40, n_opts=2, timeout=1)
    assert env == 7 and not failed
    assert msgs[0].severity == "information" and msgs[0].line == 40


def test_benchmark_classifies_bookkeeping():
    sys.path.insert(0, str(ROOT / "benchmarks"))
    try:
        import naturalness as nb
    finally:
        sys.path.remove(str(ROOT / "benchmarks"))
    ang, dist = geo.angle, geo.dist
    hyps = [geo.triangle(A, B, C)]
    assert nb.bookkeeping_kind(A != B, hyps) == "distinctness"
    assert nb.bookkeeping_kind(dist(A, B) > 0, hyps) == "positivity"
    assert nb.bookkeeping_kind(dist(B, A) == dist(A, B), hyps) == "notation"
    assert nb.bookkeeping_kind(ang(A, B, C) == ang(C, B, A), hyps) == "notation"
    assert nb.bookkeeping_kind(ang(A, B, C) == ang(A, C, B), hyps) == ""  # a real fact
    assert nb.bookkeeping_kind(geo.triangle(B, A, C), hyps) == "notation"


def test_every_label_selects_its_fact():
    from pyleanx.fact_search import _catalog, facts_for

    for e in _catalog():
        names = [getattr(g, "name", None) for g in facts_for(e.label)]
        assert getattr(e.obj, "name", None) in names, (e.qualified, e.label)


def test_a_family_label_cites_every_member_and_prints_once():
    c = pl.claim(A != B, because="corresponding parts of congruent triangles (CPCTC)")
    assert len(c.facts) == 6
    thm = pl.Theorem("fam", [A, B], conclusion=A != B, proof=pl.proof(c, pl.conclude()))
    text = str(thm.prose())
    assert text.count("corresponding parts of congruent triangles (CPCTC)") == 1


def test_citing_a_hypothesis_that_does_not_exist_is_refused_with_a_suggestion():
    x = pl.symbol("x", pl.Real)
    with pytest.raises(pl.TacticError, match=r"cites 'hz'.*Did you mean hx\?"):
        pl.Theorem("t", [x], assumptions={"hx": x > 0}, conclusion=x >= 0,
                   proof=pl.proof(pl.claim(x >= 0, because="hz"), pl.conclude()))
    # library names, and names introduced inside the proof, are accepted
    pl.Theorem("u", [x], assumptions={"hx": x > 0}, conclusion=x >= 0,
               proof=pl.proof(pl.claim(x >= 1 - 1, because=["hx", "le_of_lt"], name="h0"),
                              pl.conclude(because="h0")))
    thm = _pyth(pl.similarly("h1", exchange=(A, B), name="h2"))  # choose names hD hAD hBD
    assert thm.proof is not None


def test_hypothesis_like_names():
    from pyleanx.proofs import _hyp_like

    assert all(_hyp_like(n) for n in ["h", "hx", "h1", "hABC", "hε", "hx'", "hD"])
    assert not any(_hyp_like(n) for n in ["mul_pos", "Real.pi", "hasSum", "abs_nonneg",
                                         "hypothesis_long_name"])


def test_a_one_word_label_selects_its_fact():
    # "by SSS" as a textbook writes it; not a Lean name called SSS
    c = pl.claim(geo.congruent((A, B, C), (D, B, C)), because=["SSS", "h"])
    assert [getattr(f, "name", None) for f in c.facts] == [geo.sss.name, "h"]
    # other one-word reasons are still names
    assert [f.name for f in pl.claim(A != B, because="hAB").facts] == ["hAB"]
    assert [f.name for f in pl.claim(A != B, because="sss").facts] == ["sss"]


def test_similarly_replace_takes_pairs():
    x = pl.symbol("x", pl.Real)
    s = pl.similarly("h1", replace=(x, -x))
    assert len(s.mapping) == 1 and s.mapping[0][0] is x
    assert len(pl.similarly("h1", replace=[(x, -x), (x, x + 1)]).mapping) == 2
    with pytest.raises(pl.TacticError, match=r"replace=\[\(x, -x\)\]"):
        pl.similarly("h1", replace=x)
