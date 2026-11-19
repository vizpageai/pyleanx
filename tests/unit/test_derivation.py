"""The derivation graph of a written proof (no Lean)."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import geometry as geo

A, B, C, D = geo.points("A B C D")
x, y = pl.symbols("x y", pl.Real)


def _pyth() -> pl.Theorem:
    AB, AC, AD, BC = (geo.dist(A, B), geo.dist(A, C), geo.dist(A, D), geo.dist(B, C))  # noqa: N806
    return pl.Theorem(
        "p", [A, B, C], assumptions={"hABC": geo.triangle(A, B, C),
                                      "hC": geo.right_angle(A, C, B)},
        conclusion=AC ** 2 + BC ** 2 == AB ** 2,
        proof=pl.proof(
            pl.choose(D, such_that=pl.And(geo.strictly_between(D, A, B),
                                          geo.right_angle(A, D, C), geo.right_angle(B, D, C)),
                      because=["drop the altitude to the hypotenuse", "hABC", "hC"],
                      names="hD hAD hBD"),
            pl.claim(AC ** 2 == AD * AB, because=["hABC", "hC", "hD", "hAD"], name="h1"),
            pl.similarly("h1", exchange=(A, B), name="h2"),
            pl.conclude(because=["h1", "h2"])))


def test_nodes_record_statements_citations_and_scope():
    d = _pyth().derivation()
    assert [n.kind for n in d] == ["hypothesis", "hypothesis", "choose", "claim", "claim",
                                   "conclusion"]
    assert d["hAD"].kind == "choose" and d["hAD"].introduces == ("hD", "hAD", "hBD")
    assert d["h1"].cites == ("hABC", "hC", "hD", "hAD")
    assert d["h2"].cites == ("hABC", "hC", "hD", "hBD")     # "similarly": hAD became hBD
    assert d["hD"].facts == ("PyLeanX.Geometry.altitude_to_hypotenuse",)
    assert d["h1"].scope == ("hABC", "hC", "hD", "hAD", "hBD")
    assert d.introduced == {"hABC", "hC", "hD", "hAD", "hBD", "h1", "h2"}


def test_dependencies_follow_citations_transitively_in_proof_order():
    d = _pyth().derivation()
    assert d.depends_on("h2") == ("hABC", "hC", "hD", "hBD")
    assert d.cited_by("h1") == ("",)        # cited only by the conclusion
    with pytest.raises(KeyError, match="no hypothesis or step called 'nope'"):
        d["nope"]


def test_nested_proofs_cases_and_fixed_hypotheses():
    thm = pl.Theorem(
        "t", [x], assumptions={"hx": x > 0}, conclusion=pl.Forall(y, pl.Implies(y > x, y > 0)),
        proof=pl.proof(
            pl.fix(y, assume={"hy": y > x}),
            pl.claim(y > 0, because=["hx", "hy"], name="hpos",
                     proof=pl.proof(pl.claim(y >= x, because="hy", name="hle"),
                                    pl.conclude(because=["hle", "hx"]))),
            pl.conclude(because="hpos")))
    d = thm.derivation()
    assert d["hy"].kind == "fix"
    assert d["hle"].scope[:2] == ("hx", "hy")       # the nested step sees the fixed hypothesis
    assert {"hy", "hpos", "hle"} <= d.introduced
    assert pl.derivation(thm).theorem == "t"
