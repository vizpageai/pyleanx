"""The numeric evaluator behind ``sanity_check`` (no Lean)."""

from __future__ import annotations

import math

import pytest

import pyleanx as pl
from pyleanx import analysis as an
from pyleanx import geometry as geo
from pyleanx.numeric import Unsupported, evaluate

x, y = pl.symbols("x y", pl.Real)
A, B, C, D = geo.points("A B C D")


def ev(e, **vals):
    env = {}
    for name, v in vals.items():
        var = {"x": x, "y": y, "A": A, "B": B, "C": C, "D": D}[name]
        env[var.uid] = v
    return evaluate(e, env)


def test_arithmetic_follows_lean_conventions():
    assert ev(x / 0, x=3.0) == 0.0  # Lean: x / 0 = 0
    assert ev(pl.sqrt(x), x=-4.0) == 0.0  # Mathlib: √ of a negative number is 0
    assert ev(pl.abs(x - y), x=1.0, y=3.0) == 2.0
    assert math.isclose(ev(an.sin(x) ** 2 + an.cos(x) ** 2, x=0.7), 1.0)
    assert math.isclose(ev(pl.exp(pl.log(x)), x=2.5), 2.5)
    assert ev(pl.min(x, y), x=1.0, y=2.0) == 1.0 and ev(pl.max(x, y), x=1.0, y=2.0) == 2.0


def test_comparisons_and_connectives():
    assert ev(x + y == y + x, x=0.1, y=0.2)  # tolerance for rounding
    assert ev(pl.And(x > 0, y < 0), x=1.0, y=-1.0)
    assert ev(pl.Or(x > 0, y > 0), x=-1.0, y=1.0)
    assert ev(pl.Implies(x > 0, y > 0), x=-1.0, y=-1.0)
    assert not ev(pl.Not(x == x), x=1.0)
    assert ev(x != y, x=1.0, y=2.0)


def test_plane_geometry():
    o, e1, e2, mid = (0.0, 0.0), (2.0, 0.0), (0.0, 2.0), (1.0, 0.0)
    assert ev(geo.dist(A, B), A=o, B=e1) == 2.0
    assert math.isclose(ev(geo.angle(B, A, C), A=o, B=e1, C=e2), math.pi / 2)
    assert ev(geo.angle(A, A, B), A=o, B=e1) == pytest.approx(math.pi / 2)  # zero vector
    assert ev(geo.strictly_between(D, A, B), A=o, B=e1, D=mid)
    assert not ev(geo.strictly_between(A, A, B), A=o, B=e1)
    assert ev(geo.on_segment(A, A, B), A=o, B=e1)
    assert ev(geo.triangle(A, B, C), A=o, B=e1, C=e2)
    assert not ev(geo.triangle(A, B, D), A=o, B=e1, D=mid)
    assert ev(A == A, A=o) and ev(A != B, A=o, B=e1)


def test_unknown_constructs_are_reported_not_guessed():
    f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))
    with pytest.raises(Unsupported):
        ev(pl.Forall(y, y > x), x=1.0)
    with pytest.raises(Unsupported):
        evaluate(f(x) > 0, {x.uid: 1.0, f.uid: None})
    with pytest.raises(Unsupported):
        ev(x > 0)  # no value for x


def test_chains_are_checked_link_by_link():
    thm = pl.Theorem("c", [x], assumptions={"hx": x > 1},
                     conclusion=x ** 2 > 1,
                     proof=pl.proof(pl.chain(x ** 2, ("=", x + x), (">", 1))))
    rep = thm.sanity_check()
    assert not rep.ok and "Step 1 looks false" in str(rep)


def test_points_the_hypotheses_determine_are_constructed():
    M, N = geo.points("M N")
    thm = pl.Theorem("mid", [A, B, C, M, N],
                     assumptions={"hM": geo.is_midpoint(M, A, B),
                                  "hN": geo.is_midpoint(N, A, C)},
                     conclusion=geo.dist(M, N) == geo.dist(B, C) / 3,  # false: it is 1/2
                     proof=pl.proof(pl.conclude()))
    rep = thm.sanity_check()
    assert rep.samples > 0 and "The statement looks false" in str(rep)
    between = pl.Theorem("bt", [A, B, D], assumptions={"h": geo.strictly_between(D, A, B)},
                         conclusion=geo.dist(A, D) + geo.dist(D, B) == geo.dist(A, B),
                         proof=pl.proof(pl.conclude()))
    rep = between.sanity_check()
    assert rep.ok and rep.samples == 300


def test_cli_sanity_and_facts(tmp_path, capsys):
    from pyleanx.cli import main

    script = tmp_path / "s.py"
    script.write_text(
        "import pyleanx as pl\n"
        "x = pl.symbol('x', pl.Real)\n"
        "THEOREMS = [pl.Theorem('f', [x], conclusion=x ** 2 > x, proof=pl.proof(pl.conclude()))]\n",
        encoding="utf-8")
    assert main(["sanity", str(script)]) == 1
    assert "looks false" in capsys.readouterr().out
    assert main(["facts", "AA", "similarity", "--limit", "2"]) == 0
    assert "geo.similar_AA" in capsys.readouterr().out
    assert main(["facts", "--json", "segment", "addition"]) == 0
    assert '"name": "geo.segment_addition"' in capsys.readouterr().out
