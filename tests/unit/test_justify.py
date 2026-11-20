"""The justification engine: rules in ordered slots, registered by packs (no Lean)."""

from __future__ import annotations

import pytest

import pyleanx.geometry  # noqa: F401 - registers the geometry pack
from pyleanx import justify as j


@pytest.fixture
def toy_pack():
    """A pack registered only for one test."""
    saved = list(j._RULES), dict(j._PACKS)
    j.register_pack("toy", sorts={"Toy"}, symbols=("Toy.",))
    yield "toy"
    j._RULES[:], j._PACKS = saved[0], saved[1]


def test_core_rules_come_in_order_and_without_repeats():
    alts = j.alternatives(["h"], ["h"])
    assert alts[:4] == ["assumption", "contradiction", "(with_reducible exact h)",
                        "(with_reducible exact (h).symm)"]
    assert len(alts) == len(set(alts))
    assert alts[-2:] == ["(aesop; done)", "grind"]
    assert "grind" not in j.alternatives(["h"], ["h"], avoid=["foo"])


def test_a_pack_inserts_rules_at_their_priority_and_only_when_active(toy_pack):
    j.add_rule("step", 15, "toy_tactic", pack=toy_pack, name="t")
    j.add_rule("close", 15, "toy_closer", pack=toy_pack, name="c")
    with j.active_packs(frozenset({toy_pack})):
        alts = j.alternatives(["h"], ["h"])
        assert alts[2] == "toy_tactic"                         # between 10 and 20
        assert any("toy_closer" in a for a in alts if a.startswith("(apply h;"))
    with j.active_packs(frozenset()):
        assert not any("toy" in a for a in j.alternatives(["h"], ["h"]))
    assert "toy_tactic" in j.alternatives(["h"], ["h"])         # outside a theorem: all packs


def test_registering_a_rule_again_replaces_it(toy_pack):
    j.add_rule("step", 15, "first_version", pack=toy_pack, name="t")
    j.add_rule("step", 15, "second_version", pack=toy_pack, name="t")
    alts = j.alternatives([], [])
    assert "second_version" in alts and "first_version" not in alts


def test_packs_are_chosen_by_vocabulary(toy_pack):
    assert j.packs_using({"Toy"}, ()) == {toy_pack}
    assert j.packs_using((), {"Toy.frob"}) == {toy_pack}
    assert "geometry" in j.packs_using({"Point"}, ())
    assert j.packs_using({"Real"}, {"Real.sqrt"}) == frozenset()


def test_rules_need_a_registered_pack_and_a_known_slot():
    with pytest.raises(ValueError, match="register the pack"):
        j.add_rule("step", 1, "x", pack="nowhere")
    with pytest.raises(ValueError, match="unknown slot"):
        j.add_rule("nowhere", 1, "x")


def test_geometry_rules_belong_to_the_geometry_pack():
    names = {r.name for r in j._RULES if r.pack == "geometry"}
    assert {"angles up to orientation", "distances up to orientation",
            "close:distinct vertices"} <= names
    with j.active_packs(frozenset()):
        assert not any("angle_comm" in a for a in j.alternatives(["h"], ["h"]))


def test_intros_copy_only_where_the_goal_can_introduce_something():
    import pyleanx as pl

    x = pl.symbol("x", pl.Real)
    relation = pl.claim(x >= 0, because="hx", name="h").justification()
    binder = pl.claim(pl.Forall(x, x * x >= 0), name="h").justification()
    inequality = pl.claim(x != 0, because="hx", name="h").justification()  # ≠ is → False
    assert not any(a.startswith("(intros;") for a in relation.alternatives())
    assert any(a.startswith("(intros;") for a in binder.alternatives())
    assert any(a.startswith("(intros;") for a in inequality.alternatives())
