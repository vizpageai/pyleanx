"""Proof graphs: rendering and target resolution (no Lean needed)."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import mathlib as M
from pyleanx.errors import ProjectError, PyLeanXError
from pyleanx.proofgraph import _target, from_json, lean_source


def node(name, kind, module, uses=(), stmt=(), axioms=(), depth=0):
    return {"name": name, "kind": kind, "module": module, "type": f"type of {name}",
            "depth": depth, "statement_uses": list(stmt), "body_uses": list(uses),
            "axioms": list(axioms)}


RAW = {
    "root": "Real.sin_sq_add_cos_sq",
    "nodes": [
        node("Real.sin_sq_add_cos_sq", "theorem", "Mathlib.Analysis.Trig",
             uses=["Real.cos_sq_add_sin_sq", "add_comm"], stmt=["Real.sin", "Real"],
             axioms=["propext", "Quot.sound", "Classical.choice"]),
        node("Real.cos_sq_add_sin_sq", "theorem", "Mathlib.Analysis.Trig",
             uses=["Complex.cos_sq_add_sin_sq"], axioms=["propext", "Classical.choice"], depth=1),
        node("add_comm", "theorem", "Mathlib.Algebra.Group.Defs", uses=["Eq"], depth=1),
        node("Real.sin", "def", "Mathlib.Analysis.Trig", uses=["Complex.sin"],
             axioms=["Classical.choice"], depth=1),
        node("Real", "inductive", "Mathlib.Data.Real.Basic", depth=1),
    ],
    "closure": {"constants": 900, "declarations": 700, "height": 40,
                "layers": {"Mathlib": 600, "Init": 90, "Batteries": 10},
                "kinds": {"theorem": 500, "def": 200}},
    "axioms": [{"name": "propext", "module": "Init.Core", "type": "∀ {a b : Prop}, …", "depth": 9},
               {"name": "Quot.sound", "module": "Init.Core", "type": "…", "depth": 12},
               {"name": "Classical.choice", "module": "Init.Prelude", "type": "…", "depth": 8}],
    "primitives": [{"name": "Eq", "module": "Init.Prelude"}, {"name": "Nat", "module": "Init.Prelude"}],
}


def test_graph_structure_and_queries():
    g = from_json(RAW, depth=1)
    assert g.axioms == ("Classical.choice", "Quot.sound", "propext")
    assert g.uses("Real.sin_sq_add_cos_sq") == ("Real.cos_sq_add_sin_sq", "add_comm",
                                                "Real.sin", "Real")
    assert g.used_by("add_comm") == ("Real.sin_sq_add_cos_sq",)
    assert g.hidden("Real.cos_sq_add_sin_sq") == 1  # Complex.cos_sq_add_sin_sq not drawn
    assert ("Real.sin_sq_add_cos_sq", "Real.sin", "statement") in g.edges()
    assert g.nodes["Real.cos_sq_add_sin_sq"].layer == "Mathlib"


def test_text_tree_and_foundation():
    g = from_json(RAW, depth=1)
    text = str(g)
    assert text.splitlines()[0].startswith("Real.sin_sq_add_cos_sq  [theorem")
    assert "├─ Real.cos_sq_add_sin_sq" in text and "(+1 more)" in text
    assert "axioms: Classical.choice, Quot.sound, propext" in text
    assert "Lean's built-in types reached: Eq, Nat" in text
    assert "700 declarations (Mathlib 600, Lean core 90, Batteries 10)" in text
    assert ": type of add_comm" in g.tree(statements=True)


def test_repeated_nodes_are_marked():
    raw = dict(RAW, nodes=[node("a", "theorem", "M.A", uses=["b", "c"]),
                           node("b", "theorem", "M.A", uses=["c"], depth=1),
                           node("c", "theorem", "M.A", depth=1)], root="a")
    assert "↑ c" in from_json(raw, depth=2).tree()


def test_diagrams():
    g = from_json(RAW, depth=1)
    mer = g.to_mermaid()
    assert mer.startswith("flowchart TD") and "n0 --> n1" in mer and "n0 -.-> n3" in mer
    assert '[("propext<br/>axiom")]' in mer and "classDef axiom" in mer
    assert "-.- ax" in mer  # frontier linked to the axioms it rests on
    dot = g.to_dot()
    assert dot.startswith("digraph proof") and "shape=cylinder" in dot
    assert "mermaid" in g._repr_markdown_() and "<pre class='mermaid'>" in g.to_html()
    assert g.to_json()["nodes"][0]["name"] == "Real.sin_sq_add_cos_sq"


def test_lean_error_is_reported():
    with pytest.raises(ProjectError, match="unknown constant"):
        from_json({"error": "unknown constant foo"}, depth=1)


def test_lean_source_is_filled_in():
    src = lean_source("Real.sin_sq_add_cos_sq", ["Mathlib.Analysis.Trig"], 3, 50, "C:/x/g.json")
    assert "@@" not in src and "import Mathlib.Analysis.Trig" in src
    assert '"Real.sin_sq_add_cos_sq".toName' in src and "maxDepth : Nat := 3" in src
    assert "showAll : Bool := false" in src
    assert "showAll : Bool := true" in lean_source("x", [], 1, 1, "o", show_all=True)
    assert "sorry" not in src


def test_targets(monkeypatch):
    names = {"Real.sin_sq_add_cos_sq": ["Mathlib.Analysis.Trig", "theorem"],
             "Nat.add_comm": ["Init", "theorem"]}
    monkeypatch.setattr(M, "_index", lambda: names)
    monkeypatch.setattr(M, "_CHILDREN", {})
    assert _target("Real.sin_sq_add_cos_sq") == ("Real.sin_sq_add_cos_sq", ("Mathlib.Analysis.Trig",))
    assert _target("Nat.add_comm") == ("Nat.add_comm", ())
    assert _target(pl.analysis.sin_sq_add_cos_sq)[0] == "Real.sin_sq_add_cos_sq"
    with pytest.raises(TypeError):
        _target(3)  # type: ignore[arg-type]
    with pytest.raises(PyLeanXError):
        pl.proof_graph("x", detail="everything")
