"""pl.explain: step extraction and rendering (no Lean needed)."""

from __future__ import annotations

from types import SimpleNamespace as NS

import pytest

import pyleanx as pl
from pyleanx.explain import _split_goal, collect_steps, from_json, source_file

SRC = """theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  Eq.trans (by rw [cosh_mul_I, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))
"""


def pos(line, col):
    return NS(line=line, column=col)


def tnode(a, b, kind, before, after, synthetic=False):
    stx = NS(range=NS(start=pos(*a), finish=pos(*b), synthetic=synthetic), kind=kind)
    return NS(kind="TacticInfo", node=NS(stx=stx, goals_before=before, goals_after=after))


G0 = "x : ℂ\n⊢ sin x ^ 2 + cos x ^ 2 = cosh (x * I) ^ 2 - sinh (x * I) ^ 2"
G1 = "x : ℂ\n⊢ sin x ^ 2 + cos x ^ 2 = cos x ^ 2 - sinh (x * I) ^ 2"
G2 = "x : ℂ\n⊢ sin x ^ 2 + cos x ^ 2 = sinh (x * I) ^ 2 + cos x ^ 2"


def fake_tree():
    nodes = [
        tnode((2, 12), (2, 14), "Lean.Parser.Term.byTactic", [G0], []),          # "by"
        tnode((2, 15), (2, 40), "Lean.Parser.Tactic.tacticSeq", [G0], []),       # wrapper
        tnode((2, 15), (2, 40), "Lean.Parser.Tactic.rwSeq", [G0], []),           # rw [...]
        tnode((2, 19), (2, 29), "Lean.Parser.Tactic.rwRule", [G0], [G1]),
        tnode((2, 31), (2, 39), "Lean.Parser.Tactic.rwRule", [G1], [G2]),
        tnode((2, 39), (2, 40), "Lean.Parser.Tactic.tacticRfl", [G2], []),       # "]"
        tnode((2, 19), (2, 29), "x", [G0], [G1], synthetic=True),
        tnode((9, 0), (9, 5), "Lean.Parser.Tactic.simp", ["⊢ other"], []),       # elsewhere
    ]
    return [NS(dfs_walk=lambda: iter(nodes))]


def test_steps_follow_the_source_and_nesting():
    tactics = [NS(start_pos=pos(2, 19), end_pos=pos(2, 29),
                  used_constants=["Complex.cosh_mul_I"])]
    steps = collect_steps(fake_tree(), tactics, SRC.splitlines(), (1, 0), (3, 33))
    assert [s["text"] for s in steps] == ["rw [cosh_mul_I, add_comm]", "cosh_mul_I", "add_comm",
                                          "rfl (attempted by rw after the last rule)"]
    assert [s["depth"] for s in steps] == [0, 1, 1, 1]
    assert steps[1]["before"] == [G0] and steps[1]["after"] == [G1]
    assert steps[1]["uses"] == ["Complex.cosh_mul_I"]


def test_goal_split():
    assert _split_goal(G0) == (("x : ℂ",), "sin x ^ 2 + cos x ^ 2 = cosh (x * I) ^ 2 - sinh (x * I) ^ 2")
    assert _split_goal("⊢ 1 = 1") == ((), "1 = 1")


def raw(exact=True):
    return {
        "name": "Complex.sin_sq_add_cos_sq", "module": "Mathlib.Analysis.Complex.Trigonometric",
        "file": "Mathlib/Analysis/Complex/Trigonometric.lean", "first_line": 465,
        "last_line": 467, "statement": "∀ (x : ℂ), Complex.sin x ^ 2 + Complex.cos x ^ 2 = 1",
        "source": SRC.rstrip(), "exact": exact,
        "evidence": {"package": "mathlib", "revision": "d13f23b723b8", "value_hash": "123",
                     "reason": "" if exact else "the re-elaborated proof term differs"},
        "steps": [{"text": "rw [cosh_mul_I, add_comm]", "line": 466, "column": 14, "depth": 0,
                   "goals_before": [G0], "goals_after": [], "uses": []},
                  {"text": "cosh_mul_I", "line": 466, "column": 18, "depth": 1,
                   "goals_before": [G0], "goals_after": [G1],
                   "uses": ["Complex.cosh_mul_I", "Complex.cosh"]}],
        "cited": ["Complex.cosh_sq_sub_sinh_sq", "Complex.cosh"],
        "lemmas": {**{n: {"name": n, "kind": "theorem", "module": "M", "type": f"stmt of {n}"}
                      for n in ("Complex.cosh_sq_sub_sinh_sq", "Complex.cosh_mul_I")},
                   "Complex.cosh": {"name": "Complex.cosh", "kind": "def", "module": "M",
                                    "type": "ℂ → ℂ"}},
    }


def test_rendering():
    e = from_json(raw())
    text = str(e)
    assert text.startswith("Complex.sin_sq_add_cos_sq\n  Mathlib/Analysis/Complex/Trigonometric.lean:465-467")
    assert "  465 │ theorem sin_sq_add_cos_sq" in text
    assert "exact: re-elaborating this source gives the same proof term" in text
    assert "1. rw [cosh_mul_I, add_comm]" in text and "   2. cosh_mul_I" in text
    assert "x : ℂ" in text and "→ ⊢ sin x ^ 2 + cos x ^ 2 = cos x ^ 2 - sinh (x * I) ^ 2" in text
    assert "uses: Complex.cosh_mul_I\n" in text and "→ no goals" in text
    assert "Lemmas in the proof term: Complex.cosh_sq_sub_sinh_sq\n" in text
    assert "Complex.cosh_mul_I : stmt of Complex.cosh_mul_I" in text
    assert "Definitions, types and axioms involved:\n  Complex.cosh : ℂ → ℂ" in text
    assert e.used == ("Complex.cosh_sq_sub_sinh_sq", "Complex.cosh", "Complex.cosh_mul_I")
    assert "✅ exact" in e._repr_markdown_()
    assert e.to_json()["name"] == "Complex.sin_sq_add_cos_sq"


def test_not_exact_is_said_plainly():
    e = from_json(raw(exact=False))
    assert "NOT shown to be exact: the re-elaborated proof term differs" in str(e)
    assert "not shown to be exact" in e._repr_markdown_()


def test_source_file_prefers_pinned_packages(tmp_path):
    f = tmp_path / ".lake" / "packages" / "mathlib" / "Mathlib" / "A" / "B.lean"
    f.parent.mkdir(parents=True)
    f.write_text("theorem t : True := trivial\n", encoding="utf-8")
    (tmp_path / "lake-manifest.json").write_text(
        '{"packages": [{"name": "mathlib", "rev": "abc"}]}', encoding="utf-8")
    path, info = source_file(NS(path=tmp_path), "Mathlib.A.B")
    assert path == f and info["package"] == "mathlib" and info["pinned"] == "abc"


def test_exported():
    assert pl.explain is not None and "explain" in pl.__all__
    with pytest.raises(TypeError):
        pl.explain(3)  # type: ignore[arg-type]


def test_automation_internals_are_collapsed():
    r = raw()
    r["cited"] = ["Lean.Omega.tidy_sat", "Complex.cosh_sq_sub_sinh_sq",
                  "Mathlib.Tactic.Ring.of_eq"]
    r["lemmas"]["Lean.Omega.tidy_sat"] = {"name": "Lean.Omega.tidy_sat", "kind": "theorem",
                                          "module": "Init", "type": "certificate"}
    e = from_json(r)
    text = str(e)
    assert "Lemmas in the proof term: Complex.cosh_sq_sub_sinh_sq\n" in text
    assert "Lean.Omega.tidy_sat :" not in text
    assert "(+ 2 internal lemmas of automation tactics" in text
    assert e.automation == ("Lean.Omega.tidy_sat", "Mathlib.Tactic.Ring.of_eq")


def test_a_pyleanx_theorem_is_explained_from_its_verified_source(monkeypatch):
    import sys

    ex = sys.modules["pyleanx.explain"]  # `pl.explain` is the function, not the module

    seen = {}
    monkeypatch.setattr(ex, "_explain_theorem",
                        lambda thm, proj, timeout, refresh: seen.setdefault("thm", thm))
    monkeypatch.setattr("pyleanx.project.find_project", lambda p=None: None)
    x = pl.symbol("x", pl.Real)
    t = pl.Theorem("t", [x], conclusion=0 <= x**2, proof=pl.positivity())
    assert pl.explain(t) is t and seen["thm"] is t
    r = raw()
    r["evidence"] = {"package": "PyLeanX theorem", "source_sha256": "ab" * 32,
                     "axioms": ["propext"], "reason": ""}
    assert "this is the Lean source PyLeanX verifies" in str(from_json(r))
