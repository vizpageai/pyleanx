"""M7 theorem bank and canonical (de)serialisation, without running Lean."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

import pyleanx as pl
from pyleanx import geometry as geo
from pyleanx.bank import (
    BankEntry,
    BankError,
    CrossSystemError,
    Formalization,
    TheoremBank,
    VersionMismatchError,
    statement_hash,
)
from pyleanx.render.lean import render_statement
from pyleanx.serialize import SerializationError, theorem_from_canonical

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture()
def project():
    return pl.LeanProject(ROOT / "lean-project")


def _sample_theorems():
    x, y = pl.symbols("x y", pl.Real)
    n = pl.symbol("n", pl.Nat)
    P = pl.prop_symbol("P")
    A, B, C = geo.points("A B C")
    z = pl.symbol("z", pl.Real)
    return [
        pl.Theorem("t_ring", [x, y], conclusion=(x + y)**2 == x**2 + 2*x*y + y**2,
                   proof=pl.ring()),
        pl.Theorem("t_hyp", [x], assumptions={"hx": pl.Le(0, x)},
                   conclusion=pl.sqrt(x)**2 == x, proof=pl.exact(pl.analysis.sq_sqrt("hx"))),
        pl.Theorem("t_nat", [n], conclusion=n + 0 == n, proof=pl.simp()),
        pl.Theorem("t_logic", [P], conclusion=pl.Implies(P, P),
                   proof=pl.intro("h") >> pl.exact("h")),
        pl.Theorem("t_geo", [A, B, C],
                   conclusion=geo.dist(A, C) <= geo.dist(A, B) + geo.dist(B, C),
                   proof=pl.exact(geo.dist_triangle(A, B, C))),
        pl.Theorem("t_quant", [], conclusion=pl.Forall([z], pl.Exists([x], x > z)),
                   proof=pl.intro("z") >> pl.use(z + 1) >> pl.linarith()),
        pl.Theorem("t_misc", [x, n],
                   conclusion=pl.cast(n, pl.Real) + abs(-x) >= pl.min(x, x) - pl.rat(1, 2, pl.Real),
                   proof=pl.steps(pl.simp("abs_neg", only=True, at=()), pl.rw(pl.rev("h"))),
                   imports=["Mathlib.Order.MinMax"]),
        pl.Theorem("t_branch", [P], conclusion=pl.And(P, pl.TRUE) | pl.Not(P),
                   proof=pl.branches(pl.norm_num(), pl.nlinarith(pl.mathlib.sq_nonneg(x)))),
    ]


@pytest.mark.parametrize("idx", range(8))
def test_canonical_round_trip_is_exact(idx):
    thm = _sample_theorems()[idx]
    data = json.loads(json.dumps(thm.canonical()))
    again = theorem_from_canonical(data)
    assert json.dumps(again.canonical(), sort_keys=True) == json.dumps(data, sort_keys=True)
    assert render_statement(again) == render_statement(thm)
    # proof text identical too (lemma imports are supplied separately)
    assert again.to_lean(audit=False).split(":= by")[1] == thm.to_lean(audit=False).split(":= by")[1]


def test_deserialiser_rejects_unknowns_and_free_variables():
    good = _sample_theorems()[0].canonical()
    bad_sort = json.loads(json.dumps(good).replace('"Real"', '"Quaternion"'))
    with pytest.raises(SerializationError, match="unknown sort"):
        theorem_from_canonical(bad_sort)
    free = json.loads(json.dumps(good))
    free["variables"] = free["variables"][:1]
    with pytest.raises(SerializationError, match="free or mistyped"):
        theorem_from_canonical(free)
    weird = json.loads(json.dumps(good))
    weird["proof"] = ["sorry"]
    with pytest.raises(SerializationError, match="unknown tactic"):
        theorem_from_canonical(weird)
    fn = json.loads(json.dumps(good))
    fn["conclusion"] = ["eq", ["app", "Evil.fn", [["var", "x", "Real"]]], ["var", "x", "Real"]]
    with pytest.raises(SerializationError, match="unknown function"):
        theorem_from_canonical(fn)


def _decl(project, bid="geometry.triangle_inequality", **kw):
    stmt = "∀ {α : Type u_1} [inst : PseudoMetricSpace α] (x y z : α), dist x z ≤ dist x y + dist y z"
    bank = kw.pop("bank", None)
    if bank is None:  # (an empty bank is falsy: it is a container)
        bank = TheoremBank()
    bank.add_declaration(bid, geo.dist_triangle, stmt, Formalization.of_project(project),
                         aliases=("triangle inequality",), tags=("geometry",),
                         description="dist x z <= dist x y + dist y z", **kw)
    return bank


def test_entry_separates_id_from_lean_name_and_hashes_statement(project):
    bank = _decl(project)
    e = bank.get("geometry.triangle_inequality")
    assert e.lean_name == "dist_triangle" and e.id != e.lean_name
    assert e.statement_sha256 == statement_hash(e.statement)
    assert e.imports == geo.dist_triangle.imports
    assert e.formalization.library_revision == project.mathlib_revision
    assert bank.get("Triangle Inequality") is e  # alias, case-insensitive


def test_tampered_statement_is_rejected(project):
    d = _decl(project).get("geometry.triangle_inequality").to_dict()
    d["statement"] = d["statement"].replace("≤", "≥")
    with pytest.raises(BankError, match="hash"):
        BankEntry.from_dict(d)


def test_search_ranks_alias_and_name_hits(project):
    bank = _decl(project)
    bank.add_declaration("algebra.sq_nonneg", pl.algebra.sq_nonneg, "∀ (a : R), 0 ≤ a ^ 2",
                         Formalization.of_project(project), aliases=("square nonnegative",))
    hits = bank.search("triangle inequality")
    assert hits[0].entry.id == "geometry.triangle_inequality"
    assert bank.search("dist")[0].entry.id == "geometry.triangle_inequality"
    assert bank.search("square")[0].entry.id == "algebra.sq_nonneg"
    assert bank.search("nonexistent words") == []
    assert [h.entry.id for h in bank.search("triangle", tags=["geometry"])] == \
        ["geometry.triangle_inequality"]


def test_ref_gives_name_with_imports_for_matching_version(project):
    ref = _decl(project).ref("triangle inequality", project)
    assert ref.name == "dist_triangle" and ref.imports


def test_version_mismatch_and_cross_system_are_refused(project):
    bank = TheoremBank()
    old = Formalization("lean4", "mathlib", project.toolchain, "0" * 40)
    bank.add_declaration("geometry.old", "dist_triangle", "stmt", old)
    with pytest.raises(VersionMismatchError):
        bank.ref("geometry.old", project)
    coq = Formalization("coq", "mathcomp", "8.20", "abc")
    bank.add(BankEntry(id="external.coq_triangle", lean_name="Rle_triangle",
                       kind="declaration", statement="forall x y, ...",
                       statement_sha256=statement_hash("forall x y, ..."), formalization=coq))
    with pytest.raises(CrossSystemError, match="never assumes"):
        bank.ref("external.coq_triangle", project)
    _decl(project, bank=bank)
    e = bank.link("geometry.triangle_inequality", "coq", "Rle_triangle", "same idea?")
    assert e.related[0]["status"] == "unverified"
    assert bank.ref("geometry.triangle_inequality", project).name == "dist_triangle"


def _fake_result(thm, project, status=pl.Status.VERIFIED):
    return pl.VerificationResult(theorem=thm.name, status=status, axioms=("propext",),
                                 lean_source=thm.to_lean(), toolchain=project.toolchain,
                                 mathlib_revision=project.mathlib_revision, fingerprint="f" * 64)


def test_add_theorem_requires_verified_matching_result(project):
    thm = _sample_theorems()[4]
    bank = TheoremBank()
    with pytest.raises(BankError, match="only verified"):
        bank.add_theorem(thm, _fake_result(thm, project, pl.Status.REJECTED), id="my.t")
    other = _sample_theorems()[0]
    with pytest.raises(BankError, match="not"):
        bank.add_theorem(thm, _fake_result(other, project), id="my.t")
    e = bank.add_theorem(thm, _fake_result(thm, project), id="my.tri", tags=["geometry"])
    assert e.kind == "theorem" and e.evidence["fingerprint"] == "f" * 64
    assert "Mathlib.Topology.MetricSpace.Pseudo.Defs" in e.imports
    with pytest.raises(BankError, match="PyLeanX theorem"):
        bank.ref("my.tri", project)
    loaded = bank.load("my.tri", project)
    assert render_statement(loaded) == render_statement(thm)
    assert "import Mathlib.Topology.MetricSpace.Pseudo.Defs" in loaded.to_lean()


def test_bank_persists_and_reloads(tmp_path, project):
    path = tmp_path / "bank.json"
    bank = _decl(project, bank=TheoremBank(path))
    thm = _sample_theorems()[0]
    bank.add_theorem(thm, _fake_result(thm, project), id="my.sq")
    main = _sample_theorems()[2]
    bank.add_theorem(main, _fake_result(main, project), id="my.main", dependencies=["my.sq"])
    bank.save()
    again = TheoremBank(path)
    assert len(again) == 3
    assert [t.name for t in again.load_with_dependencies("my.main", project)] == \
        ["t_ring", "t_nat"]
    with pytest.raises(BankError, match="nope"):
        again.add_theorem(main, _fake_result(main, project), id="my.x", dependencies=["nope"])
