"""M7 gate: search -> exact versioned declaration -> apply in proof -> kernel-checked result."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import algebra as alg
from pyleanx import geometry as geo
from pyleanx.bank import CATALOG_META

pytestmark = pytest.mark.lean


def test_m7_gate_search_apply_verify(lean_project, tmp_path):
    path = tmp_path / "bank.json"
    bank = pl.TheoremBank(path)
    items = {"geometry.dist_triangle": geo.dist_triangle, "algebra.sq_nonneg": alg.sq_nonneg,
             "algebra.add_sq": alg.add_sq}
    entries = bank.index_declarations(items, lean_project, meta=CATALOG_META, timeout=1800)
    assert len(entries) == 3
    tri = bank.get("geometry.dist_triangle")
    # the statement is what Lean reports for the pinned Mathlib, not hand-written
    assert "dist x z ≤ dist x y + dist y z" in tri.statement
    assert tri.formalization.library_revision == lean_project.mathlib_revision
    assert tri.formalization.toolchain == lean_project.toolchain

    # search -> exact versioned declaration
    hit = bank.search("triangle inequality")[0]
    assert hit.entry.id == "geometry.dist_triangle"
    lemma = bank.ref(hit.entry.id, lean_project)
    assert lemma.name == "dist_triangle"

    # apply in a proof -> kernel check + audit
    A, B, C = geo.points("A B C")
    thm = pl.Theorem("m7_tri", [A, B, C],
                     conclusion=geo.dist(A, C) <= geo.dist(A, B) + geo.dist(B, C),
                     proof=pl.exact(lemma(A, B, C)))
    res = thm.verify(lean_project, use_cache=False, timeout=1800)
    assert res.verified, res.summary()

    # bank the verified theorem, persist, reload in a "new process", reuse it
    bank.add_theorem(thm, res, id="user.triangle", aliases=["my triangle lemma"],
                     dependencies=[])
    bank.save()
    fresh = pl.TheoremBank(path)
    loaded = fresh.load("my triangle lemma", lean_project)
    X, Y, Z = geo.points("X Y Z")
    main = pl.Theorem("m7_main", [X, Y, Z],
                      conclusion=geo.dist(X, Z) <= geo.dist(X, Y) + geo.dist(Y, Z) + 1,
                      proof=pl.linarith(pl.ref(loaded)(X, Y, Z)))
    r_lemma, r_main = pl.verify_all([loaded, main], project=lean_project, use_cache=False,
                                    timeout=1800)
    assert r_lemma.verified, r_lemma.summary()
    assert r_main.verified, r_main.summary()

    # a cross-system link is recorded but never used as an equivalence
    fresh.link("geometry.dist_triangle", "isabelle", "dist_triangle", "presumably the same")
    with pytest.raises(pl.CrossSystemError):
        fresh.add_declaration("ext.isa_tri", "dist_triangle", "dist x z <= ...",
                              pl.Formalization("isabelle", "HOL", "2025", "x"))
        fresh.ref("ext.isa_tri", lean_project)
