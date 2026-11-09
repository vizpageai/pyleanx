"""Real Lean: library declarations are shown as Lean states them (no restatement)."""

from __future__ import annotations

import pytest

import pyleanx as pl
from pyleanx import algebra as alg

pytestmark = pytest.mark.lean


def test_infoview_shows_mathlib_statements(lean_project):
    views = pl.infoview(alg.two_mul_le_add_sq, alg.sq_nonneg, alg.abs_add_le,
                        project=lean_project, timeout=1800)
    by_name = {v.name: v for v in views}
    assert by_name["two_mul_le_add_sq"].conclusion == "2 * a * b ≤ a ^ 2 + b ^ 2"
    assert by_name["sq_nonneg"].conclusion == "0 ≤ a ^ 2"
    assert by_name["abs_add_le"].conclusion == "|a + b| ≤ |a| + |b|"
    for v in views:
        assert v.goal.splitlines()[-1].startswith("⊢ ")
        assert any(b.kind == "instance" for b in v.binders)
        print(f"\n{v.name}\n{v.goal}")


def test_infoview_unknown_name_is_an_error(lean_project):
    with pytest.raises(pl.ProjectError):
        pl.infoview(pl.ref("no_such_lemma_xyz", imports=[alg.sq_nonneg.imports[0]]),
                    project=lean_project, timeout=1800)
