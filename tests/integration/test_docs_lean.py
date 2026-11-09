"""Every tutorial page runs top to bottom against the real pinned Lean.

The pages contain their own `assert result.verified` / `assert not bad.verified` checks,
so a tutorial that drifts from the code or from Mathlib fails here.
"""

from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from docs_blocks import TUTORIALS, python_blocks  # noqa: E402

pytestmark = pytest.mark.lean
NEEDS_REPL = {"interactive.md", "ai.md"}


@pytest.mark.parametrize("page", TUTORIALS, ids=lambda p: p.name)
def test_tutorial_runs(page, lean_project, tmp_path, monkeypatch):
    if page.name in NEEDS_REPL and importlib.util.find_spec("lean_interact") is None:
        pytest.skip("needs pip install 'pyleanx[interactive]'")
    import pyleanx as pl

    monkeypatch.setenv("PYLEANX_PROJECT", str(lean_project.path))
    monkeypatch.chdir(tmp_path)           # examples may write files
    ns: dict = {"__name__": f"docs_{page.stem}"}
    try:
        for i, block in enumerate(python_blocks(page)):
            exec(compile(block, f"{page.name}[{i}]", "exec"), ns)  # noqa: S102
    finally:
        pl.shutdown_sessions()
    assert os.environ["PYLEANX_PROJECT"] == str(lean_project.path)
