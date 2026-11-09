"""Documentation hygiene: code compiles, navigation is complete, public API is documented."""

from __future__ import annotations

import inspect
import re
import sys
from pathlib import Path

import pytest

import pyleanx as pl

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from docs_blocks import ROOT, TUTORIALS, python_blocks  # noqa: E402


@pytest.mark.parametrize("page", TUTORIALS, ids=lambda p: p.name)
def test_tutorial_blocks_compile(page):
    blocks = python_blocks(page)
    assert blocks, f"{page.name} has no runnable python blocks"
    for i, block in enumerate(blocks):
        compile(block, f"{page.name}[{i}]", "exec")


def test_readme_blocks_compile():
    for i, block in enumerate(python_blocks(ROOT / "README.md")):
        compile(block, f"README[{i}]", "exec")


def test_every_docs_page_is_in_the_navigation():
    nav = (ROOT / "mkdocs.yml").read_text(encoding="utf-8")
    listed = set(re.findall(r":\s*([\w/.-]+\.md)\s*$", nav, re.M))
    pages = {p.relative_to(ROOT / "docs").as_posix() for p in (ROOT / "docs").rglob("*.md")}
    assert pages - listed == set(), "pages missing from mkdocs.yml nav"
    assert listed - pages == set(), "nav entries without a page"


def test_public_callables_have_docstrings():
    missing = []
    for name in pl.__all__:
        obj = getattr(pl, name)
        if (inspect.isfunction(obj) or inspect.isclass(obj)) and not inspect.getdoc(obj):
            missing.append(name)
    assert missing == [], f"exported without a docstring: {missing}"
