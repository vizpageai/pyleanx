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

# Pages whose examples need resources CI does not have (shown as ```py, compiled only).
ILLUSTRATIVE = {"libraries.md"}


@pytest.mark.parametrize("page", TUTORIALS, ids=lambda p: p.name)
def test_tutorial_blocks_compile(page):
    blocks = python_blocks(page)
    if page.name not in ILLUSTRATIVE:
        assert blocks, f"{page.name} has no runnable python blocks"
    shown = re.findall(r"^```py\n(.*?)^```", page.read_text(encoding="utf-8"), re.S | re.M)
    for i, block in enumerate(blocks + shown):
        compile(block, f"{page.name}[{i}]", "exec")


def _undefined_names(blocks: list[str]) -> list[tuple[int, list[str]]]:
    """Names each block reads that neither it nor an earlier block defines."""
    import ast
    import builtins

    defined = set(dir(builtins))
    out = []
    for i, block in enumerate(blocks):
        tree = ast.parse(block)
        used = set()
        for n in ast.walk(tree):
            if isinstance(n, ast.Name):
                (defined.add if isinstance(n.ctx, ast.Store) else used.add)(n.id)
            elif isinstance(n, (ast.Import, ast.ImportFrom)):
                defined.update((a.asname or a.name).split(".")[0] for a in n.names)
            elif isinstance(n, (ast.FunctionDef, ast.ClassDef)):
                defined.add(n.name)
            elif isinstance(n, ast.arg):
                defined.add(n.arg)
        if missing := sorted(used - defined):
            out.append((i, missing))
    return out


@pytest.mark.parametrize("page", TUTORIALS, ids=lambda p: p.name)
def test_tutorial_blocks_define_what_they_use(page):
    # The runnable blocks are executed top to bottom by the Lean doc test; an excerpt that
    # uses names from an example file must be a ```py block (compiled, not run).
    assert _undefined_names(python_blocks(page)) == []


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
