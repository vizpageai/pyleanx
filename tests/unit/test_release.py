"""Release consistency: one version everywhere, a dated changelog section, usable notes."""

from __future__ import annotations

import re
from pathlib import Path

import pyleanx as pl

ROOT = Path(__file__).resolve().parents[2]


def _notes(version: str) -> str:
    """The changelog section the release workflow publishes (same rule as release.yml)."""
    out, inside = [], False
    for line in (ROOT / "CHANGELOG.md").read_text(encoding="utf-8").splitlines():
        if line.startswith(f"## [{version}]"):
            inside = True
            continue
        if inside and line.startswith("## ["):
            break
        if inside:
            out.append(line)
    return "\n".join(out).strip()


def test_one_version_everywhere():
    v = pl.__version__
    cff = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    assert re.search(rf'^version: "{re.escape(v)}"$', cff, re.M)
    if not re.search(r"(dev|rc|a|b)\d*$", v):  # a release has a dated changelog section
        changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
        assert re.search(rf"^## \[{re.escape(v)}\] - \d{{4}}-\d{{2}}-\d{{2}}$", changelog, re.M)
        assert 'date-released: "' in cff


def test_release_notes_are_not_empty():
    notes = _notes(pl.__version__)
    assert len(notes.splitlines()) > 10 and "### " in notes


def test_release_workflow_extracts_notes_with_plain_string_matching():
    wf = (ROOT / ".github" / "workflows" / "release.yml").read_text(encoding="utf-8")
    # a regex like "^## \[" v "\]" makes "[0.1.0]" a character class and extracts nothing
    assert 'index($0, h) == 1' in wf and '"## [$v]"' in wf
