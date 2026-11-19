"""Generated and enumerated project files are complete and current (no Lean)."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_every_example_has_an_expected_outcome_or_a_reason():
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        import run_examples
    finally:
        sys.path.remove(str(ROOT / "scripts"))
    assert run_examples.unclassified() == []
    listed = set(run_examples.CASES) | set(run_examples.SKIPPED) | run_examples.HELPERS
    on_disk = {p.stem for p in run_examples.EXAMPLES.glob("*.py")}
    assert listed <= on_disk, sorted(listed - on_disk)  # no stale entries either


def test_the_facts_page_is_up_to_date():
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        import gen_facts_doc
    finally:
        sys.path.remove(str(ROOT / "scripts"))
    assert gen_facts_doc.main(["--check"]) == 0, "run python scripts/gen_facts_doc.py"


def test_ci_failures_become_annotations(monkeypatch, capsys):
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        import run_examples
    finally:
        sys.path.remove(str(ROOT / "scripts"))
    monkeypatch.delenv("GITHUB_ACTIONS", raising=False)  # this test may itself run on CI
    run_examples.annotate("quiet", "outside CI nothing is printed")
    assert capsys.readouterr().out == ""
    monkeypatch.setenv("GITHUB_ACTIONS", "true")
    run_examples.annotate("example a:b", "exit 1 (want 0)\n100% wrong")
    assert capsys.readouterr().out == "::error title=example a%3Ab::exit 1 (want 0)%0A100%25 wrong\n"
