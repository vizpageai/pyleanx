"""The example runner knows every example script (no Lean)."""

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
