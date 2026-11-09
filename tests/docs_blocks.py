"""Shared helper: the runnable ```python blocks of a Markdown page."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TUTORIALS = sorted((ROOT / "docs" / "tutorials").glob("*.md"))
_BLOCK = re.compile(r"^```python\n(.*?)^```", re.S | re.M)


def python_blocks(path: Path) -> list[str]:
    return _BLOCK.findall(path.read_text(encoding="utf-8"))
