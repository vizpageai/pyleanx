"""Capture the user's Python source location for diagnostics."""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass

_PKG_DIR = os.path.dirname(os.path.abspath(__file__))


@dataclass(frozen=True)
class Origin:
    filename: str
    lineno: int

    def __str__(self) -> str:
        return f"{self.filename}:{self.lineno}"


def caller_origin() -> Origin | None:
    """First stack frame outside the pyleanx package, if any."""
    frame = sys._getframe(1)
    while frame is not None:
        fn = os.path.abspath(frame.f_code.co_filename)
        if not fn.startswith(_PKG_DIR):
            return Origin(frame.f_code.co_filename, frame.f_lineno)
        frame = frame.f_back
    return None
