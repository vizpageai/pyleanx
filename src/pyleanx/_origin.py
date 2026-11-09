"""Capture the user's Python source location for diagnostics."""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from types import FrameType

_PKG_DIR = os.path.dirname(os.path.abspath(__file__))


@dataclass(frozen=True)
class Origin:
    filename: str
    lineno: int

    def __str__(self) -> str:
        return f"{self.filename}:{self.lineno}"


def caller_origin() -> Origin | None:
    """First stack frame outside the pyleanx package, if any."""
    frame: FrameType | None = sys._getframe(1)
    while frame is not None:
        fn = os.path.abspath(frame.f_code.co_filename)
        if not fn.startswith(_PKG_DIR):
            return Origin(frame.f_code.co_filename, frame.f_lineno)
        frame = frame.f_back
    return None


def resolve_annotations(obj: object, skip: int = 2) -> dict[str, object]:
    """``inspect.get_annotations(obj, eval_str=True)``, also seeing the *caller's* locals.

    With ``from __future__ import annotations`` annotations are strings; a sort defined in
    the enclosing function (``Vec = pl.define_type(...)``) is then only visible through the
    decorating frame's locals. ``skip`` frames are skipped to reach that frame.
    """
    import inspect

    frame = sys._getframe(skip)
    scopes: dict[str, object] = {}
    f: FrameType | None = frame
    # nearest frames win; stop after a few levels (decorator plumbing)
    chain = []
    for _ in range(4):
        if f is None:
            break
        chain.append(f)
        f = f.f_back
    for fr in reversed(chain):
        scopes.update(fr.f_locals)
    try:
        return inspect.get_annotations(obj, eval_str=True, locals=scopes)  # type: ignore[arg-type]
    except NameError:
        return inspect.get_annotations(obj, eval_str=True)  # type: ignore[arg-type]
