"""Exception hierarchy for PyLeanX.

All errors raised *before* Lean runs are Python-side structural errors. They never
imply anything about mathematical truth; they mean the request could not be
faithfully represented.
"""

from __future__ import annotations


class PyLeanXError(Exception):
    """Base class for all PyLeanX errors."""


class SymbolicTruthValueError(PyLeanXError, TypeError):
    """Raised when a symbolic expression is used where Python needs a bool."""

    def __init__(self, expr_text: str = "") -> None:
        shown = f" ({expr_text})" if expr_text else ""
        super().__init__(
            f"A symbolic PyLeanX expression{shown} has no Python truth value. "
            "`==`, `<`, ... build propositions; they do not decide them. "
            "Use pl.And/pl.Or/pl.Not (or &, |, ~) instead of `and`/`or`/`not`, "
            "pl.And(a <= x, x <= b) instead of chained comparisons, "
            "e.same_structure(other) for structural comparison, "
            "and Theorem(...).verify() to have Lean decide truth."
        )


class SortError(PyLeanXError, TypeError):
    """Ill-sorted expression (e.g. Nat + Real without an explicit cast)."""


class LiteralError(PyLeanXError, TypeError):
    """A Python value cannot be used as an exact mathematical literal."""


class ScopeError(PyLeanXError):
    """Free/undeclared variable, duplicate binder, or name capture."""


class IdentifierError(PyLeanXError, ValueError):
    """A name is not a safe Lean identifier."""


class TacticError(PyLeanXError, ValueError):
    """A proof/tactic tree is malformed."""


class UnsupportedConstructError(PyLeanXError):
    """The construct is valid Python but not representable in this version."""


class ProjectError(PyLeanXError):
    """The pinned Lean project is missing or inconsistent."""
