"""Lean identifier validation (name hygiene).

User-supplied names are restricted to a conservative subset (ASCII letters,
Greek letters, digits, subscript digits, ``_`` and ``'``) so that no string can
ever change the structure of the generated Lean file. ``λ``, ``Π`` and ``Σ`` are
excluded because Lean uses them as syntax. There is no quoting mechanism (« »);
illegal names are rejected.
"""

from __future__ import annotations

import re

from .errors import IdentifierError

_GREEK = "α-κμ-ωΑ-ΟΡΤ-Ω"  # α-ω, Α-Ω minus λ Π Σ
_SUB = "₀-₉"  # subscript digits ₀ … ₉
_LETTER = f"A-Za-z{_GREEK}"
_REST = f"A-Za-z0-9_'{_GREEK}{_SUB}"
_IDENT = re.compile(rf"[{_LETTER}][{_REST}]*\Z|_[{_LETTER}0-9][{_REST}]*\Z")

# Lean 4 keywords/commands plus names whose shadowing would change the meaning
# of generated code.
RESERVED = frozenset(
    """
    abbrev admit at attribute axiom by calc class deriving do else end example exists
    extends forall from fun have if import in induction infix infixl infixr instance
    lemma let local macro macro_rules match mutual namespace noncomputable nofun nomatch
    notation obtain omit open opaque partial postfix prefix private protected rec
    section set_option show sorry structure suffices syntax termination_by decreasing_by
    then theorem universe unsafe variable where with elab elab_rules initialize
    builtin_initialize declare_syntax_cat inductive def instance export renaming hiding
    Type Sort Prop Nat Int Rat Real True False Not And Or Iff Eq
    """.split()
)


def validate_identifier(name: object, what: str = "identifier") -> str:
    """Return ``name`` if it is a safe, plain Lean identifier, else raise."""
    if not isinstance(name, str):
        raise IdentifierError(f"{what} must be a str, got {type(name).__name__}")
    if not _IDENT.match(name):
        raise IdentifierError(
            f"{what} {name!r} is not a safe Lean identifier: use ASCII or Greek letters, "
            "digits (incl. subscripts ₀-₉), '_' and \"'\", starting with a letter "
            "(no spaces, dots, newlines or punctuation; λ Π Σ are Lean syntax)"
        )
    if name in RESERVED:
        raise IdentifierError(f"{what} {name!r} is a reserved Lean keyword or core name")
    return name


def validate_qualified_name(name: object, what: str = "declaration name") -> str:
    """Validate a dotted library name such as ``Nat.add_zero``.

    Each component must be a plain identifier, but core namespace components such
    as ``Nat`` or ``Real`` are permitted inside a qualified path.
    """
    if not isinstance(name, str) or not name:
        raise IdentifierError(f"{what} must be a non-empty str")
    parts = name.split(".")
    for part in parts:
        if not _IDENT.match(part):
            raise IdentifierError(f"{what} {name!r} has an invalid component {part!r}")
    if len(parts) == 1 and parts[0] in RESERVED - {"True", "False"}:
        raise IdentifierError(f"{what} {name!r} is a reserved Lean keyword")
    return name
