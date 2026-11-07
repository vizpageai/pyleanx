"""Sort (type) descriptors and the explicit compatibility rules between them.

These are *descriptors* of Lean types, not Python numeric types. PyLeanX never
inserts coercions silently; the only conversions are the explicit embeddings
allowed by :func:`can_cast`.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = ["Sort", "Nat", "Int", "Rat", "Real", "Prop", "NUMERIC_SORTS", "can_cast"]


@dataclass(frozen=True)
class Sort:
    """A primitive Lean type known to PyLeanX."""

    name: str
    lean: str
    numeric: bool
    rank: int  # position in the embedding chain Nat -> Int -> Rat -> Real
    imports: tuple[str, ...] = ()
    unicode: str = ""  # Mathlib notation (ℝ, ℕ, ...) used when unicode_types=True
    unicode_imports: tuple[str, ...] = ()  # module that defines that notation
    latex: str = ""

    def lean_name(self, unicode: bool = False) -> str:
        return self.unicode if unicode and self.unicode else self.lean

    @property
    def is_prop(self) -> bool:
        return self.name == "Prop"

    @property
    def allows_negation(self) -> bool:
        return self.numeric and self.name != "Nat"

    @property
    def allows_fractions(self) -> bool:
        return self.name in ("Rat", "Real")

    def __repr__(self) -> str:
        return f"pl.{self.name}"


Nat = Sort("Nat", "Nat", numeric=True, rank=0, unicode="ℕ",
           unicode_imports=("Mathlib.Data.Nat.Notation",), latex=r"\mathbb{N}")
Int = Sort("Int", "Int", numeric=True, rank=1, unicode="ℤ",
           unicode_imports=("Mathlib.Data.Int.Notation",), latex=r"\mathbb{Z}")
Rat = Sort("Rat", "Rat", numeric=True, rank=2, imports=("Mathlib.Data.Rat.Defs",), unicode="ℚ",
           unicode_imports=("Mathlib.Data.Rat.Init",), latex=r"\mathbb{Q}")
Real = Sort("Real", "Real", numeric=True, rank=3, imports=("Mathlib.Basic.Real.Basic",),
            unicode="ℝ", latex=r"\mathbb{R}")
Prop = Sort("Prop", "Prop", numeric=False, rank=-1, latex=r"\mathrm{Prop}")

NUMERIC_SORTS = (Nat, Int, Rat, Real)


def can_cast(src: Sort, dst: Sort) -> bool:
    """Only the canonical, meaning-preserving embeddings Nat -> Int -> Rat -> Real."""
    return src.numeric and dst.numeric and src.rank < dst.rank
