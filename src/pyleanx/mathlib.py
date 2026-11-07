"""A small, curated set of Mathlib lemma references with the imports they need.

Each entry is a typed :class:`~pyleanx.proofs.Name`; nothing here asserts a lemma's
statement -- Lean checks every use. Names are tied to the pinned Mathlib revision.
"""

from __future__ import annotations

from .proofs import Name

_ORDER_RING = "Mathlib.Algebra.Order.Ring.Unbundled.Basic"

sq_nonneg = Name("sq_nonneg", (_ORDER_RING,))
mul_self_nonneg = Name("mul_self_nonneg", (_ORDER_RING,))
add_comm = Name("add_comm")
mul_comm = Name("mul_comm")
add_assoc = Name("add_assoc")
mul_assoc = Name("mul_assoc")
Nat_add_zero = Name("Nat.add_zero")  # noqa: N816 - mirrors the Lean name
Nat_zero_add = Name("Nat.zero_add")  # noqa: N816
le_refl = Name("le_refl")
le_trans = Name("le_trans")
add_pos = Name("add_pos")
mul_pos = Name("mul_pos")

__all__ = [
    "sq_nonneg", "mul_self_nonneg", "add_comm", "mul_comm", "add_assoc", "mul_assoc",
    "Nat_add_zero", "Nat_zero_add", "le_refl", "le_trans", "add_pos", "mul_pos",
]
