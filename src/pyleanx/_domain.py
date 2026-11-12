"""Shared versioning for the domain modules (``pyleanx.algebra/analysis/geometry``).

Every curated lemma reference names a declaration *in the pinned Mathlib*.
``tests/integration/test_domains_lean.py`` checks each one with ``#check`` against that
revision. Under a different Mathlib the names may have moved; :func:`catalog_status`
reports this, and Lean itself still rejects any wrong use.
"""

from __future__ import annotations

from collections.abc import Mapping

from .proofs import Name

#: Mathlib revision the catalogs were checked against (lean-project/lake-manifest.json).
VERIFIED_MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"
VERIFIED_TOOLCHAIN = "leanprover/lean4:v4.34.1"
CATALOG_VERSION = "1"


def lemma(name: str, *imports: str, label: str = "") -> Name:
    """A library fact; ``label`` says in words what it states (used in printed proofs)."""
    return Name(name, tuple(imports), label=label)


def collect_lemmas(namespace: Mapping[str, object]) -> dict[str, Name]:
    """Public module-level :class:`Name` objects, in definition order."""
    return {k: v for k, v in list(namespace.items())
            if isinstance(v, Name) and not k.startswith("_")}


def catalog_status(project_mathlib: str | None) -> str:
    if project_mathlib == VERIFIED_MATHLIB:
        return "ok"
    return (f"domain catalogs were checked against Mathlib {VERIFIED_MATHLIB[:12]}, the "
            f"project uses {str(project_mathlib)[:12]}; lemma names may differ (Lean still "
            "checks every use)")


def all_catalogs() -> Mapping[str, Mapping[str, Name]]:
    from . import algebra, analysis, geometry, mathlib

    return {
        "mathlib": {n: getattr(mathlib, n) for n in mathlib.__all__},
        "algebra": algebra.LEMMAS,
        "analysis": analysis.LEMMAS,
        "geometry": geometry.LEMMAS,
    }
