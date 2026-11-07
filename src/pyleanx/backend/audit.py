"""Axiom-dependency audit: parse ``#print axioms`` output and apply a trust policy.

Compile success alone is not proof: a declaration can depend on ``sorryAx``,
user ``axiom``s or native-evaluation trust (``Lean.ofReduceBool``,
``Lean.trustCompiler``), possibly transitively. Lean's ``#print axioms`` reports
the transitive closure; this module parses it and decides acceptance.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Iterable
from dataclasses import dataclass, field

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
NATIVE_AXIOMS = frozenset({"Lean.ofReduceBool", "Lean.trustCompiler", "Lean.ofReduceNat"})

_DEPENDS = re.compile(r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]\s*$", re.S)
_NO_AXIOMS = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms\s*$")


@dataclass(frozen=True)
class AxiomReport:
    theorem: str
    axioms: tuple[str, ...]


def parse_axiom_report(text: str) -> AxiomReport | None:
    """Parse one ``#print axioms`` message; ``None`` if it is not one."""
    text = text.strip()
    m = _NO_AXIOMS.match(text)
    if m:
        return AxiomReport(m.group("name"), ())
    m = _DEPENDS.match(text)
    if m:
        raw = m.group("axioms").replace("\n", " ")
        axioms = tuple(a.strip() for a in raw.split(",") if a.strip())
        return AxiomReport(m.group("name"), axioms)
    return None


def _is_native(ax: str) -> bool:
    return ax in NATIVE_AXIOMS or "_native" in ax or ax.startswith("Lean.ofReduce")


@dataclass(frozen=True)
class AxiomPolicy:
    """Which axioms a verified proof may depend on.

    Default: only Lean's three standard axioms. ``sorryAx`` is never allowed.
    ``allow_raw_tactics`` gates untrusted tactic text (see docs/security.md).
    """

    allowed: frozenset[str] = STANDARD_AXIOMS
    allow_native: bool = False
    allow_raw_tactics: bool = False
    extra_allowed: frozenset[str] = field(default_factory=frozenset)

    def check(self, axioms: Iterable[str]) -> list[str]:
        """Return a list of violations (empty means accepted)."""
        problems = []
        for ax in axioms:
            if ax == "sorryAx":
                problems.append("depends on sorryAx (an incomplete proof: `sorry`/`admit` or an "
                                "elaboration error recovered as sorry)")
            elif _is_native(ax):
                if not self.allow_native:
                    problems.append(f"depends on native-evaluation trust axiom {ax}")
            elif ax not in self.allowed and ax not in self.extra_allowed:
                problems.append(f"depends on non-standard axiom {ax}")
        return problems

    def to_dict(self) -> dict:
        return {
            "allowed": sorted(self.allowed),
            "extra_allowed": sorted(self.extra_allowed),
            "allow_native": self.allow_native,
            "allow_raw_tactics": self.allow_raw_tactics,
        }

    def fingerprint(self) -> str:
        blob = json.dumps(self.to_dict(), sort_keys=True).encode()
        return hashlib.sha256(blob).hexdigest()[:16]


DEFAULT_POLICY = AxiomPolicy()
