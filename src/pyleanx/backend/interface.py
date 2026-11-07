"""Backend-independent verification result types."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from enum import StrEnum
from typing import Any

SCHEMA_VERSION = 1


class Status(StrEnum):
    VERIFIED = "verified"
    REJECTED = "rejected"  # Lean reported errors (false statement, failed tactic, ...)
    TIMEOUT = "timeout"
    ENVIRONMENT_ERROR = "environment_error"  # Lean/project/imports unavailable
    POLICY_REJECTED = "policy_rejected"  # compiled, but audit failed or input not allowed


@dataclass(frozen=True)
class Diagnostic:
    severity: str  # error | warning | information
    message: str
    line: int | None = None
    column: int | None = None
    end_line: int | None = None
    end_column: int | None = None
    span_kind: str | None = None
    span_label: str | None = None
    python_origin: str | None = None
    source: str = "lean"  # lean | pyleanx

    def __str__(self) -> str:
        loc = f"{self.line}:{self.column}: " if self.line is not None else ""
        where = f" [{self.span_label}]" if self.span_label else ""
        origin = f" (python: {self.python_origin})" if self.python_origin else ""
        return f"{loc}{self.severity}: {self.message}{where}{origin}"


@dataclass
class VerificationResult:
    """Outcome of checking one theorem. ``verified`` is True only for status VERIFIED."""

    theorem: str
    status: Status
    diagnostics: list[Diagnostic] = field(default_factory=list)
    axioms: tuple[str, ...] | None = None
    lean_source: str = ""
    toolchain: str | None = None
    mathlib_revision: str | None = None
    source_map: list[dict] = field(default_factory=list)
    duration_ms: float = 0.0
    cache_hit: bool = False
    fingerprint: str = ""
    policy: dict = field(default_factory=dict)
    raw_tactics_used: bool = False
    backend: str = "subprocess"

    @property
    def verified(self) -> bool:
        return self.status is Status.VERIFIED

    @property
    def errors(self) -> list[Diagnostic]:
        return [d for d in self.diagnostics if d.severity == "error"]

    def summary(self) -> str:
        head = f"{self.theorem}: {self.status.value}"
        if self.cache_hit:
            head += " (cached)"
        if self.axioms is not None:
            head += f"; axioms={list(self.axioms)}"
        lines = [head] + [f"  {d}" for d in self.diagnostics if d.severity != "information"]
        return "\n".join(lines)

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["status"] = self.status.value
        d["verified"] = self.verified
        d["axioms"] = list(self.axioms) if self.axioms is not None else None
        d["schema_version"] = SCHEMA_VERSION
        return d

    def to_json(self, **kwargs: Any) -> str:
        return json.dumps(self.to_dict(), ensure_ascii=False, **kwargs)

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> VerificationResult:
        d = dict(d)
        d.pop("verified", None)
        d.pop("schema_version", None)
        d["status"] = Status(d["status"])
        d["diagnostics"] = [Diagnostic(**x) for x in d.get("diagnostics", [])]
        if d.get("axioms") is not None:
            d["axioms"] = tuple(d["axioms"])
        return cls(**d)

    def __repr__(self) -> str:
        return f"<VerificationResult {self.theorem} {self.status.value}>"

    def _repr_markdown_(self) -> str:  # Jupyter
        mark = "✅" if self.verified else "❌"
        lines = [f"{mark} **{self.theorem}**: `{self.status.value}`"
                 + (" (cached)" if self.cache_hit else "")]
        if self.axioms is not None:
            lines.append(f"axioms: `{', '.join(self.axioms) or 'none'}`")
        for d in self.diagnostics:
            if d.severity != "information":
                lines.append(f"- {d.severity}: `{d.message.splitlines()[0]}`"
                             + (f" ({d.span_label})" if d.span_label else ""))
        return "\n\n".join(lines)
