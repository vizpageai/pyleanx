"""Map generated Lean line ranges back to PyLeanX objects and Python origins."""

from __future__ import annotations

from dataclasses import asdict, dataclass

from .._origin import Origin


@dataclass(frozen=True)
class SourceSpan:
    """Lines ``start_line..end_line`` (1-based, inclusive) of the generated file."""

    start_line: int
    end_line: int
    kind: str  # header | theorem | binders | statement | tactic | axiom_audit
    theorem: str | None
    label: str
    origin: Origin | None = None

    def contains(self, line: int) -> bool:
        return self.start_line <= line <= self.end_line

    def to_dict(self) -> dict:
        d = asdict(self)
        d["origin"] = str(self.origin) if self.origin else None
        return d


@dataclass
class SourceMap:
    spans: list[SourceSpan]

    def innermost(self, line: int, theorem: str | None = None) -> SourceSpan | None:
        """Smallest span containing ``line`` (optionally restricted to a theorem)."""
        best: SourceSpan | None = None
        for s in self.spans:
            if not s.contains(line) or (theorem is not None and s.theorem != theorem):
                continue
            if best is None or (s.end_line - s.start_line) < (best.end_line - best.start_line):
                best = s
        return best

    def theorem_span(self, name: str) -> SourceSpan | None:
        for s in self.spans:
            if s.kind == "theorem" and s.theorem == name:
                return s
        return None

    def audit_line(self, name: str) -> int | None:
        for s in self.spans:
            if s.kind == "axiom_audit" and s.theorem == name:
                return s.start_line
        return None

    def for_theorem(self, name: str) -> list[SourceSpan]:
        return [s for s in self.spans if s.theorem == name]

    def to_list(self) -> list[dict]:
        return [s.to_dict() for s in self.spans]
