"""Explanations of the usual failures of analysis steps (shown by ``pl.explain_failure``)."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pyleanx.pack import DomainPack

HINTS = (
    (r"Integrable|IntegrableOn|LocallyIntegrable",
     "an integrability condition is missing: cite the hypothesis that f is integrable (or "
     "locally integrable), or state the integrability of the function the step integrates"),
    (r"≠ ⊤|< ⊤|ENNReal",
     "a measure must be finite here: cite the hypothesis that the set has finite measure, "
     "or that it is compact or contained in a set of finite measure"),
    (r"MeasurableSet|Measurable|AEStronglyMeasurable",
     "a measurability condition is missing: cite the measurability of the set or function"),
    (r"Filter\.Tendsto|nhds|atTop",
     "a limit statement did not match: check that the limit is taken at the same point and "
     "in the same direction as in the cited fact"),
    (r"HasDerivAt|deriv|Differentiable",
     "a derivative fact did not match: check differentiability at the point and that the "
     "function is written the same way as in the cited fact"),
)


def register(pack: DomainPack) -> None:
    for pattern, text in HINTS:
        pack.hint(pattern, text)
