"""Justification rules of analysis: the side conditions a textbook never writes.

"f is integrable, so |f| is integrable"; "|f| ≥ 0 almost everywhere"; "∫|f| ≥ 0"; "a
compact set has finite measure"; "a subset of a set of finite measure has finite
measure"; "an integrable function is integrable on every set". A cited lemma that needs
one of these gets it from the rules below, so the proof does not state it as a step.

Every tactic here was checked against the pinned Mathlib (see the package's tests), and
Lean checks every use: a rule can only fail to apply, never make a step count as proved.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pyleanx.pack import DomainPack

#: integrability, from an integrable or locally integrable hypothesis
INTEGRABILITY = (
    "exact MeasureTheory.Integrable.abs ‹_›",
    "exact MeasureTheory.Integrable.integrableOn ‹_›",
    "exact (MeasureTheory.Integrable.abs ‹_›).integrableOn",
    "exact MeasureTheory.Integrable.intervalIntegrable ‹_›",
    "exact MeasureTheory.LocallyIntegrable.integrableOn_isCompact ‹_› (isCompact_closedBall _ _)",
)
#: nonnegativity of functions almost everywhere, and of integrals
NONNEGATIVITY = (
    "exact Filter.Eventually.of_forall (fun _ => by positivity)",
    "exact MeasureTheory.integral_nonneg (fun _ => by positivity)",
)
#: finiteness of measures
FINITE_MEASURE = (
    "exact MeasureTheory.measure_ne_top_of_subset ‹_› ‹_›",
    "exact IsCompact.measure_lt_top ‹_›",
    "exact (IsCompact.measure_lt_top ‹_›).ne",
    "exact measure_closedBall_lt_top",
    "exact measure_closedBall_lt_top.ne",
    "exact lt_top_iff_ne_top.mpr ‹_›",
)

ALL = INTEGRABILITY + NONNEGATIVITY + FINITE_MEASURE


def register(pack: DomainPack) -> None:
    """Add the rules to ``pack``: as closers of side goals (after the core's cheap ones,
    before ``simp_all``), and as alternatives for a step that states such a condition."""
    pack.rule("cheap_close", 112, INTEGRABILITY + FINITE_MEASURE[:3], name="cheap:side conditions")
    pack.rule("close", 112, ALL, name="close:side conditions")
    pack.rule("step", 205, ALL, name="side conditions")
