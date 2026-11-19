"""PyLeanX Analysis: real and measure-theoretic analysis, as textbook proofs checked by Lean.

A domain package for PyLeanX, separate from its core (like torchvision for torch): it
uses only PyLeanX's public API, and PyLeanX never imports it. Importing it registers the
analysis pack:

    import pyleanx as pl
    import pyleanx_analysis as an

* **Vocabulary**: ``an.real`` (sequences, limits, continuity, derivatives, the classical
  theorems) and ``an.integration`` (Lebesgue measure, integrability, intervals, maximal
  averages), also re-exported here (``an.integrable``, ``an.tendsto``, …).
* **Justification rules** (``pyleanx_analysis.rules``): the side conditions a textbook
  never writes (|f| is integrable, |f| ≥ 0 a.e., ∫|f| ≥ 0, compact sets have finite
  measure, …) are supplied when a cited lemma needs them. They apply only to theorems that
  use measure-theoretic vocabulary.
* **Numeric sanity checks** (``pyleanx_analysis.numeric``): real functions are sampled
  (random smooth functions, or the function a hypothesis defines), and derivatives and
  integrals over intervals are evaluated numerically, so ``thm.sanity_check()`` tries
  analysis statements on examples before Lean runs.
* **Explanations** for the usual failures of analysis steps.

The vocabulary currently lives in the PyLeanX distribution (``pyleanx.analysis``,
``pyleanx.realvar``); this package is its public face and will become its home.
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import analysis as real
from pyleanx import realvar as integration
from pyleanx.analysis import *  # noqa: F403 - the vocabulary of real analysis
from pyleanx.realvar import *  # noqa: F403 - the vocabulary of measure and integration

from . import rules as _rules

__version__ = "0.1.0.dev0"

#: the analysis pack: active in theorems about measure, integrals and integrability
pack = pl.domain_pack(
    "analysis",
    symbols=("MeasureTheory.", "IntervalIntegrable", "Measurable", "MeasurableSet",
             "AEMeasurable", "ENNReal.", "IsCompact"),
)
_rules.register(pack)
pack.facts("pyleanx_analysis.facts", prefix="ana", title="Analysis (pyleanx-analysis)")

from . import hints as _hints  # noqa: E402
from . import numeric as _numeric  # noqa: E402

_hints.register(pack)
_numeric.register(pack)

__all__ = ["integration", "pack", "real", "__version__"]
