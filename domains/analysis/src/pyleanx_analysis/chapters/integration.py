"""Chapter: integrals of absolute values and Markov's inequality.

Each theorem is written twice:

* ``*_core`` cites every side condition as a step, as the core alone requires;
* the plain version is the textbook proof; the analysis pack supplies "|f| is integrable"
  and "|f| ≥ 0 almost everywhere" when the cited theorem needs them.

Both are checked by Lean. ``python -m pyleanx_analysis.chapters.integration`` verifies them.
"""

from __future__ import annotations

import pyleanx as pl
from pyleanx import realvar as rv

from .. import facts

f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))
alpha, c, r = pl.symbols("α c r", pl.Real)

#: {x : α ≤ |f(x)|}
level = rv.pred_set(lambda x: alpha <= pl.abs(f(x)), pl.Real)
markov_statement = alpha * rv.measure(level) <= rv.l1_norm(f)

# ---------------------------------------------------------------------------------------
# 1. Markov's inequality: α·|{|f| ≥ α}| ≤ ∫|f|
# ---------------------------------------------------------------------------------------
markov = pl.Theorem(
    "markov_inequality", [f, alpha],
    assumptions={"hf": rv.integrable(f)},
    conclusion=markov_statement,
    proof=pl.proof(pl.conclude(because=facts.markov)),
)

markov_core = pl.Theorem(
    "markov_inequality_core", [f, alpha],
    assumptions={"hf": rv.integrable(f)},
    conclusion=markov_statement,
    proof=pl.proof(
        pl.claim(rv.ae_nonneg(rv.abs_fun(f)), because=[rv.everywhere_ae, rv.abs_nonneg],
                 name="h0"),
        pl.claim(rv.integrable(rv.abs_fun(f)), because=[rv.integrable_abs, "hf"], name="h1"),
        pl.conclude(because=[facts.markov, "h0", "h1"]),
    ),
)

# ---------------------------------------------------------------------------------------
# 2. The integral of |f| over an interval is at most its integral over ℝ
# ---------------------------------------------------------------------------------------
over_interval = pl.integral(lambda x: pl.abs(f(x)), pl.Real, within=rv.interval(c, r))
interval_statement = over_interval <= rv.l1_norm(f)

interval_bound = pl.Theorem(
    "integral_over_interval_le", [f, c, r],
    assumptions={"hf": rv.integrable(f)},
    conclusion=interval_statement,
    proof=pl.proof(pl.conclude(because=facts.set_integral_le)),
)

interval_bound_core = pl.Theorem(
    "integral_over_interval_le_core", [f, c, r],
    assumptions={"hf": rv.integrable(f)},
    conclusion=interval_statement,
    proof=pl.proof(
        pl.claim(rv.integrable(rv.abs_fun(f)), because=[rv.integrable_abs, "hf"], name="h1"),
        pl.claim(rv.ae_nonneg(rv.abs_fun(f)), because=[rv.everywhere_ae, rv.abs_nonneg],
                 name="h0"),
        pl.conclude(because=[facts.set_integral_le, "h1", "h0"]),
    ),
)

THEOREMS = [markov, markov_core, interval_bound, interval_bound_core]

if __name__ == "__main__":
    import sys

    results = pl.verify_all(THEOREMS, timeout=3600)
    for thm, res in zip(THEOREMS, results, strict=True):
        print(thm.prose(res), "\n")
    sys.exit(0 if all(r.verified for r in results) else 1)
