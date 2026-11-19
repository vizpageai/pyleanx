"""Citable facts of integration theory (Mathlib theorems), by name.

    because=[facts.markov, "hf"]

Each is a Mathlib declaration at the pinned revision; Lean checks every use.
"""

from __future__ import annotations

from pyleanx.proofs import Name

_BOCHNER = "Mathlib.MeasureTheory.Integral.Bochner.Set"

markov = Name("MeasureTheory.mul_meas_ge_le_integral_of_nonneg", (_BOCHNER,),
              label="Markov's inequality")
set_integral_le = Name("MeasureTheory.setIntegral_le_integral", (_BOCHNER,),
                       label="the integral over a set is at most the integral of a "
                             "nonnegative function")
integral_mono = Name("MeasureTheory.integral_mono", (_BOCHNER,),
                     label="the integral is monotone")
integral_add = Name("MeasureTheory.integral_add", (_BOCHNER,),
                    label="the integral of a sum is the sum of the integrals")
abs_integral_le = Name("MeasureTheory.abs_integral_le_integral_abs", (_BOCHNER,),
                       label="|∫ f| ≤ ∫ |f|")

LEMMAS = {"markov": markov, "set_integral_le": set_integral_le, "integral_mono": integral_mono,
          "integral_add": integral_add, "abs_integral_le": abs_integral_le}
