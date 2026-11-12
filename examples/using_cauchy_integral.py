"""Using a proved theorem: Cauchy's integral formula computes a contour integral.

    ∮_{|z| = 2} z²/(z − 1) dz = 2πi.

Proof: f(z) = z² is holomorphic (a polynomial) and 1 lies inside the circle, so by
Cauchy's integral formula the integral is 2πi · f(1) = 2πi.

How citing works
----------------
* Cite the theorem *object* (``because=cauchy_integral_formula``), not its name as a
  string. The citation carries the theorem with its proof: the generated Lean file
  contains the cited theorem and its proof first, so Lean re-checks it on every run.
* So a citing theorem is verified only if the cited proof is accepted too. If the cited
  proof is wrong, the citing theorem is rejected; if the cited theorem has no proof,
  PyLeanX refuses to build the Lean file at all.
* A proved theorem can also be stored in a theorem bank with its verification evidence
  and cited later from there (see the end of this file).

Run:  python examples/using_cauchy_integral.py
"""

from __future__ import annotations

from readable_cauchy_integral import cauchy_integral_formula  # the proved theorem

import pyleanx as pl
from pyleanx import complex_analysis as ca

zero, one = pl.ascribe(0, ca.C), pl.ascribe(1, ca.C)
two = pl.real(2)
square = pl.fun(lambda z: z**2, ca.C)

contour_integral = pl.Theorem(
    "contour_integral_z_sq", [],
    conclusion=ca.circle_integral(lambda z: pl.smul(ca.inv(z - one), z**2), zero, two)
    == ca.two_pi_i(),
    proof=pl.proof(
        pl.claim(ca.holomorphic_on(square, ca.closed_ball(zero, two)), name="hf",
                 note="z ↦ z² is a polynomial"),
        pl.claim(ca.mem(one, ca.ball(zero, two)), name="hw", note="|1 − 0| = 1 < 2"),
        pl.chain(ca.circle_integral(lambda z: pl.smul(ca.inv(z - one), z**2), zero, two),
                 ("=", pl.smul(ca.two_pi_i(), one**2), cauchy_integral_formula),
                 ("=", ca.two_pi_i(), None, "1² = 1")),
    ),
)

if __name__ == "__main__":
    # One Lean run checks the formula (cited, with its proof) and this computation.
    result = contour_integral.verify(timeout=1800)
    print(contour_integral.prose(result))
    if not result.verified:
        raise SystemExit(1)

    # Optional: keep the proved formula in a theorem bank and cite it from there later.
    import tempfile
    from pathlib import Path

    bank = pl.TheoremBank(Path(tempfile.mkdtemp()) / "bank.json")
    formula_result = cauchy_integral_formula.verify(timeout=1800)
    bank.add_theorem(cauchy_integral_formula, formula_result, id="cauchy_integral_formula",
                     tags=["complex analysis"])
    loaded = bank.load("cauchy_integral_formula")  # rebuilt exactly; hash-checked
    print("banked and reloaded:", loaded.name, "| evidence:",
          bank.get("cauchy_integral_formula").evidence["axioms"])
