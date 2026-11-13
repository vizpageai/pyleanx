"""Helpers for the lecture notebook ``lecture_harmonic_analysis.ipynb``.

Fourier series and the Fourier transform, written as in Stein–Shakarchi's *Fourier Analysis*
and Tao's harmonic analysis notes, every step checked by Lean (``check``). Statements here;
students write the proofs. ``python examples/harmonic_lecture.py`` re-checks all solutions.
"""

from __future__ import annotations

import cmath
import math
from collections.abc import Sequence
from typing import Any

from analysis_lecture import _display, _Plot, _sliders
from lecture_tools import check as check  # noqa: PLC0414 - re-exported for the notebook

import pyleanx as pl
from pyleanx import complex_analysis as ca
from pyleanx import harmonic as ha

f, g, h = pl.symbols("f g h", ha.CFun)
n = pl.symbol("n", pl.Int)
x, xi = pl.symbols("x ξ", pl.Real)


def R(k: object) -> pl.Expr:
    """An integer as a real number (printed k)."""
    return pl.cast(k, pl.Real)


def Cx(k: object) -> pl.Expr:
    """An integer as a complex number (printed k)."""
    from pyleanx.terms import ascribe

    return ascribe(k, ca.C)


def _proof(steps: Sequence[pl.Tactic]) -> pl.Tactic | None:
    return pl.proof(*steps) if steps else None


# =========================================================================================
# Statements
# =========================================================================================

def decay(*steps: pl.Tactic) -> pl.Theorem:
    """Example 1: smoothness gives decay, |f̂(n)| = |(f′)^(n)| / |n| (integration by parts)."""
    return pl.Theorem(
        "decay_of_coefficients", [f, g, n],
        assumptions={"hd": ha.derivative(f, g), "hg": ha.integrable_on_circle(g),
                     "hper": f(-pl.analysis.pi()) == f(pl.analysis.pi()), "hn": n != 0},
        conclusion=pl.norm(ha.coeff(f, n)) == pl.norm(ha.coeff(g, n)) / pl.abs(R(n)),
        proof=_proof(steps))


def riemann_lebesgue_l2(*steps: pl.Tactic) -> pl.Theorem:
    """Example 2: the Riemann–Lebesgue lemma for L² functions, from Bessel's inequality."""
    return pl.Theorem("riemann_lebesgue_for_L2", [f],
                      assumptions={"hf": ha.L2(f)}, conclusion=ha.coeffs_tend_to_zero(f),
                      proof=_proof(steps))


def uniqueness(*steps: pl.Tactic) -> pl.Theorem:
    """Example 3: a function is determined by its Fourier transform (via inversion)."""
    return pl.Theorem(
        "fourier_uniqueness", [f, g],
        assumptions={"hcf": ha.continuous(f), "hcg": ha.continuous(g),
                     "hf": ha.integrable(f), "hg": ha.integrable(g),
                     "hF": ha.integrable(ha.ft_fun(f)), "hG": ha.integrable(ha.ft_fun(g)),
                     "heq": ha.ft_fun(f) == ha.ft_fun(g)},
        conclusion=pl.Forall(x, f(x) == g(x)), proof=_proof(steps))


def exercise_1(*steps: pl.Tactic) -> pl.Theorem:
    """Two derivatives: |f̂(n)| = |(f″)^(n)| / n²."""
    return pl.Theorem(
        "decay_two_derivatives", [f, g, h, n],
        assumptions={"hdf": ha.derivative(f, g), "hdg": ha.derivative(g, h),
                     "hg": ha.integrable_on_circle(g), "hh": ha.integrable_on_circle(h),
                     "hperf": f(-pl.analysis.pi()) == f(pl.analysis.pi()),
                     "hperg": g(-pl.analysis.pi()) == g(pl.analysis.pi()),
                     "hn": n != 0},
        conclusion=pl.norm(ha.coeff(f, n))
        == pl.norm(ha.coeff(h, n)) / (pl.abs(R(n)) * pl.abs(R(n))),
        proof=_proof(steps))


def exercise_2(*steps: pl.Tactic) -> pl.Theorem:
    """If f ∈ L² and every Fourier coefficient vanishes, then ∫|f|² = 0."""
    k = pl.symbol("n", pl.Int)
    return pl.Theorem(
        "zero_coefficients_zero_energy", [f],
        assumptions={"hf": ha.L2(f), "h0": pl.Forall(k, ha.coeff(f, k) == 0)},
        conclusion=ha.mean_square(f) == 0, proof=_proof(steps))


def exercise_3(*steps: pl.Tactic) -> pl.Theorem:
    """f(0) = ∫ f̂(ξ) dξ (inversion at the origin)."""
    return pl.Theorem(
        "value_at_zero", [f],
        assumptions={"hc": ha.continuous(f), "hf": ha.integrable(f),
                     "hF": ha.integrable(ha.ft_fun(f))},
        conclusion=f(0) == pl.integral(lambda ξ: ha.ft(f, ξ)),
        proof=_proof(steps))


EXERCISES = {1: exercise_1, 2: exercise_2, 3: exercise_3}
EXAMPLES = {"decay": decay, "riemann_lebesgue_l2": riemann_lebesgue_l2,
            "uniqueness": uniqueness}


# =========================================================================================
# Reference solutions
# =========================================================================================

def _decay_steps() -> list[pl.Tactic]:
    claim, chain = pl.claim, pl.chain
    I = ca.I()  # noqa: E741 - the imaginary unit
    return [
        claim(ha.coeff(g, n) == I * Cx(n) * ha.coeff(f, n), because=ha.coeff_derivative,
              note="integration by parts; the boundary terms cancel since f(−π) = f(π)"),
        chain(pl.norm(ha.coeff(g, n)),
              ("=", pl.norm(I * Cx(n) * ha.coeff(f, n)), "step1"),
              ("=", pl.abs(R(n)) * pl.norm(ha.coeff(f, n)), ha.norm_I_mul_int),
              name="habs"),
        claim(pl.abs(R(n)) != 0, because=[ha.abs_int_ne_zero, "hn"]),
        pl.conclude(because=ha.div_of_mul, note="divide by |n| ≠ 0"),
    ]


def _solutions() -> dict[Any, list[pl.Tactic]]:
    claim, conclude, chain = pl.claim, pl.conclude, pl.chain
    example_1 = decay(*_decay_steps())
    return {
        "decay": _decay_steps(),
        "riemann_lebesgue_l2": [
            claim(ha.summable(pl.fun(lambda n: pl.norm(ha.coeff(f, n)) ** 2, pl.Int)),
                  because=ha.bessel_summable),
            claim(ha.tends_to_zero(pl.fun(lambda n: pl.norm(ha.coeff(f, n)) ** 2, pl.Int)),
                  because=ha.terms_tend_to_zero),
            conclude(because=ha.tendsto_zero_of_norm_sq),
        ],
        "uniqueness": [
            pl.fix(x),
            claim(g(x) == ha.ift(ha.ft_fun(g), x), because=ha.inversion, name="hgx"),
            chain(f(x),
                  ("=", ha.ift(ha.ft_fun(f), x), ha.inversion, "Fourier inversion for f"),
                  ("=", ha.ift(ha.ft_fun(g), x), "heq", "f̂ = ĝ"),
                  ("=", g(x), "hgx", "Fourier inversion for g")),
        ],
        1: [
            claim(pl.norm(ha.coeff(f, n)) == pl.norm(ha.coeff(g, n)) / pl.abs(R(n)),
                  because=example_1, note="Example 1 for f"),
            claim(pl.norm(ha.coeff(g, n)) == pl.norm(ha.coeff(h, n)) / pl.abs(R(n)),
                  because=example_1, note="Example 1 for f′"),
            chain(pl.norm(ha.coeff(f, n)),
                  ("=", pl.norm(ha.coeff(g, n)) / pl.abs(R(n)), "step1"),
                  ("=", pl.norm(ha.coeff(h, n)) / pl.abs(R(n)) / pl.abs(R(n)), "step2"),
                  ("=", pl.norm(ha.coeff(h, n)) / (pl.abs(R(n)) * pl.abs(R(n))), ha.div_div)),
        ],
        2: [
            claim(ha.coeff_sq_sum(f) == ha.mean_square(f), because=ha.parseval),
            claim(ha.coeff_sq_sum(f) == 0, because=ha.sum_of_zero_coeffs),
            conclude(),
        ],
        3: [
            chain(f(0),
                  ("=", ha.ift(ha.ft_fun(f), 0), ha.inversion, "Fourier inversion"),
                  ("=", pl.integral(lambda ξ: ha.ft(f, ξ)), ha.ift_at_zero)),
        ],
    }


def solution(key: Any) -> pl.Theorem:
    return {**EXAMPLES, **EXERCISES}[key](*_solutions()[key])


def all_solutions() -> list[pl.Theorem]:
    return [solution(k) for k in _solutions()]


def show_solution(key: Any) -> Any:
    return check(solution(key))


# =========================================================================================
# Figures
# =========================================================================================

def _square(t: float) -> float:
    t = (t + math.pi) % (2 * math.pi) - math.pi
    return 1.0 if t > 0 else -1.0


def _square_partial(t: float, N: int) -> float:
    return 4 / math.pi * sum(math.sin(k * t) / k for k in range(1, N + 1, 2))


def figure_partial_sums(N: int = 9) -> tuple[str, str]:
    """S_N f for the square wave f = sign on (−π, π): convergence and the Gibbs overshoot."""
    N = max(1, int(N))
    p = _Plot((-math.pi, math.pi), (-1.5, 1.5),
              title=f"square wave and its Fourier partial sum S_{N}")
    p.curve(_square, colour="axis", steps=400)
    p.curve(lambda t: _square_partial(t, N), colour="line", steps=600)
    peak = max(_square_partial(math.pi * k / 2000, N) for k in range(1, 1000))
    return p.svg(), (f"N = {N}: max of S_N ≈ <b>{peak:.4f}</b> (overshoot ≈ "
                     f"{(peak - 1) / 2 * 100:.1f}% of the jump; it does not vanish as N → ∞: "
                     "the Gibbs phenomenon)")


def explore_partial_sums() -> None:
    _sliders(lambda N: figure_partial_sums(int(N)), N=(9.0, 1.0, 101.0, 2.0))


def _coeffs(fn: Any, kmax: int, m: int = 2048) -> list[float]:
    """|f̂(k)| for k = 1..kmax by the trapezoid rule on [−π, π]."""
    pts = [-math.pi + 2 * math.pi * j / m for j in range(m)]
    vals = [fn(t) for t in pts]
    out = []
    for k in range(1, kmax + 1):
        s = sum(v * cmath.exp(-1j * k * t) for v, t in zip(vals, pts, strict=True)) / m
        out.append(abs(s))
    return out


def figure_decay(kmax: int = 30) -> str:
    """log |f̂(n)| for a jump (1/n), a corner (1/n²) and a smooth function (fast)."""
    series = {
        "miss": ("square wave: jump ⇒ ~1/n", _coeffs(_square, kmax)),
        "line": ("triangle wave: corner ⇒ ~1/n²", _coeffs(lambda t: abs(t), kmax)),
        "hit": ("e^{cos x}: smooth ⇒ faster than any power", _coeffs(lambda t: math.exp(
            math.cos(t)), kmax)),
    }
    p = _Plot((0, kmax + 1), (-16, 0.5), title="log₁₀ |f̂(n)|: smoothness ⇒ decay")
    for colour, (_, vals) in series.items():
        for k, v in enumerate(vals, start=1):
            if v > 1e-16:
                p.dot(k, math.log10(v), colour, r=2.6)
    y = -9.5
    for colour, (label, _) in series.items():
        p.dot(kmax * 0.42, y, colour, r=3.5)
        p.text(kmax * 0.45, y, label, anchor="start", dy=4)
        y -= 1.6
    return p.svg()


def figure_riemann_lebesgue(freq: float = 8.0) -> tuple[str, str]:
    """f(x) cos(nx) for f(x) = 1 − x²/π²: the oscillation cancels and the integral → 0."""
    fn = lambda t: 1 - t * t / math.pi**2  # noqa: E731
    k = max(0.0, freq)
    p = _Plot((-math.pi, math.pi), (-1.1, 1.1), title=f"f(x)·cos({k:g}x) and f(x)")
    p.curve(fn, colour="axis")
    p.curve(lambda t: fn(t) * math.cos(k * t), colour="line", steps=800)
    m = 4000
    integral = sum(fn(-math.pi + 2 * math.pi * (j + 0.5) / m)
                   * math.cos(k * (-math.pi + 2 * math.pi * (j + 0.5) / m)) for j in range(m))
    integral *= 2 * math.pi / m / (2 * math.pi)
    return p.svg(), (f"(1/2π)∫ f(x) cos({k:g}x) dx ≈ <b>{integral:.5f}</b> "
                     "→ 0 as the frequency grows (Riemann–Lebesgue)")


def explore_riemann_lebesgue() -> None:
    _sliders(lambda frequency: figure_riemann_lebesgue(frequency),
             frequency=(8.0, 0.0, 60.0, 1.0))


def figure_gaussian(a: float = 1.0) -> tuple[str, str]:
    """e^{−πax²} and its Fourier transform a^{−1/2} e^{−πξ²/a}: narrow ↔ wide."""
    p = _Plot((-3, 3), (-0.05, max(1.05, 1 / math.sqrt(a) + 0.05)),
              title="f(x) = e^{−πax²} (dark) and f̂(ξ) = a^{−1/2} e^{−πξ²/a} (blue)")
    p.curve(lambda t: math.exp(-math.pi * a * t * t), colour="dot")
    p.curve(lambda s: math.exp(-math.pi * s * s / a) / math.sqrt(a), colour="line")
    return p.svg(), (f"a = {a:.2f}: the narrower f, the wider f̂ (uncertainty principle); "
                     "a = 1 is the fixed point e^{−πx²}")


def explore_gaussian() -> None:
    _sliders(lambda a: figure_gaussian(a), a=(1.0, 0.1, 6.0, 0.05))


def show(svg: str, note: str = "") -> None:
    _display(svg, note)


if __name__ == "__main__":
    import sys

    sols = all_solutions()
    results = pl.verify_all(sols, timeout=3600)
    ok = True
    for thm, res in zip(sols, results, strict=True):
        print(thm.prose(res), "\n")
        if not res.verified:
            for d in res.errors[:3]:
                print("   ", d.span_label, "|", d.message[:300].replace("\n", " | "))
        ok = ok and res.verified
    sys.exit(0 if ok else 1)
