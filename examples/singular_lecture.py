"""Figures for ``lecture_singular_integrals.ipynb`` (the theorems are in singular_integrals.py)."""

from __future__ import annotations

import random

from analysis_lecture import _display, _Plot, _sliders
from lecture_tools import check as check  # noqa: PLC0414 - re-exported for the notebook


def show(svg: str, note: str = "") -> None:
    _display(svg, note)


# -----------------------------------------------------------------------------------------
# Vitali's selection
# -----------------------------------------------------------------------------------------

def _intervals(n: int, seed: int) -> list[tuple[float, float]]:
    rnd = random.Random(seed)
    return [(rnd.uniform(0, 10), rnd.uniform(0.15, 1.3)) for _ in range(n)]


def vitali_select(family: list[tuple[float, float]]) -> list[int]:
    """Greedy selection: largest radius first, skip intervals meeting a chosen one."""
    order = sorted(range(len(family)), key=lambda k: -family[k][1])
    chosen: list[int] = []
    for k in order:
        c, r = family[k]
        if all(abs(c - family[j][0]) > r + family[j][1] for j in chosen):
            chosen.append(k)
    return chosen


def figure_vitali(n: int = 14, seed: int = 3) -> tuple[str, str]:
    fam = _intervals(int(n), int(seed))
    chosen = vitali_select(fam)
    rows = len(fam) + 2
    p = _Plot((-3, 13), (-1.5, rows + 0.5), w=560, h=330,
              title="Vitali: disjoint intervals (orange); their 3× dilates (dashed) cover all")
    for row, (c, r) in enumerate(fam):
        y = rows - 1 - row
        colour = "mark" if row in chosen else "line"
        p.parts.append(f'<line x1="{p.X(c - r):.1f}" y1="{p.Y(y):.1f}" x2="{p.X(c + r):.1f}" '
                       f'y2="{p.Y(y):.1f}" stroke="{"#c2410c" if row in chosen else "#1d4ed8"}" '
                       f'stroke-width="{4 if row in chosen else 2.2}"/>')
        del colour
    for k in chosen:
        c, r = fam[k]
        p.parts.append(f'<line x1="{p.X(c - 3 * r):.1f}" y1="{p.Y(0):.1f}" '
                       f'x2="{p.X(c + 3 * r):.1f}" y2="{p.Y(0):.1f}" stroke="#c2410c" '
                       'stroke-width="2" stroke-dasharray="5 4"/>')
    covered = all(any(abs(fam[i][0] - fam[j][0]) + fam[i][1] <= 3 * fam[j][1] + 1e-12
                      for j in chosen) for i in range(len(fam)))
    total = sum(2 * r for _, r in fam)
    picked = sum(2 * fam[j][1] for j in chosen)
    note = (f"{len(chosen)} of {len(fam)} intervals selected, pairwise disjoint; every interval "
            f"lies in the 3× dilate of a selected one: <b>{covered}</b><br>"
            f"Σ|I| over all = {total:.2f}, over the selected = {picked:.2f}; "
            f"|⋃ I| ≤ 3 Σ_selected |I| = {3 * picked:.2f}")
    return p.svg(), note


def explore_vitali() -> None:
    _sliders(lambda n, seed: figure_vitali(int(n), int(seed)),
             n=(14.0, 2.0, 30.0, 1.0), seed=(3.0, 0.0, 50.0, 1.0))


# -----------------------------------------------------------------------------------------
# The maximal function and the weak-type bound
# -----------------------------------------------------------------------------------------

def _f(x: float) -> float:
    """A sample integrable function: two bumps."""
    return (2.0 if 0 <= x <= 1 else 0.0) + (1.0 if 3 <= x <= 5 else 0.0)


_NORM = 2.0 * 1 + 1.0 * 2  # ‖f‖₁


def _avg(x: float, r: float, m: int = 200) -> float:
    h = 2 * r / m
    return sum(abs(_f(x - r + (k + 0.5) * h)) for k in range(m)) * h / (2 * r)


def maximal(x: float) -> float:
    """Mf(x) = sup over centred intervals of the average of |f| (sampled radii)."""
    radii = [0.02 * 1.15**k for k in range(45)]
    return max(_avg(x, r) for r in radii)


def figure_maximal(alpha: float = 0.6) -> tuple[str, str]:
    xs = [-4 + 14 * k / 280 for k in range(281)]
    mf = [maximal(x) for x in xs]
    p = _Plot((-4, 10), (-0.1, 2.3), w=560, h=300,
              title=f"f (dark), Mf (blue) and the level set {{Mf > {alpha:.2f}}} (yellow)")
    step = xs[1] - xs[0]
    level = [x for x, m in zip(xs, mf, strict=True) if m > alpha]
    for x in level:
        p.rect(x - step / 2, x + step / 2, -0.1, 2.3, "box")
    p.curve(_f, colour="dot", steps=600)
    p.parts.append('<polyline points="' + " ".join(
        f"{p.X(x):.1f},{p.Y(m):.1f}" for x, m in zip(xs, mf, strict=True))
        + '" fill="none" stroke="#1d4ed8" stroke-width="2.2"/>')
    p.hline(alpha, "mark", dash=True, label="α")
    measure = len(level) * step
    return p.svg(), (f"α = {alpha:.2f}: α·|{{Mf > α}}| ≈ <b>{alpha * measure:.2f}</b> ≤ "
                     f"4‖f‖₁ = {4 * _NORM:.0f} (theorem 5)")


def explore_maximal() -> None:
    _sliders(lambda alpha: figure_maximal(alpha), alpha=(0.6, 0.05, 2.0, 0.05))
