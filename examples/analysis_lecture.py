"""Helpers for the lecture notebook ``lecture_real_analysis.ipynb``.

* the statements of the worked examples and exercises (students write only the proofs);
* reference solutions, every one checked by Lean (``python examples/analysis_lecture.py``);
* figures: sequences with an ε-band and functions with an ε–δ window, as SVG, with sliders;
* ``check`` (shared with the geometry lecture): verify a proof and name the failing step.
"""

from __future__ import annotations

import html
from collections.abc import Callable, Sequence
from typing import Any

from lecture_tools import check as check  # noqa: PLC0414 - re-exported for the notebook

import pyleanx as pl
from pyleanx import analysis as an

Seq = pl.Fn(pl.Nat, pl.Real)
Fun = pl.Fn(pl.Real, pl.Real)
a, b = pl.symbols("a b", Seq)
f = pl.symbol("f", Fun)
p = pl.symbol("p", Fun)
phi = pl.symbol("φ", pl.Fn(pl.Nat, pl.Nat))
L, L2, eps, x, x0, c = pl.symbols("L L' ε x x₀ c", pl.Real)
n, m, N, N1, N2 = pl.symbols("n m N N₁ N₂", pl.Nat)


def R(k: object) -> pl.Expr:
    """A natural number as a real number (``(n : ℝ)``)."""
    return pl.cast(k, pl.Real)


# -----------------------------------------------------------------------------------------
# The definitions, written out (used in `suffices` steps and in claims)
# -----------------------------------------------------------------------------------------

def eps_N(term: Callable[[Any], Any], limit: object) -> pl.Expr:
    """∀ ε > 0, ∃ N, ∀ n ≥ N, |term(n) − limit| < ε."""
    e = pl.symbol("ε", pl.Real)
    k, j = pl.symbols("N n", pl.Nat)
    return pl.Forall(e, pl.Implies(e > 0, pl.Exists(k, pl.Forall(
        j, pl.Implies(j >= k, pl.abs(term(j) - limit) < e)))))


def eventually_close(N_: object, term: Callable[[Any], Any], limit: object,
                     bound: object) -> pl.Expr:
    """∀ n ≥ N, |term(n) − limit| < bound."""
    j = pl.symbol("n", pl.Nat)
    return pl.Forall(j, pl.Implies(j >= N_, pl.abs(term(j) - limit) < bound))


def eps_delta(fx: Callable[[Any], Any], at: object) -> pl.Expr:
    """∀ ε > 0, ∃ δ, δ > 0 ∧ ∀ x, |x − x₀| < δ → |f(x) − f(x₀)| < ε."""
    e, d, t = pl.symbols("ε δ x", pl.Real)
    return pl.Forall(e, pl.Implies(e > 0, pl.Exists(d, pl.And(d > 0, pl.Forall(
        t, pl.Implies(pl.abs(t - at) < d, pl.abs(fx(t) - fx(at)) < e))))))


def cauchy_eps(term: Callable[[Any], Any]) -> pl.Expr:
    """∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |term(m) − term(n)| < ε."""
    e = pl.symbol("ε", pl.Real)
    k, i, j = pl.symbols("N m n", pl.Nat)
    return pl.Forall(e, pl.Implies(e > 0, pl.Exists(k, pl.Forall(i, pl.Implies(
        i >= k, pl.Forall(j, pl.Implies(j >= k, pl.abs(term(i) - term(j)) < e)))))))


def _proof(steps: Sequence[pl.Tactic]) -> pl.Tactic | None:
    return pl.proof(*steps) if steps else None


# =========================================================================================
# Statements
# =========================================================================================

def one_over_n(*steps: pl.Tactic) -> pl.Theorem:
    """Example 1: 1/(n+1) → 0, from the definition."""
    return pl.Theorem("one_over_n_tends_to_zero", [],
                      conclusion=an.tendsto(pl.fun(lambda n: 1 / (R(n) + 1), pl.Nat), 0),
                      proof=_proof(steps))


def limits_unique(*steps: pl.Tactic) -> pl.Theorem:
    """Example 2: a sequence has at most one limit (proof by contradiction)."""
    return pl.Theorem("limits_are_unique", [a, L, L2],
                      assumptions={"hL": an.tendsto(a, L), "hL'": an.tendsto(a, L2)},
                      conclusion=L == L2, proof=_proof(steps))


def linear_continuous(*steps: pl.Tactic) -> pl.Theorem:
    """Example 3: f(x) = 3x + 1 is continuous at every x₀ (ε–δ)."""
    t = pl.symbol("x", pl.Real)
    return pl.Theorem("three_x_plus_one_continuous", [f, x0],
                      assumptions={"hf": pl.Forall(t, f(t) == 3 * t + 1)},
                      conclusion=an.continuous_at(f, x0), proof=_proof(steps))


def bounded_cauchy_subsequence(*steps: pl.Tactic) -> pl.Theorem:
    """Example 4: every bounded sequence has a Cauchy subsequence (citing big theorems)."""
    M = pl.symbol("M", pl.Real)
    k = pl.symbol("n", pl.Nat)
    return pl.Theorem(
        "bounded_sequence_has_cauchy_subsequence", [a, M],
        assumptions={"hM": pl.Forall(k, pl.abs(a(k)) <= M)},
        conclusion=pl.Exists(phi, pl.And(an.strictly_increasing(phi),
                                         an.cauchy(pl.fun(lambda n: a(phi(n)), pl.Nat)))),
        proof=_proof(steps))


def exercise_1(*steps: pl.Tactic) -> pl.Theorem:
    """If aₙ → L then aₙ₊₁ → L."""
    return pl.Theorem("shifted_sequence_limit", [a, L],
                      assumptions={"hL": an.tendsto(a, L)},
                      conclusion=an.tendsto(pl.fun(lambda n: a(n + 1), pl.Nat), L),
                      proof=_proof(steps))


def exercise_2(*steps: pl.Tactic) -> pl.Theorem:
    """If aₙ → L and L > 0, then aₙ > 0 for all large n."""
    k = pl.symbol("n", pl.Nat)
    return pl.Theorem("eventually_positive", [a, L],
                      assumptions={"hL": an.tendsto(a, L), "hpos": L > 0},
                      conclusion=pl.Exists(N, pl.Forall(k, pl.Implies(k >= N, a(k) > 0))),
                      proof=_proof(steps))


def exercise_3(*steps: pl.Tactic) -> pl.Theorem:
    """x³ + x − 1 has a root in [0, 1] (intermediate value theorem)."""
    return pl.Theorem("cubic_has_root", [],
                      conclusion=pl.Exists(c, pl.And(0 <= c, c <= 1, c**3 + c - 1 == 0)),
                      proof=_proof(steps))


def exercise_4(*steps: pl.Tactic) -> pl.Theorem:
    """A convergent sequence is Cauchy (the ε/2 argument)."""
    return pl.Theorem("convergent_is_cauchy", [a, L],
                      assumptions={"hL": an.tendsto(a, L)},
                      conclusion=an.cauchy(a), proof=_proof(steps))


EXERCISES = {1: exercise_1, 2: exercise_2, 3: exercise_3, 4: exercise_4}
EXAMPLES = {"one_over_n": one_over_n, "limits_unique": limits_unique,
            "linear_continuous": linear_continuous,
            "bounded_cauchy_subsequence": bounded_cauchy_subsequence}


# =========================================================================================
# Reference solutions (each checked by Lean)
# =========================================================================================

def _solutions() -> dict[Any, list[pl.Tactic]]:
    claim, conclude, chain = pl.claim, pl.conclude, pl.chain
    M = pl.max(N1, N2)
    third = pl.symbol("x", pl.Real)
    return {
        "one_over_n": [
            pl.suffices(eps_N(lambda k: 1 / (R(k) + 1), 0), because=an.tendsto_iff),
            pl.fix(eps, assume={"hε": eps > 0}),
            pl.choose(N, such_that=1 / eps < R(N), because=an.archimedean, names="hN"),
            pl.take(N),
            pl.fix(n, assume={"hn": n >= N}),
            claim(R(N) <= R(n), because="hn", note="n ≥ N"),
            claim(1 / eps < R(n) + 1, note="1/ε < N ≤ n < n + 1"),
            claim(1 / (R(n) + 1) < eps, because=an.reciprocal_lt),
            claim(1 / (R(n) + 1) > 0, name="hpos"),
            chain(pl.abs(1 / (R(n) + 1) - 0),
                  ("=", pl.abs(1 / (R(n) + 1))),
                  ("=", 1 / (R(n) + 1), [an.abs_of_pos, "hpos"]),
                  ("<", eps)),
        ],
        "limits_unique": [
            claim(eps_N(a, L), because=[an.tendsto_iff, "hL"], name="hL_eps"),
            claim(eps_N(a, L2), because=[an.tendsto_iff, "hL'"], name="hL'_eps"),
            pl.suppose_not(L != L2, name="hne"),
            claim(pl.abs(L - L2) > 0, because=an.abs_pos),
            pl.choose(N1, such_that=eventually_close(N1, a, L, pl.abs(L - L2) / 2),
                      because="hL_eps", names="hN₁", note="the definition with ε = |L − L'|/2"),
            pl.choose(N2, such_that=eventually_close(N2, a, L2, pl.abs(L - L2) / 2),
                      because="hL'_eps", names="hN₂", note="the definition with ε = |L − L'|/2"),
            claim(pl.abs(a(M) - L) < pl.abs(L - L2) / 2, because="hN₁",
                  note="max(N₁, N₂) ≥ N₁"),
            claim(pl.abs(a(M) - L2) < pl.abs(L - L2) / 2, because="hN₂",
                  note="max(N₁, N₂) ≥ N₂"),
            chain(pl.abs(L - L2),
                  ("=", pl.abs((L - a(M)) + (a(M) - L2)), None, "add and subtract"),
                  ("<=", pl.abs(L - a(M)) + pl.abs(a(M) - L2), an.triangle_inequality),
                  ("<", pl.abs(L - L2) / 2 + pl.abs(L - L2) / 2, an.abs_sub_comm),
                  ("=", pl.abs(L - L2))),
            conclude(note="|L − L'| < |L − L'| is impossible"),
        ],
        "linear_continuous": [
            pl.suffices(eps_delta(f, x0), because=an.continuous_at_iff),
            pl.fix(eps, assume={"hε": eps > 0}),
            pl.take(eps / 3, such_that=eps / 3 > 0),
            pl.fix(third, assume={"hx": pl.abs(third - x0) < eps / 3}),
            chain(pl.abs(f(third) - f(x0)),
                  ("=", pl.abs(3 * (third - x0)), "hf", "f(x) = 3x + 1"),
                  ("=", 3 * pl.abs(third - x0), [an.abs_mul, an.abs_of_pos]),
                  ("<", 3 * (eps / 3)),
                  ("=", eps)),
        ],
        "bounded_cauchy_subsequence": [
            pl.choose([phi, L], such_that=pl.And(
                an.strictly_increasing(phi),
                an.tendsto(pl.fun(lambda n: a(phi(n)), pl.Nat), L)),
                because=[an.bolzano_weierstrass, "hM"], names="hφ hlim"),
            pl.take(phi, such_that=an.strictly_increasing(phi), because="hφ"),
            conclude(because=[an.convergent_cauchy, "hlim"]),
        ],
        1: [
            claim(eps_N(a, L), because=[an.tendsto_iff, "hL"], name="hL_eps"),
            pl.suffices(eps_N(lambda k: a(k + 1), L), because=an.tendsto_iff),
            pl.fix(eps, assume={"hε": eps > 0}),
            pl.choose(N, such_that=eventually_close(N, a, L, eps), because="hL_eps",
                      names="hN"),
            pl.take(N),
            pl.fix(n, assume={"hn": n >= N}),
            conclude(because="hN", note="n + 1 ≥ N"),
        ],
        2: [
            claim(eps_N(a, L), because=[an.tendsto_iff, "hL"], name="hL_eps"),
            pl.choose(N, such_that=eventually_close(N, a, L, L / 2), because="hL_eps",
                      names="hN", note="the definition with ε = L/2"),
            pl.take(N),
            pl.fix(n, assume={"hn": n >= N}),
            claim(pl.abs(a(n) - L) < L / 2, because="hN", note="by the choice of N"),
            claim(pl.And(-(L / 2) < a(n) - L, a(n) - L < L / 2), because=an.abs_lt),
            conclude(note="aₙ > L − L/2 = L/2 > 0"),
        ],
        3: [
            pl.let(p, lambda t: t**3 + t - 1),
            claim(an.continuous_on(p, 0, 1), note="polynomials are continuous"),
            claim(p(0) <= 0, note="p(0) = −1"),
            claim(0 <= p(1), note="p(1) = 1"),
            pl.choose(c, such_that=pl.And(0 <= c, c <= 1, p(c) == 0), because=an.ivt,
                      names="h0c hc1 hpc"),
            pl.take(c),
            conclude(note="p(c) = c³ + c − 1"),
        ],
        4: [
            claim(eps_N(a, L), because=[an.tendsto_iff, "hL"], name="hL_eps"),
            pl.suffices(cauchy_eps(a), because=an.cauchy_iff),
            pl.fix(eps, assume={"hε": eps > 0}),
            pl.choose(N, such_that=eventually_close(N, a, L, eps / 2), because="hL_eps",
                      names="hN", note="the definition with ε/2"),
            pl.take(N),
            pl.fix(m, assume={"hm": m >= N}),
            pl.fix(n, assume={"hn": n >= N}),
            claim(pl.abs(a(m) - L) < eps / 2, because="hN", note="m ≥ N"),
            claim(pl.abs(a(n) - L) < eps / 2, because="hN", note="n ≥ N"),
            chain(pl.abs(a(m) - a(n)),
                  ("=", pl.abs((a(m) - L) + (L - a(n))), None, "add and subtract"),
                  ("<=", pl.abs(a(m) - L) + pl.abs(L - a(n)), an.triangle_inequality),
                  ("<", eps / 2 + eps / 2, an.abs_sub_comm),
                  ("=", eps)),
        ],
    }


def solution(key: Any) -> pl.Theorem:
    """A reference solution: ``solution(1)`` … ``solution(4)`` or an example's name."""
    return {**EXAMPLES, **EXERCISES}[key](*_solutions()[key])


def all_solutions() -> list[pl.Theorem]:
    return [solution(k) for k in _solutions()]


def show_solution(key: Any) -> Any:
    return check(solution(key))


# =========================================================================================
# Figures (SVG plots, no plotting library needed)
# =========================================================================================

_C = {"axis": "#6b7280", "grid": "#e5e7eb", "band": "#dbeafe", "line": "#1d4ed8",
      "dot": "#111827", "hit": "#16a34a", "miss": "#dc2626", "mark": "#c2410c",
      "box": "#fde68a"}


class _Plot:
    def __init__(self, xr: tuple[float, float], yr: tuple[float, float], w: int = 520,
                 h: int = 300, title: str = "") -> None:
        self.xr, self.yr, self.w, self.h, self.pad = xr, yr, w, h, 36
        self.parts: list[str] = []
        self.title = title

    def X(self, v: float) -> float:
        return self.pad + (v - self.xr[0]) / (self.xr[1] - self.xr[0]) * (self.w - 2 * self.pad)

    def Y(self, v: float) -> float:
        v = max(min(v, self.yr[1] + 10), self.yr[0] - 10)
        return self.h - self.pad - (v - self.yr[0]) / (self.yr[1] - self.yr[0]) * (
            self.h - 2 * self.pad)

    def rect(self, x1: float, x2: float, y1: float, y2: float, colour: str) -> None:
        self.parts.append(f'<rect x="{self.X(x1):.1f}" y="{self.Y(y2):.1f}" '
                          f'width="{self.X(x2) - self.X(x1):.1f}" '
                          f'height="{self.Y(y1) - self.Y(y2):.1f}" fill="{_C[colour]}" '
                          'fill-opacity="0.7"/>')

    def hline(self, y: float, colour: str, dash: bool = False, label: str = "") -> None:
        d = ' stroke-dasharray="5 4"' if dash else ""
        self.parts.append(f'<line x1="{self.X(self.xr[0]):.1f}" y1="{self.Y(y):.1f}" '
                          f'x2="{self.X(self.xr[1]):.1f}" y2="{self.Y(y):.1f}" '
                          f'stroke="{_C[colour]}" stroke-width="1.4"{d}/>')
        if label:
            self.text(self.xr[1], y, label, anchor="end", dy=-4)

    def vline(self, x: float, colour: str, dash: bool = False, label: str = "") -> None:
        d = ' stroke-dasharray="5 4"' if dash else ""
        self.parts.append(f'<line x1="{self.X(x):.1f}" y1="{self.Y(self.yr[0]):.1f}" '
                          f'x2="{self.X(x):.1f}" y2="{self.Y(self.yr[1]):.1f}" '
                          f'stroke="{_C[colour]}" stroke-width="1.4"{d}/>')
        if label:
            self.text(x, self.yr[1], label, dy=-4)

    def dot(self, x: float, y: float, colour: str, r: float = 3.2) -> None:
        self.parts.append(f'<circle cx="{self.X(x):.1f}" cy="{self.Y(y):.1f}" r="{r}" '
                          f'fill="{_C[colour]}"/>')

    def curve(self, fn: Callable[[float], float], colour: str = "line", steps: int = 200) -> None:
        pts = []
        for i in range(steps + 1):
            t = self.xr[0] + (self.xr[1] - self.xr[0]) * i / steps
            pts.append(f"{self.X(t):.1f},{self.Y(fn(t)):.1f}")
        self.parts.append(f'<polyline points="{" ".join(pts)}" fill="none" '
                          f'stroke="{_C[colour]}" stroke-width="2.2"/>')

    def text(self, x: float, y: float, s: str, anchor: str = "middle", dy: float = 0) -> None:
        self.parts.append(f'<text x="{self.X(x):.1f}" y="{self.Y(y) + dy:.1f}" '
                          f'text-anchor="{anchor}" font-size="12" fill="#111827">'
                          f'{html.escape(s)}</text>')

    def svg(self) -> str:
        axes = (f'<line x1="{self.pad}" y1="{self.Y(0):.1f}" x2="{self.w - self.pad}" '
                f'y2="{self.Y(0):.1f}" stroke="{_C["axis"]}"/>'
                if self.yr[0] <= 0 <= self.yr[1] else "")
        if self.xr[0] <= 0 <= self.xr[1]:
            axes += (f'<line x1="{self.X(0):.1f}" y1="{self.pad}" x2="{self.X(0):.1f}" '
                     f'y2="{self.h - self.pad}" stroke="{_C["axis"]}"/>')
        title = (f'<text x="{self.w / 2}" y="16" text-anchor="middle" font-size="13" '
                 f'font-weight="bold">{html.escape(self.title)}</text>' if self.title else "")
        return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{self.h}" '
                f'style="background:#fff;font-family:sans-serif">{title}{axes}'
                f'{"".join(self.parts)}</svg>')


def _display(svg: str, note: str = "") -> None:
    from IPython.display import HTML, display

    extra = f"<div style='font-family:sans-serif;font-size:14px'>{note}</div>" if note else ""
    display(HTML(f"<div style='display:flex;gap:20px;align-items:center;flex-wrap:wrap'>"
                 f"{svg}{extra}</div>"))


def show(svg: str) -> None:
    _display(svg)


def _sliders(build: Callable[..., tuple[str, str]], **spec: Any) -> None:
    try:
        import ipywidgets as w
    except ImportError:  # pragma: no cover - static fallback
        _display(*build(**{k: v[0] for k, v in spec.items()}))
        return
    from IPython.display import display

    controls = {k: w.FloatSlider(value=v[0], min=v[1], max=v[2], step=v[3], description=k,
                                 readout_format=".3f") for k, v in spec.items()}
    out = w.interactive_output(lambda **kw: _display(*build(**kw)), controls)
    display(w.VBox([w.HBox(list(controls.values())), out]))


def figure_sequence(eps_: float = 0.15, terms: int = 30,
                    seq: Callable[[int], float] = lambda k: 1 / (k + 1), limit: float = 0.0,
                    title: str = "aₙ = 1/(n+1) and the ε-band around 0") -> tuple[str, str]:
    """The first terms, the band |y − L| < ε, and the first N after which every term stays."""
    vals = [seq(k) for k in range(terms)]
    lo, hi = min(vals + [limit - eps_]), max(vals + [limit + eps_])
    span = hi - lo or 1
    p = _Plot((-1, terms), (lo - 0.1 * span, hi + 0.1 * span), title=title)
    p.rect(-1, terms, limit - eps_, limit + eps_, "band")
    p.hline(limit, "line", dash=True, label=f"L = {limit:g}")
    first = next((k for k in range(terms) if all(abs(v - limit) < eps_ for v in vals[k:])),
                 None)
    for k, v in enumerate(vals):
        p.dot(k, v, "hit" if first is not None and k >= first else "miss")
    if first is not None:
        p.vline(first - 0.5, "mark", dash=True, label=f"N = {first}")
    note = (f"ε = {eps_:.3f}: every term from <b>n = {first}</b> on lies in the band"
            if first is not None else f"ε = {eps_:.3f}: choose more terms to see N")
    if seq(0) == 1.0 and limit == 0.0:
        note += f"<br>(the proof's choice: any N &gt; 1/ε = {1 / eps_:.2f})"
    return p.svg(), note


def explore_sequence() -> None:
    _sliders(lambda epsilon: figure_sequence(epsilon), epsilon=(0.15, 0.02, 0.6, 0.01))


def figure_eps_delta(eps_: float = 0.6, x0_: float = 1.0) -> tuple[str, str]:
    fn = lambda t: 3 * t + 1  # noqa: E731
    d = eps_ / 3
    p = _Plot((x0_ - 2, x0_ + 2), (fn(x0_) - 5, fn(x0_) + 5),
              title="f(x) = 3x + 1: inside the δ-strip, f stays in the ε-strip")
    p.rect(x0_ - 2, x0_ + 2, fn(x0_) - eps_, fn(x0_) + eps_, "band")
    p.rect(x0_ - d, x0_ + d, fn(x0_) - 5, fn(x0_) + 5, "box")
    p.curve(fn)
    p.vline(x0_ - d, "mark", dash=True)
    p.vline(x0_ + d, "mark", dash=True, label="x₀ ± δ")
    p.hline(fn(x0_) + eps_, "line", dash=True, label="f(x₀) ± ε")
    p.hline(fn(x0_) - eps_, "line", dash=True)
    p.dot(x0_, fn(x0_), "dot")
    return p.svg(), f"ε = {eps_:.3f} &nbsp;⟹&nbsp; δ = ε/3 = {d:.3f}"


def explore_eps_delta() -> None:
    _sliders(lambda epsilon, x0: figure_eps_delta(epsilon, x0),
             epsilon=(0.6, 0.05, 3.0, 0.05), x0=(1.0, -3.0, 3.0, 0.1))


def figure_ivt() -> str:
    fn = lambda t: t**3 + t - 1  # noqa: E731
    p = _Plot((-0.2, 1.2), (-1.4, 1.6), title="p(x) = x³ + x − 1 on [0, 1]")
    p.curve(fn)
    p.dot(0, fn(0), "miss")
    p.dot(1, fn(1), "hit")
    root = 0.6823278038280193
    p.dot(root, 0, "mark", r=4.5)
    p.text(0, fn(0), "p(0) = −1", dy=16)
    p.text(1, fn(1), "p(1) = 1", dy=-8)
    p.text(root, 0, "c ≈ 0.682", dy=-10)
    return p.svg()


def figure_two_limits(gap: float = 1.0) -> str:
    """Why limits are unique: the ε-bands around L and L' with ε = |L − L'|/2 are disjoint."""
    p = _Plot((-1, 20), (-0.8, gap + 0.8), title="ε = |L − L′|/2: the two bands cannot overlap")
    e = gap / 2
    p.rect(-1, 20, -e, e, "band")
    p.rect(-1, 20, gap - e, gap + e, "box")
    p.hline(0, "line", dash=True, label="L")
    p.hline(gap, "mark", dash=True, label="L′")
    for k in range(20):
        p.dot(k, (-1) ** k * 0.7 / (k + 1), "dot")
    return p.svg()


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
