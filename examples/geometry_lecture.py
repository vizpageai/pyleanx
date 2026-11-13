"""Helpers for the lecture notebook ``lecture_congruent_triangles.ipynb``.

* figures: small SVG drawings (no plotting library needed) and slider explorers;
* the worked examples and the exercises as PyLeanX theorems;
* ``check``: verify a student's proof with Lean and say which step Lean could not justify.

The exercise *statements* are fixed here; students only write the proof steps. A teacher
can verify every reference solution with ``python examples/geometry_lecture.py``.
"""

from __future__ import annotations

import html
import math
import re
from collections.abc import Callable, Sequence
from typing import Any

from lecture_tools import check as _check

import pyleanx as pl
from pyleanx import geometry as geo

A, B, C, D, M = geo.points("A B C D M")
dist, angle = geo.dist, geo.angle
pi = pl.analysis.pi

# =========================================================================================
# Figures (SVG)
# =========================================================================================

Point = tuple[float, float]
_PALETTE = {"fill1": "#cfe3ff", "fill2": "#ffe0c2", "line": "#1f2937", "mark": "#c2410c",
            "aux": "#6b7280", "label": "#111827"}


def _sub(p: Point, q: Point) -> Point:
    return (p[0] - q[0], p[1] - q[1])


def _len(v: Point) -> float:
    return math.hypot(v[0], v[1])


def measure_angle(pts: dict[str, Point], a: str, b: str, c: str) -> float:
    """∠abc in degrees."""
    u, v = _sub(pts[a], pts[b]), _sub(pts[c], pts[b])
    cos = (u[0] * v[0] + u[1] * v[1]) / (_len(u) * _len(v))
    return math.degrees(math.acos(max(-1.0, min(1.0, cos))))


def measure_dist(pts: dict[str, Point], a: str, b: str) -> float:
    return _len(_sub(pts[a], pts[b]))


def _names(s: str) -> list[str]:
    """Point names in a label: \"BC'\" -> ['B', \"C'\"]."""
    return re.findall(r"[A-Za-z]'*", s)


def draw(pts: dict[str, Point], segments: Sequence[str] = (), *,
         fills: Sequence[tuple[str, str]] = (), ticks: dict[str, int] | None = None,
         arcs: dict[str, int] | None = None, right: Sequence[str] = (),
         dashed: Sequence[str] = (), title: str = "", size: int = 340) -> str:
    """An SVG figure. ``segments``/``dashed``: two-letter names ("AB"); ``fills``:
    (three-letter triangle, colour key); ``ticks``: {"AB": 1} equal-length marks;
    ``arcs``: {"ABC": 1} equal-angle marks at the middle letter; ``right``: right angles."""
    ticks, arcs = ticks or {}, arcs or {}
    xs = [p[0] for p in pts.values()]
    ys = [p[1] for p in pts.values()]
    span = max(max(xs) - min(xs), max(ys) - min(ys), 1e-9)
    pad = 34
    s = (size - 2 * pad) / span
    ox = pad + ((size - 2 * pad) - (max(xs) - min(xs)) * s) / 2
    oy = pad + ((size - 2 * pad) - (max(ys) - min(ys)) * s) / 2

    def T(p: Point) -> Point:  # math (y up) -> svg (y down)
        return (ox + (p[0] - min(xs)) * s, size - (oy + (p[1] - min(ys)) * s))

    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{size}" height="{size + 18}" '
           f'viewBox="0 -18 {size} {size + 18}" style="background:#fff;font-family:sans-serif">']
    if title:
        out.append(f'<text x="{size / 2}" y="-2" text-anchor="middle" font-size="13" '
                   f'fill="{_PALETTE["label"]}">{html.escape(title)}</text>')
    for tri, colour in fills:
        poly = " ".join(f"{T(pts[k])[0]:.1f},{T(pts[k])[1]:.1f}" for k in _names(tri))
        out.append(f'<polygon points="{poly}" fill="{_PALETTE[colour]}" fill-opacity="0.75"/>')
    for seg in segments:
        (x1, y1), (x2, y2) = (T(pts[k]) for k in _names(seg))
        out.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                   f'stroke="{_PALETTE["line"]}" stroke-width="2"/>')
    for seg in dashed:
        (x1, y1), (x2, y2) = (T(pts[k]) for k in _names(seg))
        out.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                   f'stroke="{_PALETTE["aux"]}" stroke-width="1.6" stroke-dasharray="6 4"/>')
    for seg, n in ticks.items():  # n short strokes across the middle of the segment
        p, q = (T(pts[k]) for k in _names(seg))
        mx, my = (p[0] + q[0]) / 2, (p[1] + q[1]) / 2
        dx, dy = q[0] - p[0], q[1] - p[1]
        L = math.hypot(dx, dy) or 1
        ux, uy, nx, ny = dx / L, dy / L, -dy / L, dx / L
        for k in range(n):
            off = (k - (n - 1) / 2) * 5
            cx, cy = mx + ux * off, my + uy * off
            out.append(f'<line x1="{cx - nx * 6:.1f}" y1="{cy - ny * 6:.1f}" '
                       f'x2="{cx + nx * 6:.1f}" y2="{cy + ny * 6:.1f}" '
                       f'stroke="{_PALETTE["mark"]}" stroke-width="2"/>')
    for ang, n in arcs.items():
        a, b, c = (T(pts[k]) for k in _names(ang))
        t1 = math.atan2(a[1] - b[1], a[0] - b[0])
        t2 = math.atan2(c[1] - b[1], c[0] - b[0])
        d = (t2 - t1 + math.pi) % (2 * math.pi) - math.pi
        for k in range(n):
            r = 18 + 5 * k
            x1, y1 = b[0] + r * math.cos(t1), b[1] + r * math.sin(t1)
            x2, y2 = b[0] + r * math.cos(t1 + d), b[1] + r * math.sin(t1 + d)
            sweep = 1 if d > 0 else 0
            out.append(f'<path d="M{x1:.1f},{y1:.1f} A{r},{r} 0 0 {sweep} {x2:.1f},{y2:.1f}" '
                       f'fill="none" stroke="{_PALETTE["mark"]}" stroke-width="1.8"/>')
    for ang in right:
        a, b, c = (T(pts[k]) for k in _names(ang))
        u = (a[0] - b[0], a[1] - b[1])
        v = (c[0] - b[0], c[1] - b[1])
        lu, lv = math.hypot(*u) or 1, math.hypot(*v) or 1
        r = 11
        p1 = (b[0] + u[0] / lu * r, b[1] + u[1] / lu * r)
        p3 = (b[0] + v[0] / lv * r, b[1] + v[1] / lv * r)
        p2 = (p1[0] + v[0] / lv * r, p1[1] + v[1] / lv * r)
        out.append(f'<polyline points="{p1[0]:.1f},{p1[1]:.1f} {p2[0]:.1f},{p2[1]:.1f} '
                   f'{p3[0]:.1f},{p3[1]:.1f}" fill="none" stroke="{_PALETTE["mark"]}" '
                   'stroke-width="1.6"/>')
    cx = sum(T(p)[0] for p in pts.values()) / len(pts)
    cy = sum(T(p)[1] for p in pts.values()) / len(pts)
    for name, p in pts.items():
        x, y = T(p)
        dx, dy = x - cx, y - cy
        L = math.hypot(dx, dy) or 1
        lx, ly = x + dx / L * 15, y + dy / L * 15 + 5
        out.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3" fill="{_PALETTE["line"]}"/>')
        out.append(f'<text x="{lx:.1f}" y="{ly:.1f}" text-anchor="middle" font-size="15" '
                   f'font-weight="bold" fill="{_PALETTE["label"]}">{name}</text>')
    out.append("</svg>")
    return "".join(out)


def _show(svg: str, table: dict[str, float] | None = None) -> None:
    from IPython.display import HTML, display

    rows = ""
    if table:
        rows = "".join(f"<tr><td style='padding:2px 10px'>{html.escape(k)}</td>"
                       f"<td style='padding:2px 10px;text-align:right'>{v:.2f}</td></tr>"
                       for k, v in table.items())
        rows = (f"<table style='font-family:monospace;font-size:14px;border-collapse:collapse'>"
                f"{rows}</table>")
    display(HTML(f"<div style='display:flex;gap:24px;align-items:center;flex-wrap:wrap'>"
                 f"{svg}{rows}</div>"))


def show(svg: str) -> None:
    """Display an SVG figure from :func:`draw`."""
    _show(svg)


def _explore(build: Callable[..., tuple[str, dict[str, float]]], **sliders: Any) -> None:
    """Sliders when ipywidgets is available, otherwise one static picture."""
    try:
        import ipywidgets as w
    except ImportError:  # pragma: no cover - static fallback
        _show(*build(**{k: v[0] for k, v in sliders.items()}))
        return
    controls = {k: w.FloatSlider(value=v[0], min=v[1], max=v[2], step=v[3], description=k,
                                 continuous_update=True) for k, v in sliders.items()}
    out = w.interactive_output(lambda **kw: _show(*build(**kw)), controls)
    from IPython.display import display

    display(w.VBox([w.HBox(list(controls.values())), out]))


# --- the figures of this lecture ---------------------------------------------------------

def kite_points(spread: float = 35.0, side: float = 4.0, diag: float = 6.0) -> dict[str, Point]:
    """A = vertex, C on the axis; B and D make equal angles ``spread`` with AC."""
    t = math.radians(spread)
    return {"A": (0.0, 0.0), "C": (diag, 0.0),
            "B": (side * math.cos(t), side * math.sin(t)),
            "D": (side * math.cos(t), -side * math.sin(t))}


def figure_kite(spread: float = 35.0, side: float = 4.0) -> str:
    pts = kite_points(spread, side)
    return draw(pts, ["AB", "AD", "BC", "DC", "AC"], fills=[("ABC", "fill1"), ("ADC", "fill2")],
                ticks={"AB": 1, "AD": 1}, arcs={"BAC": 1, "CAD": 1},
                title="AB = AD, ∠BAC = ∠DAC")


def explore_kite() -> None:
    def build(spread: float, side: float) -> tuple[str, dict[str, float]]:
        pts = kite_points(spread, side)
        return figure_kite(spread, side), {
            "AB": measure_dist(pts, "A", "B"), "AD": measure_dist(pts, "A", "D"),
            "∠BAC (°)": measure_angle(pts, "B", "A", "C"),
            "∠DAC (°)": measure_angle(pts, "D", "A", "C"),
            "BC": measure_dist(pts, "B", "C"), "DC": measure_dist(pts, "D", "C")}
    _explore(build, spread=(35.0, 5.0, 85.0, 1.0), side=(4.0, 1.0, 9.0, 0.1))


def isosceles_points(apex: float = 4.0, half_base: float = 2.5) -> dict[str, Point]:
    return {"A": (0.0, apex), "B": (-half_base, 0.0), "C": (half_base, 0.0), "M": (0.0, 0.0)}


def figure_isosceles(apex: float = 4.0, half_base: float = 2.5, *, right_at_m: bool = True,
                     apex_arcs: bool = False) -> str:
    pts = isosceles_points(apex, half_base)
    return draw(pts, ["AB", "AC", "BC", "AM"], fills=[("ABM", "fill1"), ("ACM", "fill2")],
                ticks={"AB": 2, "AC": 2, "BM": 1, "MC": 1},
                arcs={"BAM": 1, "MAC": 1} if apex_arcs else {},
                right=["AMC"] if right_at_m else [], title="AB = AC, M the midpoint of BC")


def explore_isosceles() -> None:
    def build(height: float, half_base: float) -> tuple[str, dict[str, float]]:
        pts = isosceles_points(height, half_base)
        return figure_isosceles(height, half_base, right_at_m=False, apex_arcs=True), {
            "AB": measure_dist(pts, "A", "B"), "AC": measure_dist(pts, "A", "C"),
            "∠AMB (°)": measure_angle(pts, "A", "M", "B"),
            "∠AMC (°)": measure_angle(pts, "A", "M", "C"),
            "∠BAM (°)": measure_angle(pts, "B", "A", "M"),
            "∠CAM (°)": measure_angle(pts, "C", "A", "M")}
    _explore(build, height=(4.0, 0.5, 8.0, 0.1), half_base=(2.5, 0.5, 6.0, 0.1))


def bowtie_points(turn: float = 50.0, ad: float = 6.0, bc: float = 4.0) -> dict[str, Point]:
    """AD and BC cross at their common midpoint M (the origin)."""
    t = math.radians(turn)
    return {"A": (-ad / 2, 0.0), "D": (ad / 2, 0.0), "M": (0.0, 0.0),
            "B": (-bc / 2 * math.cos(t), bc / 2 * math.sin(t)),
            "C": (bc / 2 * math.cos(t), -bc / 2 * math.sin(t))}


def figure_bowtie(turn: float = 50.0, ad: float = 6.0, bc: float = 4.0) -> str:
    pts = bowtie_points(turn, ad, bc)
    return draw(pts, ["AD", "BC", "AB", "DC"], fills=[("AMB", "fill1"), ("DMC", "fill2")],
                ticks={"AM": 1, "MD": 1, "BM": 2, "MC": 2}, arcs={"AMB": 1, "DMC": 1},
                title="AD and BC bisect each other at M")


def explore_bowtie() -> None:
    def build(turn: float, bc: float) -> tuple[str, dict[str, float]]:
        pts = bowtie_points(turn, 6.0, bc)
        return figure_bowtie(turn, 6.0, bc), {
            "∠AMB (°)": measure_angle(pts, "A", "M", "B"),
            "∠DMC (°)": measure_angle(pts, "D", "M", "C"),
            "AB": measure_dist(pts, "A", "B"), "DC": measure_dist(pts, "D", "C")}
    _explore(build, turn=(50.0, 10.0, 170.0, 1.0), bc=(4.0, 1.0, 9.0, 0.1))


def shared_side_points(b_angle: float = 50.0, c_angle: float = 60.0) -> dict[str, Point]:
    """Triangles ABC and DBC on opposite sides of BC with equal angles at B and at C."""
    tb, tc = math.radians(b_angle), math.radians(c_angle)
    base = 6.0
    # apex where the rays from B (angle tb) and from C (angle pi - tc) meet
    r = base * math.sin(tc) / math.sin(tb + tc)
    ax, ay = r * math.cos(tb), r * math.sin(tb)
    return {"B": (0.0, 0.0), "C": (base, 0.0), "A": (ax, ay), "D": (ax, -ay)}


def figure_shared_side(b_angle: float = 50.0, c_angle: float = 60.0) -> str:
    pts = shared_side_points(b_angle, c_angle)
    return draw(pts, ["AB", "AC", "DB", "DC", "BC"], fills=[("ABC", "fill1"), ("DBC", "fill2")],
                arcs={"ABC": 1, "CBD": 1, "BCA": 2, "DCB": 2},
                title="∠ABC = ∠DBC, ∠BCA = ∠BCD")


def explore_shared_side() -> None:
    def build(angle_B: float, angle_C: float) -> tuple[str, dict[str, float]]:
        pts = shared_side_points(angle_B, angle_C)
        return figure_shared_side(angle_B, angle_C), {
            "AB": measure_dist(pts, "A", "B"), "DB": measure_dist(pts, "D", "B"),
            "AC": measure_dist(pts, "A", "C"), "DC": measure_dist(pts, "D", "C")}
    _explore(build, angle_B=(50.0, 10.0, 120.0, 1.0), angle_C=(60.0, 10.0, 120.0, 1.0))


def figure_isosceles_right() -> str:
    pts = {"B": (0.0, 0.0), "A": (0.0, 4.0), "C": (4.0, 0.0)}
    return draw(pts, ["AB", "BC", "CA"], fills=[("ABC", "fill1")], ticks={"BA": 1, "BC": 1},
                right=["ABC"], arcs={"BAC": 1, "BCA": 1}, title="BA = BC, ∠ABC = 90°")


# =========================================================================================
# Theorems: worked examples, exercises (statements fixed; students write the steps)
# =========================================================================================

def kite(*steps: pl.Tactic) -> pl.Theorem:
    """Worked example 1 (SAS)."""
    return pl.Theorem(
        "kite_sides", [A, B, C, D],
        assumptions={"hAB": dist(A, B) == dist(A, D), "hA": angle(B, A, C) == angle(D, A, C)},
        conclusion=dist(B, C) == dist(D, C), proof=pl.proof(*steps) if steps else None)


def isosceles_median(*steps: pl.Tactic) -> pl.Theorem:
    """Worked example 2 (SSS + CPCTC + a straight angle)."""
    return pl.Theorem(
        "isosceles_median_perpendicular", [A, B, C, M],
        assumptions={"hABC": geo.triangle(A, B, C), "hiso": dist(A, B) == dist(A, C),
                     "hM": geo.is_midpoint(M, B, C)},
        conclusion=geo.right_angle(A, M, B), proof=pl.proof(*steps) if steps else None)


def exercise_1(*steps: pl.Tactic) -> pl.Theorem:
    """Segments AD and BC bisect each other at M. Prove AB = DC."""
    return pl.Theorem(
        "bisecting_segments", [A, B, C, D, M],
        assumptions={"hAD": geo.is_midpoint(M, A, D), "hBC": geo.is_midpoint(M, B, C),
                     "hA_D": A != D, "hB_C": B != C},
        conclusion=dist(A, B) == dist(D, C), proof=pl.proof(*steps) if steps else None)


def exercise_2(*steps: pl.Tactic) -> pl.Theorem:
    """In isosceles ABC (AB = AC), the median AM bisects the apex angle."""
    return pl.Theorem(
        "median_bisects_apex_angle", [A, B, C, M],
        assumptions={"hiso": dist(A, B) == dist(A, C), "hM": geo.is_midpoint(M, B, C)},
        conclusion=angle(B, A, M) == angle(C, A, M), proof=pl.proof(*steps) if steps else None)


def exercise_3(*steps: pl.Tactic) -> pl.Theorem:
    """Triangles ABC and DBC share BC, with equal angles at B and at C. Prove AB = DB."""
    return pl.Theorem(
        "shared_side_asa", [A, B, C, D],
        assumptions={"hABC": geo.triangle(A, B, C), "hB": angle(A, B, C) == angle(D, B, C),
                     "hC": angle(B, C, A) == angle(B, C, D)},
        conclusion=dist(A, B) == dist(D, B), proof=pl.proof(*steps) if steps else None)


def exercise_4(*steps: pl.Tactic) -> pl.Theorem:
    """The base angles of an isosceles right triangle are 45°."""
    return pl.Theorem(
        "isosceles_right_triangle_base_angles", [A, B, C],
        assumptions={"hABC": geo.triangle(A, B, C), "hright": geo.right_angle(A, B, C),
                     "hiso": dist(B, A) == dist(B, C)},
        conclusion=angle(B, A, C) == pi() / 4, proof=pl.proof(*steps) if steps else None)


EXERCISES = {1: exercise_1, 2: exercise_2, 3: exercise_3, 4: exercise_4}


def _solutions() -> dict[Any, list[pl.Tactic]]:
    claim, conclude = pl.claim, pl.conclude
    return {
        "kite": [
            claim(dist(B, A) == dist(D, A), because=geo.dist_comm),
            claim(geo.congruent((B, A, C), (D, A, C)), because=geo.sas,
                  note="SAS: BA = DA, ∠BAC = ∠DAC, AC = AC"),
            claim(dist(C, B) == dist(C, D), because=geo.cpctc_ca),
            conclude(because=geo.dist_comm),
        ],
        "isosceles_median": [
            claim(dist(B, M) == dist(C, M), because=geo.midpoint_equal_halves),
            claim(geo.congruent((B, M, A), (C, M, A)), because=geo.sss,
                  note="SSS: BM = CM, MA = MA, AB = AC"),
            claim(angle(B, M, A) == angle(C, M, A), because=geo.cpctc_angle_b),
            claim(B != C, because=geo.distinct_bc("hABC")),
            claim(angle(B, M, C) == pi(), because=geo.midpoint_straight),
            claim(angle(A, M, B) + angle(A, M, C) == pi(), because=geo.linear_pair),
            conclude(because=geo.angle_comm, note="two equal angles adding up to 180°"),
        ],
        1: [
            claim(angle(A, M, D) == pi(), because=geo.midpoint_straight),
            claim(angle(B, M, C) == pi(), because=geo.midpoint_straight),
            claim(angle(A, M, B) == angle(D, M, C), because=geo.vertical_angles),
            claim(dist(A, M) == dist(D, M), because=geo.midpoint_equal_halves),
            claim(dist(B, M) == dist(C, M), because=geo.midpoint_equal_halves),
            claim(dist(M, B) == dist(M, C), because=geo.dist_comm),
            claim(geo.congruent((A, M, B), (D, M, C)), because=geo.sas,
                  note="SAS: AM = DM, ∠AMB = ∠DMC, MB = MC"),
            claim(dist(B, A) == dist(C, D), because=geo.cpctc_ca),
            conclude(because=geo.dist_comm),
        ],
        2: [
            claim(dist(B, M) == dist(C, M), because=geo.midpoint_equal_halves),
            claim(geo.congruent((B, M, A), (C, M, A)), because=geo.sss,
                  note="SSS: BM = CM, MA = MA, AB = AC"),
            claim(angle(M, A, B) == angle(M, A, C), because=geo.cpctc_angle_c),
            conclude(because=geo.angle_comm),
        ],
        3: [
            claim(geo.congruent((A, B, C), (D, B, C)), because=geo.asa,
                  note="ASA: ∠ABC = ∠DBC, BC = BC, ∠BCA = ∠BCD"),
            conclude(because=geo.cpctc_ab),
        ],
        4: [
            claim(angle(B, A, C) == angle(B, C, A), because=geo.isosceles_base_angles),
            claim(A != B, because=geo.distinct_ab("hABC")),
            claim(angle(A, B, C) + angle(B, C, A) + angle(C, A, B) == pi(),
                  because=geo.angle_sum),
            conclude(because=geo.angle_comm, note="2·∠BAC + 90° = 180°"),
        ],
    }


def solution(key: Any) -> pl.Theorem:
    """A reference solution: ``solution(1)`` … ``solution(4)``, ``"kite"``,
    ``"isosceles_median"``."""
    build = {"kite": kite, "isosceles_median": isosceles_median, **EXERCISES}[key]
    return build(*_solutions()[key])


def all_solutions() -> list[pl.Theorem]:
    return [solution(k) for k in _solutions()]


# =========================================================================================
# Checking a student's proof
# =========================================================================================

_CPCTC = ("Check which parts CPCTC gives: in △abc ≅ △a'b'c', `cpctc_ab` gives ab = a'b', "
          "`cpctc_bc` gives bc = b'c', `cpctc_ca` gives ca = c'a'.")


def check(thm: pl.Theorem | None, *, timeout: float = 1800) -> Any:
    """Check a proof with Lean and show the result as a readable proof (see
    :func:`lecture_tools.check`)."""
    return _check(thm, timeout=timeout,
                  hint="Check that the statement of the step is really true *here* (watch the "
                       "order of the letters: ∠BAC is the angle at A), and that the cited fact "
                       "and the earlier steps give it.",
                  timeout_hint=_CPCTC)


def show_solution(key: Any) -> Any:
    """Show (and check) a reference solution."""
    return check(solution(key))


if __name__ == "__main__":
    import sys

    sols = all_solutions()
    results = pl.verify_all(sols, timeout=1800)
    ok = True
    for thm, res in zip(sols, results, strict=True):
        print(thm.prose(res), "\n")
        ok = ok and res.verified
    sys.exit(0 if ok else 1)
