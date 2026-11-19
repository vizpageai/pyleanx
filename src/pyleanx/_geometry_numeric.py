"""Plane geometry for the numeric sanity check (registered with :mod:`pyleanx.numeric`).

Points of the plane are sampled at random; distances, angles, betweenness, collinearity,
lines (parallel, perpendicular, incidence) and midpoints are evaluated; and figures are
drawn the way one draws them, so that hypotheses random points almost never meet hold:
a point strictly between A and B goes on the segment, an isosceles apex on a circle, a
right angle's free leg on the perpendicular, a parallelogram's fourth vertex where two
parallels meet, an equilateral apex where two circles meet. Every hypothesis is still
evaluated afterwards; a construction only makes a sample likely to qualify.
"""

from __future__ import annotations

import math
import random
from dataclasses import dataclass
from typing import Any

from .expr import App, Compare, Var
from .numeric import (
    _TOL,
    Construction,
    Unsupported,
    _close,
    _free_uids,
    evaluate,
)
from .pack import DomainPack
from .terms import Apply, Const, TypeTerm

pack = DomainPack("geometry")


def _point(v: Any) -> tuple[float, float]:
    if isinstance(v, tuple) and len(v) == 2:
        return v
    raise Unsupported("not a point")


def _dist(a: Any, b: Any) -> float:
    if isinstance(a, tuple):
        (x1, y1), (x2, y2) = _point(a), _point(b)
        return math.hypot(x1 - x2, y1 - y2)
    return abs(float(a) - float(b))


def _angle(a: Any, b: Any, c: Any) -> float:
    (ax, ay), (bx, by), (cx, cy) = _point(a), _point(b), _point(c)
    u, v = (ax - bx, ay - by), (cx - bx, cy - by)
    nu, nv = math.hypot(*u), math.hypot(*v)
    if nu == 0 or nv == 0:
        return math.pi / 2  # Mathlib's convention for a zero vector
    cos = max(-1.0, min(1.0, (u[0] * v[0] + u[1] * v[1]) / (nu * nv)))
    return math.acos(cos)


def _set_points(e: Any, env: dict[int, Any]) -> list[Any]:
    """The elements of ``insert a (insert b (singleton c))``."""
    if isinstance(e, Apply) and isinstance(e.fn, Const):
        if e.fn.name == "singleton" and len(e.args) == 1:
            return [evaluate(e.args[0], env)]
        if e.fn.name == "insert" and len(e.args) == 2:
            return [evaluate(e.args[0], env), *_set_points(e.args[1], env)]
    raise Unsupported("set")


@dataclass(frozen=True)
class _Line:
    """The line through two points (as a value of the evaluator)."""

    points: tuple[tuple[float, float], ...]

    @property
    def direction(self) -> tuple[float, float]:
        if len(self.points) < 2:
            return (0.0, 0.0)
        (x0, y0), (x1, y1) = self.points[0], self.points[1]
        return (x1 - x0, y1 - y0)


def _line(v: Any) -> _Line:
    if isinstance(v, _Line):
        return v
    raise Unsupported("not a line")


def _zero(u: tuple[float, float]) -> bool:
    return math.hypot(*u) <= _TOL


def _collinear(pts: list[Any]) -> bool:
    ps = [_point(p) for p in pts]
    if len(ps) < 3:
        return True
    (x0, y0) = ps[0]
    for (x1, y1) in ps[1:]:
        for (x2, y2) in ps[1:]:
            if abs((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) > 1e-9:
                return False
    return True


def _between(a: Any, p: Any, b: Any, strict: bool) -> bool:
    (ax, ay), (px, py), (bx, by) = _point(a), _point(p), _point(b)
    if not _collinear([a, p, b]):
        return False
    dx, dy = bx - ax, by - ay
    n = dx * dx + dy * dy
    if n == 0:
        return (px, py) == (ax, ay) and not strict
    t = ((px - ax) * dx + (py - ay) * dy) / n
    if strict:
        return 1e-12 < t < 1 - 1e-12
    return -1e-12 <= t <= 1 + 1e-12


# --- evaluation -----------------------------------------------------------------------
pack.function("dist", _dist)
pack.function("EuclideanGeometry.angle", _angle)
pack.sampler("Point", lambda rng: (rng.uniform(-5, 5), rng.uniform(-5, 5)))


def _betweenness(name: str) -> Any:
    def ev(args: tuple, env: dict[int, Any]) -> Any:
        if len(args) != 4 or not isinstance(args[0], TypeTerm):
            return NotImplemented
        a, p, b = (evaluate(x, env) for x in args[1:])
        return _between(a, p, b, strict=name == "Sbtw")
    return ev


pack.apply("Sbtw", _betweenness("Sbtw"))
pack.apply("Wbtw", _betweenness("Wbtw"))
pack.apply("Collinear", lambda args, env: _collinear(_set_points(args[1], env))
               if len(args) == 2 else NotImplemented)
pack.apply("dist", lambda args, env: _dist(evaluate(args[0], env), evaluate(args[1], env))
               if len(args) == 2 else NotImplemented)
pack.apply("affineSpan", lambda args, env: _Line(tuple(  # line[ℝ, a, b]
    _point(p) for p in _set_points(args[1], env))) if len(args) == 2 else NotImplemented)
pack.apply("AffineSubspace.direction",  # a line stands for its direction here
               lambda args, env: evaluate(args[0], env) if len(args) == 1 else NotImplemented)


def _parallel(args: tuple, env: dict[int, Any]) -> Any:
    if len(args) != 2:
        return NotImplemented
    u, v = _line(evaluate(args[0], env)).direction, _line(evaluate(args[1], env)).direction
    if _zero(u) or _zero(v):
        return _zero(u) and _zero(v)   # two points are parallel; a point and a line not
    return _close(u[0] * v[1] - u[1] * v[0], 0.0)


def _orthogonal(args: tuple, env: dict[int, Any]) -> Any:
    if len(args) != 2:
        return NotImplemented
    u, v = _line(evaluate(args[0], env)).direction, _line(evaluate(args[1], env)).direction
    return _close(u[0] * v[0] + u[1] * v[1], 0.0)


def _member(args: tuple, env: dict[int, Any]) -> Any:
    if len(args) != 2:
        return NotImplemented
    s = evaluate(args[0], env)
    if isinstance(s, _Line):
        return _collinear([*s.points, evaluate(args[1], env)])
    return NotImplemented


def _midpoint(args: tuple, env: dict[int, Any]) -> Any:
    if len(args) != 3 or not isinstance(args[0], TypeTerm):
        return NotImplemented
    (x1, y1), (x2, y2) = _point(evaluate(args[1], env)), _point(evaluate(args[2], env))
    return ((x1 + x2) / 2, (y1 + y2) / 2)


pack.apply("AffineSubspace.Parallel", _parallel)
pack.apply("Submodule.IsOrtho", _orthogonal)
pack.apply("Membership.mem", _member)
pack.apply("midpoint", _midpoint)


# --- drawing the figure ------------------------------------------------------------------
def _line_ends(e: Any) -> tuple[Any, Any] | None:
    """The two point expressions of ``line[ℝ, a, b]``."""
    if (isinstance(e, Apply) and isinstance(e.fn, Const) and e.fn.name == "affineSpan"
            and len(e.args) == 2):
        s = e.args[1]
        if (isinstance(s, Apply) and isinstance(s.fn, Const) and s.fn.name == "insert"
                and isinstance(s.args[1], Apply) and isinstance(s.args[1].fn, Const)
                and s.args[1].fn.name == "singleton"):
            return s.args[0], s.args[1].args[0]
    return None


def _parallel_constraint(h: Any) -> tuple[Var, Any, Any, Any] | None:
    """For ``line(P, Q) ∥ line(R, X)`` (any order) with X a point variable: (X, R, P, Q):
    X lies on the line through R in the direction Q − P."""
    if not (isinstance(h, Apply) and isinstance(h.fn, Const)
            and h.fn.name == "AffineSubspace.Parallel" and len(h.args) == 2):
        return None
    l1, l2 = _line_ends(h.args[0]), _line_ends(h.args[1])
    if l1 is None or l2 is None:
        return None
    for (p, q), (r, x) in ((l1, l2), (l1, l2[::-1]), (l2, l1), (l2, l1[::-1])):
        if isinstance(x, Var) and all(x.uid not in _free_uids(e) for e in (p, q, r)):
            return x, r, p, q
    return None


def _place_on_parallels(hyps: list[Any], env: dict[int, Any], rng: random.Random) -> None:
    """A point on a line parallel to another goes on that parallel through its partner; with
    two such lines (a parallelogram's fourth vertex) it goes where they meet."""
    by_point: dict[int, list[tuple[Var, Any, Any, Any]]] = {}
    for h in hyps:
        c = _parallel_constraint(h)
        if c is not None:
            by_point.setdefault(c[0].uid, []).append(c)
    for uid, cons in by_point.items():
        try:
            lines = []
            for _, r, p, q in cons[:2]:
                (rx, ry), (px, py), (qx, qy) = (_point(evaluate(e, env)) for e in (r, p, q))
                lines.append(((rx, ry), (qx - px, qy - py)))
            if len(lines) == 1:
                (rx, ry), (ux, uy) = lines[0]
                t = rng.choice((-1, 1)) * rng.uniform(0.3, 2.0)
                env[uid] = (rx + t * ux, ry + t * uy)
                continue
            ((ax, ay), (ux, uy)), ((bx, by), (vx, vy)) = lines
            det = ux * vy - uy * vx
            if abs(det) <= _TOL:
                continue
            t = ((bx - ax) * vy - (by - ay) * vx) / det
            env[uid] = (ax + t * ux, ay + t * uy)
        except (Unsupported, ValueError, ZeroDivisionError, OverflowError):
            continue


def _right_angle(h: Any, env: dict[int, Any]) -> tuple[Any, Any, Var] | None:
    """For ``∠PVQ = π/2`` (either side) with Q, or else P, a point variable: (P, V, free)."""
    if not (isinstance(h, Compare) and h.op == "eq"):
        return None
    for ang, other in ((h.lhs, h.rhs), (h.rhs, h.lhs)):
        if not (isinstance(ang, App) and ang.func.lean_name == "EuclideanGeometry.angle"
                and len(ang.args) == 3):
            continue
        if _free_uids(other):
            continue
        try:
            if not _close(float(evaluate(other, env)), math.pi / 2):
                continue
        except (Unsupported, TypeError, ValueError):
            continue
        p, v, q = ang.args
        for a, b in ((p, q), (q, p)):
            if isinstance(b, Var) and b.uid not in _free_uids(a) | _free_uids(v):
                return a, v, b
    return None


def _all_equal_lengths(h: Any) -> list[tuple[Any, Any, Var]]:
    """Every reading of ``|PQ| = |PR|`` as "R on the circle about P through Q"."""
    def ends(e: Any) -> tuple[Any, Any] | None:
        if isinstance(e, App) and e.func.lean_name == "dist" and len(e.args) == 2:
            return e.args[0], e.args[1]
        return None

    if not (isinstance(h, Compare) and h.op == "eq"):
        return []
    left, right = ends(h.lhs), ends(h.rhs)
    if left is None or right is None:
        return []
    out = []
    for a, b in ((left, right), (right, left)):
        for p, q in (a, a[::-1]):
            for p2, r in (b, b[::-1]):
                if (p._key() == p2._key() and isinstance(r, Var)
                        and r.uid not in _free_uids(p) and r.uid not in _free_uids(q)):
                    out.append((p, q, r))
    return out


def _equal_lengths(h: Any, uses: dict[int, int] | None = None) -> tuple[Any, Any, Var] | None:
    """For ``|PQ| = |PR|`` (endpoints in any order, either side) with R a point variable:
    (P, Q, R). Of two candidate R, the one fewer hypotheses mention is moved (so a point
    that also defines others, like A in ``O = midpoint(A, B)``, stays where it is)."""
    found = _all_equal_lengths(h)
    if not found:
        return None
    counts = uses or {}
    return min(found, key=lambda f: counts.get(f[2].uid, 0))


def _circle_meet(c1: tuple[float, float], r1: float, c2: tuple[float, float], r2: float,
                 rng: random.Random) -> tuple[float, float] | None:
    """One of the (at most two) intersections of two circles, chosen at random."""
    d = math.dist(c1, c2)
    if d <= _TOL or d > r1 + r2 or d < abs(r1 - r2):
        return None
    a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
    h = math.sqrt(max(r1 * r1 - a * a, 0.0))
    ux, uy = (c2[0] - c1[0]) / d, (c2[1] - c1[1]) / d
    mx, my = c1[0] + a * ux, c1[1] + a * uy
    s = rng.choice((-1, 1))
    return (mx - s * h * uy, my + s * h * ux)


def _same_pair(eq: tuple[Any, Any, Var] | None, v: Any, p: Any, q: Var) -> bool:
    """Does ``eq`` (from :func:`_equal_lengths`) say |VP| = |VQ|?"""
    if eq is None:
        return False
    centre, a, b = eq
    return (centre._key() == v._key()
            and {a._key(), b._key()} == {p._key(), q._key()})


def _right_angle_shape(h: Any) -> bool:
    return isinstance(h, Compare) and h.op == "eq" and any(
        isinstance(s, App) and s.func.lean_name == "EuclideanGeometry.angle"
        for s in (h.lhs, h.rhs))


class _Figure:
    """The geometry pack's construction hook."""

    def setup(self, c: Construction) -> dict[str, Any]:
        # a point on two circles (|AB| = |AC| and |BA| = |BC|: an equilateral triangle's
        # apex) is placed at one of their intersections; those hypotheses do not move it
        circles: dict[int, list[tuple[int, tuple[Any, Any, Var]]]] = {}
        for i, h in enumerate(c.hyps):
            for eq in _all_equal_lengths(h):
                circles.setdefault(eq[2].uid, []).append((i, eq))
        two = {uid: cs for uid, cs in circles.items()
               if len({x[1][0]._key() for x in cs}) >= 2}
        return {"two_circles": two, "on_two_circles": {i for cs in two.values() for i, _ in cs}}

    def before_pass(self, c: Construction, state: dict[str, Any]) -> None:
        _place_on_parallels(c.hyps, c.env, c.rng)
        for uid, cs in state["two_circles"].items():
            try:
                (_, (c1_, q1_, _)), (_, (c2_, q2_, _)) = cs[0], next(
                    x for x in cs[1:] if x[1][0]._key() != cs[0][1][0]._key())
                c1, q1 = _point(evaluate(c1_, c.env)), _point(evaluate(q1_, c.env))
                c2, q2 = _point(evaluate(c2_, c.env)), _point(evaluate(q2_, c.env))
                hit = _circle_meet(c1, math.dist(c1, q1), c2, math.dist(c2, q2), c.rng)
                if hit is not None:
                    c.env[uid] = hit
                    c.owner[uid] = -1
            except (Unsupported, ValueError, ZeroDivisionError, OverflowError, StopIteration):
                continue

    def first(self, h: Any) -> bool:
        # right angles first: a point that is also equidistant is then placed by both
        return _right_angle_shape(h)

    def place(self, c: Construction, state: dict[str, Any], i: int, h: Any) -> bool:
        env, rng = c.env, c.rng
        if (isinstance(h, Apply) and isinstance(h.fn, Const) and h.fn.name in ("Sbtw", "Wbtw")
                and len(h.args) == 4 and isinstance(h.args[2], Var)):
            a_, p, b_ = h.args[1], h.args[2], h.args[3]
            if c.may_place(p.uid, i):
                a, b = _point(evaluate(a_, env)), _point(evaluate(b_, env))
                t = rng.uniform(0.05, 0.95) if h.fn.name == "Sbtw" else rng.random()
                env[p.uid] = (a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]))
            else:
                # the middle point is already placed (vertical angles: O between A and B,
                # and between C and D): put an end beyond it instead
                for near, far in ((a_, b_), (b_, a_)):
                    if isinstance(far, Var) and c.may_place(far.uid, i):
                        n, m = _point(evaluate(near, env)), _point(env[p.uid])
                        s = rng.uniform(0.3, 2.0)
                        env[far.uid] = (m[0] + s * (m[0] - n[0]), m[1] + s * (m[1] - n[1]))
                        break
            return True
        equal = _equal_lengths(h, c.uses)
        if equal is not None:
            # |PQ| = |PR|: R goes on the circle about P through Q (an isosceles triangle)
            centre, through, free = equal
            if i in state["on_two_circles"] or not c.may_place(free.uid, i):
                return True
            cq, q = _point(evaluate(centre, env)), _point(evaluate(through, env))
            r, phi = math.dist(cq, q), rng.uniform(0, 2 * math.pi)
            env[free.uid] = (cq[0] + r * math.cos(phi), cq[1] + r * math.sin(phi))
            return True
        right = _right_angle(h, env)
        if right is not None:
            # ∠PVQ = 90°: Q goes on the perpendicular to VP at V; at distance |VP| if the
            # legs are also equal (an isosceles right triangle)
            p_, v_, free = right
            if not c.may_place(free.uid, i):
                return True
            px, py = _point(evaluate(p_, env))
            vx, vy = _point(evaluate(v_, env))
            equal_legs = any(_same_pair(_equal_lengths(g, c.uses), v_, p_, free)
                             for g in c.hyps)
            s = rng.choice((-1, 1)) * (1.0 if equal_legs else rng.uniform(0.3, 2.0))
            env[free.uid] = (vx - s * (py - vy), vy + s * (px - vx))
            return True
        return False


pack.construction(_Figure())
