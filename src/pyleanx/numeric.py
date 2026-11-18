"""A numeric sanity check of statements and proof steps (no Lean, nothing is proved).

Before Lean spends minutes on a proof, try the statement and each step on random numbers:

    report = thm.sanity_check()
    print(report)      # "Step 3 looks false: with x = 1.5, y = -2 ... |x + y| ≤ |x| is 0.5 ≤ ..."

Variables of sort ℝ, ℕ, ℤ and points of the plane are sampled at random; samples that
violate a hypothesis are discarded. A step that evaluates to false on a sample satisfying
all hypotheses (and every earlier step) is reported with that sample: it cannot be proved
as stated. When nothing can be evaluated (functions, sets, integrals, quantifiers, or
hypotheses no random sample meets, such as an exact right angle) the check says so and
stays silent. It never claims anything is true.
"""

from __future__ import annotations

import math
import random
from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import Any

from .expr import App, BinOp, Cast, Compare, Expr, Lit, Logic, Neg, NotP, PropConst, Quant, Var
from .terms import Apply, Const, TypeTerm

_TOL = 1e-7


class Unsupported(Exception):  # noqa: N818 - control flow, not an error for users
    """The expression uses something the evaluator does not know."""


def _close(a: float, b: float) -> bool:
    return abs(a - b) <= _TOL * max(1.0, abs(a), abs(b))


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


def _set_points(e: Expr, env: dict[int, Any]) -> list[Any]:
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


_FUNCS: dict[str, Any] = {
    "abs": lambda x: abs(x),
    "min": lambda a, b: min(a, b),
    "max": lambda a, b: max(a, b),
    "Real.sqrt": lambda x: math.sqrt(x) if x > 0 else 0.0,
    "Real.exp": lambda x: math.exp(x) if x < 700 else math.inf,
    "Real.log": lambda x: math.log(abs(x)) if x != 0 else 0.0,
    "Real.sin": math.sin,
    "Real.cos": math.cos,
    "Real.pi": lambda: math.pi,
    "dist": _dist,
    "EuclideanGeometry.angle": _angle,
}


def evaluate(e: Expr, env: dict[int, Any]) -> Any:
    """The value of ``e`` (a float, a point, or a bool for propositions)."""
    if isinstance(e, Var):
        if e.uid not in env:
            raise Unsupported(f"no value for {e.name}")
        return env[e.uid]
    if isinstance(e, Lit):
        return float(e.value)
    if isinstance(e, PropConst):
        return e.value
    if isinstance(e, Cast):
        return evaluate(e.arg, env)
    if isinstance(e, Neg):
        return -evaluate(e.arg, env)
    if isinstance(e, BinOp):
        a, b = evaluate(e.lhs, env), evaluate(e.rhs, env)
        if isinstance(a, tuple) or isinstance(b, tuple):
            raise Unsupported("vector arithmetic")
        if e.op == "add":
            return a + b
        if e.op == "sub":
            return a - b
        if e.op == "mul":
            return a * b
        if e.op == "div":
            return 0.0 if b == 0 else a / b  # Lean: x / 0 = 0
        if e.op == "pow":
            try:
                return a ** b if float(b).is_integer() or a >= 0 else math.nan
            except OverflowError:
                return math.inf
        raise Unsupported(e.op)
    if isinstance(e, App):
        f = _FUNCS.get(e.func.lean_name)
        if f is None:
            raise Unsupported(e.func.lean_name)
        return f(*(evaluate(a, env) for a in e.args))
    if isinstance(e, Compare):
        a, b = evaluate(e.lhs, env), evaluate(e.rhs, env)
        if isinstance(a, tuple) or isinstance(b, tuple):
            if e.op in ("eq", "ne"):
                same = _dist(a, b) <= 1e-9
                return same if e.op == "eq" else not same
            raise Unsupported("point comparison")
        if any(isinstance(x, float) and math.isnan(x) for x in (a, b)):
            raise Unsupported("nan")
        return {"eq": lambda: _close(a, b), "ne": lambda: not _close(a, b),
                "lt": lambda: a < b and not _close(a, b),
                "le": lambda: a <= b or _close(a, b),
                "gt": lambda: a > b and not _close(a, b),
                "ge": lambda: a >= b or _close(a, b)}.get(e.op, _unsupported(e.op))()
    if isinstance(e, NotP):
        return not evaluate(e.arg, env)
    if isinstance(e, Logic):
        a = evaluate(e.lhs, env)
        if e.op == "and":
            return a and evaluate(e.rhs, env)
        if e.op == "or":
            return a or evaluate(e.rhs, env)
        if e.op == "implies":
            return (not a) or evaluate(e.rhs, env)
        if e.op == "iff":
            return a == evaluate(e.rhs, env)
    if isinstance(e, Apply) and isinstance(e.fn, Const):
        name, args = e.fn.name, e.args
        if name in ("Sbtw", "Wbtw") and len(args) == 4 and isinstance(args[0], TypeTerm):
            a, p, b = (evaluate(x, env) for x in args[1:])
            return _between(a, p, b, strict=name == "Sbtw")
        if name == "Collinear" and len(args) == 2:
            return _collinear(_set_points(args[1], env))
        if name == "dist" and len(args) == 2:
            return _dist(evaluate(args[0], env), evaluate(args[1], env))
        if name == "affineSpan" and len(args) == 2:  # line[ℝ, a, b]
            return _Line(tuple(_point(p) for p in _set_points(args[1], env)))
        if name == "AffineSubspace.direction" and len(args) == 1:
            return evaluate(args[0], env)  # a line stands for its direction here
        if name == "AffineSubspace.Parallel" and len(args) == 2:
            u, v = _line(evaluate(args[0], env)).direction, _line(evaluate(args[1], env)).direction
            if _zero(u) or _zero(v):
                return _zero(u) and _zero(v)   # two points are parallel; a point and a line not
            return _close(u[0] * v[1] - u[1] * v[0], 0.0)
        if name == "Submodule.IsOrtho" and len(args) == 2:
            u, v = _line(evaluate(args[0], env)).direction, _line(evaluate(args[1], env)).direction
            return _close(u[0] * v[0] + u[1] * v[1], 0.0)
        if name == "Membership.mem" and len(args) == 2:
            s = evaluate(args[0], env)
            if isinstance(s, _Line):
                return _collinear([*s.points, evaluate(args[1], env)])
        if name == "midpoint" and len(args) == 3 and isinstance(args[0], TypeTerm):
            (x1, y1), (x2, y2) = _point(evaluate(args[1], env)), _point(evaluate(args[2], env))
            return ((x1 + x2) / 2, (y1 + y2) / 2)
    if isinstance(e, Quant):
        raise Unsupported("quantifier")
    raise Unsupported(type(e).__name__)


def _unsupported(op: str) -> Any:
    def f() -> bool:
        raise Unsupported(op)
    return f


def _sample(sort_name: str, rng: random.Random) -> Any:
    if sort_name == "Real":
        r = rng.random()
        if r < 0.25:
            return float(rng.randint(-4, 4))
        if r < 0.35:
            return rng.choice([0.5, -0.5, 0.1, -0.1, 1e-3])
        return rng.uniform(-5, 5)
    if sort_name == "Nat":
        return float(rng.randint(0, 12))
    if sort_name == "Int":
        return float(rng.randint(-10, 10))
    if sort_name == "Point":
        return (rng.uniform(-5, 5), rng.uniform(-5, 5))
    raise Unsupported(sort_name)


@dataclass
class Finding:
    """A step (or the statement) that is false on a sample meeting every hypothesis."""

    where: str            # "the statement" or "step 3"
    statement: str        # the step in prose
    sample: dict[str, Any]
    detail: str = ""

    def __str__(self) -> str:
        vals = ", ".join(f"{k} = {_fmt(v)}" for k, v in self.sample.items())
        return (f"{self.where[0].upper() + self.where[1:]} looks false: with {vals} (all "
                f"hypotheses hold), “{self.statement}” fails{self.detail}.")


def _fmt(v: Any) -> str:
    if isinstance(v, tuple):
        return "(" + ", ".join(_fmt(x) for x in v) + ")"
    if isinstance(v, float) and v.is_integer():
        return str(int(v))
    return f"{v:.4g}"


@dataclass
class SanityReport:
    theorem: str
    findings: list[Finding] = field(default_factory=list)
    samples: int = 0          # samples meeting all hypotheses
    checked_steps: int = 0    # steps that could be evaluated
    note: str = ""

    @property
    def ok(self) -> bool:
        return not self.findings

    def _repr_markdown_(self) -> str:  # Jupyter
        if self.findings:
            return "\n\n".join(f"❌ {f}" for f in self.findings)
        mark = "⚠️" if self.note else "✓"
        return f"{mark} {self}"

    def __str__(self) -> str:
        if self.findings:
            return "\n".join(str(f) for f in self.findings)
        if self.note:
            return f"{self.theorem}: {self.note}"
        return (f"{self.theorem}: no counterexample in {self.samples} random samples "
                f"({self.checked_steps} steps evaluated). This is not a proof.")


def _claims(proof: Any) -> Iterable[tuple[int, Expr]]:
    """Top-level claims of a proof, numbered as in the prose."""
    from .proofs import Chain, Claim, SupposeNot

    if proof is None:
        return
    for i, step in enumerate(proof.flat(), start=1):
        if isinstance(step, SupposeNot):
            return  # later steps hold only under the assumption made for contradiction
        if isinstance(step, Claim) and step.prop is not None:
            yield i, step.prop
        elif isinstance(step, Chain):
            first = step.first
            for rel, term, _facts, _note in step.links:
                op = {"=": "eq", "≤": "le", "<": "lt", "≥": "ge", ">": "gt"}.get(rel)
                if op is not None:
                    yield i, Compare(op, first, term)
                first = term


_REL = {"eq": "=", "ne": "≠", "lt": "<", "le": "≤", "gt": ">", "ge": "≥"}


def _detail(prop: Expr, env: dict[int, Any]) -> str:
    """`` (the left side is 0.88, the right side 0.83)`` for a comparison."""
    if not isinstance(prop, Compare):
        return ""
    try:
        a, b = evaluate(prop.lhs, env), evaluate(prop.rhs, env)
    except (Unsupported, ValueError, ZeroDivisionError, OverflowError):
        return ""
    if isinstance(a, tuple) or isinstance(b, tuple):
        return ""
    return f": the left side is {_fmt(a)}, the right side {_fmt(b)}"


def _construct(hyps: list[Expr], env: dict[int, Any], rng: random.Random) -> None:
    """Place points the hypotheses determine, as one draws a figure: D strictly between A and
    B goes on the segment; ``M = midpoint(A, B)`` and any ``x = expression`` are computed.
    (Every hypothesis is still evaluated afterwards; nothing is assumed.)"""
    hyps = list(_conjuncts(hyps))
    uses = _uses(hyps)
    owner: dict[int, int] = {}  # point -> the hypothesis that placed it (no other moves it)

    def may_place(uid: int, i: int) -> bool:
        if owner.setdefault(uid, i) != i:
            return False
        return True

    # a point on two circles (|AB| = |AC| and |BA| = |BC|: an equilateral triangle's apex) is
    # placed at one of their intersections; the hypotheses involved do not move it again
    circles: dict[int, list[tuple[int, tuple[Any, Any, Var]]]] = {}
    for i, h in enumerate(hyps):
        for eq in _all_equal_lengths(h):
            circles.setdefault(eq[2].uid, []).append((i, eq))
    two_circles = {uid: cs for uid, cs in circles.items()
                   if len({c[1][0]._key() for c in cs}) >= 2}
    on_two_circles = {i for cs in two_circles.values() for i, _ in cs}

    for _ in range(2):  # a second pass resolves points defined from constructed points
        _place_on_parallels(hyps, env, rng)
        for uid, cs in two_circles.items():
            try:
                (_, (c1_, q1_, _)), (_, (c2_, q2_, _)) = cs[0], next(
                    c for c in cs[1:] if c[1][0]._key() != cs[0][1][0]._key())
                c1, q1 = _point(evaluate(c1_, env)), _point(evaluate(q1_, env))
                c2, q2 = _point(evaluate(c2_, env)), _point(evaluate(q2_, env))
                hit = _circle_meet(c1, math.dist(c1, q1), c2, math.dist(c2, q2), rng)
                if hit is not None:
                    env[uid] = hit
                    owner[uid] = -1
            except (Unsupported, ValueError, ZeroDivisionError, OverflowError, StopIteration):
                continue
        # right angles first: a point that is also equidistant is then placed by both
        order = sorted(range(len(hyps)), key=lambda j: not _right_angle_shape(hyps[j]))
        for i in order:
            h = hyps[i]
            try:
                between = (isinstance(h, Apply) and isinstance(h.fn, Const)
                           and h.fn.name in ("Sbtw", "Wbtw") and len(h.args) == 4
                           and isinstance(h.args[2], Var))
                defines = (isinstance(h, Compare) and h.op == "eq"
                           and isinstance(h.lhs, Var) and h.lhs.uid not in _free_uids(h.rhs))
                if between:
                    assert isinstance(h, Apply) and isinstance(h.fn, Const)
                    a_, p, b_ = h.args[1], h.args[2], h.args[3]
                    assert isinstance(p, Var)
                    if may_place(p.uid, i):
                        a, b = _point(evaluate(a_, env)), _point(evaluate(b_, env))
                        t = rng.uniform(0.05, 0.95) if h.fn.name == "Sbtw" else rng.random()
                        env[p.uid] = (a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]))
                    else:
                        # the middle point is already placed (vertical angles: O between A
                        # and B, and between C and D): put an end beyond it instead
                        for near, far in ((a_, b_), (b_, a_)):
                            if isinstance(far, Var) and may_place(far.uid, i):
                                n, m = _point(evaluate(near, env)), _point(env[p.uid])
                                s = rng.uniform(0.3, 2.0)
                                env[far.uid] = (m[0] + s * (m[0] - n[0]), m[1] + s * (m[1] - n[1]))
                                break
                elif defines:
                    assert isinstance(h, Compare) and isinstance(h.lhs, Var)
                    env[h.lhs.uid] = evaluate(h.rhs, env)
                elif (equal := _equal_lengths(h, uses)) is not None:
                    # |PQ| = |PR|: R goes on the circle about P through Q (an isosceles
                    # triangle is drawn this way)
                    centre, through, free = equal
                    if i in on_two_circles or not may_place(free.uid, i):
                        continue
                    c, q = _point(evaluate(centre, env)), _point(evaluate(through, env))
                    r, phi = math.dist(c, q), rng.uniform(0, 2 * math.pi)
                    env[free.uid] = (c[0] + r * math.cos(phi), c[1] + r * math.sin(phi))
                elif (right := _right_angle(h, env)) is not None:
                    # ∠PVQ = 90°: Q goes on the perpendicular to VP at V; at distance |VP|
                    # if the legs are also equal (an isosceles right triangle)
                    p_, v_, free = right
                    if not may_place(free.uid, i):
                        continue
                    px, py = _point(evaluate(p_, env))
                    vx, vy = _point(evaluate(v_, env))
                    equal_legs = any(_same_pair(_equal_lengths(g, uses, any_free=True),
                                                v_, p_, free) for g in hyps)
                    s = rng.choice((-1, 1)) * (1.0 if equal_legs else rng.uniform(0.3, 2.0))
                    env[free.uid] = (vx - s * (py - vy), vy + s * (px - vx))
            except (Unsupported, ValueError, ZeroDivisionError, OverflowError):
                continue


def _conjuncts(hyps: Iterable[Expr]) -> Iterable[Expr]:
    for h in hyps:
        if isinstance(h, Logic) and h.op == "and":
            yield from _conjuncts([h.lhs, h.rhs])
        else:
            yield h


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


def _place_on_parallels(hyps: list[Expr], env: dict[int, Any], rng: random.Random) -> None:
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


def _equal_lengths(h: Any, uses: dict[int, int] | None = None,
                   any_free: bool = False) -> tuple[Any, Any, Var] | None:
    """For ``|PQ| = |PR|`` (endpoints in any order, either side) with R a point variable:
    (P, Q, R). Of two candidate R, the one fewer hypotheses mention is moved (so a point
    that also defines others, like A in ``O = midpoint(A, B)``, stays where it is)."""
    del any_free  # kept for call sites that only test the shape

    def ends(e: Any) -> tuple[Any, Any] | None:
        if isinstance(e, App) and e.func.lean_name == "dist" and len(e.args) == 2:
            return e.args[0], e.args[1]
        return None

    if not (isinstance(h, Compare) and h.op == "eq"):
        return None
    left, right = ends(h.lhs), ends(h.rhs)
    if left is None or right is None:
        return None
    found: list[tuple[Any, Any, Var]] = []
    for a, b in ((left, right), (right, left)):
        for p, q in (a, a[::-1]):
            for p2, r in (b, b[::-1]):
                if (p._key() == p2._key() and isinstance(r, Var)
                        and r.uid not in _free_uids(p) and r.uid not in _free_uids(q)):
                    found.append((p, q, r))
    if not found:
        return None
    counts = uses or {}
    return min(found, key=lambda f: counts.get(f[2].uid, 0))


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


def _uses(hyps: list[Expr]) -> dict[int, int]:
    """How many hypotheses mention each variable."""
    out: dict[int, int] = {}
    for h in hyps:
        for uid in _free_uids(h):
            out[uid] = out.get(uid, 0) + 1
    return out


def _right_angle_shape(h: Any) -> bool:
    return isinstance(h, Compare) and h.op == "eq" and any(
        isinstance(s, App) and s.func.lean_name == "EuclideanGeometry.angle"
        for s in (h.lhs, h.rhs))


def _free_uids(e: Any) -> set[int]:
    if isinstance(e, Var):
        return {e.uid}
    out: set[int] = set()
    for c in getattr(e, "children", lambda: ())():
        out |= _free_uids(c)
    if isinstance(e, Apply):
        for a in e.args:
            out |= _free_uids(a)
    return out


def sanity_check(thm: Any, samples: int = 300, seed: int = 0) -> SanityReport:
    """Try the statement and each top-level step on random values (see module docstring)."""
    from .prose import plain

    rep = SanityReport(thm.name)
    rng = random.Random(seed)
    try:
        sorts = [(v, v.sort.name) for v in thm.variables]
        for _, s in sorts:
            _sample(s, rng)
    except Unsupported as exc:
        rep.note = f"variables of sort {exc} cannot be sampled; nothing was checked"
        return rep
    hyps = [h.prop for h in thm.assumptions]
    steps = list(_claims(thm.proof))
    usable_steps: set[int] = set()
    tries = 0
    while rep.samples < samples and tries < samples * 40:
        tries += 1
        env = {v.uid: _sample(s, rng) for v, s in sorts}
        _construct(hyps, env, rng)
        try:
            if not all(evaluate(h, env) for h in hyps):
                continue
        except Unsupported as exc:
            rep.note = f"a hypothesis uses {exc}, which cannot be evaluated; nothing was checked"
            return rep
        except (ValueError, ZeroDivisionError, OverflowError):
            continue
        rep.samples += 1
        sample = {v.name: env[v.uid] for v, _ in sorts}
        try:
            if not evaluate(thm.conclusion, env):
                rep.findings.append(Finding("the statement", plain(thm.conclusion), sample,
                                            _detail(thm.conclusion, env)))
                return rep
        except (Unsupported, ValueError, ZeroDivisionError, OverflowError):
            pass
        for idx, prop in steps:
            try:
                value = evaluate(prop, env)
            except (Unsupported, ValueError, ZeroDivisionError, OverflowError):
                # a later step may still be checkable; this one is skipped
                continue
            usable_steps.add(idx)
            if not value:
                rep.findings.append(Finding(f"step {idx}", plain(prop), sample,
                                            _detail(prop, env)))
                rep.checked_steps = len(usable_steps)
                return rep
    rep.checked_steps = len(usable_steps)
    if rep.samples == 0:
        rep.note = ("no random sample satisfies the hypotheses (e.g. an exact right angle); "
                    "nothing was checked")
    return rep
