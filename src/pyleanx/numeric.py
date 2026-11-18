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
    for _ in range(2):  # a second pass resolves points defined from constructed points
        for h in hyps:
            try:
                between = (isinstance(h, Apply) and isinstance(h.fn, Const)
                           and h.fn.name in ("Sbtw", "Wbtw") and len(h.args) == 4
                           and isinstance(h.args[2], Var))
                defines = (isinstance(h, Compare) and h.op == "eq"
                           and isinstance(h.lhs, Var) and h.lhs.uid not in _free_uids(h.rhs))
                if between:
                    assert isinstance(h, Apply) and isinstance(h.fn, Const)
                    a, b = _point(evaluate(h.args[1], env)), _point(evaluate(h.args[3], env))
                    t = rng.uniform(0.05, 0.95) if h.fn.name == "Sbtw" else rng.random()
                    p = h.args[2]
                    assert isinstance(p, Var)
                    env[p.uid] = (a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]))
                elif defines:
                    assert isinstance(h, Compare) and isinstance(h.lhs, Var)
                    env[h.lhs.uid] = evaluate(h.rhs, env)
                elif (equal := _equal_lengths(h)) is not None:
                    # |PQ| = |PR|: R goes on the circle about P through Q (an isosceles
                    # triangle is drawn this way)
                    centre, through, free = equal
                    c, q = _point(evaluate(centre, env)), _point(evaluate(through, env))
                    r, phi = math.dist(c, q), rng.uniform(0, 2 * math.pi)
                    env[free.uid] = (c[0] + r * math.cos(phi), c[1] + r * math.sin(phi))
            except (Unsupported, ValueError, ZeroDivisionError, OverflowError):
                continue


def _equal_lengths(h: Any) -> tuple[Any, Any, Var] | None:
    """For ``|PQ| = |PR|`` (in any order of endpoints) with R a point variable: (P, Q, R)."""
    def ends(e: Any) -> tuple[Any, Any] | None:
        if isinstance(e, App) and e.func.lean_name == "dist" and len(e.args) == 2:
            return e.args[0], e.args[1]
        return None

    if not (isinstance(h, Compare) and h.op == "eq"):
        return None
    left, right = ends(h.lhs), ends(h.rhs)
    if left is None or right is None:
        return None
    for p, q in (left, left[::-1]):
        for p2, r in (right, right[::-1]):
            if (p._key() == p2._key() and isinstance(r, Var) and r.uid not in _free_uids(p)
                    and r.uid not in _free_uids(q)):
                return p, q, r
    return None


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
