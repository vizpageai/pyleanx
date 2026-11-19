"""A numeric sanity check of statements and proof steps (no Lean, nothing is proved).

Before Lean spends minutes on a proof, try the statement and each step on random numbers:

    report = thm.sanity_check()
    print(report)      # "Step 3 looks false: with x = 1.5, y = -2 ... |x + y| ≤ |x| is 0.5 ≤ ..."

Variables of sort ℝ, ℕ and ℤ are sampled at random, and so are the sorts a domain pack
registers (the geometry pack: points of the plane, with its constructions of figures; see
``register_sampler``, ``register_apply``, ``register_construction``); samples that
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
from .terms import Apply, BigOp, Const, Lam

_TOL = 1e-7


class Unsupported(Exception):  # noqa: N818 - control flow, not an error for users
    """The expression uses something the evaluator does not know."""


def _close(a: float, b: float) -> bool:
    return abs(a - b) <= _TOL * max(1.0, abs(a), abs(b))


#: where two real functions are compared (spread out, irrational, avoiding special points)
_FUNCTION_POINTS = (-2.7182818, -1.4142136, -0.5772157, 0.3010300, 0.6931472, 1.2599210,
                    1.7320508, 2.2360680, 3.1415927, 4.6692016)


def _vector_distance(a: Any, b: Any) -> float:
    """Distance of two vector values (points), for comparing them."""
    if not (isinstance(a, tuple) and isinstance(b, tuple) and len(a) == len(b)):
        raise Unsupported("not a point")
    return math.dist(a, b)


# --- what packs register --------------------------------------------------------------
#: functions by Lean name (an ``App``): the numeric prelude here; packs add theirs
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
}
#: constant-headed applications (``Apply``) by head name: handler(args, env) -> value, or
#: ``NotImplemented`` when the handler does not apply to these arguments
_APPLY: dict[str, Any] = {}
#: samplers of values by sort name: sampler(rng) -> value
_SAMPLERS: dict[str, Any] = {}
#: construction hooks, in registration order (see :class:`Construction`)
_CONSTRUCTIONS: dict[str, Any] = {}
#: big operators (∑, ∏, ∫) by kind: handler(e, env) -> value, or NotImplemented
_BIGOPS: dict[str, Any] = {}


def register_bigop(kind: str, handler: Any) -> None:
    """Evaluate big operators of ``kind`` ("sum", "prod", "integral") with
    ``handler(e, env)``; the handler returns ``NotImplemented`` for cases it does not cover."""
    _BIGOPS[kind] = handler


def register_function(lean_name: str, fn: Any) -> None:
    """Evaluate applications of the function ``lean_name`` with ``fn`` (on values)."""
    _FUNCS[lean_name] = fn


def register_apply(head: str, handler: Any) -> None:
    """Evaluate ``head args…`` (a constant applied to terms) with ``handler(args, env)``;
    the handler returns ``NotImplemented`` for arguments it does not handle."""
    _APPLY[head] = handler


def register_sampler(sort_name: str, sampler: Any) -> None:
    """Draw random values of a sort with ``sampler(rng)``."""
    _SAMPLERS[sort_name] = sampler


def register_construction(hook: Any, *, name: str) -> None:
    """Add a construction hook (registering ``name`` again replaces it).

    A hook has ``setup(c) -> state``, ``before_pass(c, state)``, ``first(h) -> bool``
    (hypotheses to handle before the others) and ``place(c, state, i, h) -> bool``
    (handle hypothesis ``i``; True when it applied). See :class:`Construction`.
    """
    _CONSTRUCTIONS[name] = hook


@dataclass
class Construction:
    """What a construction hook sees while a sample is drawn."""

    hyps: list[Expr]                # the hypotheses, split at ∧
    env: dict[int, Any]             # variable uid -> value (filled in place)
    rng: random.Random
    uses: dict[int, int]            # how many hypotheses mention each variable
    owner: dict[int, int] = field(default_factory=dict)  # uid -> hypothesis that placed it
    #: hypotheses (indices into ``hyps``) that hold by construction: a definition such as
    #: ∀ t, f t = 3t + 1 used to build f's sample. They are not evaluated again.
    defined: set[int] = field(default_factory=set)

    def may_place(self, uid: int, i: int) -> bool:
        """May hypothesis ``i`` place variable ``uid``? (One placed by another hypothesis
        is not moved again.)"""
        return self.owner.setdefault(uid, i) == i


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
        if callable(a) or callable(b):
            # functions are equal when they agree everywhere; a point where they differ is
            # a counterexample (agreement at the points tried proves nothing)
            if e.op not in ("eq", "ne") or not (callable(a) and callable(b)):
                raise Unsupported("comparison of functions")
            try:
                same = all(_close(float(a(p)), float(b(p))) for p in _FUNCTION_POINTS)
            except (TypeError, ValueError, OverflowError, ZeroDivisionError) as exc:
                raise Unsupported("comparison of functions") from exc
            return same if e.op == "eq" else not same
        if isinstance(a, tuple) or isinstance(b, tuple):
            if e.op in ("eq", "ne"):
                same = _vector_distance(a, b) <= 1e-9
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
    if isinstance(e, Lam):
        # a function: a Python closure over the sample
        params = e.vars

        def closure(*vals: Any) -> Any:
            bound = {v.uid: x for v, x in zip(params, vals, strict=True)}
            return evaluate(e.body, {**env, **bound})
        return closure
    if isinstance(e, BigOp):
        handler = _BIGOPS.get(e.kind)
        if handler is not None:
            value = handler(e, env)
            if value is not NotImplemented:
                return value
        raise Unsupported(f"{e.kind}")
    if isinstance(e, Apply) and isinstance(e.fn, Var):
        # a function-valued variable whose sample is a Python function (a pack's sampler, or
        # a construction from a defining hypothesis such as ∀ t, f t = 3t + 1)
        fn = evaluate(e.fn, env)
        if callable(fn):
            return fn(*(evaluate(a, env) for a in e.args))
        raise Unsupported(f"no function value for {e.fn.name}")
    if isinstance(e, Apply) and isinstance(e.fn, Const):
        handler = _APPLY.get(e.fn.name)
        if handler is not None:
            value = handler(e.args, env)
            if value is not NotImplemented:
                return value
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
    sampler = _SAMPLERS.get(sort_name)
    if sampler is not None:
        return sampler(rng)
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
    if callable(v):  # a sampled function: its description, or the hypothesis defining it
        return str(getattr(v, "label", "(as a hypothesis defines it)"))
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


# --- finite sums and products (core arithmetic) --------------------------------------
_MAX_TERMS = 10_000


def _finset_range(args: tuple, env: dict[int, Any]) -> Any:
    """``Finset.range n`` = {0, …, n − 1}."""
    if len(args) != 1:
        return NotImplemented
    n = evaluate(args[0], env)
    if not (isinstance(n, float) and n.is_integer() and 0 <= n <= _MAX_TERMS):
        raise Unsupported("Finset.range of a large or non-natural number")
    return range(int(n))


def _finite_bigop(e: Any, env: dict[int, Any]) -> Any:
    """∑ / ∏ over a finite set whose elements can be listed (e.g. ``Finset.range n``)."""
    if e.over is None:
        return NotImplemented
    dom = evaluate(e.over, env)
    if not isinstance(dom, (range, tuple, frozenset)) or len(dom) > _MAX_TERMS:
        raise Unsupported("a sum over a set that cannot be listed")
    terms = [evaluate(e.body, {**env, e.var.uid: float(i)}) for i in dom]
    if e.kind == "sum":
        return float(math.fsum(terms))
    out = 1.0
    for x in terms:
        out *= x
    return out


_APPLY["Finset.range"] = _finset_range
_BIGOPS["sum"] = _finite_bigop
_BIGOPS["prod"] = _finite_bigop


def _construct(hyps: list[Expr], env: dict[int, Any], rng: random.Random) -> list[Expr]:
    """Place the values the hypotheses determine, as one draws a figure: any
    ``x = expression`` is computed, and registered construction hooks place the rest (the
    geometry pack: a point strictly between A and B goes on the segment, …). Every
    hypothesis is still evaluated afterwards; nothing is assumed."""
    hyps = list(_conjuncts(hyps))
    c = Construction(hyps, env, rng, _uses(hyps))
    _fill(c)
    return [h for i, h in enumerate(hyps) if i not in c.defined]


def _fill(c: Construction) -> None:
    hyps, env = c.hyps, c.env
    hooks = [(hook, hook.setup(c)) for hook in _CONSTRUCTIONS.values()]
    for _ in range(2):  # a second pass resolves values defined from constructed ones
        for hook, state in hooks:
            hook.before_pass(c, state)
        order = sorted(range(len(hyps)),
                       key=lambda j: not any(hook.first(hyps[j]) for hook, _ in hooks))
        for i in order:
            h = hyps[i]
            try:
                if (isinstance(h, Compare) and h.op == "eq" and isinstance(h.lhs, Var)
                        and h.lhs.uid not in _free_uids(h.rhs)):
                    env[h.lhs.uid] = evaluate(h.rhs, env)
                    continue
                for hook, state in hooks:
                    if hook.place(c, state, i, h):
                        break
            except (Unsupported, ValueError, ZeroDivisionError, OverflowError):
                continue


def _conjuncts(hyps: Iterable[Expr]) -> Iterable[Expr]:
    for h in hyps:
        if isinstance(h, Logic) and h.op == "and":
            yield from _conjuncts([h.lhs, h.rhs])
        else:
            yield h


def _uses(hyps: list[Expr]) -> dict[int, int]:
    """How many hypotheses mention each variable."""
    out: dict[int, int] = {}
    for h in hyps:
        for uid in _free_uids(h):
            out[uid] = out.get(uid, 0) + 1
    return out


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
        to_check = _construct(hyps, env, rng)
        try:
            if not all(evaluate(h, env) for h in to_check):
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
