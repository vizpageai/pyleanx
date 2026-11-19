"""Analysis in the numeric sanity check: real functions, derivatives and integrals.

* A variable ``f : ℝ → ℝ`` is sampled as a random smooth function: a polynomial plus a
  sine (continuous and differentiable, not integrable over ℝ), or a combination of
  Gaussians (also integrable over ℝ). Each sample knows these properties, so hypotheses
  such as ``Continuous f`` or ``Integrable f`` are evaluated honestly: a sample that does
  not satisfy a hypothesis is discarded, never assumed to satisfy it.
* A hypothesis ``∀ t, f t = e(t)`` *defines* ``f``: the sample is that function.
* ``deriv f x`` is computed by Richardson extrapolation of central differences, and
  ``∫ x in a..b, g x`` (and ``∫ x, g x`` for integrable samples) by adaptive Simpson's
  rule, both to about 1e-10, far below the comparison tolerance (1e-7, relative).

The check proves nothing; it finds steps that are false on an example.
"""

from __future__ import annotations

import math
import random
from typing import TYPE_CHECKING, Any

from pyleanx.expr import Compare, Quant, Var
from pyleanx.numeric import Construction, Unsupported, evaluate
from pyleanx.terms import Apply

if TYPE_CHECKING:
    from pyleanx.pack import DomainPack

FUNCTION_SORT = "Real → Real"
SEQUENCE_SORT = "Nat → Real"


class SampledFunction:
    """A random real function with the properties the sample is known to have."""

    def __init__(self, fn: Any, *, integrable: bool, label: str) -> None:
        self.fn, self.integrable, self.label = fn, integrable, label
        self.continuous = self.differentiable = True

    def __call__(self, x: float) -> float:
        return float(self.fn(float(x)))

    def __repr__(self) -> str:
        return self.label


def sample_function(rng: random.Random) -> SampledFunction:
    """A random smooth function on ℝ (half of them integrable over ℝ)."""
    if rng.random() < 0.5:
        a = [rng.uniform(-2, 2) for _ in range(4)]
        b = rng.uniform(0.5, 2.0)
        return SampledFunction(
            lambda x: a[0] + a[1] * x + a[2] * x * x + a[3] * math.sin(b * x),
            integrable=False,
            label=f"x ↦ {a[0]:.3g} + {a[1]:.3g}x + {a[2]:.3g}x² + {a[3]:.3g}·sin({b:.3g}x)")
    c = [rng.uniform(-2, 2) for _ in range(2)]
    m, s = rng.uniform(-1, 1), rng.uniform(0.5, 1.5)
    return SampledFunction(
        lambda x: c[0] * math.exp(-x * x) + c[1] * math.exp(-((x - m) / s) ** 2),
        integrable=True,
        label=f"x ↦ {c[0]:.3g}·e^(−x²) + {c[1]:.3g}·e^(−((x − {m:.3g})/{s:.3g})²)")


class SampledSequence:
    """A random real sequence, labelled for counterexamples."""

    def __init__(self, fn: Any, label: str) -> None:
        self.fn, self.label = fn, label

    def __call__(self, n: float) -> float:
        return float(self.fn(int(n)))

    def __repr__(self) -> str:
        return self.label


def sample_sequence(rng: random.Random) -> SampledSequence:
    """A random real sequence: rational, alternating, geometric or bounded oscillating."""
    kind = rng.randrange(4)
    c, d = rng.uniform(-3, 3), rng.uniform(-3, 3)
    if kind == 0:
        return SampledSequence(lambda n: c + d / (n + 1), f"n ↦ {c:.3g} + {d:.3g}/(n + 1)")
    if kind == 1:
        return SampledSequence(lambda n: c + d * (-1) ** n / (n + 1),
                               f"n ↦ {c:.3g} + {d:.3g}·(−1)ⁿ/(n + 1)")
    if kind == 2:
        r = rng.uniform(-0.95, 0.95)
        return SampledSequence(lambda n: c + d * r ** n, f"n ↦ {c:.3g} + {d:.3g}·{r:.3g}ⁿ")
    b = rng.uniform(0.3, 2.0)
    return SampledSequence(lambda n: c + d * math.sin(b * n), f"n ↦ {c:.3g} + {d:.3g}·sin({b:.3g}n)")


# --- derivatives and integrals ---------------------------------------------------------
def derivative(f: Any, x: float) -> float:
    """f′(x) by Richardson extrapolation of central differences."""
    if not callable(f):
        raise Unsupported("derivative of a non-function")
    h, d = 1e-2, []
    for _ in range(4):
        d.append((f(x + h) - f(x - h)) / (2 * h))
        h /= 2
    for k in range(1, 4):  # eliminate the h², h⁴, … error terms
        d = [(4 ** k * d[i + 1] - d[i]) / (4 ** k - 1) for i in range(len(d) - 1)]
    return d[0]


def integral(g: Any, a: float, b: float, tol: float = 1e-11) -> float:
    """∫_a^b g by adaptive Simpson's rule (oriented: ∫_b^a = −∫_a^b)."""
    if a == b:
        return 0.0
    if a > b:
        return -integral(g, b, a, tol)

    def simpson(lo: float, hi: float, flo: float, fmid: float, fhi: float) -> float:
        return (hi - lo) / 6 * (flo + 4 * fmid + fhi)

    def go(lo: float, hi: float, flo: float, fmid: float, fhi: float, whole: float,
           eps: float, depth: int) -> float:
        mid = (lo + hi) / 2
        lm, rm = (lo + mid) / 2, (mid + hi) / 2
        flm, frm = g(lm), g(rm)
        left, right = simpson(lo, mid, flo, flm, fmid), simpson(mid, hi, fmid, frm, fhi)
        if depth <= 0 or abs(left + right - whole) <= 15 * eps:
            return left + right + (left + right - whole) / 15
        return (go(lo, mid, flo, flm, fmid, left, eps / 2, depth - 1)
                + go(mid, hi, fmid, frm, fhi, right, eps / 2, depth - 1))

    flo, fmid, fhi = g(a), g((a + b) / 2), g(b)
    return go(a, b, flo, fmid, fhi, simpson(a, b, flo, fmid, fhi), tol, 40)


def _integral_op(e: Any, env: dict[int, Any]) -> Any:
    if e.over is not None:
        return NotImplemented  # an integral over a set: not evaluated

    def g(x: float) -> float:
        return float(evaluate(e.body, {**env, e.var.uid: x}))

    if e.bounds is not None:
        a, b = (float(evaluate(x, env)) for x in e.bounds)
        return integral(g, a, b)
    # ∫ over ℝ: only for integrands built from integrable samples (they decay like e^(−x²))
    if not _decays(e.body, env):
        raise Unsupported("an integral over ℝ of a function not known to be integrable")
    return integral(g, -40.0, 40.0)


def _decays(body: Any, env: dict[int, Any]) -> bool:
    """Does the integrand involve only integrable samples (applied, possibly under |·|)?"""
    found = False
    stack = [body]
    while stack:
        node = stack.pop()
        if isinstance(node, Apply) and isinstance(node.fn, Var):
            fn = env.get(node.fn.uid)
            if not (isinstance(fn, SampledFunction) and fn.integrable):
                return False
            found = True
        stack.extend(getattr(node, "children", lambda: ())())
        stack.extend(getattr(node, "args", ()) if isinstance(node, Apply) else ())
    return found


# --- predicates on sampled functions ------------------------------------------------------
def _function_property(flag: str, position: int = 0) -> Any:
    def handler(args: tuple, env: dict[int, Any]) -> Any:
        if len(args) <= position:
            return NotImplemented
        fn = evaluate(args[position], env)
        if isinstance(fn, SampledFunction):
            return bool(getattr(fn, flag))
        if callable(fn):
            raise Unsupported(f"whether a defined function is {flag}")
        return NotImplemented
    return handler


# --- functions defined by a hypothesis ---------------------------------------------------
class _Definitions:
    """A hypothesis ``∀ t, f t = e(t)`` makes the sample of ``f`` that function."""

    def setup(self, c: Construction) -> dict[str, Any]:
        defs = []
        for i, h in enumerate(c.hyps):
            if (isinstance(h, Quant) and h.kind == "forall" and len(h.vars) == 1
                    and isinstance(h.body, Compare) and h.body.op == "eq"
                    and isinstance(h.body.lhs, Apply) and isinstance(h.body.lhs.fn, Var)
                    and len(h.body.lhs.args) == 1 and isinstance(h.body.lhs.args[0], Var)
                    and h.body.lhs.args[0].uid == h.vars[0].uid):
                defs.append((i, h.body.lhs.fn, h.vars[0], h.body.rhs))
        return {"defs": defs}

    def before_pass(self, c: Construction, state: dict[str, Any]) -> None:
        for i, f, t, rhs in state["defs"]:
            if not c.may_place(f.uid, i):
                continue
            def defined(x: float, _t: Var = t, _rhs: Any = rhs,
                        _env: dict[int, Any] = c.env) -> float:
                return float(evaluate(_rhs, {**_env, _t.uid: x}))
            c.env[f.uid] = defined
            c.defined.add(i)  # holds by construction

    def first(self, h: Any) -> bool:
        return False

    def place(self, c: Construction, state: dict[str, Any], i: int, h: Any) -> bool:
        return any(i == j for j, *_ in state["defs"])


def register(pack: DomainPack) -> None:
    pack.sampler(FUNCTION_SORT, sample_function)
    pack.sampler(SEQUENCE_SORT, sample_sequence)
    pack.function("deriv", derivative)
    pack.bigop("integral", _integral_op)
    for head in ("Continuous", "ContinuousOn"):
        pack.apply(head, _function_property("continuous"))
    for head in ("Differentiable", "DifferentiableOn"):
        pack.apply(head, _function_property("differentiable", position=1))
    pack.apply("MeasureTheory.Integrable", _function_property("integrable"))
    pack.apply("MeasureTheory.LocallyIntegrable", _function_property("continuous"))
    pack.construction(_Definitions())
