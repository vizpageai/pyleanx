"""Rebuild theorems from their canonical JSON (``Theorem.canonical()``).

Used by the theorem bank (M7) and the agent API (M8) to store and exchange theorems
as data. Deserialisation is strict: unknown sorts, functions, tactics or free names
raise :class:`SerializationError`, and the rebuilt theorem's canonical form must equal
the input exactly. Nothing is executed and nothing is trusted: the rebuilt theorem
still has to be checked by Lean.
"""

from __future__ import annotations

import json
from collections.abc import Callable, Iterable, Mapping
from fractions import Fraction
from typing import Any

from .errors import PyLeanXError
from .expr import (
    FALSE,
    TRUE,
    BinOp,
    Cast,
    Compare,
    Expr,
    Func,
    Lit,
    Logic,
    Neg,
    NotP,
    Quant,
    Var,
    abs_,
    max_,
    min_,
)
from .proofs import (
    Apply,
    Assumption,
    Branches,
    Constructor,
    Decide,
    Exact,
    Intro,
    Linarith,
    Name,
    Nlinarith,
    NormNum,
    Omega,
    Positivity,
    RawTactic,
    Rewrite,
    Rfl,
    Ring,
    Simp,
    Steps,
    Tactic,
    Term,
    TermApp,
    Use,
)
from .types import SORTS, Sort


class SerializationError(PyLeanXError):
    """Canonical data does not describe a theorem this PyLeanX can rebuild exactly."""


_FUNCS: dict[str, Func] = {}


def register_func(func: Func) -> Func:
    """Make a custom :class:`~pyleanx.Func` reconstructible by name."""
    other = _FUNCS.get(func.lean_name)
    if other is not None and other != func:
        raise SerializationError(f"a different function {func.lean_name!r} is registered")
    _FUNCS[func.lean_name] = func
    return func


def _builtin_funcs() -> None:
    if _FUNCS:
        return
    from . import analysis, expr, geometry

    for f in (expr._SQRT, expr._EXP, expr._LOG, analysis._SIN, analysis._COS, analysis._PI,
              geometry._DIST, geometry._ANGLE_F):
        register_func(f)


_POLY: dict[str, Callable[..., Expr]] = {"abs": abs_, "min": min_, "max": max_}
_ARITH = {"add", "sub", "mul", "div", "mod", "pow"}
_CMP = {"eq", "ne", "lt", "le", "gt", "ge"}
_LOGIC = {"and", "or", "implies", "iff"}


def _json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, ensure_ascii=False)


def _sort(name: Any) -> Sort:
    s = SORTS.get(name) if isinstance(name, str) else None
    if s is None:
        raise SerializationError(f"unknown sort {name!r}")
    return s


class _Decoder:
    def __init__(self, scope: Mapping[str, Var]) -> None:
        self.scope = dict(scope)
        # Inside proofs, terms may mention names introduced by tactics (``intro z``);
        # Lean sees those by name only, so they are rebuilt as fresh variables there.
        self.in_proof = False
        self.proof_locals: dict[tuple[str, str], Var] = {}

    def expr(self, d: Any) -> Expr:
        if not isinstance(d, list) or not d:
            raise SerializationError(f"bad expression {d!r}")
        tag = d[0]
        if tag == "var":
            _, name, sort = d
            v = self.scope.get(name)
            if v is not None and v.sort.name == sort:
                return v
            if self.in_proof:
                key = (name, sort)
                if key not in self.proof_locals:
                    self.proof_locals[key] = Var(name, _sort(sort))
                return self.proof_locals[key]
            raise SerializationError(f"free or mistyped variable {name!r}")
        if tag == "lit":
            _, value, sort = d
            return Lit(Fraction(value), _sort(sort) if sort is not None else None)
        if tag == "propconst":
            return TRUE if d[1] else FALSE
        if tag in _ARITH:
            lhs, rhs = self.expr(d[1]), self.expr(d[2])
            sort = lhs.sort if lhs.sort is not None else rhs.sort
            if tag == "pow":
                sort = lhs.sort
            return BinOp(tag, lhs, rhs, sort)
        if tag == "neg":
            arg = self.expr(d[1])
            return Neg(arg, arg.sort)
        if tag == "cast":
            return Cast(self.expr(d[2]), _sort(d[1]))
        if tag == "app":
            name, args = d[1], [self.expr(a) for a in d[2]]
            if name in _POLY:
                return _POLY[name](*args)
            _builtin_funcs()
            func = _FUNCS.get(name)
            if func is None:
                raise SerializationError(f"unknown function {name!r}; use register_func")
            return func(*args)
        if tag in _CMP:
            return Compare(tag, self.expr(d[1]), self.expr(d[2]))
        if tag == "not":
            return NotP(self.expr(d[1]))
        if tag in _LOGIC:
            return Logic(tag, self.expr(d[1]), self.expr(d[2]))
        if tag in ("forall", "exists"):
            saved = dict(self.scope)
            vs = []
            for vd in d[1]:
                if not (isinstance(vd, list) and len(vd) == 3 and vd[0] == "var"):
                    raise SerializationError(f"bad bound variable {vd!r}")
                v = Var(vd[1], _sort(vd[2]))
                self.scope[v.name] = v
                vs.append(v)
            body = self.expr(d[2])
            self.scope = saved
            return Quant(tag, tuple(vs), body)
        raise SerializationError(f"unknown expression tag {tag!r}")

    def term(self, d: Any) -> Term:
        if isinstance(d, list) and d and d[0] == "name":
            return Name(d[1])
        if isinstance(d, list) and len(d) == 3 and d[0] == "app" and isinstance(d[1], list):
            fn = self.term(d[1])
            if not isinstance(fn, Name):
                raise SerializationError(f"bad lemma application {d!r}")
            return TermApp(fn, tuple(self.term(a) for a in d[2]))
        return self.expr(d)

    def tactic(self, d: Any) -> Tactic:
        if not isinstance(d, list) or not d:
            raise SerializationError(f"bad tactic {d!r}")
        kw = d[0]
        simple = {"ring": Ring, "omega": Omega, "positivity": Positivity, "rfl": Rfl,
                  "decide": Decide, "constructor": Constructor, "assumption": Assumption}
        if kw in simple and len(d) == 1:
            return simple[kw]()
        with_lemmas = {"linarith": Linarith, "nlinarith": Nlinarith, "norm_num": NormNum}
        if kw in with_lemmas:
            return with_lemmas[kw](lemmas=tuple(self.term(t) for t in d[1]))
        if kw == "simp":
            return Simp(only=bool(d[1]), lemmas=tuple(self.term(t) for t in d[2]),
                        at=tuple(d[3]))
        if kw == "intro":
            return Intro(names=tuple(d[1]))
        if kw == "exact":
            return Exact(term=self.term(d[1]))
        if kw == "apply":
            return Apply(term=self.term(d[1]))
        if kw == "rw":
            return Rewrite(rules=tuple((self.term(t), bool(r)) for t, r in d[1]), at=tuple(d[2]))
        if kw == "use":
            return Use(witnesses=tuple(self.expr(w) for w in d[1]))
        if kw == "steps":
            return Steps(tactics=tuple(self.tactic(t) for t in d[1]))
        if kw == "branches":
            return Branches(branches=tuple(self.tactic(t) for t in d[1]))
        if kw == "raw":
            return RawTactic(text=d[1])
        raise SerializationError(f"unknown tactic {kw!r}")


def theorem_from_canonical(data: Mapping[str, Any], *, imports: Iterable[str] = ()) -> Any:
    """Rebuild a :class:`~pyleanx.Theorem` from ``Theorem.canonical()`` output.

    ``imports`` are added to the theorem's own imports (canonical lemma references do
    not record the modules they need, so callers such as the bank store the resolved
    import list separately).
    """
    from .theorem import Theorem

    try:
        variables = [Var(name, _sort(sort)) for tag, name, sort in data["variables"]]
        dec = _Decoder({v.name: v for v in variables})
        hyps = [(name, dec.expr(prop)) for name, prop in data["assumptions"]]
        concl = dec.expr(data["conclusion"])
        dec.in_proof = True
        proof =dec.tactic(data["proof"]) if data.get("proof") is not None else None
        thm_imports = list(dict.fromkeys([*data.get("imports", []), *imports]))
        thm = Theorem(data["name"], variables, hyps, concl, imports=thm_imports, proof=proof)
    except SerializationError:
        raise
    except (KeyError, TypeError, ValueError, IndexError) as exc:
        raise SerializationError(f"malformed canonical theorem: {exc}") from exc
    except PyLeanXError as exc:
        raise SerializationError(f"canonical theorem is not well-formed: {exc}") from exc
    expected = dict(data)
    expected["imports"] = thm_imports
    if _json(thm.canonical()) != _json(expected):
        raise SerializationError("rebuilt theorem differs from its canonical description")
    return thm
