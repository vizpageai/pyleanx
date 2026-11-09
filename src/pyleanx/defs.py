"""User definitions: ``@pl.define`` (functions), ``pl.define_type`` (type abbreviations) and
``@pl.structure`` (records), rendered as Lean ``def``/``abbrev``/``structure``.

Definitions are emitted, in dependency order, before the theorems that use them in the same
Lean file, so Lean checks them together; an error in a definition rejects every theorem in
that file (fail closed). Definitions contain no proofs, so they cannot smuggle ``sorry``;
the axiom audit of each theorem still covers everything it depends on.

    Vec = pl.define_type("Vec", pl.EuclideanSpace(3))

    @pl.define(returns=pl.Real)
    def q(v: Vec):
        return pl.sqrt(1 + pl.norm(v)**2)

    @pl.structure
    class Datum:
        f0: pl.Fn(pl.Prod(Vec, Vec), pl.Real)
        E0: pl.Fn(Vec, Vec)
"""

from __future__ import annotations

import inspect
from collections.abc import Callable, Iterable
from typing import Any

from ._origin import Origin, caller_origin, resolve_annotations
from .binders import check_scope
from .errors import ScopeError, SortError
from .expr import Expr, Var, _lift, iter_subexprs, make_var
from .names import validate_identifier, validate_qualified_name
from .terms import Apply, Const
from .types import UNKNOWN, Fn, LeanType, Sort, _intern

__all__ = ["Definition", "TypeDefinition", "StructureDefinition", "define", "define_type",
           "structure", "collect_definitions", "mk"]


class _Def:
    """Common behaviour of the three kinds of definitions."""

    name: str
    origin: Origin | None
    doc: str

    def dependencies(self) -> list[_Def]:  # pragma: no cover - abstract
        raise NotImplementedError

    def imports(self) -> list[str]:  # pragma: no cover - abstract
        raise NotImplementedError

    def render(self, unicode_types: bool = False) -> list[str]:  # pragma: no cover
        raise NotImplementedError

    def canonical(self) -> Any:  # pragma: no cover - abstract
        raise NotImplementedError

    def _doc_lines(self) -> list[str]:
        if not self.doc:
            return []
        text = " ".join(self.doc.split()).replace("-/", "- /")
        return [f"/-- {text} -/"]

    def __repr__(self) -> str:
        return f"<pl.{type(self).__name__} {self.name}>"


def _sort_defs(s: Sort) -> list[_Def]:
    return [d for d in getattr(s, "definitions", ()) if isinstance(d, _Def)]


def _expr_defs(e: Expr) -> list[_Def]:
    from .terms import Ascribe, BigOp, Lam, TypeTerm

    out: list[_Def] = []
    for sub in iter_subexprs(e):
        if isinstance(sub, Const) and isinstance(sub.definition, _Def):
            out.append(sub.definition)
        if sub.sort is not None:
            out.extend(_sort_defs(sub.sort))
        if isinstance(sub, TypeTerm):
            out.extend(_sort_defs(sub.type))
        if isinstance(sub, (Lam, BigOp)):
            for v in sub.vars:
                out.extend(_sort_defs(v.sort))
        if isinstance(sub, Ascribe):
            out.extend(_sort_defs(sub.sort))
        quant_vars = getattr(sub, "vars", None)
        if quant_vars and not isinstance(sub, (Lam, BigOp)):
            for v in quant_vars:
                out.extend(_sort_defs(v.sort))
    return out


class Definition(_Def):
    """``noncomputable def name (params) : returns := body``."""

    def __init__(self, name: str, params: tuple[Var, ...], body: Expr, returns: Sort, *,
                 doc: str = "", origin: Origin | None = None) -> None:
        self.name = validate_qualified_name(name, "definition name")
        self.params = params
        self.body = body
        self.returns = returns
        self.doc = doc
        self.origin = origin
        names = {}
        for p in params:
            if p.name in names:
                raise ScopeError(f"definition {name}: parameter {p.name!r} declared twice")
            names[p.name] = p
        check_scope(body, names, f"definition {name}")

    @property
    def sort(self) -> Sort:
        return Fn(*(p.sort for p in self.params), self.returns) if self.params else self.returns

    @property
    def const(self) -> Const:
        return Const(self.name, self.sort, (), definition=self,
                     arity=len(self.params), result=self.returns)

    def __call__(self, *args: object) -> Expr:
        if len(args) != len(self.params):
            raise SortError(f"{self.name} takes {len(self.params)} argument(s), got {len(args)}")
        if not args:
            return self.const
        from .terms import _arg

        return Apply(self.const, tuple(_arg(a) for a in args), self.returns)

    def dependencies(self) -> list[_Def]:
        out = [d for p in self.params for d in _sort_defs(p.sort)]
        out.extend(_sort_defs(self.returns))
        out.extend(_expr_defs(self.body))
        return [d for d in out if d is not self]

    def imports(self) -> list[str]:
        from .imports import expr_imports

        out = [i for p in self.params for i in p.sort.imports]
        out.extend(self.returns.imports)
        out.extend(i for i in expr_imports(self.body))
        return out

    def render(self, unicode_types: bool = False) -> list[str]:
        from .render.lean import _ExprRenderer, binder_groups

        r = _ExprRenderer(unicode_types)
        binders = (" " + binder_groups(self.params, unicode_types)) if self.params else ""
        ret = self.returns.lean_name(unicode_types)
        head = f"noncomputable def {self.name}{binders} : {ret} :="
        return [*self._doc_lines(), head, "  " + r.render(self.body)[0]]

    def canonical(self) -> Any:
        return ["def", self.name, [p.canonical() for p in self.params], self.body.canonical(),
                self.returns.canonical(), self.doc]


class TypeDefinition(_Def):
    """``abbrev Name : Type := <type>`` (a reducible name for a type)."""

    def __init__(self, name: str, target: Sort, *, doc: str = "",
                 origin: Origin | None = None) -> None:
        self.name = validate_qualified_name(name, "type name")
        self.target = target
        self.doc = doc
        self.origin = origin
        self.type: LeanType = _intern(LeanType(
            self.name, self.name, numeric=False, rank=-2, imports=(), opaque=True,
            kind=target.kind if isinstance(target, LeanType) and target.kind == "struct"
            else "type",
            fields=target.fields if isinstance(target, LeanType) else (),
            definitions=(self,), latex=target.latex))

    def dependencies(self) -> list[_Def]:
        return _sort_defs(self.target)

    def imports(self) -> list[str]:
        return list(self.target.imports)

    def render(self, unicode_types: bool = False) -> list[str]:
        return [*self._doc_lines(),
                f"abbrev {self.name} : Type := {self.target.lean_name(unicode_types)}"]

    def canonical(self) -> Any:
        return ["abbrev", self.name, self.target.canonical(), self.doc]


class StructureDefinition(_Def):
    """``structure Name where field : T …``."""

    def __init__(self, name: str, fields: tuple[tuple[str, Sort], ...], *, doc: str = "",
                 origin: Origin | None = None) -> None:
        self.name = validate_qualified_name(name, "structure name")
        if not fields:
            raise SortError(f"structure {name} needs at least one field")
        seen = set()
        for fname, fsort in fields:
            validate_identifier(fname, "field name")
            if fname in seen:
                raise ScopeError(f"structure {name}: field {fname!r} declared twice")
            if not isinstance(fsort, Sort):
                raise SortError(f"structure {name}: field {fname!r} needs a sort, got {fsort!r}")
            seen.add(fname)
        self.fields = fields
        self.doc = doc
        self.origin = origin
        self.type: LeanType = _intern(LeanType(
            self.name, self.name, numeric=False, rank=-2, imports=(), opaque=True,
            kind="struct", fields=fields, definitions=(self,)))

    def dependencies(self) -> list[_Def]:
        return [d for _, s in self.fields for d in _sort_defs(s)]

    def imports(self) -> list[str]:
        return [i for _, s in self.fields for i in s.imports]

    def render(self, unicode_types: bool = False) -> list[str]:
        lines = [*self._doc_lines(), f"structure {self.name} where"]
        lines += [f"  {n} : {s.lean_name(unicode_types)}" for n, s in self.fields]
        return lines

    def canonical(self) -> Any:
        return ["structure", self.name, [[n, s.canonical()] for n, s in self.fields], self.doc]


# =====================================================================================
# Public API
# =====================================================================================


def define(fn: Callable[..., object] | None = None, *, returns: Sort | None = None,
           name: str | None = None) -> Any:
    """Turn a Python function into a Lean definition (``noncomputable def``).

    Parameter annotations give the argument sorts; ``returns`` the result sort (inferred
    from the body when PyLeanX knows it). The function runs once, with fresh symbols.
    Returns a :class:`Definition`, which is called like a function in statements.
    """

    def build(f: Callable[..., object]) -> Definition:
        hints = resolve_annotations(f)
        origin = Origin(f.__code__.co_filename, f.__code__.co_firstlineno)
        params = []
        for pname in inspect.signature(f).parameters:
            sort = hints.get(pname)
            if not isinstance(sort, Sort):
                raise SortError(f"@define {f.__name__}: parameter {pname!r} needs a sort "
                                "annotation such as `x: pl.Real`")
            params.append(make_var(pname, sort, origin))
        body = _lift(f(*params))
        ret = returns or body.sort
        if ret is None or ret is UNKNOWN:
            raise SortError(f"@define {f.__name__}: cannot infer the result sort; pass "
                            "returns=…")
        return Definition(name or f.__name__, tuple(params), body, ret,
                          doc=(f.__doc__ or "").strip(), origin=origin)

    return build(fn) if fn is not None else build


def define_type(name: str, target: Sort, *, doc: str = "") -> LeanType:
    """``abbrev name : Type := target``; returns the new type (a sort)."""
    if not isinstance(target, Sort):
        raise SortError("define_type needs a sort, e.g. pl.EuclideanSpace(3)")
    return TypeDefinition(name, target, doc=doc, origin=caller_origin()).type


def structure(cls: type | None = None, *, name: str | None = None) -> Any:
    """Turn an annotated class into a Lean ``structure``; returns the new type (a sort).

    Fields of a structure-typed variable are accessed as attributes (``d.f0``) and
    instances are built with ``pl.mk(T, f0=…, …)``.
    """

    def build(c: type) -> LeanType:
        hints = resolve_annotations(c)
        fields: list[tuple[str, Sort]] = []
        for k, v in hints.items():
            if not isinstance(v, Sort):
                raise SortError(f"@structure {c.__name__}: field {k!r} needs a sort")
            fields.append((k, v))
        return StructureDefinition(name or c.__name__, tuple(fields),
                                   doc=(c.__doc__ or "").strip(),
                                   origin=caller_origin()).type

    return build(cls) if cls is not None else build


def mk(struct: LeanType, **values: object) -> Expr:
    """A structure value ``{ f0 := …, E0 := … }`` of type ``struct``."""
    from .terms import StructLit

    if not isinstance(struct, LeanType) or struct.kind != "struct":
        raise SortError("pl.mk needs a structure type made with @pl.structure")
    names = [n for n, _ in struct.fields]
    if set(values) != set(names):
        raise SortError(f"pl.mk({struct.name}): give exactly the fields {names}")
    return StructLit(tuple((n, _lift(values[n])) for n in names), struct)


def collect_definitions(exprs: Iterable[Expr], sorts: Iterable[Sort] = ()) -> list[_Def]:
    """All definitions used (transitively), dependencies first, each once."""
    roots: list[_Def] = []
    for e in exprs:
        roots.extend(_expr_defs(e))
    for s in sorts:
        roots.extend(_sort_defs(s))
    order: list[_Def] = []
    state: dict[int, str] = {}

    def visit(d: _Def, stack: tuple[str, ...]) -> None:
        st = state.get(id(d))
        if st == "done":
            return
        if st == "active":
            raise ScopeError("definition cycle: " + " -> ".join((*stack, d.name)))
        state[id(d)] = "active"
        for dep in d.dependencies():
            visit(dep, (*stack, d.name))
        state[id(d)] = "done"
        order.append(d)

    for d in roots:
        visit(d, ())
    names: dict[str, _Def] = {}
    for d in order:
        other = names.get(d.name)
        if other is not None and other is not d:
            raise ScopeError(f"two different definitions are named {d.name!r}")
        names[d.name] = d
    return order


def proof_exprs(t: object) -> list[Expr]:
    """Expressions appearing inside a tactic tree (witnesses, terms, ``have`` statements)."""
    import dataclasses

    out: list[Expr] = []

    def walk(x: object) -> None:
        if isinstance(x, Expr):
            out.append(x)
        elif isinstance(x, (tuple, list)):
            for y in x:
                walk(y)
        elif dataclasses.is_dataclass(x) and not isinstance(x, type):
            for f in dataclasses.fields(x):
                if f.name != "origin":
                    walk(getattr(x, f.name))

    walk(t)
    return out


def theorem_definitions(thm: Any) -> list[_Def]:
    """Definitions a theorem needs (statement, variable sorts and proof), in order."""
    exprs = [thm.conclusion, *(h.prop for h in thm.assumptions)]
    if thm.proof is not None:
        exprs.extend(proof_exprs(thm.proof))
    return collect_definitions(exprs, [v.sort for v in thm.variables])


def module_definitions(theorems: Iterable[Any]) -> list[_Def]:
    """Definitions for several theorems, each emitted once, dependencies first."""
    order: list[_Def] = []
    seen: set[int] = set()
    for thm in theorems:
        for d in theorem_definitions(thm):
            if id(d) not in seen:
                seen.add(id(d))
                order.append(d)
    names: dict[str, _Def] = {}
    for d in order:
        if names.setdefault(d.name, d) is not d:
            raise ScopeError(f"two different definitions are named {d.name!r}")
    return order
