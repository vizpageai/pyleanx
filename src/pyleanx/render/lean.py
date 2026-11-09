"""IR -> Lean 4 source.

Rendering is pure and deterministic: identical IR (and import settings) always
yields byte-identical Lean text. Parenthesisation follows Lean 4 notation
precedences, erring on the side of extra parentheses.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING

from ..errors import UnsupportedConstructError
from ..expr import (
    App,
    BinOp,
    Cast,
    Compare,
    Expr,
    Lit,
    Logic,
    Neg,
    NotP,
    PropConst,
    Quant,
    Var,
)
from ..imports import resolve_imports
from ..proofs import (
    Apply,
    Branches,
    Exact,
    Intro,
    Name,
    RawTactic,
    Rewrite,
    Simp,
    Steps,
    Tactic,
    Term,
    TermApp,
    Use,
    _Simple,
    _WithLemmas,
)
from ..types import Nat, Sort
from .sourcemap import SourceMap, SourceSpan

if TYPE_CHECKING:
    from ..theorem import Theorem

MAX = 1024  # atoms / applications

_ARITH = {
    # op: (symbol, precedence, lhs_min, rhs_min)
    "add": ("+", 65, 65, 66),
    "sub": ("-", 65, 65, 66),
    "mul": ("*", 70, 70, 71),
    "div": ("/", 70, 70, 71),
    "mod": ("%", 70, 70, 71),
    "pow": ("^", 75, 76, 75),
    "smul": ("•", 73, 74, 73),
}
_CMP = {"eq": "=", "ne": "≠", "lt": "<", "le": "≤", "gt": ">", "ge": "≥"}
_LOGIC = {
    "iff": ("↔", 20, 21, 21),
    "implies": ("→", 25, 26, 25),
    "or": ("∨", 30, 31, 30),
    "and": ("∧", 35, 36, 35),
}


def _paren(text: str, prec: int, need: int) -> str:
    return f"({text})" if prec < need else text


def _has_anchor(e: Expr) -> bool:
    """Does this arithmetic group contain a leaf that fixes its type for Lean?"""
    from ..terms import Apply, Ascribe, BigOp, Const, Field, Norm

    if isinstance(e, (Var, Cast, App, Const, Apply, Ascribe, BigOp, Field, Norm)):
        return True
    if isinstance(e, BinOp):
        if e.op == "pow":
            return _has_anchor(e.lhs)
        return _has_anchor(e.lhs) or _has_anchor(e.rhs)
    if isinstance(e, Neg):
        return _has_anchor(e.arg)
    return False


def _needs_ascription(sort: Sort | None, *group: Expr) -> bool:
    if sort is None or sort is Nat or sort.opaque:
        return False
    return not any(_has_anchor(g) for g in group)


def _lit_text(value: Fraction) -> tuple[str, int]:
    if value.denominator == 1:
        n = value.numerator
        return (str(n), MAX) if n >= 0 else (f"-{-n}", 75)
    num, den = value.numerator, value.denominator
    text = f"{num} / {den}" if num >= 0 else f"-{-num} / {den}"
    return text, 70


class _ExprRenderer:
    def __init__(self, unicode_types: bool = False) -> None:
        self.unicode_types = unicode_types

    def render(self, e: Expr, ascribe: bool = False) -> tuple[str, int]:
        """Return (text, precedence) for ``e``."""
        if isinstance(e, Var):
            return e.name, MAX
        if isinstance(e, Lit):
            text, prec = _lit_text(e.value)
            if ascribe and e.sort is not None:
                return f"({text} : {e.sort.lean_name(self.unicode_types)})", MAX
            return text, prec
        if isinstance(e, PropConst):
            return ("True" if e.value else "False"), MAX
        if isinstance(e, BinOp):
            sym, prec, lmin, rmin = _ARITH[e.op]
            lt = self.sub(e.lhs, lmin, ascribe)
            if e.op == "pow":
                rt = self.sub(e.rhs, rmin, _needs_ascription(e.rhs.sort, e.rhs))
            else:
                rt = self.sub(e.rhs, rmin, ascribe)
            return f"{lt} {sym} {rt}", prec
        if isinstance(e, Neg):
            inner, iprec = self.render(e.arg, ascribe)
            return "-" + (inner if iprec >= MAX else f"({inner})"), 75
        if isinstance(e, Cast):
            inner, iprec = self.render(e.arg, _needs_ascription(e.arg.sort, e.arg))
            if iprec < MAX:
                inner = f"({inner})"
            return f"(↑{inner} : {e.sort.lean_name(self.unicode_types)})", MAX
        if isinstance(e, App):
            if not e.args:  # a constant such as Real.pi
                return e.func.lean_name, MAX
            parts = [e.func.lean_name]
            for a in e.args:
                parts.append(self.sub(a, MAX, _needs_ascription(a.sort, a)))
            return " ".join(parts), MAX - 1
        if isinstance(e, Compare):
            asc = _needs_ascription(e.lhs.sort, e.lhs, e.rhs)
            lt = self.sub(e.lhs, 51, asc)
            rt = self.sub(e.rhs, 51, asc)
            return f"{lt} {_CMP[e.op]} {rt}", 50
        if isinstance(e, NotP):
            return f"¬{self.sub(e.arg, 40)}", 40
        if isinstance(e, Logic):
            sym, prec, lmin, rmin = _LOGIC[e.op]
            return f"{self.sub(e.lhs, lmin)} {sym} {self.sub(e.rhs, rmin)}", prec
        if isinstance(e, Quant):
            q = "∀" if e.kind == "forall" else "∃"
            return f"{q} {binder_groups(e.vars, self.unicode_types)}, {self.sub(e.body, 0)}", 0
        return self.render_term(e)

    def type_text(self, s: Sort) -> str:
        return s.lean_name(self.unicode_types)

    def render_term(self, e: Expr) -> tuple[str, int]:
        from ..terms import Apply, Ascribe, BigOp, Const, Field, Lam, Norm, Pair, TypeTerm

        if isinstance(e, Const):
            return e.name, MAX
        if isinstance(e, TypeTerm):
            text = self.type_text(e.type)
            simple = " " not in text or (text.startswith("(") and text.endswith(")"))
            return (text if simple else f"({text})"), MAX
        if isinstance(e, Apply):
            parts = [self.sub(e.fn, MAX)]
            parts.extend(self.sub(a, MAX) for a in e.args)
            return " ".join(parts), MAX - 1
        if isinstance(e, Lam):
            return (f"fun {binder_groups(e.vars, self.unicode_types)} => "
                    f"{self.sub(e.body, 0)}"), 0
        if isinstance(e, BigOp):
            sym = {"sum": "∑", "prod": "∏", "integral": "∫"}[e.kind]
            v = e.var
            if e.bounds is not None:
                lo, hi = (self.sub(b, MAX) for b in e.bounds)
                head = f"{sym} {v.name} in {lo}..{hi}"
            elif e.over is not None:
                head = f"{sym} {v.name} ∈ {self.sub(e.over, MAX)}"
            else:
                head = f"{sym} {v.name} : {self.type_text(v.sort)}"
            # Mathlib parses the body of ∑/∏/∫ at precedence 67: `∑ i, f i + 1` would mean
            # `(∑ i, f i) + 1`, so lower-precedence bodies are parenthesized.
            return f"{head}, {self.sub(e.body, 67)}", 0
        if isinstance(e, Pair):
            return f"({self.sub(e.fst, 0)}, {self.sub(e.snd, 0)})", MAX
        if isinstance(e, Field):
            return f"{self.sub(e.arg, MAX)}.{e.name}", MAX
        if isinstance(e, Ascribe):
            return f"({self.sub(e.arg, 0)} : {self.type_text(e.sort)})", MAX
        if isinstance(e, Norm):
            return f"‖{self.sub(e.arg, 0)}‖", MAX
        from ..terms import StructLit

        if isinstance(e, StructLit):
            vals = ", ".join(f"{n} := {self.sub(v, 0)}" for n, v in e.values)
            return f"({{ {vals} }} : {self.type_text(e.sort)})", MAX
        raise UnsupportedConstructError(f"cannot render {type(e).__name__}")  # pragma: no cover

    def sub(self, e: Expr, need: int, ascribe: bool = False) -> str:
        text, prec = self.render(e, ascribe)
        if prec < need:
            return f"({text})"
        # Arguments in application position must be atoms.
        if need >= MAX and prec < MAX:
            return f"({text})"
        return text


def render_expr(e: Expr, unicode_types: bool = False) -> str:
    asc = _needs_ascription(e.sort, e) if e.sort is not None and e.sort.numeric else False
    return _ExprRenderer(unicode_types).render(e, asc)[0]


def binder_groups(variables: Sequence[Var], unicode_types: bool = False) -> str:
    """``(x y : Real) (n : Nat)`` grouping consecutive variables of the same sort."""
    groups: list[tuple[Sort, list[str]]] = []
    for v in variables:
        if groups and groups[-1][0] is v.sort:
            groups[-1][1].append(v.name)
        else:
            groups.append((v.sort, [v.name]))
    return " ".join(f"({' '.join(ns)} : {s.lean_name(unicode_types)})" for s, ns in groups)


# =====================================================================================
# Tactics
# =====================================================================================


def render_term(t: Term) -> str:
    if isinstance(t, Name):
        return t.name
    if isinstance(t, TermApp):
        args = []
        for a in t.args:
            text = render_term(a)
            atomic = isinstance(a, Name) or (isinstance(a, Var))
            args.append(text if atomic else f"({text})")
        return " ".join([t.fn.name, *args])
    if isinstance(t, Expr):
        return render_expr(t)
    raise UnsupportedConstructError(f"cannot render term {t!r}")  # pragma: no cover


def _lemma_list(lemmas: Sequence[Term]) -> str:
    return "[" + ", ".join(render_term(t) for t in lemmas) + "]"


def _at(names: Sequence[str]) -> str:
    return (" at " + " ".join(names)) if names else ""


def render_tactic_lines(t: Tactic) -> list[str]:
    """Lines (without base indentation) for one tactic node."""
    if isinstance(t, Steps):
        return [line for s in t.tactics for line in render_tactic_lines(s)]
    if isinstance(t, Branches):
        out: list[str] = []
        for b in t.branches:
            lines = render_tactic_lines(b)
            out.append("· " + lines[0])
            out.extend("  " + ln for ln in lines[1:])
        return out
    if isinstance(t, Simp):
        head = "simp only" if t.only else "simp"
        lem = (" " + _lemma_list(t.lemmas)) if (t.lemmas or t.only) else ""
        return [head + lem + _at(t.at)]
    if isinstance(t, _WithLemmas):
        return [t.keyword + ((" " + _lemma_list(t.lemmas)) if t.lemmas else "")]
    if isinstance(t, _Simple):
        return [t.keyword]
    if isinstance(t, Intro):
        return ["intro " + " ".join(t.names)]
    if isinstance(t, Exact):
        return ["exact " + render_term(t.term)]
    if isinstance(t, Apply):
        return ["apply " + render_term(t.term)]
    if isinstance(t, Rewrite):
        rules = ", ".join(("← " if r else "") + render_term(x) for x, r in t.rules)
        return [f"rw [{rules}]" + _at(t.at)]
    if isinstance(t, Use):
        ws = []
        for w in t.witnesses:
            text = render_expr(w)
            ws.append(text)
        return ["use " + ", ".join(ws)]
    if isinstance(t, RawTactic):
        return t.text.splitlines()
    return _structured_lines(t)


def _by(t: Tactic | None, indent: str = "  ") -> list[str]:
    """``by <tactic>`` on one line when short, else ``by`` + an indented block."""
    from ..proofs import Auto

    lines = render_tactic_lines(t if t is not None else Auto())
    if len(lines) == 1:
        return ["by " + lines[0]]
    return ["by", *(indent + ln for ln in lines)]


def _attach(head: str, block: list[str], indent: str = "  ") -> list[str]:
    """``head`` followed by a ``by`` block (continuation lines indented under it)."""
    return [head + " " + block[0], *(indent + ln for ln in block[1:])]


def _structured_lines(t: Tactic) -> list[str]:
    from ..proofs import Auto, Calc, Cases, Ext, Have, Induction, Obtain, Show, Unfold

    if isinstance(t, Auto):
        return ["first", *("  | " + alt for alt in t.alternatives())]
    if isinstance(t, Have):
        return _attach(f"have {t.name} : {render_expr(t.prop)} :=", _by(t.proof))
    if isinstance(t, Show):
        return [f"show {render_expr(t.prop)}"]
    if isinstance(t, Calc):
        out = [f"calc {render_expr(t.first)}"]
        for rel, rhs, proof in t.links:
            out.extend("  " + ln for ln in _attach(f"_ {rel} {render_expr(rhs)} :=", _by(proof)))
        return out
    if isinstance(t, Obtain):
        return [f"obtain ⟨{', '.join(t.names)}⟩ := {render_term(t.source)}"]
    if isinstance(t, Cases):
        alts = " | ".join(
            (f"⟨{', '.join(a)}⟩" if len(a) > 1 else a[0]) for a in t.alternatives)
        return [f"rcases {render_term(t.source)} with {alts}"]
    if isinstance(t, Induction):
        k, ih = t.succ_names
        return [f"induction {t.var} with",
                *_alternative("| zero =>", t.zero),
                *_alternative(f"| succ {k} {ih} =>", t.succ)]
    if isinstance(t, Unfold):
        return ["unfold " + " ".join(t.names)]
    if isinstance(t, Ext):
        return ["ext" + ("".join(" " + n for n in t.names))]
    raise UnsupportedConstructError(f"cannot render tactic {type(t).__name__}")


def _alternative(head: str, t: Tactic | None) -> list[str]:
    """``| case => tac`` (one line) or the block on its own, deeper-indented lines."""
    from ..proofs import Auto

    lines = render_tactic_lines(t if t is not None else Auto())
    if len(lines) == 1:
        return [f"{head} {lines[0]}"]
    return [head, *("    " + ln for ln in lines)]


# =====================================================================================
# Modules
# =====================================================================================


def _statement_parts(thm: Theorem, r: _ExprRenderer) -> tuple[str, str]:
    """(``theorem name binders :``, rendered conclusion)."""
    binders = []
    if thm.variables:
        binders.append(binder_groups(thm.variables, r.unicode_types))
    for h in thm.assumptions:
        binders.append(f"({h.name} : {r.render(h.prop)[0]})")
    head = f"theorem {thm.name}" + ((" " + " ".join(binders)) if binders else "") + " :"
    return head, r.render(thm.conclusion)[0]


def render_statement(thm: Theorem, unicode_types: bool = False) -> str:
    """``theorem name binders :\\n    conclusion`` with no proof (for hashing/display)."""
    head, concl = _statement_parts(thm, _ExprRenderer(unicode_types))
    return f"{head}\n    {concl}"


def render_open_statement(thm: Theorem, unicode_types: bool = False) -> str:
    """The statement with a ``sorry`` placeholder, used ONLY to open an interactive
    proof state. Never part of anything that is verified."""
    from ..defs import theorem_definitions

    head, concl = _statement_parts(thm, _ExprRenderer(unicode_types))
    defs = [ln for d in theorem_definitions(thm) for ln in (*d.render(unicode_types), "")]
    return "\n".join(defs) + f"{head}\n    {concl} := by\n  sorry"


@dataclass(frozen=True)
class RenderedModule:
    source: str
    source_map: SourceMap
    imports: tuple[str, ...]
    theorem_names: tuple[str, ...]


class _Builder:
    def __init__(self) -> None:
        self.lines: list[str] = []
        self.spans: list[SourceSpan] = []

    @property
    def next_line(self) -> int:
        return len(self.lines) + 1

    def add(self, *lines: str) -> tuple[int, int]:
        start = self.next_line
        self.lines.extend(lines)
        return start, self.next_line - 1


def _uses_auto(t: Tactic | None) -> bool:
    from ..proofs import Auto

    if t is None:
        return False
    if isinstance(t, Auto) or _auto_default(t):
        return True
    return any(_uses_auto(s) for s in t.sub_tactics())


def _auto_default(t: Tactic) -> bool:
    """Structured steps without an explicit proof are closed by ``auto``."""
    name = type(t).__name__
    if name == "Have":
        return getattr(t, "proof", None) is None
    if name == "Calc":
        return any(p is None for _, _, p in getattr(t, "links", ()))
    if name == "Induction":
        return getattr(t, "zero", None) is None or getattr(t, "succ", None) is None
    return False


def render_module(
    theorems: Sequence[Theorem],
    *,
    import_mode: str = "minimal",
    extra_imports: Sequence[str] = (),
    audit: bool = True,
    unicode_types: bool = False,
) -> RenderedModule:
    """Render one Lean file containing ``theorems`` in order (later ones may cite earlier)."""
    names = [t.name for t in theorems]
    if len(set(names)) != len(names):
        from ..errors import ScopeError

        raise ScopeError(f"duplicate theorem names in one module: {names}")
    imports = resolve_imports(theorems, extra_imports, import_mode, unicode_types)
    b = _Builder()
    header_lines = [f"import {m}" for m in imports]
    if header_lines:
        header_lines.append("")
    header_lines.append("set_option autoImplicit false")
    if any(_uses_auto(t.proof) for t in theorems):
        # `first | …` alternatives that are never tried would each produce linter warnings.
        header_lines += ["set_option linter.unusedTactic false",
                         "set_option linter.unreachableTactic false"]
    s, e = b.add(*header_lines)
    b.spans.append(SourceSpan(s, e, "header", None, "imports and options"))
    from ..defs import module_definitions

    for d in module_definitions(theorems):
        b.add("")
        s, e = b.add(*d.render(unicode_types))
        b.spans.append(SourceSpan(s, e, "definition", None, f"definition {d.name}", d.origin))
    r = _ExprRenderer(unicode_types)
    for thm in theorems:
        b.add("")
        thm_start = b.next_line
        head, concl = _statement_parts(thm, r)
        s, e = b.add(head)
        b.spans.append(SourceSpan(s, e, "binders", thm.name, "variables and hypotheses",
                                  thm.origin))
        for h in thm.assumptions:
            b.spans.append(SourceSpan(s, e, "hypothesis", thm.name, f"hypothesis {h.name}",
                                      h.origin or thm.origin))
        if thm.proof is None:
            # Statement-only rendering (compile/show-lean). Never verified.
            s, e = b.add(f"    {concl} := by")
            b.spans.append(SourceSpan(s, e, "statement", thm.name, "conclusion", thm.origin))
            s, e = b.add("  fail \"pyleanx: no proof supplied\"")
            b.spans.append(SourceSpan(s, e, "tactic", thm.name, "missing proof", thm.origin))
        else:
            s, e = b.add(f"    {concl} := by")
            b.spans.append(SourceSpan(s, e, "statement", thm.name, "conclusion", thm.origin))
            for idx, step in enumerate(thm.proof.flat(), start=1):
                lines = render_tactic_lines(step)
                s, e = b.add(*("  " + ln for ln in lines))
                label = f"step {idx}: {lines[0].strip()}"
                b.spans.append(SourceSpan(s, e, "tactic", thm.name, label, step.origin))
        thm_end = b.next_line - 1
        b.spans.append(SourceSpan(thm_start, thm_end, "theorem", thm.name, thm.name, thm.origin))
        if audit:
            b.add("")
            s, e = b.add(f"#print axioms {thm.name}")
            b.spans.append(SourceSpan(s, e, "axiom_audit", thm.name, "axiom audit"))
    source = "\n".join(b.lines) + "\n"
    return RenderedModule(source, SourceMap(b.spans), imports, tuple(names))
