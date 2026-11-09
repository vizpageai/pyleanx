"""IR -> LaTeX, for display only (Jupyter, docs, papers).

LaTeX output is a human-readable *view*. It is never sent to Lean and plays no
part in verification; ``to_lean()`` remains the authoritative statement.
"""

from __future__ import annotations

from collections.abc import Sequence
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
from ..types import Sort

if TYPE_CHECKING:
    from ..theorem import Theorem

MAX = 1024

_GREEK = {
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta", "ε": r"\varepsilon",
    "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta", "ι": r"\iota", "κ": r"\kappa", "μ": r"\mu",
    "ν": r"\nu", "ξ": r"\xi", "ο": "o", "π": r"\pi", "ρ": r"\rho", "σ": r"\sigma",
    "ς": r"\varsigma", "τ": r"\tau", "υ": r"\upsilon", "φ": r"\varphi", "χ": r"\chi",
    "ψ": r"\psi", "ω": r"\omega", "Γ": r"\Gamma", "Δ": r"\Delta", "Θ": r"\Theta",
    "Ξ": r"\Xi", "Υ": r"\Upsilon", "Φ": r"\Phi", "Ψ": r"\Psi", "Ω": r"\Omega",
}
# Greek capitals that look like Latin letters.
_GREEK.update({g: lat for g, lat in zip("ΑΒΕΖΗΙΚΜΝΟΡΤΧ", "ABEZHIKMNOPTX", strict=True)})
_SUBSCRIPT = {chr(0x2080 + i): str(i) for i in range(10)}

_CMP = {"eq": "=", "ne": r"\neq", "lt": "<", "le": r"\leq", "gt": ">", "ge": r"\geq"}
_LOGIC = {
    # op: (symbol, prec, lhs_min, rhs_min) -- same precedences as Lean
    "iff": (r"\leftrightarrow", 20, 21, 21),
    "implies": (r"\to", 25, 26, 25),
    "or": (r"\lor", 30, 31, 30),
    "and": (r"\land", 35, 36, 35),
}
_FUNCS = {"Real.exp": r"\exp", "Real.log": r"\log", "min": r"\min", "max": r"\max"}


def latex_name(name: str) -> str:
    """``α`` -> ``\\alpha``; ``x₁``/``x1``/``x_1`` -> ``x_{1}``; ``abc`` -> ``\\mathit{abc}``."""
    stem = name.rstrip("'")
    primes = "'" * (len(name) - len(stem))
    # trailing digits (Unicode subscripts or ASCII) become a subscript
    i = len(stem)
    while i > 1 and (stem[i - 1] in _SUBSCRIPT or stem[i - 1].isdigit()):
        i -= 1
    if i < len(stem):
        base = stem[:i].rstrip("_") or stem[:i]
        sub = "".join(_SUBSCRIPT.get(c, c) for c in stem[i:])
    elif "_" in stem.strip("_"):
        base, _, rest = stem.lstrip("_").partition("_")
        sub = _base_latex(rest.replace("_", ""))
    else:
        base, sub = stem, ""
    text = _base_latex(base)
    if sub:
        text += "_{" + sub + "}"
    return text + primes


def _base_latex(base: str) -> str:
    if len(base) == 1:
        return _GREEK.get(base, base)
    if base and all(c in _GREEK for c in base):
        return " ".join(_GREEK[c] for c in base)
    # multi-letter names: italic word, Greek letters converted, underscores escaped
    word = "".join(_GREEK.get(c, c) for c in base).replace("_", r"\_")
    return r"\mathit{" + word + "}"


def _const_latex(name: str) -> str:
    """``Real.pi`` -> ``\\pi``; ``OAI.RVM.q`` -> ``\\mathrm{q}`` (last component)."""
    last = name.rsplit(".", 1)[-1]
    known = {"pi": r"\pi", "exp": r"\exp", "log": r"\log", "sin": r"\sin", "cos": r"\cos",
             "sqrt": r"\sqrt", "fderiv": r"D", "deriv": r"\frac{d}{dx}"}
    if last in known:
        return known[last]
    return latex_name(last) if len(last) == 1 else r"\operatorname{" + last.replace(
        "_", r"\_") + "}"


def latex_sort(sort: Sort) -> str:
    from ..types import LeanType

    if sort.latex:
        return sort.latex
    if isinstance(sort, LeanType):
        if sort.kind == "fn":
            *dom, cod = sort.parts
            return r" \to ".join([*(latex_sort(d) for d in dom), latex_sort(cod)])
        if sort.kind == "prod":
            return r" \times ".join(latex_sort(p) for p in sort.parts)
        text = sort.lean.replace("ℝ", r"\mathbb{R}").replace("ℕ", r"\mathbb{N}")
        return r"\mathrm{" + text.replace("_", r"\_").replace(" ", r"\ ") + "}"
    return r"\mathrm{" + sort.name + "}"


def _lit(value) -> tuple[str, int]:
    if value.denominator == 1:
        n = value.numerator
        return (str(n), MAX) if n >= 0 else (f"-{-n}", 75)
    num, den = abs(value.numerator), value.denominator
    frac = rf"\frac{{{num}}}{{{den}}}"
    return (frac, MAX) if value >= 0 else ("-" + frac, 75)


def _leftmost(e: Expr) -> Expr:
    while isinstance(e, BinOp) and e.op in ("add", "sub", "mul", "mod"):
        e = e.lhs
    if isinstance(e, BinOp) and e.op == "pow":
        return _leftmost(e.lhs)
    return e


def _paren(text: str) -> str:
    return r"\left(" + text + r"\right)"


class _Latex:
    def render(self, e: Expr) -> tuple[str, int]:
        if isinstance(e, Var):
            return latex_name(e.name), MAX
        if isinstance(e, Lit):
            return _lit(e.value)
        if isinstance(e, PropConst):
            return (r"\top" if e.value else r"\bot"), MAX
        if isinstance(e, BinOp):
            return self.binop(e)
        if isinstance(e, Neg):
            return "-" + self.sub(e.arg, 75 if not isinstance(e.arg, Neg) else MAX), 75
        if isinstance(e, Cast):
            # (n : ℝ): explicit embedding, shown the way Lean writes the ascription
            return _paren(f"{self.render(e.arg)[0]} : {latex_sort(e.sort)}"), MAX
        if isinstance(e, App):
            return self.app(e)
        if isinstance(e, Compare):
            return f"{self.sub(e.lhs, 51)} {_CMP[e.op]} {self.sub(e.rhs, 51)}", 50
        if isinstance(e, NotP):
            return rf"\neg {self.sub(e.arg, 40)}", 40
        if isinstance(e, Logic):
            sym, prec, lmin, rmin = _LOGIC[e.op]
            return f"{self.sub(e.lhs, lmin)} {sym} {self.sub(e.rhs, rmin)}", prec
        if isinstance(e, Quant):
            q = r"\forall" if e.kind == "forall" else r"\exists"
            return rf"{q} {binders_latex(e.vars)},\ {self.sub(e.body, 0)}", 0
        return self.term(e)

    def term(self, e: Expr) -> tuple[str, int]:
        from ..terms import Apply, Ascribe, BigOp, Const, Field, Lam, Norm, Pair, TypeTerm

        if isinstance(e, Const):
            if e.latex:
                return e.latex, MAX
            return _const_latex(e.name), MAX
        if isinstance(e, TypeTerm):
            return latex_sort(e.type), MAX
        if isinstance(e, Apply):
            fn = e.fn
            args = [self.render(a)[0] for a in e.args]
            if isinstance(fn, Const) and fn.latex and "{0}" in fn.latex:
                try:
                    return fn.latex.format(*args), MAX
                except IndexError:
                    pass
            head = self.sub(fn, MAX)
            return head + _paren(", ".join(args)), MAX - 1
        if isinstance(e, Lam):
            vs = ", ".join(latex_name(v.name) for v in e.vars)
            return rf"{vs} \mapsto {self.sub(e.body, 0)}", 0
        if isinstance(e, BigOp):
            v = latex_name(e.var.name)
            body = self.sub(e.body, 66)
            if e.kind == "integral":
                if e.bounds is not None:
                    lo, hi = (self.render(b)[0] for b in e.bounds)
                    return rf"\int_{{{lo}}}^{{{hi}}} {body}\, d{v}", 66
                return rf"\int_{{{latex_sort(e.var.sort)}}} {body}\, d{v}", 66
            sym = r"\sum" if e.kind == "sum" else r"\prod"
            dom = (rf"{v} \in {self.render(e.over)[0]}" if e.over is not None
                   else rf"{v} \in {latex_sort(e.var.sort)}")
            return rf"{sym}_{{{dom}}} {body}", 66
        if isinstance(e, Pair):
            return _paren(f"{self.render(e.fst)[0]}, {self.render(e.snd)[0]}"), MAX
        if isinstance(e, Field):
            name = {"1": "1", "2": "2", "fst": "1", "snd": "2"}.get(e.name)
            base = self.sub(e.arg, MAX)
            if name is not None:
                return f"{base}_{{{name}}}", MAX
            return rf"{base}.\mathrm{{{e.name.replace('_', chr(92) + '_')}}}", MAX
        if isinstance(e, Ascribe):
            return self.render(e.arg)
        if isinstance(e, Norm):
            return rf"\left\lVert {self.render(e.arg)[0]} \right\rVert", MAX
        from ..terms import StructLit

        if isinstance(e, StructLit):
            vals = r",\ ".join(rf"\mathrm{{{n}}} = {self.render(v)[0]}" for n, v in e.values)
            return r"\left\{" + vals + r"\right\}", MAX
        raise UnsupportedConstructError(f"no LaTeX for {type(e).__name__}")  # pragma: no cover

    def sub(self, e: Expr, need: int) -> str:
        text, prec = self.render(e)
        return _paren(text) if prec < need else text

    def binop(self, e: BinOp) -> tuple[str, int]:
        if e.op == "div":
            # \frac groups its arguments; no parentheses needed
            return rf"\frac{{{self.render(e.lhs)[0]}}}{{{self.render(e.rhs)[0]}}}", MAX - 1
        if e.op == "pow":
            base = self.sub(e.lhs, MAX)
            if isinstance(e.lhs, App) and e.lhs.func.lean_name == "Real.sqrt":
                base = _paren(self.render(e.lhs)[0])
            return f"{base}^{{{self.render(e.rhs)[0]}}}", 75
        if e.op in ("add", "sub"):
            sym = "+" if e.op == "add" else "-"
            return f"{self.sub(e.lhs, 65)} {sym} {self.sub(e.rhs, 66)}", 65
        if e.op == "mod":
            return rf"{self.sub(e.lhs, 70)} \bmod {self.sub(e.rhs, 71)}", 70
        if e.op == "smul":
            return rf"{self.sub(e.lhs, 74)} \, {self.sub(e.rhs, 73)}", 73
        # multiplication: juxtapose when the right factor starts with a letter-like atom
        lhs = self.sub(e.lhs, 70)
        rhs = self.sub(e.rhs, 71)
        first = _leftmost(e.rhs)
        rhs_paren = rhs.startswith(r"\left(")
        juxtapose = (isinstance(first, (Var, App)) or rhs_paren) and not rhs.startswith("-")
        sep = " " if juxtapose else r" \cdot "
        return f"{lhs}{sep}{rhs}", 70

    def app(self, e: App) -> tuple[str, int]:
        name = e.func.lean_name
        args = [self.render(a)[0] for a in e.args]
        if name == "Real.sqrt":
            return rf"\sqrt{{{args[0]}}}", MAX
        if name == "abs":
            return rf"\left|{args[0]}\right|", MAX
        custom = e.func.latex
        if custom and "{0}" in custom:
            return custom.format(*args), MAX
        if custom and not args:
            return custom, MAX
        if custom and len(args) == 1 and isinstance(e.args[0], Var):
            return f"{custom} {args[0]}", MAX - 1  # \sin x
        op = custom or _FUNCS.get(name) or r"\operatorname{" + name.replace("_", r"\_") + "}"
        return op + _paren(", ".join(args)), MAX - 1


def binders_latex(variables: Sequence[Var]) -> str:
    """``x, y \\in \\mathbb{R},\\ n \\in \\mathbb{N}`` (``P : \\mathrm{Prop}`` for propositions)."""
    groups: list[tuple[Sort, list[str]]] = []
    for v in variables:
        if groups and groups[-1][0] is v.sort:
            groups[-1][1].append(latex_name(v.name))
        else:
            groups.append((v.sort, [latex_name(v.name)]))
    parts = []
    for sort, names in groups:
        rel = ":" if sort.is_prop else r"\in"
        parts.append(f"{', '.join(names)} {rel} {latex_sort(sort)}")
    return r",\ ".join(parts)


def expr_to_latex(e: Expr) -> str:
    return _Latex().render(e)[0]


def theorem_to_latex(thm: Theorem) -> str:
    """Display-math statement: ``\\forall`` binders, hypotheses ``\\Rightarrow`` conclusion."""
    r = _Latex()
    parts = []
    if thm.variables:
        parts.append(rf"\forall {binders_latex(thm.variables)},\quad ")
    if thm.assumptions:
        hyps = r",\ ".join(r.render(h.prop)[0] for h in thm.assumptions)
        parts.append(hyps + r" \;\Longrightarrow\; ")
    parts.append(r.render(thm.conclusion)[0])
    return "".join(parts)


def theorem_markdown(thm: Theorem, lean_source: str) -> str:
    """Markdown for Jupyter: title, typeset statement, and the generated Lean."""
    status = "proof script attached" if thm.proof is not None else "no proof yet"
    hyp_lines = ""
    if thm.assumptions:
        hyp_lines = "\n".join(
            f"- ${latex_name(h.name)}:\\ {expr_to_latex(h.prop)}$" for h in thm.assumptions)
        hyp_lines = "\n\nHypotheses:\n\n" + hyp_lines
    return (
        f"**Theorem** `{thm.name}` ({status}, not yet verified)\n\n"
        f"$$\n{theorem_to_latex(thm)}\n$$"
        f"{hyp_lines}\n\n"
        f"<details><summary>Lean source</summary>\n\n```lean\n{lean_source}```\n\n</details>\n"
    )
