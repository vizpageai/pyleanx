"""A written proof read back as prose: ``pl.prose(theorem)``.

Proofs built from ``pl.let``, ``pl.claim`` and ``pl.conclude`` read like a textbook:

    Theorem. For all x ∈ ℝ: sin² x + cos² x = 1.
    Proof.
      1. Let f(t) = sin² t + cos² t.
      2. f is differentiable.
      3. f′(t) = 0 for all t.  (sin′ = cos, cos′ = −sin)
      4. f(x) = f(0), since a differentiable function with derivative 0 is constant.
      5. f(0) = 1.  (sin 0 = 0, cos 0 = 1)
      Hence sin² x + cos² x = 1. ∎

This is a *view* of the proof that Lean checks, step by step: every printed step is a
``have`` in the Lean source, and the ∎ line reports the verification result only when one
is supplied. Other tactics are shown as Lean text.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

from .expr import Expr
from .proofs import Claim, Conclude, Let, Name, Steps, Tactic, TermApp

if TYPE_CHECKING:
    from .backend.interface import VerificationResult
    from .theorem import Theorem

_SUP = str.maketrans("0123456789+-n", "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻ⁿ")
_SYMBOLS = {
    "angle": "∠", "parallel": "∥", "sim": "∼", "triangle": "△", "neg": "¬", "in": "∈",
    "notin": "∉", "forall": "∀", "exists": "∃", "le": "≤", "leq": "≤", "ge": "≥", "geq": "≥",
    "ne": "≠", "neq": "≠", "cdot": "·", "times": "×", "mapsto": "↦", "to": "→", "pi": "π",
    "Longrightarrow": "⟹", "Rightarrow": "⇒", "iff": "⟺", "land": "∧", "lor": "∨",
    "wedge": "∧", "vee": "∨", "sum": "∑", "prod": "∏", "int": "∫", "infty": "∞",
    "lvert": "|", "rvert": "|", "lVert": "‖", "rVert": "‖", "bmod": "mod", "quad": " ",
    "qquad": " ", "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε",
    "theta": "θ", "lambda": "λ", "mu": "μ", "sigma": "σ", "phi": "φ", "omega": "ω",
}
_BB = {"R": "ℝ", "N": "ℕ", "Z": "ℤ", "Q": "ℚ", "C": "ℂ"}


def _group(s: str, i: int) -> tuple[str, int]:
    """The ``{…}`` group starting at ``s[i]`` (or one character), and the index after it."""
    if i < len(s) and s[i] == "{":
        depth = 0
        for j in range(i, len(s)):
            depth += {"{": 1, "}": -1}.get(s[j], 0)
            if depth == 0:
                return s[i + 1:j], j + 1
        return s[i + 1:], len(s)
    return (s[i], i + 1) if i < len(s) else ("", i)


def _atomic(t: str) -> bool:
    return bool(re.fullmatch(r"[\w′|∠]+|\(.*\)|\|.*\|", t)) and " " not in t.strip("()|")


def latex_text(s: str) -> str:
    """Unicode text for the LaTeX PyLeanX produces (display only)."""
    out: list[str] = []
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\":
            m = re.match(r"\\([A-Za-z]+)|\\(.)", s[i:])
            assert m is not None
            cmd = m.group(1) or m.group(2)
            i += m.end()
            if cmd in ("left", "right"):
                continue
            if cmd == "frac":
                num, i = _group(s, i)
                den, i = _group(s, i)
                n, d = latex_text(num), latex_text(den)
                out.append(f"{n if _atomic(n) else f'({n})'}/{d if _atomic(d) else f'({d})'}")
            elif cmd == "sqrt":
                arg, i = _group(s, i)
                a = latex_text(arg)
                out.append(f"√{a}" if re.fullmatch(r"\w|\d+|\(.*\)", a) else f"√({a})")
            elif cmd in ("text", "operatorname", "mathrm"):
                arg, i = _group(s, i)
                out.append(arg)
            elif cmd == "mathbb":
                arg, i = _group(s, i)
                out.append(_BB.get(arg, arg))
            elif cmd == "overline":
                arg, i = _group(s, i)
                out.append(f"segment {latex_text(arg)}")
            elif cmd in (",", ";", " ", "!"):
                out.append(" " if cmd != "!" else "")
            elif cmd in _SYMBOLS:
                out.append(_SYMBOLS[cmd])
            else:
                out.append(cmd)  # \sin, \cos, \log, \exp …
            continue
        if c in "^_":
            arg, i = _group(s, i + 1)
            t = latex_text(arg)
            if c == "^" and re.fullmatch(r"[0-9+\-n]+", t):
                out.append(t.translate(_SUP))
            else:
                out.append(f"{c}{t}" if _atomic(t) else f"{c}({t})")
            continue
        if c in "{}":
            i += 1
            continue
        out.append(c)
        i += 1
    text = re.sub(r"\s+", " ", "".join(out)).strip()
    text = re.sub(r"\((sin|cos|tan) (\w+)\)([²³⁴])", r"\1\3 \2", text)  # (sin x)² → sin² x
    text = re.sub(r"\|\s*([^|]*?)\s*\|", r"|\1|", text)  # | AD | → |AD|
    text = re.sub(r"([∠△]) ", r"\1", text).replace("'", "′")
    text = re.sub(r"¬ ?(\w+) collinear", r"\1 is a triangle", text)
    text = re.sub(r"(?<![A-Za-z])([A-Za-z]) ([A-Za-z])(?![A-Za-z])", r"\1\2", text)  # a b → ab
    return text


def plain(e: Expr, functions: tuple[str, ...] = ()) -> str:
    """Readable one-line text for an expression (from its LaTeX display): sin² x, f′(t),
    ∠ABC, AD/AB, √(ab), ∀ t ∈ ℝ. Display only; Lean checks the expression itself."""
    del functions  # function application already prints as f(x)
    return latex_text(e.to_latex())


def _fact_text(t: Any, hyps: dict[str, str], fns: tuple[str, ...] = ()) -> str:
    if isinstance(t, Name):
        if t.label:
            return t.label
        if t.name in hyps:
            return f"{hyps[t.name]} ({t.name})"
        return t.name
    if isinstance(t, TermApp):
        return _fact_text(t.fn, hyps, fns)
    if isinstance(t, Expr):
        return plain(t, fns)
    return str(t)


@dataclass
class ProseStep:
    kind: str  # let | claim | conclude | lean
    text: str  # plain text of the statement
    latex: str  # LaTeX of the statement ("" for Lean steps)
    reason: str = ""  # human reason: the note, else the cited facts in words
    name: str = ""


@dataclass
class Prose:
    """A theorem and its written proof, ready to read (``print`` or Jupyter)."""

    name: str
    statement: str
    statement_latex: str
    steps: list[ProseStep] = field(default_factory=list)
    avoid: tuple[str, ...] = ()
    status: str = ""  # "" when no verification result was supplied

    # ------------------------------------------------------------------ text
    def __str__(self) -> str:
        out = [f"Theorem ({self.name}). {self.statement}", "Proof."]
        n = 0
        for s in self.steps:
            if s.kind == "conclude":
                tail = f" ({s.reason})" if s.reason else ""
                out.append(f"  Hence {s.text}{tail}. ∎")
                continue
            n += 1
            if s.kind == "let":
                out.append(f"  {n}. Let {s.text}.")
            elif s.kind == "lean":
                out.append(f"  {n}. [Lean] {s.text}")
            else:
                tail = f"  ({s.reason})" if s.reason else ""
                text = "F" + s.text[1:] if s.text.startswith("for all ") else s.text
                out.append(f"  {n}. {text}.{tail}")
        if self.avoid:
            out.append("  Without using: " + ", ".join(self.avoid) + ".")
        out.append(self.status or "  (not yet checked by Lean: call .verify())")
        return "\n".join(out)

    def to_markdown(self) -> str:
        out = [f"**Theorem** (`{self.name}`). ${self.statement_latex}$", "",
               "*Proof.*", ""]
        n = 0
        for s in self.steps:
            if s.kind == "conclude":
                tail = f" ({s.reason})" if s.reason else ""
                out.append(f"\nHence ${s.latex}${tail}. ∎")
                continue
            n += 1
            if s.kind == "let":
                out.append(f"{n}. Let ${s.latex}$.")
            elif s.kind == "lean":
                out.append(f"{n}. Lean: `{s.text}`")
            else:
                tail = f" — *{s.reason}*" if s.reason else ""
                out.append(f"{n}. ${s.latex}$.{tail}")
        if self.avoid:
            out.append("\nWithout using: " + ", ".join(f"`{a}`" for a in self.avoid) + ".")
        out.append("\n" + (self.status.strip() or "*Not yet checked by Lean.*"))
        return "\n".join(out)

    def _repr_markdown_(self) -> str:
        return self.to_markdown()


def _let_texts(t: Let, fns: tuple[str, ...]) -> tuple[str, str]:
    from .terms import Lam

    v = t.var.name
    if isinstance(t.value, Lam):
        args = ", ".join(x.name for x in t.value.vars)
        return (f"{v}({args}) = {plain(t.value.body, fns)}",
                f"{v}({args}) = {t.value.body.to_latex()}")
    return f"{v} = {plain(t.value, fns)}", f"{v} = {t.value.to_latex()}"


def _steps(t: Tactic | None) -> list[Tactic]:
    if t is None:
        return []
    if isinstance(t, Steps):
        return [x for s in t.tactics for x in _steps(s)]
    return [t]


def prose(thm: Theorem, result: VerificationResult | None = None) -> Prose:
    """The theorem's proof as readable steps; pass ``thm.verify()``'s result to include
    Lean's verdict. Only ``verified`` results are reported as checked."""
    steps = _steps(thm.proof)
    fns: tuple[str, ...] = ()
    hyps = {h.name: plain(h.prop, fns) for h in thm.assumptions}
    stmt = plain(thm.conclusion, fns)
    if thm.assumptions:
        stmt = "If " + ", ".join(hyps.values()) + ", then " + stmt
    if thm.variables:
        from .render.latex import latex_sort

        groups: dict[str, list[str]] = {}
        for v in thm.variables:
            groups.setdefault(latex_text(latex_sort(v.sort)), []).append(v.name)
        binders = ", ".join(f"{', '.join(ns)} ∈ {s}" for s, ns in groups.items())
        stmt = f"For all {binders}: {stmt[0].lower() + stmt[1:] if thm.assumptions else stmt}"
    out = Prose(thm.name, stmt + ".", thm.to_latex(), avoid=tuple(getattr(thm, "avoid", ())))
    for s in steps:
        if isinstance(s, Let):
            text, latex = _let_texts(s, fns)
            out.steps.append(ProseStep("let", text, latex, s.note))
        elif isinstance(s, Claim):
            reason = s.note or ", ".join(_fact_text(f, hyps, fns) for f in s.facts)
            out.steps.append(ProseStep("claim", plain(s.prop, fns), s.prop.to_latex(), reason,
                                       s.name))
        elif isinstance(s, Conclude):
            reason = s.note or ", ".join(_fact_text(f, hyps, fns) for f in s.facts)
            out.steps.append(ProseStep("conclude", plain(thm.conclusion, fns),
                                       thm.conclusion.to_latex(), reason))
        else:
            out.steps.append(ProseStep("lean", str(s).replace("\n", "; "), ""))
    if result is not None:
        if result.verified:
            axioms = ", ".join(getattr(result, "axioms", ()) or ()) or "none"
            out.status = f"  ✔ Checked by Lean (axioms: {axioms})."
        else:
            out.status = f"  ✘ Lean did not accept this proof ({result.status.value})."
    return out
