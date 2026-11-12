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

from .expr import FALSE, Expr, Logic, NotP, Quant, Var
from .proofs import (
    CaseSplit,
    Chain,
    Choose,
    Claim,
    Conclude,
    Fix,
    InductionOn,
    Let,
    Name,
    Steps,
    Suffices,
    SupposeNot,
    Tactic,
    Take,
    TermApp,
)

_WRITTEN = (Claim, Conclude, Let, Fix, Take, Choose, SupposeNot, CaseSplit, InductionOn, Chain,
            Suffices)

if TYPE_CHECKING:
    from .backend.interface import VerificationResult
    from .theorem import Theorem

_SUP = str.maketrans("0123456789+-n", "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻ⁿ")
_SUB = str.maketrans("0123456789nikm", "₀₁₂₃₄₅₆₇₈₉ₙᵢₖₘ")
_SYMBOLS = {
    "angle": "∠", "parallel": "∥", "sim": "∼", "triangle": "△", "neg": "¬", "in": "∈",
    "notin": "∉", "forall": "∀", "exists": "∃", "le": "≤", "leq": "≤", "ge": "≥", "geq": "≥",
    "ne": "≠", "neq": "≠", "cdot": "·", "times": "×", "mapsto": "↦", "to": "→", "pi": "π",
    "Longrightarrow": "⟹", "Rightarrow": "⇒", "iff": "⟺", "land": "∧", "lor": "∨",
    "wedge": "∧", "vee": "∨", "sum": "∑", "prod": "∏", "int": "∫", "infty": "∞",
    "oint": "∮", "setminus": "∖", "partial": "∂",
    "lvert": "|", "rvert": "|", "lVert": "‖", "rVert": "‖", "bmod": "mod", "quad": " ",
    "qquad": " ", "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε",
    "theta": "θ", "varepsilon": "ε", "mid": "∣", "varphi": "φ", "lambda": "λ", "mu": "μ",
    "sigma": "σ", "phi": "φ", "omega": "ω",
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
            elif cmd == "bar":
                arg, i = _group(s, i)
                out.append(latex_text(arg) + "̄")
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
            elif c == "_" and re.fullmatch(r"[0-9nikm]+", t):
                out.append(t.translate(_SUB))
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
    # casts are implicit in writing: (k + 1 : ℝ) x → (k + 1)x, (n : ℝ) x → nx
    text = re.sub(r"\((\w+) : [ℝℚℤℕ]\)", r"\1", text)
    text = re.sub(r"\(([^():]+) : [ℝℚℤℕ]\)", r"(\1)", text)
    text = re.sub(r"(?<![A-Za-z])([A-Za-z]) ([A-Za-z])(?![A-Za-z])", r"\1\2", text)  # a b → ab
    text = re.sub(r"(?<![\w.])(\d+) ([A-Za-z(])", r"\1\2", text)  # 2 k → 2k, 2 (k → 2(k
    text = re.sub(r"(?<![A-Za-z])([A-Za-z]) \(", r"\1(", text)  # k (n + 1) → k(n + 1)
    text = re.sub(r"\) ([A-Za-z])(?![A-Za-z])", r")\1", text)  # (1 + k) x → (1 + k)x
    text = text.replace(") (", ")(")  # (2k + 1) (k + 1) → (2k + 1)(k + 1)
    text = re.sub(r"(?<![A-Za-z])([A-Za-z]) ([A-Za-z])(?![A-Za-z])", r"\1\2", text)
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
    """One printed step. ``blocks`` hold nested proofs (cases, induction, a claim's
    own proof): each is ``(heading text, heading LaTeX-markdown, steps)``."""

    kind: str  # let | claim | conclude | fix | take | choose | suppose | cases | induction
    #            | chain | suffices | lean
    text: str  # plain text of the sentence (without number or reason)
    latex: str  # markdown with $…$ maths ("" for Lean steps)
    reason: str = ""  # the note, else the cited facts in words
    name: str = ""
    blocks: list[tuple[str, str, list[ProseStep]]] = field(default_factory=list)


def _sentence(s: ProseStep, md: bool) -> str:
    body = s.latex if md else s.text
    reason = s.reason
    if s.kind == "conclude":
        tail = f" ({reason})" if reason else ""
        return f"{body}{tail}."
    if md:
        tail = f" — *{reason}*" if reason else ""
        return f"{body}.{tail}"
    tail = f"  ({reason})" if reason else ""
    return f"{body}.{tail}"


def _lines(steps: list[ProseStep], prefix: str, depth: int, md: bool, top: bool,
           start: int = 0) -> list[str]:
    """Numbered lines; the blocks of one step continue its numbering (3.1, 3.2 in case 1,
    3.3 in case 2), so every printed number names one step."""
    out: list[str] = []
    pad = ("   " if md else "  ") * depth + ("" if md else "  ")
    n = start
    for s in steps:
        if s.kind == "conclude":
            end = " ∎" if top else ""
            text = _sentence(s, md)
            out.append(("\n" if md and top else "") + f"{pad}{text}{end}")
            continue
        n += 1
        num = f"{prefix}{n}"
        if s.kind == "lean":
            out.append(f"{pad}{num}. " + (f"Lean: `{s.text}`" if md else f"[Lean] {s.text}"))
        else:
            out.append(f"{pad}{num}. {_sentence(s, md)}")
        done = 0
        for head_text, head_md, sub in s.blocks:
            inner = ("   " if md else "  ") * (depth + 1) + ("" if md else "  ")
            if head_text:
                out.append(f"{inner}{head_md if md else head_text}")
            out.extend(_lines(sub, f"{num}.", depth + 1, md, False, done))
            done += sum(1 for x in sub if x.kind != "conclude")
    return out


@dataclass
class Prose:
    """A theorem and its written proof, ready to read (``print`` or Jupyter)."""

    name: str
    statement: str
    statement_latex: str
    steps: list[ProseStep] = field(default_factory=list)
    avoid: tuple[str, ...] = ()
    status: str = ""  # "" when no verification result was supplied

    def __str__(self) -> str:
        out = [f"Theorem ({self.name}). {self.statement}", "Proof."]
        out.extend(_lines(self.steps, "", 0, False, True))
        if self.avoid:
            out.append("  Without using: " + ", ".join(self.avoid) + ".")
        out.append(self.status or "  (not yet checked by Lean: call .verify())")
        return "\n".join(out)

    def to_markdown(self) -> str:
        out = [f"**Theorem** (`{self.name}`). ${self.statement_latex}$", "", "*Proof.*", ""]
        out.extend(_lines(self.steps, "", 0, True, True))
        if self.avoid:
            out.append("\nWithout using: " + ", ".join(f"`{a}`" for a in self.avoid) + ".")
        out.append("\n" + (self.status.strip() or "*Not yet checked by Lean.*"))
        return "\n".join(out)

    def _repr_markdown_(self) -> str:
        return self.to_markdown()


def _m(e: Expr) -> str:
    return f"${e.to_latex()}$"


def _let_texts(t: Let) -> tuple[str, str]:
    from .terms import Lam

    v = t.var.name
    if isinstance(t.value, Lam):
        args = ", ".join(x.name for x in t.value.vars)
        return (f"Let {v}({args}) = {plain(t.value.body)}",
                f"Let ${v}({args}) = {t.value.body.to_latex()}$")
    return f"Let {v} = {plain(t.value)}", f"Let ${v} = {t.value.to_latex()}$"


def _sort_text(s: Any) -> tuple[str, str]:
    from .render.latex import latex_sort

    tex = latex_sort(s)
    return latex_text(tex), tex


def _var_list(vs: tuple[Var, ...]) -> tuple[str, str]:
    groups: dict[tuple[str, str], list[str]] = {}
    for v in vs:
        groups.setdefault(_sort_text(v.sort), []).append(v.name)
    text = ", ".join(f"{', '.join(ns)} ∈ {st}" for (st, _), ns in groups.items())
    tex = ", ".join(f"${', '.join(ns)} \\in {sl}$" for (_, sl), ns in groups.items())
    return text, tex


def _peel_forall(target: Expr | None, fixed: tuple[Var, ...]) -> Expr | None:
    from .binders import substitute

    for v in fixed:
        if not (isinstance(target, Quant) and target.kind == "forall" and target.vars):
            return None
        first, rest = target.vars[0], target.vars[1:]
        body = substitute(target.body, {first.uid: v})
        target = Quant("forall", rest, body) if rest else body
    return target


def _peel_implies(target: Expr | None, n: int) -> Expr | None:
    for _ in range(n):
        if isinstance(target, Logic) and target.op == "implies":
            target = target.rhs
        elif isinstance(target, NotP):
            target = FALSE
        else:
            return None
    return target


def _instantiate_exists(target: Expr | None, ws: tuple[Expr, ...]) -> Expr | None:
    from .binders import substitute

    for w in ws:
        if not (isinstance(target, Quant) and target.kind == "exists" and target.vars):
            return None
        first, rest = target.vars[0], target.vars[1:]
        body = substitute(target.body, {first.uid: w})
        target = Quant("exists", rest, body) if rest else body
    return target


class _Reader:
    def __init__(self, hyps: dict[str, str]) -> None:
        self.hyps = dict(hyps)
        self.labels: dict[str, str] = {}  # step name -> printed number ("3.1")
        self.prefix = ""

    def fact(self, f: Any) -> str:
        if isinstance(f, Name) and not f.label and f.name in self.labels:
            return f"by step {self.labels[f.name]}"
        return _fact_text(f, self.hyps)

    def reason(self, facts: tuple[Any, ...], note: str) -> str:
        return note or ", ".join(self.fact(f) for f in facts)

    def block(self, t: Tactic | None, target: Expr | None,
              prefix: str | None = None, start: int = 0) -> list[ProseStep]:
        saved = self.prefix
        if prefix is not None:
            self.prefix = prefix
        out: list[ProseStep] = []
        n = start
        for s in _steps(t):
            if not isinstance(s, Conclude):
                n += 1
            here = f"{self.prefix}{n}"
            for nm in (getattr(s, "name", ""),):
                if nm and isinstance(s, (Claim, Chain)):
                    self.labels[nm] = here
            self.here = here
            step, target = self.step(s, target)
            out.append(step)
        self.prefix = saved
        return out

    def step(self, s: Tactic, target: Expr | None) -> tuple[ProseStep, Expr | None]:
        if isinstance(s, Let):
            text, tex = _let_texts(s)
            return ProseStep("let", text, tex, s.note), target
        if isinstance(s, Claim):
            self.hyps[s.name] = plain(s.prop)
            st = ProseStep("claim", plain(s.prop), _m(s.prop), self.reason(s.facts, s.note),
                           s.name)
            if s.proof is not None and _is_written(s.proof):
                st.reason = s.note
                st.blocks.append(("Proof.", "*Proof.*",
                                  self.block(s.proof, s.prop, f"{self.here}.")))
            return st, target
        if isinstance(s, Conclude):
            reason = self.reason(s.facts, s.note)
            if target is not None and target._key() == FALSE._key():
                text, tex = "This is a contradiction", "This is a contradiction"
            elif target is not None:
                text, tex = f"Hence {plain(target)}", f"Hence {_m(target)}"
            else:
                text, tex = "This proves the claim", "This proves the claim"
            return ProseStep("conclude", text, tex, reason), target
        if isinstance(s, Fix):
            vt, vtex = _var_list(s.vars)
            ht = " and ".join(plain(p) for _, p in s.hyps)
            htex = " and ".join(_m(p) for _, p in s.hyps)
            for n, p in s.hyps:
                self.hyps[n] = plain(p)
            if s.vars and s.hyps:
                text, tex = f"Let {vt} with {ht}", f"Let {vtex} with {htex}"
            elif s.vars:
                text, tex = f"Let {vt} be arbitrary", f"Let {vtex} be arbitrary"
            else:
                text, tex = f"Assume {ht}", f"Assume {htex}"
            new = _peel_implies(_peel_forall(target, s.vars), len(s.hyps))
            return ProseStep("fix", text, tex, s.note), new
        if isinstance(s, Take):
            names = (target.vars if isinstance(target, Quant) and target.kind == "exists"
                     else ())
            parts, tparts = [], []
            for i, w in enumerate(s.witnesses):
                if i < len(names) and plain(w) != names[i].name:
                    parts.append(f"{names[i].name} = {plain(w)}")
                    tparts.append(f"${names[i].name} = {w.to_latex()}$")
                else:
                    parts.append(plain(w))
                    tparts.append(_m(w))
            new = _instantiate_exists(target, s.witnesses)
            return ProseStep("take", "Take " + ", ".join(parts),
                             "Take " + ", ".join(tparts), s.note), new
        if isinstance(s, Choose):
            vt = ", ".join(v.name for v in s.vars)
            self.hyps.update({n: plain(s.prop) for n in s.names})
            return ProseStep("choose", f"Choose {vt} such that {plain(s.prop)}",
                             f"Choose ${vt}$ such that {_m(s.prop)}",
                             self.reason(s.facts, s.note)), target
        if isinstance(s, SupposeNot):
            if s.prop is not None:
                self.hyps[s.name] = plain(s.prop)
                text, tex = plain(s.prop), _m(s.prop)
            elif target is not None:
                text, tex = f"¬({plain(target)})", f"$\\neg({target.to_latex()})$"
            else:
                text, tex = "the claim is false", "the claim is false"
            return ProseStep("suppose", f"Suppose, for contradiction, that {text}",
                             f"Suppose, for contradiction, that {tex}", s.note), FALSE
        if isinstance(s, CaseSplit):
            props = [c.prop for c in s.cases]
            st = ProseStep("cases",
                           "Either " + " or ".join(plain(p) for p in props),
                           "Either " + " or ".join(_m(p) for p in props),
                           self.reason(s.facts, s.note))
            here = self.here
            done = 0
            for i, c in enumerate(s.cases, start=1):
                self.hyps[c.name] = plain(c.prop)
                note = f" ({c.note})" if c.note else ""
                sub = self.block(c.body, target, f"{here}.", done)
                done += sum(1 for x in sub if x.kind != "conclude")
                st.blocks.append((f"Case {i}: {plain(c.prop)}.{note}",
                                  f"*Case {i}:* {_m(c.prop)}.{note}", sub))
            return st, target
        if isinstance(s, InductionOn):
            from .binders import substitute
            from .expr import _lift

            nv, kv = s.var, s.k
            here = self.here
            zero = _lift(0) if nv.sort is None else _lit0(nv.sort)
            p0 = substitute(target, {nv.uid: zero}) if target is not None else None
            pk = substitute(target, {nv.uid: kv}) if target is not None else None
            pk1 = substitute(target, {nv.uid: kv + 1}) if target is not None else None
            if pk is not None:
                self.hyps[s.ih] = plain(pk)
            st = ProseStep("induction", f"We use induction on {nv.name}",
                           f"We use induction on ${nv.name}$", s.note)
            st.blocks.append(
                ("Base case" + (f": {plain(p0)}." if p0 is not None else "."),
                 "*Base case*" + (f": {_m(p0)}." if p0 is not None else "."),
                 self.block(s.base, p0, f"{here}.")))
            head = (f"Inductive step: assume {plain(pk)} ({s.ih}); we show {plain(pk1)}."
                    if pk is not None and pk1 is not None else
                    f"Inductive step: assume the claim for {kv.name} ({s.ih}).")
            head_md = (f"*Inductive step:* assume {_m(pk)} ({s.ih}); we show {_m(pk1)}."
                       if pk is not None and pk1 is not None else head)
            done = sum(1 for x in st.blocks[0][2] if x.kind != "conclude")
            st.blocks.append((head, head_md, self.block(s.step, pk1, f"{here}.", done)))
            return st, target
        if isinstance(s, Chain):
            parts = [plain(s.first)]
            tparts = [s.first.to_latex()]
            reasons = []
            for rel, e, facts, note in s.links:
                r = self.reason(facts, note)
                parts.append(f"{rel} {plain(e)}" + (f" ({r})" if r else ""))
                tparts.append(f"{_TEX_REL[rel]} {e.to_latex()}" + (
                    f" \\quad \\text{{({_tex_escape(r)})}}" if r else ""))
                reasons.append(r)
            stmt = s.statement()
            self.hyps[s.name] = plain(stmt)
            text = " ".join(parts)
            tex = "$" + " ".join(tparts) + "$"
            return ProseStep("chain", text, tex, "", s.name), target
        if isinstance(s, Suffices):
            return ProseStep("suffices", f"It suffices to show {plain(s.prop)}",
                             f"It suffices to show {_m(s.prop)}",
                             self.reason(s.facts, s.note)), s.prop
        return ProseStep("lean", str(s).replace("\n", "; "), ""), None


_TEX_REL = {"=": "=", "≤": r"\le", "<": "<", "≥": r"\ge", ">": ">"}


def _tex_escape(s: str) -> str:
    return re.sub(r"([{}%$&#_])", r"\\\1", s)


def _lit0(sort: Any) -> Expr:
    from .expr import _lit

    return _lit(0, sort)


def _is_written(t: Tactic) -> bool:
    return any(isinstance(s, _WRITTEN) for s in _steps(t))


def _steps(t: Tactic | None) -> list[Tactic]:
    if t is None:
        return []
    if isinstance(t, Steps):
        return [x for s in t.tactics for x in _steps(s)]
    return [t]


def _statement(thm: Theorem) -> str:
    from .render.lean import theorem_type_params

    hyps = [plain(h.prop) for h in thm.assumptions]
    stmt = plain(thm.conclusion)
    if hyps:
        stmt = "if " + ", ".join(hyps) + ", then " + stmt
    lead = []
    for p in theorem_type_params(thm):
        what = p.label or ("type with " + ", ".join(p.classes) if p.classes else "type")
        lead.append(f"every {what} {p.lean}")
    if thm.variables:
        lead.append("all " + _var_list(thm.variables)[0])
    if lead:
        return f"For {' and '.join(lead)}: {stmt}."
    return stmt[0].upper() + stmt[1:] + "."


def prose(thm: Theorem, result: VerificationResult | None = None) -> Prose:
    """The theorem's proof as readable steps; pass ``thm.verify()``'s result to include
    Lean's verdict. Only ``verified`` results are reported as checked."""
    hyps = {h.name: plain(h.prop) for h in thm.assumptions}
    out = Prose(thm.name, _statement(thm), thm.to_latex(),
                avoid=tuple(getattr(thm, "avoid", ())))
    out.steps = _Reader(hyps).block(thm.proof, thm.conclusion)
    if result is not None:
        if result.verified:
            axioms = ", ".join(getattr(result, "axioms", ()) or ()) or "none"
            out.status = f"  ✔ Checked by Lean (axioms: {axioms})."
        else:
            out.status = f"  ✘ Lean did not accept this proof ({result.status.value})."
    return out
