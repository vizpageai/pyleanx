"""Lean's pretty-printed goals and statements -> LaTeX, for display only.

Goals come back from Lean as text (``x y : ℝ\\nh : 0 < x\\n⊢ 0 < x * y + x``). This module
turns that text into readable mathematics for Jupyter and the docs. It is a best-effort
*view*: tokens it does not understand are shown verbatim, the Lean text stays available
next to it, and nothing here is ever sent back to Lean.
"""

from __future__ import annotations

import re

from .latex import latex_name

_SYMBOLS = {
    "≤": r"\le", "≥": r"\ge", "≠": r"\ne", "→": r"\to", "↔": r"\leftrightarrow",
    "∧": r"\land", "∨": r"\lor", "¬": r"\neg", "∀": r"\forall", "∃": r"\exists",
    "∈": r"\in", "∉": r"\notin", "⊆": r"\subseteq", "⊂": r"\subset", "∩": r"\cap",
    "∪": r"\cup", "∑": r"\sum", "∏": r"\prod", "∫": r"\int", "•": r"\cdot", "×": r"\times",
    "∘": r"\circ", "⊢": r"\vdash", "∞": r"\infty", "⊤": r"\top", "⊥": r"\bot", "↦": r"\mapsto",
    "=>": r"\mapsto", "*": r"\cdot", "≈": r"\approx", "∣": r"\mid", "⁻¹": "^{-1}",
    "ℝ": r"\mathbb{R}", "ℕ": r"\mathbb{N}", "ℤ": r"\mathbb{Z}", "ℚ": r"\mathbb{Q}",
    "ℂ": r"\mathbb{C}", "%": r"\bmod", "∂": r"\partial", "<": "<", ">": ">", "=": "=",
    "+": "+", "-": "-", "/": "/", ",": ",", ":": ":", "(": "(", ")": ")", "[": "[",
    "]": "]", "{": r"\{", "}": r"\}", "⟨": r"\langle", "⟩": r"\rangle", "|": "|",
    "..": r"..", "·": r"\cdot", "↑": "", "fun": "", "in": r"\in",
}
_TOKEN = re.compile(r"""
    (?P<num>\d+(?:\.\d+)?)
  | (?P<ident>[^\W\d][\w.'✝₀-₉ᵢ-ᵪ!?]*)
  | (?P<sym>=>|\.\.|⁻¹|[^\s\w])
  | (?P<space>\s+)
""", re.X)


def _tokens(text: str) -> list[str]:
    out = []
    for m in _TOKEN.finditer(text):
        if m.lastgroup != "space":
            out.append(m.group())
    return out


def _ident(tok: str) -> str:
    tok = tok.replace("✝", "")
    if "." in tok.strip("."):
        last = tok.rsplit(".", 1)[-1]
        known = {"sqrt": r"\sqrt", "exp": r"\exp", "log": r"\log", "sin": r"\sin",
                 "cos": r"\cos", "pi": r"\pi"}
        if last in known:
            return known[last]
        return r"\operatorname{" + last.replace("_", r"\_") + "}"
    return latex_name(tok) if tok else ""


def _group(toks: list[str], i: int) -> tuple[str, int]:
    """Render the atom starting at ``toks[i]`` (a parenthesized group or one token)."""
    if toks[i] == "(":
        depth, j = 0, i
        while j < len(toks):
            if toks[j] == "(":
                depth += 1
            elif toks[j] == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        return _render(toks[i + 1:j]), j + 1
    return _render(toks[i:i + 1]), i + 1


def _render(toks: list[str]) -> str:
    out: list[str] = []
    i = 0
    norm_open = False
    while i < len(toks):
        t = toks[i]
        if t == "√" and i + 1 < len(toks):
            inner, i = _group(toks, i + 1)
            out.append(r"\sqrt{" + inner + "}")
            continue
        if t == "^" and i + 1 < len(toks):
            inner, i = _group(toks, i + 1)
            out.append("^{" + inner + "}")
            continue
        if t == "‖":
            out.append(r"\rVert" if norm_open else r"\lVert")
            norm_open = not norm_open
            i += 1
            continue
        if t in _SYMBOLS:
            out.append(_SYMBOLS[t])
        elif t[0].isdigit():
            out.append(t)
        elif t[0].isalpha() or t[0] == "_":
            out.append(_ident(t))
        else:
            out.append(t)
        i += 1
    text = " ".join(p for p in out if p)
    return re.sub(r"\s+([,)\]])", r"\1", text).replace("( ", "(").replace("[ ", "[")


def lean_to_latex(text: str) -> str:
    """One Lean expression (single or wrapped lines) as LaTeX."""
    return _render(_tokens(" ".join(text.split())))


def _logical_lines(goal: str) -> list[str]:
    lines: list[str] = []
    for raw in goal.splitlines():
        if raw.startswith((" ", "\t")) and lines:
            lines[-1] += " " + raw.strip()  # Lean wraps long hypotheses with indentation
        elif raw.strip():
            lines.append(raw.strip())
    return lines


def goal_to_latex(goal: str) -> str:
    """A goal (hypotheses, then ``⊢ target``) as a LaTeX ``array``."""
    rows = []
    for line in _logical_lines(goal):
        if line.startswith("⊢"):
            rows.append(r"\vdash\ " + lean_to_latex(line[1:].strip()))
            continue
        names, sep, typ = line.partition(" : ")
        if sep:
            hyps = ", ".join(_ident(n) for n in names.split())
            rows.append(f"{hyps} : {lean_to_latex(typ)}")
        else:
            rows.append(lean_to_latex(line))
    return r"\begin{array}{l}" + r" \\ ".join(rows) + r"\end{array}"
