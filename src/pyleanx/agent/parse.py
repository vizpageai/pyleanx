"""Turn tactic *text* (as an AI model writes it) into PyLeanX tactic IR.

Common single tactics with plain names (``linarith [h1, h2]``, ``rw [← mul_comm] at h``,
``exact foo a b``, ``intro x y``) become structured, trusted nodes. Anything else
(nested terms, combinators, multi-line scripts) becomes an untrusted
:class:`~pyleanx.proofs.RawTactic`, which the policy rejects unless raw tactics were
explicitly allowed, and which is then screened and audited like any raw tactic.
"""

from __future__ import annotations

import ast
import re
from collections.abc import Callable, Mapping

from ..errors import IdentifierError, TacticError
from ..expr import Expr, Var
from ..names import validate_identifier, validate_qualified_name
from ..proofs import (
    Aesop,
    Apply,
    Assumption,
    Constructor,
    Decide,
    Exact,
    Intro,
    LibrarySearch,
    Linarith,
    Name,
    Nlinarith,
    NormNum,
    Omega,
    Positivity,
    Rewrite,
    Rfl,
    Ring,
    Simp,
    Tactic,
    Term,
    TermApp,
    Use,
    raw_tactic,
)

_SIMPLE = {"ring": Ring, "omega": Omega, "positivity": Positivity, "rfl": Rfl,
           "decide": Decide, "constructor": Constructor, "assumption": Assumption,
           "aesop": Aesop, "exact?": LibrarySearch}
_WITH = {"linarith": Linarith, "nlinarith": Nlinarith, "norm_num": NormNum}


class _NotStructured(Exception):
    pass


def lemma_imports_from_catalogs() -> dict[str, tuple[str, ...]]:
    """Lean name -> imports, from the curated domain catalogs."""
    from .._domain import all_catalogs

    out: dict[str, tuple[str, ...]] = {}
    for cat in all_catalogs().values():
        for ref in cat.values():
            out.setdefault(ref.name, ref.imports)
    return out


class TacticParser:
    """Callable: ``parser("linarith [h]") -> Tactic``."""

    def __init__(self, lemma_imports: Mapping[str, tuple[str, ...]] | None = None,
                 allow_raw: bool = False, scope: Mapping[str, Var] | None = None) -> None:
        self.lemma_imports = dict(lemma_imports if lemma_imports is not None
                                  else lemma_imports_from_catalogs())
        self.allow_raw = allow_raw
        # Variables of the theorem: arithmetic over them (``sq_nonneg (a - b)``) is parsed
        # into typed expressions instead of being treated as raw text.
        self.scope = dict(scope or {})

    def __call__(self, text: str) -> Tactic:
        return self.parse(text)

    def parse(self, text: str) -> Tactic:
        if not isinstance(text, str) or not text.strip():
            raise TacticError("empty tactic text")
        t = text.strip()
        try:
            return self._structured(t)
        except (_NotStructured, IdentifierError):
            pass
        if not self.allow_raw:
            raise TacticError(
                f"`{t}` is not a recognised structured tactic; it can only run as an "
                "untrusted raw tactic, which this environment does not allow (allow_raw=False)")
        return raw_tactic(t, imports=self._imports_mentioned(t))

    # ------------------------------------------------------------------ helpers
    def _name(self, token: str) -> Name:
        validate_qualified_name(token, "lemma/hypothesis name")
        return Name(token, self.lemma_imports.get(token, ()))

    def _arith(self, text: str) -> Expr:
        """Safe arithmetic over theorem variables (no eval): + - * / ^, ints, parens."""
        if not self.scope or not re.fullmatch(r"[\w\s+\-*/^().]+", text):
            raise _NotStructured
        try:
            tree = ast.parse(text.replace("^", "**"), mode="eval")
        except SyntaxError as exc:
            raise _NotStructured from exc

        def build(node: ast.AST) -> Expr | int:
            if isinstance(node, ast.Expression):
                return build(node.body)
            if isinstance(node, ast.Name) and node.id in self.scope:
                return self.scope[node.id]
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return node.value
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
                return -build(node.operand)
            if isinstance(node, ast.BinOp):
                lhs, rhs = build(node.left), build(node.right)
                ops = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b,
                       ast.Mult: lambda a, b: a * b, ast.Div: lambda a, b: a / b,
                       ast.Pow: lambda a, b: a ** b}
                fn = ops.get(type(node.op))
                if fn is not None:
                    return fn(lhs, rhs)
            raise _NotStructured

        out = build(tree)
        if not isinstance(out, Expr):
            raise _NotStructured
        return out

    def _term(self, text: str) -> Term:
        m = re.fullmatch(r"([\w.']+)\s+\((.+)\)", text.strip())
        if m and self.scope:  # lemma applied to one arithmetic argument
            try:
                return TermApp(self._name(m.group(1)), (self._arith(m.group(2)),))
            except _NotStructured:
                pass
        parts = text.split()
        # Only `name arg arg ...` with plain names; nested terms stay raw.
        if not parts or any(c in text for c in "()⟨⟩[]{}@,:;"):
            raise _NotStructured
        head = self._name(parts[0])
        if len(parts) == 1:
            return head
        return TermApp(head, tuple(self._name(p) for p in parts[1:]))

    def _list(self, inner: str | None) -> tuple[Term, ...]:
        if inner is None or not inner.strip():
            return ()
        return tuple(self._term(x.strip()) for x in inner.split(","))

    def _at(self, text: str | None) -> tuple[str, ...]:
        if not text:
            return ()
        return tuple(validate_identifier(n, "hypothesis name") for n in text.split())

    def _structured(self, t: str) -> Tactic:
        if "\n" in t or ";" in t or "<;>" in t:
            raise _NotStructured
        if t in _SIMPLE:
            return _SIMPLE[t]()
        m = re.fullmatch(r"(linarith|nlinarith|norm_num)(?:\s*\[(.*)\])?", t)
        if m:
            return _WITH[m.group(1)](lemmas=self._list(m.group(2)))
        m = re.fullmatch(r"simp(\s+only)?(?:\s*\[(.*)\])?(?:\s+at\s+(.+))?", t)
        if m:
            return Simp(only=bool(m.group(1)), lemmas=self._list(m.group(2)),
                        at=self._at(m.group(3)))
        m = re.fullmatch(r"intro\s+(.+)", t)
        if m:
            return Intro(names=self._at(m.group(1)))
        m = re.fullmatch(r"use\s+(.+)", t)
        if m:
            return Use(witnesses=tuple(self._arith(w.strip()) for w in m.group(1).split(",")))
        m = re.fullmatch(r"(exact|apply)\s+(.+)", t)
        if m:
            term = self._term(m.group(2))
            return Exact(term=term) if m.group(1) == "exact" else Apply(term=term)
        m = re.fullmatch(r"(?:rw|rewrite)\s*\[(.+)\](?:\s+at\s+(.+))?", t)
        if m:
            rules = []
            for item in m.group(1).split(","):
                item = item.strip()
                rev = item.startswith(("←", "<-"))
                item = item.lstrip("←<-").strip()
                rules.append((self._term(item), rev))
            return Rewrite(rules=tuple(rules), at=self._at(m.group(2)))
        raise _NotStructured

    def _imports_mentioned(self, text: str) -> tuple[str, ...]:
        words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", text))
        out: list[str] = []
        for w in sorted(words):
            out.extend(self.lemma_imports.get(w, ()))
        # tactics used inside raw text
        tactic_mods = {"ring": "Mathlib.Tactic.Ring", "positivity": "Mathlib.Tactic.Positivity",
                       "linarith": "Mathlib.Tactic.Linarith",
                       "nlinarith": "Mathlib.Tactic.Linarith",
                       "norm_num": "Mathlib.Tactic.NormNum", "use": "Mathlib.Tactic.Use"}
        out.extend(m for k, m in tactic_mods.items() if k in words)
        return tuple(dict.fromkeys(out))


def tactic_from_text(text: str, *, allow_raw: bool = False,
                     lemma_imports: Mapping[str, tuple[str, ...]] | None = None) -> Tactic:
    return TacticParser(lemma_imports, allow_raw).parse(text)


ParseFn = Callable[[str], Tactic]
