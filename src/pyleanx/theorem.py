"""Theorem declarations and their lifecycle: declare -> prove -> to_lean -> verify."""

from __future__ import annotations

import inspect
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any

from ._origin import Origin, caller_origin, resolve_annotations
from .binders import check_scope, contains_untyped_literal
from .errors import ScopeError, SortError, TacticError
from .expr import Expr, Var, _as_prop, make_var
from .names import validate_identifier, validate_qualified_name
from .proofs import Tactic
from .types import Sort as SortT

if TYPE_CHECKING:
    from .backend.interface import VerificationResult
    from .project import LeanProject


@dataclass(frozen=True, eq=False)
class Hypothesis:
    """A named, ordered assumption ``(name : prop)``."""

    name: str
    prop: Expr
    origin: Origin | None = None

    def __post_init__(self) -> None:
        validate_identifier(self.name, "hypothesis name")
        _as_prop(self.prop, f"hypothesis {self.name}")


def _normalize_assumptions(assumptions: Any) -> tuple[Hypothesis, ...]:
    if assumptions is None:
        return ()
    items: list[Hypothesis] = []
    if isinstance(assumptions, Mapping):
        for k, v in assumptions.items():
            items.append(Hypothesis(k, v))
        return tuple(items)
    if isinstance(assumptions, (Expr, Hypothesis)):
        assumptions = [assumptions]
    for i, a in enumerate(assumptions, start=1):
        if isinstance(a, Hypothesis):
            items.append(a)
        elif isinstance(a, tuple) and len(a) == 2 and isinstance(a[0], str):
            items.append(Hypothesis(a[0], a[1]))
        elif isinstance(a, Expr):
            items.append(Hypothesis(f"h{i}", a))
        else:
            raise SortError(f"assumption #{i} must be a proposition or Hypothesis, got {a!r}")
    return tuple(items)


def _avoid_names(avoid: Iterable[Any]) -> tuple[str, ...]:
    """Lemma names a proof must not use (``Theorem(avoid=[an.sin_sq_add_cos_sq])``)."""
    from .proofs import Name, _term

    if isinstance(avoid, (str, Name)) or hasattr(type(avoid), "__pyleanx_term__"):
        avoid = [avoid]
    out: list[str] = []
    for a in avoid:
        t = _term(a)
        if not isinstance(t, Name):
            raise TacticError(f"avoid= takes lemma names, got {a!r}")
        if t.name not in out:
            out.append(t.name)
    return tuple(out)


class Theorem:
    """A theorem statement plus (optionally) a proof.

    ``Theorem(name, variables=[x, y], assumptions=[...], conclusion=prop)``

    The statement is closed over ``variables`` (rendered as explicit binders) and
    ``assumptions`` (rendered as named hypotheses, in order).
    """

    def __init__(
        self,
        name: str,
        variables: Sequence[Var] = (),
        assumptions: Any = None,
        conclusion: Expr | None = None,
        *,
        imports: Iterable[str] = (),
        proof: Tactic | None = None,
        avoid: Iterable[Any] = (),
    ) -> None:
        self.name = validate_identifier(name, "theorem name")
        self.variables: tuple[Var, ...] = tuple(variables)
        self.assumptions: tuple[Hypothesis, ...] = _normalize_assumptions(assumptions)
        if conclusion is None:
            raise SortError("Theorem needs a conclusion proposition")
        self.conclusion: Expr = _as_prop(conclusion, f"conclusion of {name}")
        self.imports: tuple[str, ...] = tuple(
            validate_qualified_name(i, "import module") for i in imports
        )
        self.origin = caller_origin()
        self.avoid: tuple[str, ...] = _avoid_names(avoid)
        self.proof: Tactic | None = None
        self.validate_statement()
        if proof is not None:
            self.prove(proof)

    # ------------------------------------------------------------------ statement
    def validate_statement(self) -> None:
        names: dict[str, Var] = {}
        for v in self.variables:
            if not isinstance(v, Var):
                raise ScopeError(f"{self.name}: variables must be pl.symbol(s), got {v!r}")
            if v.name in names:
                same = names[v.name].uid == v.uid
                raise ScopeError(
                    f"{self.name}: variable {v.name!r} "
                    + ("listed twice" if same else "declared twice with different objects")
                )
            names[v.name] = v
        hyp_names: set[str] = set()
        for h in self.assumptions:
            if h.name in names or h.name in hyp_names or h.name == self.name:
                raise ScopeError(f"{self.name}: hypothesis name {h.name!r} is already used")
            hyp_names.add(h.name)
            check_scope(h.prop, names, f"{self.name}, hypothesis {h.name}")
        check_scope(self.conclusion, names, f"{self.name}, conclusion")
        for part in [self.conclusion, *(h.prop for h in self.assumptions)]:
            if contains_untyped_literal(part):
                raise SortError(f"{self.name}: statement contains a literal with no inferable sort")

    # ------------------------------------------------------------------ proof
    def prove(self, tactic: Tactic) -> Theorem:
        """Attach a proof script (does NOT verify). Returns ``self`` for chaining."""
        if not isinstance(tactic, Tactic):
            raise TacticError(
                f"prove() expects a tactic such as pl.ring() or pl.steps(...), got {tactic!r}"
            )
        from .proofs import with_avoid

        self.proof = with_avoid(tactic, self.avoid)
        return self

    # ------------------------------------------------------------------ rendering
    def to_lean(self, project: LeanProject | None = None, *, audit: bool = True) -> str:
        """Deterministic Lean source for this theorem (pure; never runs Lean)."""
        from .render.lean import render_module

        mode = project.import_mode if project is not None else "minimal"
        extra = project.extra_imports if project is not None else ()
        uni = project.unicode_types if project is not None else False
        return render_module([self], import_mode=mode, extra_imports=extra, audit=audit,
                             unicode_types=uni).source

    def canonical(self) -> Any:
        data = {
            "name": self.name,
            "variables": [v.canonical() for v in self.variables],
            "assumptions": [[h.name, h.prop.canonical()] for h in self.assumptions],
            "conclusion": self.conclusion.canonical(),
            "proof": self.proof.canonical() if self.proof is not None else None,
            "imports": list(self.imports),
        }
        if self.avoid:  # absent when unused (keeps older canonical forms stable)
            data["avoid"] = list(self.avoid)
        from .defs import theorem_definitions

        defs = theorem_definitions(self)
        if defs:  # absent for definition-free theorems (keeps old canonical forms stable)
            data["definitions"] = [d.canonical() for d in defs]
        return data

    # ------------------------------------------------------------------ verification
    def verify(
        self,
        project: LeanProject | str | None = None,
        *,
        use_cache: bool = True,
        timeout: float | None = None,
    ) -> VerificationResult:
        """Check the *current* proof with Lean and audit its axioms."""
        from .backend.subprocess_backend import verify_all

        return verify_all([self], project=project, use_cache=use_cache, timeout=timeout)[0]

    def prose(self, result: VerificationResult | None = None) -> Any:
        """The proof as readable steps (see :func:`pyleanx.prose`)."""
        from .prose import prose

        return prose(self, result)

    def __repr__(self) -> str:
        state = "proved-script" if self.proof is not None else "no proof"
        return f"<pl.Theorem {self.name} ({state})>"

    def same_statement_as(self, declaration: Any, *, imports: Iterable[str] = (),
                          project: LeanProject | str | None = None,
                          timeout: float | None = None) -> Any:
        """Ask Lean whether this statement is definitionally ``declaration``'s statement.

        ``declaration`` is a name (``"OAI.RVM.global_classical_solution"``) or a binding
        from ``pyleanx.lib``. Returns a :class:`~pyleanx.faithful.SameStatement` (truthy
        when Lean proved the two propositions equal by ``rfl``).
        """
        from .faithful import same_statement

        return same_statement(self, declaration, imports=imports, project=project,
                              timeout=timeout)

    def auto_prove(self, *hints: Any, project: LeanProject | str | None = None,
                   timeout: float | None = None, library_search: bool = True) -> Any:
        """Find a closing tactic automatically and attach it as an explicit proof.

        Tries ``pl.auto``'s strategies (with ``hints``) as separate candidates in one batch
        Lean run, attaches the first that Lean verifies, and returns the
        :class:`~pyleanx.agent.ProofAttempt`. The attached proof is a concrete tactic, so
        later ``verify()`` calls are reproducible.
        """
        from . import proofs as P
        from .agent.search import try_proofs

        terms = P._terms(hints)
        cands: list[Tactic] = [P.Rfl(), P.Ring(), P.NormNum(lemmas=terms),
                               P.Simp(lemmas=terms), P.Linarith(lemmas=terms), P.Positivity(),
                               P.Nlinarith(lemmas=terms),
                               P.Auto(hints=terms, library_search=library_search)]
        return try_proofs(self, cands, project, timeout=timeout)  # attaches the winner

    def session(self, project: LeanProject | str | None = None, **kwargs: Any) -> Any:
        """Interactive proof session (goals, apply, undo) on a persistent Lean REPL.

        Needs ``pip install 'pyleanx[interactive]'``. Sessions never verify by
        themselves; ``session.verify()`` runs the batch check and axiom audit.
        """
        from .session import ProofSession

        return ProofSession(self, project, **kwargs)

    def to_latex(self) -> str:
        """Typeset statement (display only): binders, hypotheses ⟹ conclusion."""
        from .render.latex import theorem_to_latex

        return theorem_to_latex(self)

    def _repr_markdown_(self) -> str:  # Jupyter: typeset statement + collapsible Lean
        from .render.latex import theorem_markdown

        return theorem_markdown(self, self.to_lean(audit=False))


def theorem(
    fn: Callable[..., Expr] | None = None,
    *,
    proof: Tactic | None = None,
    name: str | None = None,
    assumptions: Callable[..., Any] | None = None,
    imports: Iterable[str] = (),
) -> Any:
    """Declare a theorem from a function; parameters + sort annotations are the variables.

        @pl.theorem(proof=pl.ring())
        def square_identity(x: pl.Real, y: pl.Real):
            return (x + y)**2 == x**2 + 2*x*y + y**2

    The function is called once, with fresh symbols, to build the statement (ordinary
    Python execution, not source parsing). ``assumptions`` may be a function of the same
    variables returning a list/dict of propositions. Returns a :class:`Theorem`.
    """

    def build(f: Callable[..., Expr]) -> Theorem:
        try:
            hints = resolve_annotations(f)
        except Exception as exc:  # noqa: BLE001 - unresolved annotation names
            raise SortError(f"@theorem {f.__name__}: cannot evaluate annotations: {exc}") from exc
        origin = Origin(f.__code__.co_filename, f.__code__.co_firstlineno)
        variables = []
        for pname, param in inspect.signature(f).parameters.items():
            if param.kind not in (param.POSITIONAL_ONLY, param.POSITIONAL_OR_KEYWORD):
                raise SortError(f"@theorem {f.__name__}: *args/**kwargs are not supported")
            sort = hints.get(pname)
            if not isinstance(sort, SortT):
                raise SortError(
                    f"@theorem {f.__name__}: parameter {pname!r} needs a sort annotation "
                    "such as `x: pl.Real`"
                )
            variables.append(make_var(pname, sort, origin))
        conclusion = f(*variables)
        hyps = assumptions(*variables) if assumptions is not None else None
        thm = Theorem(name or f.__name__, variables, hyps, conclusion, imports=imports,
                      proof=proof)
        thm.origin = origin
        thm.__doc__ = f.__doc__
        return thm

    return build(fn) if fn is not None else build
