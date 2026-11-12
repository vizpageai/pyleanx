"""PyLeanX: write theorems in Python, have them checked by the Lean 4 kernel.

    import pyleanx as pl
    x, y = pl.symbols("x y", pl.Real)
    thm = pl.Theorem("square_identity", variables=[x, y],
                     conclusion=(x + y)**2 == x**2 + 2*x*y + y**2)
    thm.prove(pl.ring())
    result = thm.verify()          # runs Lean + axiom audit
    assert result.verified, result.diagnostics

Python only *describes* mathematics; Lean decides it. ``result.verified`` is True
only after Lean accepted the exact generated source and the axiom audit passed.
"""

from __future__ import annotations

from . import algebra, analysis, geometry, mathlib

# ---- libraries and generated bindings (M10-M11)
from . import bindings as lib  # noqa: E402
from .analysis import cos, pi, sin
from .backend.audit import DEFAULT_POLICY, STANDARD_AXIOMS, AxiomPolicy
from .backend.cache import ResultCache
from .backend.interface import Diagnostic, Status, VerificationResult
from .backend.leaninteract import shutdown_repls as shutdown_sessions
from .backend.subprocess_backend import verify_all
from .bank import (
    BankEntry,
    BankError,
    CrossSystemError,
    Formalization,
    TheoremBank,
    VersionMismatchError,
)
from .binders import free_vars, prop_symbol, symbol, symbols

# ---- general Lean vocabulary (M11-M13): any type, fun, ∑/∫, definitions, structured proofs
from .defs import define, define_type, mk, structure  # noqa: E402
from .errors import (
    IdentifierError,
    LiteralError,
    ProjectError,
    PyLeanXError,
    ScopeError,
    SortError,
    SymbolicTruthValueError,
    TacticError,
    UnsupportedConstructError,
)
from .explain import Explanation, explain  # noqa: E402
from .expr import (
    FALSE,
    TRUE,
    And,
    Eq,
    Exists,
    Expr,
    Forall,
    Func,
    Ge,
    Gt,
    Iff,
    Implies,
    Le,
    Lt,
    Ne,
    Not,
    Or,
    Var,
    cast,
    exp,
    integer,
    log,
    nat,
    rat,
    real,
    sqrt,
)
from .expr import abs_ as abs  # noqa: A001 - intentional mathematical name
from .expr import max_ as max  # noqa: A001
from .expr import min_ as min  # noqa: A001
from .faithful import SameStatement, same_statement  # noqa: E402
from .infoview import DeclView, infoview
from .libs import add_library, build_library, list_libraries, remove_library  # noqa: E402
from .project import LeanProject, find_project
from .proofgraph import ProofGraph, proof_graph  # noqa: E402
from .proofs import (  # noqa: E402
    apply,
    assumption,
    auto,
    branches,
    calc,
    cases,
    claim,
    conclude,
    constructor,
    decide,
    exact,
    ext,
    have,
    hyp,
    induction,
    intro,
    let,
    linarith,
    nlinarith,
    norm_num,
    obtain,
    omega,
    positivity,
    proof,
    raw_tactic,
    ref,
    rev,
    rewrite,
    rfl,
    ring,
    rw,
    show,
    simp,
    steps,
    unfold,
    use,
)
from .prose import Prose, prose  # noqa: E402
from .render.lean import render_module
from .serialize import theorem_from_canonical
from .session import Goals, ProofSession, StepResult
from .terms import apply as app  # noqa: E402  (pl.apply is the tactic)
from .terms import (  # noqa: E402
    ascribe,
    const,
    field,
    fun,
    integral,
    norm,
    pair,
    smul,
    var,
)
from .terms import prod as prod  # noqa: E402
from .terms import sum as sum  # noqa: E402, A004
from .theorem import Hypothesis, Theorem, theorem
from .types import UNKNOWN, EuclideanSpace, Fin, Fn, Int, LeanType, Nat, Prod, Prop, Rat, Real, Sort  # noqa: E402
from .types import lean_type as Type  # noqa: E402, N812

__version__ = "0.1.0.dev0"


def latex(obj: Expr | Theorem) -> str:
    """LaTeX source for an expression or theorem statement (display only)."""
    return obj.to_latex()


__all__ = [
    # sorts
    "Sort", "Nat", "Int", "Rat", "Real", "Prop",
    # symbols & expressions
    "symbol", "symbols", "prop_symbol", "free_vars", "Expr", "Var", "Func",
    "Eq", "Ne", "Le", "Lt", "Ge", "Gt", "Not", "And", "Or", "Implies", "Iff", "Forall",
    "Exists", "TRUE", "FALSE",
    "cast", "nat", "integer", "rat", "real", "sqrt", "exp", "log", "abs", "min", "max",
    "sin", "cos", "pi",
    # domain modules
    "algebra", "analysis", "geometry",
    # theorems & proofs
    "Theorem", "Hypothesis", "theorem", "latex", "ring", "omega", "positivity", "rfl", "decide",
    "constructor", "assumption", "linarith", "nlinarith", "norm_num", "simp", "intro", "exact",
    "apply", "rw", "rewrite", "rev", "use", "steps", "branches", "raw_tactic", "ref", "hyp",
    # verification
    "verify_all", "VerificationResult", "Status", "Diagnostic", "AxiomPolicy",
    "DEFAULT_POLICY", "STANDARD_AXIOMS", "LeanProject", "find_project", "ResultCache",
    "render_module", "mathlib", "ProofSession", "StepResult", "Goals", "shutdown_sessions",
    # theorem bank (M7)
    "TheoremBank", "BankEntry", "Formalization", "BankError", "VersionMismatchError",
    "CrossSystemError", "theorem_from_canonical",
    # library declarations, infoview-style
    "infoview", "DeclView", "proof_graph", "ProofGraph", "explain", "Explanation",
    # general Lean vocabulary
    "Type", "LeanType", "Fn", "Prod", "Fin", "EuclideanSpace", "UNKNOWN", "var", "const", "app",
    "fun", "sum", "prod", "integral", "pair", "field", "ascribe", "smul", "norm",
    "define", "define_type", "structure", "mk",
    # structured proofs
    "auto", "have", "calc", "show", "obtain", "cases", "induction", "unfold", "ext", "proof",
    "claim", "conclude", "let", "prose", "Prose",
    # libraries, bindings, faithfulness
    "lib", "add_library", "build_library", "list_libraries", "remove_library",
    "same_statement", "SameStatement",
    # errors
    "PyLeanXError", "SymbolicTruthValueError", "SortError", "LiteralError", "ScopeError",
    "IdentifierError", "TacticError", "UnsupportedConstructError", "ProjectError",
]
