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
from .infoview import DeclView, infoview
from .project import LeanProject, find_project
from .proofs import (
    apply,
    assumption,
    branches,
    constructor,
    decide,
    exact,
    hyp,
    intro,
    linarith,
    nlinarith,
    norm_num,
    omega,
    positivity,
    raw_tactic,
    ref,
    rev,
    rewrite,
    rfl,
    ring,
    rw,
    simp,
    steps,
    use,
)
from .render.lean import render_module
from .serialize import theorem_from_canonical
from .session import Goals, ProofSession, StepResult
from .theorem import Hypothesis, Theorem, theorem
from .types import Int, Nat, Prop, Rat, Real, Sort

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
    "infoview", "DeclView",
    # errors
    "PyLeanXError", "SymbolicTruthValueError", "SortError", "LiteralError", "ScopeError",
    "IdentifierError", "TacticError", "UnsupportedConstructError", "ProjectError",
]
