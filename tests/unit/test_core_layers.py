"""Guardrails of the core (docs/core.md): golden Lean, and no domain knowledge in the core."""

from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "src" / "pyleanx"

#: modules of the core: they may not import a domain pack, nor name a domain's Lean symbols
CORE = ["types", "expr", "terms", "binders", "defs", "names", "errors", "_origin", "proofs",
        "theorem", "imports", "render/lean", "render/sourcemap", "backend/interface",
        "backend/audit", "backend/cache", "backend/subprocess_backend",
        "backend/repl_check", "project", "justify", "derivation", "ops", "numeric"]
#: domain packs (vocabulary, facts, rules); built on the core, never imported by it
DOMAINS = {"geometry", "analysis", "algebra", "numbers", "complex_analysis", "harmonic",
           "hilbert", "realvar", "_geometry_textbook", "_analysis_textbook"}
#: Lean names that belong to the geometry pack
GEOMETRY_WORDS = re.compile(r"EuclideanGeometry|Collinear|collinear|Sbtw|Wbtw|sbtw|dist_comm")


def _imports(path: Path) -> set[str]:
    mod = path.relative_to(SRC).with_suffix("").parts
    out = set()
    for n in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(n, ast.ImportFrom) and n.level:
            base = list(mod[:-n.level]) if path.name != "__init__.py" else list(mod)
            if n.module:
                out.add(".".join([*base, n.module]))
            else:
                out.update(".".join([*base, a.name]) for a in n.names)
        elif isinstance(n, ast.Import):
            out.update(a.name.removeprefix("pyleanx.") for a in n.names
                       if a.name.startswith("pyleanx."))
    return out


def _core_files() -> list[Path]:
    return [p for m in CORE if (p := SRC / f"{m}.py").exists()]


def test_the_core_imports_no_domain_pack():
    bad = {p.name: sorted(d for d in _imports(p) if d.split(".")[-1] in DOMAINS)
           for p in _core_files()}
    assert {k: v for k, v in bad.items() if v} == {}


def test_the_core_names_no_geometry():
    # Geometry's rules (∠ABC = ∠CBA, distinct vertices, betweenness) are registered by the
    # geometry pack (pyleanx.geometry), not written into the core.
    hits = {p.name: sorted(set(GEOMETRY_WORDS.findall(p.read_text(encoding="utf-8"))))
            for p in _core_files()}
    assert {k: v for k, v in hits.items() if v} == {}


def test_generated_lean_of_every_written_proof_is_unchanged():
    # A change here must be re-verified with Lean, then recorded with
    # `python scripts/golden_lean.py --update` (see docs/core.md).
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        import golden_lean
    finally:
        sys.path.remove(str(ROOT / "scripts"))
    assert golden_lean.changed() == []
