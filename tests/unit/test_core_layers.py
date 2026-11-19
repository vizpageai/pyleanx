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
        "backend/repl_check", "project", "justify", "derivation", "ops", "numeric",
        "fact_search"]
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


def test_a_third_party_domain_registers_its_facts(tmp_path, monkeypatch):
    import pyleanx as pl
    from pyleanx import fact_search

    (tmp_path / "toy_pack.py").write_text(
        "from pyleanx.proofs import Name\n"
        "LEMMAS = {'frob_comm': Name('Toy.frob_comm', label='the frobnicator commutes')}\n",
        encoding="utf-8")
    monkeypatch.syspath_prepend(str(tmp_path))
    saved = dict(fact_search._REGISTRY)
    try:
        fact_search.register_domain("toy_pack", prefix="toy", title="Toy")
        assert pl.fact("the frobnicator commutes").name == "Toy.frob_comm"
        assert any(d.module == "toy_pack" for d in fact_search.domains())
    finally:
        fact_search._REGISTRY.clear()
        fact_search._REGISTRY.update(saved)
        fact_search._catalog.cache_clear()
        fact_search._idf.cache_clear()


def test_a_domain_pack_registers_through_one_object():
    import random

    import pyleanx as pl
    from pyleanx import diagnose, justify, numeric

    saved = (list(justify._RULES), dict(justify._PACKS), dict(numeric._SAMPLERS),
             list(diagnose._HINTS))
    try:
        toy = pl.domain_pack("toy", sorts={"Toy"})
        toy.rule("step", 15, "toy_tactic", name="t")
        toy.sampler("Toy", lambda rng: rng.random())
        toy.hint(r"toy failure", "check the toy")
        with justify.active_packs(frozenset({"toy"})):
            assert "toy_tactic" in justify.alternatives(["h"], ["h"])
        assert 0 <= numeric._sample("Toy", random.Random(0)) < 1
        assert diagnose._hint("a toy failure here") == "check the toy"
    finally:
        justify._RULES[:] = saved[0]
        justify._PACKS.clear()
        justify._PACKS.update(saved[1])
        numeric._SAMPLERS.clear()
        numeric._SAMPLERS.update(saved[2])
        diagnose._HINTS[:] = saved[3]
