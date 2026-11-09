"""General Lean vocabulary, definitions, structured proofs (no Lean needed)."""

from __future__ import annotations

import json

import pytest

import pyleanx as pl
from pyleanx.backend.interface import Status
from pyleanx.backend.subprocess_backend import LeanRun, classify, parse_json_messages
from pyleanx.project import LeanProject
from pyleanx.serialize import theorem_from_canonical
from pyleanx.types import validate_type_text

V = pl.EuclideanSpace(3)


# ------------------------------------------------------------------------------ types
def test_open_types_render_and_intern():
    assert pl.EuclideanSpace(3) is V
    assert pl.Fn(V, pl.Real).lean_name() == "EuclideanSpace ℝ (Fin 3) → Real"
    assert pl.Fn(pl.Fn(pl.Real, pl.Real), pl.Real).lean_name(True) == "(ℝ → ℝ) → ℝ"
    assert pl.Prod(V, pl.Fn(V, V)).lean_name() == (
        "EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))")
    assert pl.Type("Set ℝ").lean_name() == "Set ℝ"


@pytest.mark.parametrize("bad", ["Real) (h : False", "ℝ := 0", "ℝ\n#eval 1", "ℝ -- x",
                                 "sorryAx ℝ", "(ℝ", "ℝ]", ""])
def test_type_text_cannot_escape_its_binder(bad):
    with pytest.raises(pl.IdentifierError):
        validate_type_text(bad)


# ------------------------------------------------------------------------------ terms
def test_fun_sum_integral_norm_smul_render():
    f = pl.var("f", pl.Fn(V, pl.Real))
    x = pl.var("x", V)
    c = pl.var("c", pl.Real)
    assert pl.fun(lambda y: f(y) * 2, V).to_lean() == (
        "fun (y : EuclideanSpace ℝ (Fin 3)) => f y * 2")
    assert pl.sum(pl.Fin(3), lambda i: x(i) ** 2).to_lean() == "∑ i : Fin 3, x i ^ 2"
    # the body of ∑ binds tighter than +: it must be parenthesized
    n = pl.var("n", pl.Nat)
    rng = pl.const("Finset.range")
    s = pl.sum(rng(n), lambda i: 2 * i + 1, sort=pl.Nat)
    assert s.to_lean() == "∑ i ∈ (Finset.range n), (2 * i + 1)"
    assert pl.integral(lambda t: t**2, bounds=(0, 1)).to_lean() == "∫ t in 0..1, t ^ 2"
    assert (pl.norm(pl.smul(c, x)) == pl.norm(c) * pl.norm(x)).to_lean() == "‖c • x‖ = ‖c‖ * ‖x‖"
    assert pl.ascribe(pl.var("k", pl.Fin(3)), pl.Nat).to_lean() == "(k : Nat)"


def test_function_application_checks_arity_and_sorts():
    f = pl.var("f", pl.Fn(pl.Real, pl.Real, pl.Real))
    a = pl.var("a", pl.Real)
    assert f(a).sort == pl.Fn(pl.Real, pl.Real)
    assert f(a, a).sort is pl.Real
    with pytest.raises(pl.SortError):
        f(a, a, a)
    with pytest.raises(pl.SortError):
        a(a)  # a real number is not a function


def test_scope_checks_cover_fun_and_big_operators():
    x = pl.var("x", pl.Real)
    stray = pl.var("y", pl.Real)
    with pytest.raises(pl.ScopeError):
        pl.Theorem("t", [x], conclusion=pl.app(pl.fun(lambda z: z + stray, pl.Real), x) == x)
    # a bound variable may not shadow a theorem variable
    with pytest.raises(pl.ScopeError):
        pl.Theorem("t2", [x], conclusion=pl.sum(pl.Fin(2), lambda x: pl.ascribe(x, pl.Real))
                   == x)


def test_open_types_pass_comparisons_and_numerals_through():
    x = pl.var("x", V)
    prop = pl.norm(x) <= 1
    assert prop.to_lean() == "‖x‖ ≤ 1"
    assert (x == pl.smul(2, x)).to_lean() == "x = 2 • x"
    pl.Theorem("t", [x], conclusion=pl.Le(0, pl.norm(x)))  # no untyped-literal error


def test_structures_pairs_and_fields():
    @pl.structure
    class Pt:
        px: pl.Real
        py: pl.Real

    p = pl.var("p", Pt)
    assert p.px.to_lean() == "p.px"
    with pytest.raises(AttributeError):
        p.pz  # noqa: B018
    lit = pl.mk(Pt, px=1, py=2)
    assert lit.to_lean() == "({ px := 1, py := 2 } : Pt)"
    with pytest.raises(pl.SortError):
        pl.mk(Pt, px=1)
    a, b = pl.symbols("a b", pl.Real)
    pr = pl.var("pr", pl.Prod(pl.Real, V))
    assert pl.field(pr, "fst").sort is pl.Real
    assert pl.pair(a, b).to_lean() == "(a, b)"


# ------------------------------------------------------------------------------ definitions
def test_definitions_render_in_dependency_order():
    Vec = pl.define_type("UVec", V)

    @pl.define(returns=pl.Real)
    def uq(v: Vec):
        """Energy."""
        return pl.sqrt(1 + pl.norm(v) ** 2)

    @pl.define(returns=pl.Real)
    def uq2(v: Vec):
        return uq(v) ** 2

    v = pl.var("v", Vec)
    src = pl.Theorem("t", [v], conclusion=pl.Le(1, uq2(v)), proof=pl.auto()).to_lean()
    i_abbrev = src.index("abbrev UVec : Type := EuclideanSpace ℝ (Fin 3)")
    i_q = src.index("noncomputable def uq (v : UVec) : Real :=")
    i_q2 = src.index("noncomputable def uq2 (v : UVec) : Real :=")
    i_thm = src.index("theorem t")
    assert i_abbrev < i_q < i_q2 < i_thm
    assert "/-- Energy. -/" in src
    assert src.count("noncomputable def uq ") == 1


def test_two_different_definitions_with_one_name_are_rejected():
    @pl.define(returns=pl.Real)
    def clash(x: pl.Real):
        return x

    first = clash

    @pl.define(returns=pl.Real)  # noqa: F811
    def clash(x: pl.Real):  # type: ignore[no-redef]
        return x + 1

    x = pl.var("x", pl.Real)
    t = pl.Theorem("t", [x], conclusion=first(x) == clash(x))
    with pytest.raises(pl.ScopeError):
        t.to_lean()


def test_broken_definition_rejects_every_theorem_in_the_file():
    @pl.define(returns=pl.Real)
    def bdef(x: pl.Real):
        return x

    x = pl.var("x", pl.Real)
    a = pl.Theorem("uses", [x], conclusion=bdef(x) == x, proof=pl.rfl())
    b = pl.Theorem("unrelated", [x], conclusion=x == x, proof=pl.rfl())
    mod = pl.render_module([a, b])
    span = next(s for s in mod.source_map.spans if s.kind == "definition")
    msgs = [json.dumps({"severity": "error", "pos": {"line": span.start_line, "column": 0},
                        "endPos": None, "data": "unknown identifier", "fileName": "f"})]
    for n in ("uses", "unrelated"):
        msgs.append(json.dumps({"severity": "information",
                                "pos": {"line": mod.source_map.audit_line(n), "column": 0},
                                "endPos": None, "data": f"'{n}' depends on axioms: [propext]",
                                "fileName": "f"}))
    parsed, _ = parse_json_messages("\n".join(msgs))
    run = LeanRun(returncode=1, messages=parsed, other_output="", timed_out=False, duration_ms=1)
    out = classify(run, mod, LeanProject.at("."))
    assert all(st is Status.REJECTED for st, _, _ in out.values())


# ------------------------------------------------------------------------------ proofs
def test_structured_proofs_render():
    a, b = pl.symbols("a b", pl.Real)
    t = pl.Theorem(
        "t", [a, b], conclusion=(a + b) ** 2 <= 2 * (a**2 + b**2),
        proof=pl.proof(pl.have("h", pl.Le(0, (a - b) ** 2), pl.positivity()),
                       pl.calc((a + b) ** 2, ("=", a**2 + 2 * a * b + b**2, pl.ring()),
                               ("<=", 2 * (a**2 + b**2), pl.nlinarith("h")))))
    src = t.to_lean()
    assert "  have h : 0 ≤ (a - b) ^ 2 := by positivity" in src
    assert "  calc (a + b) ^ 2" in src
    assert "    _ = a ^ 2 + 2 * a * b + b ^ 2 := by ring" in src
    assert "    _ ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [h]" in src
    n = pl.var("n", pl.Nat)
    ind = pl.Theorem("i", [n], conclusion=pl.Le(0, n),
                     proof=pl.induction("n", zero=pl.simp(), succ=pl.omega())).to_lean()
    assert "induction n with\n  | zero => simp\n  | succ k ih => omega" in ind
    y = pl.var("y", pl.Int)
    ob = pl.Theorem("o", [], assumptions={"h": pl.Exists(y, y == y)}, conclusion=pl.TRUE,
                    proof=pl.obtain("w hw", "h") >> pl.cases("hw", "p", "q r") >> pl.rfl())
    src = ob.to_lean()
    assert "obtain ⟨w, hw⟩ := h" in src and "rcases hw with p | ⟨q, r⟩" in src


def test_auto_alternatives_close_the_goal_or_fail():
    lines = pl.auto(pl.ref("sq_nonneg")(pl.var("x", pl.Real))).alternatives()
    assert "(simp [sq_nonneg x]; done)" in lines and "nlinarith [sq_nonneg x]" in lines
    assert "ring1" in lines and "ring" not in lines  # ring would leave ring_nf goals behind
    assert "exact?" not in lines and "exact?" in pl.auto(library_search=True).alternatives()


def test_raw_text_nested_in_structured_proofs_is_still_gated():
    from pyleanx.proofs import contains_raw

    x = pl.var("x", pl.Real)
    nested = pl.have("h", x == x, pl.raw_tactic("rfl"))
    assert contains_raw(nested)
    assert contains_raw(pl.calc(x, ("=", x, pl.raw_tactic("rfl"))))
    assert contains_raw(pl.induction("n", succ=pl.raw_tactic("simp")))
    t = pl.Theorem("t", [x], conclusion=x == x, proof=pl.proof(nested, pl.rfl()))
    r = t.verify(project=LeanProject.at("."))  # default policy: rejected before Lean runs
    assert r.status is Status.POLICY_REJECTED


# ------------------------------------------------------------------------------ serialization
def test_canonical_round_trip_with_definitions_and_general_terms():
    Vec = pl.define_type("RVec", V)

    @pl.structure
    class RDatum:
        e0: pl.Fn(Vec, Vec)

    @pl.define(returns=pl.Real)
    def rq(v: Vec):
        return pl.sqrt(1 + pl.norm(v) ** 2)

    v, d = pl.var("v", Vec), pl.var("d", RDatum)
    t = pl.Theorem(
        "rt", [v, d], assumptions={"h": pl.Le(1, rq(v))},
        conclusion=pl.Le(0, pl.sum(pl.Fin(3), lambda i: d.e0(v)(i) ** 2))
        & (pl.app(pl.fun(lambda w: pl.norm(w), Vec), v) == pl.norm(v)),
        proof=pl.proof(pl.have("hh", pl.Le(0, pl.norm(v)), pl.auto()),
                       pl.calc(pl.norm(v), ("=", pl.norm(v))), pl.unfold(rq)))
    data = t.canonical()
    assert [d[0] for d in data["definitions"]] == ["abbrev", "structure", "def"]
    back = theorem_from_canonical(data)
    assert back.to_lean() == t.to_lean()
    assert json.dumps(back.canonical(), sort_keys=True) == json.dumps(data, sort_keys=True)


def test_old_canonical_forms_are_unchanged():
    x = pl.symbol("x", pl.Real)
    data = pl.Theorem("t", [x], conclusion=x**2 >= 0, proof=pl.positivity()).canonical()
    assert data["variables"] == [["var", "x", "Real"]] and "definitions" not in data


# ------------------------------------------------------------------------------ faithful
def test_same_statement_check_source():
    from pyleanx.faithful import render_check, statement_term

    x = pl.var("x", pl.Real)
    t = pl.Theorem("t", [x], assumptions={"h": pl.Le(0, x)}, conclusion=pl.Le(0, pl.sqrt(x)))
    assert statement_term(t) == "∀ (x : Real) (h : 0 ≤ x), 0 ≤ Real.sqrt x"
    src = render_check(t, "Real.sqrt_nonneg", ["Mathlib.Analysis.Real.Sqrt"])
    assert "type_of% @Real.sqrt_nonneg := rfl" in src
    assert "#print axioms pyleanx_same_statement_check" in src
    with pytest.raises(pl.IdentifierError):
        render_check(t, "x; #eval 1")
