"""Real-analysis vocabulary, the textbook catalogue and the proof moves it relies on."""

from __future__ import annotations

import pyleanx as pl
from pyleanx import analysis as an
from pyleanx.proofs import LibraryFact
from pyleanx.serialize import theorem_from_canonical

Seq = pl.Fn(pl.Nat, pl.Real)
a = pl.symbol("a", Seq)
f = pl.symbol("f", pl.Fn(pl.Real, pl.Real))
eps, x, x0, L = pl.symbols("ε x x₀ L", pl.Real)


def _eps_delta():
    e, d, t = pl.symbols("ε δ x", pl.Real)
    return pl.Forall(e, pl.Implies(e > 0, pl.Exists(d, pl.And(d > 0, pl.Forall(
        t, pl.Implies(pl.abs(t - x0) < d, pl.abs(f(t) - f(x0)) < e))))))


def _linear():
    t = pl.symbol("x", pl.Real)
    return pl.Theorem(
        "lin_cont", [f, x0], assumptions={"hf": pl.Forall(t, f(t) == 3 * t + 1)},
        conclusion=an.continuous_at(f, x0),
        proof=pl.proof(
            pl.suffices(_eps_delta(), because=an.continuous_at_iff),
            pl.fix(eps, assume={"hε": eps > 0}),
            pl.take(eps / 3, such_that=eps / 3 > 0),
            pl.fix(x, assume={"hx": pl.abs(x - x0) < eps / 3}),
            pl.chain(pl.abs(f(x) - f(x0)), ("=", pl.abs(3 * (x - x0)), "hf"),
                     ("=", 3 * pl.abs(x - x0), an.abs_mul), ("<", 3 * (eps / 3)), ("=", eps)),
        ))


def test_take_with_side_condition_renders_proves_and_prints():
    thm = _linear()
    src = thm.to_lean()
    assert "refine ⟨ε / 3, ?_, ?_⟩" in src
    assert "· show ε / 3 > 0" in src
    text = str(thm.prose())
    assert "Take δ = ε/3; then ε/3 > 0." in text
    # the goal after the step is the second part: the next step is "Let x …"
    assert "Let x ∈ ℝ with |x - x₀| < ε/3." in text
    again = theorem_from_canonical(thm.canonical())

    def body(s: str) -> list[str]:  # serialized lemma names do not carry their imports
        return [ln for ln in s.splitlines() if not ln.startswith("import ")]

    assert body(again.to_lean()) == body(src)


def test_take_because_needs_such_that():
    import pytest

    with pytest.raises(pl.TacticError):
        pl.take(eps, because="h")


def test_sequences_print_as_formulas_and_casts_are_hidden():
    n = pl.symbol("n", pl.Nat)
    phi = pl.symbol("φ", pl.Fn(pl.Nat, pl.Nat))
    s = pl.And(an.tendsto(pl.fun(lambda n: 1 / (pl.cast(n, pl.Real) + 1), pl.Nat), 0),
               an.cauchy(pl.fun(lambda n: a(phi(n)), pl.Nat)), an.cauchy(a),
               an.increasing(a), an.tendsto(a, L))
    thm = pl.Theorem("t", [a, phi, L], conclusion=s)
    text = str(thm.prose())
    assert "1/(n + 1) → 0" in text and "(a(φ(n)))ₙ is Cauchy" in text
    assert "(aₙ) is Cauchy" in text and "(aₙ) is increasing" in text and "aₙ → L" in text
    md = thm.prose().to_markdown()
    assert r"\frac{1}{n + 1}" in md and r"\mathbb{R}\right)" not in md
    # Lean keeps the cast
    assert "(↑n + 1)" in thm.to_lean() or "((n : ℝ) + 1)" in thm.to_lean() or "↑n" in \
        thm.to_lean()
    del n


def test_choose_names_the_parts_of_a_conjunction():
    phi = pl.symbol("φ", pl.Fn(pl.Nat, pl.Nat))
    M = pl.symbol("M", pl.Real)
    k = pl.symbol("n", pl.Nat)
    thm = pl.Theorem(
        "bw", [a, M], assumptions={"hM": pl.Forall(k, pl.abs(a(k)) <= M)},
        conclusion=pl.Exists(phi, pl.And(an.strictly_increasing(phi),
                                         an.cauchy(pl.fun(lambda n: a(phi(n)), pl.Nat)))),
        proof=pl.proof(
            pl.choose([phi, L], such_that=pl.And(
                an.strictly_increasing(phi), an.tendsto(pl.fun(lambda n: a(phi(n)), pl.Nat), L)),
                because=[an.bolzano_weierstrass, "hM"], names="hφ hlim"),
            pl.take(phi, such_that=an.strictly_increasing(phi), because="hφ"),
            pl.conclude(because=[an.convergent_cauchy, "hlim"])))
    text = str(thm.prose())
    assert "(φ is strictly increasing (hφ))" in text
    assert "a(φ(n)) → L (hlim)" in text


def test_catalogue_labels_and_shipped_proofs():
    shipped = [v for v in an.LEMMAS.values() if isinstance(v, LibraryFact)]
    assert len(shipped) >= 29
    for fact in shipped:
        assert fact.label and "sorry" not in fact.lean and fact.name in fact.lean
    for name in ("ivt", "mvt", "rolle", "evt_max", "heine_cantor", "bolzano_weierstrass",
                 "monotone_convergence", "squeeze", "continuous_at_iff", "cauchy_iff",
                 "abs_lt", "triangle_inequality", "reverse_triangle"):
        assert name in an.LEMMAS, name
    assert an.bounded(a).to_latex().startswith(r"\exists M")
    assert "is continuous on [0, 1]" in pl.Theorem(
        "c", [f], conclusion=an.continuous_on(f, 0, 1)).prose().statement
