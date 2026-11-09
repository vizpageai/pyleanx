import pytest

import pyleanx as pl
from pyleanx.backend.declarations import render_check_file
from pyleanx.infoview import DeclView, DeclViews, parse_signature

SIG = ("two_mul_le_add_sq.{u_1} {α : Type u_1} [CommRing α] [LinearOrder α]\n"
       "  [IsStrictOrderedRing α] (a b : α) : 2 * a * b ≤ a ^ 2 + b ^ 2")


def test_render_check_file_signature_mode():
    src, _ = render_check_file(["sq_nonneg"], ["Mathlib.Algebra.Order.Ring.Unbundled.Basic"],
                               signature=True)
    assert "#check sq_nonneg" in src and "#check @" not in src
    src, _ = render_check_file(["sq_nonneg"], [])
    assert "#check @sq_nonneg" in src


def test_parse_signature_binders_and_conclusion():
    binders, concl = parse_signature(SIG, "two_mul_le_add_sq")
    assert [str(b) for b in binders] == [
        "α : Type u_1", "inst✝ : CommRing α", "inst✝ : LinearOrder α",
        "inst✝ : IsStrictOrderedRing α", "a b : α"]
    assert [b.kind for b in binders] == ["implicit", "instance", "instance", "instance",
                                         "explicit"]
    assert concl == "2 * a * b ≤ a ^ 2 + b ^ 2"


def test_parse_signature_nested_binder_types_and_named_instances():
    sig = ("foo {f : ℕ → ℕ} [inst : Fact (0 < 1)] (h : ∀ (n : ℕ), f n = n) "
           "⦃x : ℕ⦄ : f x = x")
    binders, concl = parse_signature(sig, "foo")
    assert [str(b) for b in binders] == [
        "f : ℕ → ℕ", "inst : Fact (0 < 1)", "h : ∀ (n : ℕ), f n = n", "x : ℕ"]
    assert binders[-1].kind == "strict implicit"
    assert concl == "f x = x"


def test_parse_signature_without_binders():
    assert parse_signature("Real.pi_pos : 0 < Real.pi", "Real.pi_pos") == ((), "0 < Real.pi")


def test_parse_signature_unexpected_shape_falls_back():
    assert parse_signature("something else", "foo") == ((), None)
    assert parse_signature("foo (a : ℕ", "foo") == ((), None)
    view = DeclView("foo", "foo weird", (), None)
    assert view.goal == "foo weird"


def test_goal_view_and_markdown():
    binders, concl = parse_signature(SIG, "two_mul_le_add_sq")
    view = DeclView("two_mul_le_add_sq", " ".join(SIG.split()), binders, concl)
    assert view.goal.splitlines()[-2:] == ["a b : α", "⊢ 2 * a * b ≤ a ^ 2 + b ^ 2"]
    md = view._repr_markdown_()
    assert "```lean\nα : Type u_1" in md and "<details>" in md
    both = DeclViews([view, view])
    assert both._repr_markdown_().count("```lean") == 4


def test_infoview_rejects_bad_input():
    with pytest.raises(TypeError):
        pl.infoview()
    with pytest.raises(TypeError):
        pl.infoview(42)  # type: ignore[arg-type]
    with pytest.raises(pl.IdentifierError):
        pl.infoview("bad name; #eval 1")


def test_infoview_uses_reference_imports(monkeypatch):
    seen = {}

    def fake(names, imports, project=None, *, timeout=None, signature=False):
        from pyleanx.backend.declarations import DeclInfo

        seen.update(names=list(names), imports=set(imports), signature=signature)
        return {n: DeclInfo(n, True, SIG if n == "two_mul_le_add_sq" else f"{n} : True")
                for n in names}

    monkeypatch.setattr("pyleanx.backend.declarations.check_declarations", fake)
    view = pl.infoview(pl.algebra.two_mul_le_add_sq)
    assert isinstance(view, DeclView) and view.conclusion == "2 * a * b ≤ a ^ 2 + b ^ 2"
    assert seen["signature"] is True
    assert seen["imports"] == set(pl.algebra.two_mul_le_add_sq.imports)
    views = pl.infoview("trivial")
    assert seen["imports"] == {"Mathlib"}  # nothing known -> whole Mathlib
    assert views.goal == "⊢ True"
    many = pl.infoview(pl.algebra.two_mul_le_add_sq, "trivial", imports=["Mathlib.Logic.Basic"])
    assert isinstance(many, DeclViews) and len(many) == 2
    assert "Mathlib.Logic.Basic" in seen["imports"]


def test_infoview_unknown_declaration(monkeypatch):
    from pyleanx.backend.declarations import DeclInfo

    monkeypatch.setattr("pyleanx.backend.declarations.check_declarations",
                        lambda names, imports, project=None, **kw:
                        {n: DeclInfo(n, False, None, "unknown identifier") for n in names})
    with pytest.raises(pl.ProjectError, match="unknown identifier"):
        pl.infoview("no_such_lemma", imports=["Mathlib.Logic.Basic"])


def test_cli_parser_has_infoview():
    from pyleanx.cli import build_parser

    args = build_parser().parse_args(["infoview", "sq_nonneg", "--import", "Mathlib.Tactic"])
    assert args.names == ["sq_nonneg"] and args.imports == ["Mathlib.Tactic"]
