# Contributing to PyLeanX

Thanks for helping. PyLeanX has one rule that overrides everything else:

> **Lean decides.** Python builds statements and proofs; only a pinned Lean run plus an
> `#print axioms` audit may produce `verified=True`. No change may weaken that.

## Development setup

```bash
git clone https://github.com/vizpageai/pyleanx && cd pyleanx
python -m venv .venv && . .venv/bin/activate      # Windows: .venv\Scripts\activate
pip install -e ".[dev,interactive,docs]"
cd lean-project && lake exe cache get && cd ..     # prebuilt Mathlib (several GB)
python -m pyleanx doctor
```

You need [elan](https://lean-lang.org/install/manual/). The Lean toolchain and the Mathlib
revision are pinned in `lean-project/`; do not bump them in an unrelated PR.

## Checks (all must pass)

```bash
ruff check .
mypy src/pyleanx
pytest tests/unit -q                       # fast, no Lean
pytest tests/integration -q                # real Lean; slow (minutes)
python scripts/run_examples.py             # every example, expected outcomes
mkdocs build --strict                      # documentation
```

CI runs the same on Linux, Windows and macOS (unit tests) and Linux (Lean, examples, a
clean wheel install).

## What a good PR looks like

- **Tests first** for parser, IR, rendering and policy changes. Every bug fix gets a test.
- **Real Lean** for anything that changes what reaches Lean: add or extend an integration
  test in `tests/integration/*_lean.py`.
- **Negative tests** for every new way to accept a proof (false statement, wrong tactic,
  `sorry`, user axioms, native evaluation must still be rejected).
- **No `sorry`/`admit`** in proofs, examples or tests, except deliberately failing fixtures.
- **Docs**: public API changes update `docs/` and `CHANGELOG.md` (under *Unreleased*).
- **Typed** public functions, docstrings for anything exported from `pyleanx`.
- Domain catalog additions (`algebra.py` etc.) must be checked against the pinned Mathlib
  (`PYLEANX_SLOW_TESTS=1 pytest tests/integration/test_domains_lean.py`).

## Design boundaries

- Do not reimplement Lean's type checker or kernel in Python.
- Do not add implicit coercions or float literals.
- Raw tactic text stays opt-in, screened, and audited.
- PyLeanX is not a sandbox; do not describe it as one.

## Releases

Maintainers: see [docs/releasing.md](docs/releasing.md).

By contributing you agree that your work is licensed under the project's MIT license and
that you follow the [Code of Conduct](CODE_OF_CONDUCT.md).
