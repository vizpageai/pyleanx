# Releasing (maintainers)

## One-time setup

1. **PyPI trusted publishing**: on <https://pypi.org/manage/account/publishing/> add a
   pending publisher: project `pyleanx`, owner `vizpageai`, repository `pyleanx`,
   workflow `release.yml`, environment `pypi`. No API token is stored anywhere.
2. In the GitHub repository settings, create the environment `pypi` (optionally with
   required reviewers, so every upload needs a human click).
3. **Documentation**: Settings → Pages → Source: *GitHub Actions*.

## Checklist for a release

1. CI is green on `main`: lint + types, unit matrix, **Lean integration**, examples,
   clean wheel install.
2. If the Lean/Mathlib pin moved: update `lean-project/`, `src/pyleanx/_lean_template/`,
   `_domain.VERIFIED_MATHLIB`/`VERIFIED_TOOLCHAIN`, run the slow catalog check, update the
   README and docs.
3. Set `__version__` in `src/pyleanx/__init__.py` (e.g. `0.1.0`), the version in
   `CITATION.cff`, and move *Unreleased* in `CHANGELOG.md` to the new version with the date.
4. Commit, then tag and push: `git tag -a v0.1.0 -m "PyLeanX 0.1.0" && git push origin v0.1.0`.
5. The `release` workflow builds the sdist and wheel, checks them, re-runs the clean
   install with Lean, uploads to PyPI via trusted publishing (after the
   environment approval) and creates a GitHub release with the changelog section.
6. Check `pip install pyleanx==0.1.0` in a fresh environment and the docs site.

## Version policy

See [Stability and versioning](stability.md).
