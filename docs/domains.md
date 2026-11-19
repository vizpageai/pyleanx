# Domain packages

PyLeanX's core knows logic, numbers and how to talk to Lean; mathematics comes in
**domain packages** built on it, the way torchvision is built on torch. A domain package
is a separate Python distribution that depends on `pyleanx` and is never imported by it.

| Package | Subject | Install |
|---|---|---|
| [`pyleanx-analysis`](https://github.com/vizpageai/pyleanx/tree/main/domains/analysis) | real and measure-theoretic analysis | `pip install -e domains/analysis` (from a checkout) |

The geometry, algebra and number-theory vocabularies still ship inside the `pyleanx`
distribution (`pyleanx.geometry`, …); geometry is already written as a pack through the
same interface.

## What a package contributes

Everything goes through one object, `pl.domain_pack` (see [The core](core.md)):

* **vocabulary**: the symbols statements are written with (`an.integrable(f)`,
  `an.l1_norm(f)`), printed as a textbook prints them;
* **facts**: Mathlib theorems (or theorems the package proves) cited by name,
  `because=[facts.markov, "hf"]`;
* **justification rules**: what a textbook leaves implicit in this subject. They apply
  only to theorems that use the package's vocabulary, and Lean checks every use;
* **numeric sanity checks**: how to sample the subject's objects (random functions,
  points of the plane) and evaluate its operations (derivatives, integrals, angles);
* **explanations**: how Lean's failures in this subject are said in its own terms.

## Using a package

```python
import pyleanx as pl
import pyleanx_analysis as an          # registers the analysis pack
```

Importing the package is what makes its rules take part: the Lean a proof generates
depends only on the proof and on the packages imported, never on what was looked up
earlier. `pyleanx doctor` lists the installed packages (`pyleanx.packs.load_plugins()`
imports them all).

## Writing a package

```text
my-domain/
  pyproject.toml          # depends on pyleanx; entry point below
  src/my_domain/__init__.py
```

```toml
[project.entry-points."pyleanx.packs"]
topology = "my_domain"
```

```python
# src/my_domain/__init__.py
import pyleanx as pl

pack = pl.domain_pack("topology", sorts={"TopSpace"}, symbols=("TopologicalSpace.",))
pack.facts("my_domain.facts", prefix="top", title="Topology")
pack.rule("close", 112, "exact isOpen_interior", name="interior is open")
pack.hint(r"IsOpen", "say why the set is open (it is an interior, a preimage, …)")
```

Test a rule against the pinned Mathlib before shipping it, and run the package's tests in
their own process: importing a pack changes the Lean its theorems generate.
