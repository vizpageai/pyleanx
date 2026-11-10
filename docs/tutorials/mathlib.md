# Using Mathlib

Mathlib contains hundreds of thousands of theorems. PyLeanX lets you cite them, look at
them as Lean states them, and build on them. All code on this page runs in order.

## Domain modules

```python
import pyleanx as pl
from pyleanx import algebra as alg, analysis as an, geometry as geo
```

Each module provides functions (`an.sin`, `geo.dist`, …), and a *catalog* of Mathlib
lemmas whose names and imports were checked against the pinned Mathlib. A catalog lemma is
called like a function to instantiate it:

```python
x = pl.symbol("x", pl.Real)
trig = pl.Theorem("pythagorean_identity", [x],
                  conclusion=an.sin(x)**2 + an.cos(x)**2 == 1,
                  proof=pl.exact(an.sin_sq_add_cos_sq(x)))

exp_bound = pl.Theorem("exp_tangent_line", [x],
                       conclusion=x + 1 <= pl.exp(x),
                       proof=pl.exact(an.add_one_le_exp(x)))
```

`pl.exact(term)` says "this term is the proof". Lean checks that the lemma's statement,
instantiated at `x`, is exactly the goal.

## Lemmas as hints

Automation such as `nlinarith` (nonlinear arithmetic) often needs one good hint:

```python
a, b, c, d = pl.symbols("a b c d", pl.Real)
cauchy_schwarz = pl.Theorem(
    "cauchy_schwarz_2d", [a, b, c, d],
    conclusion=(a*c + b*d)**2 <= (a**2 + b**2) * (c**2 + d**2),
    proof=pl.nlinarith(alg.sq_nonneg(a*d - b*c)))
```

The `algebra` module also has helpers that pick the proof for you:

```python
am_gm = alg.am_gm_two("am_gm", a, b)                    # 2ab ≤ a² + b²
binomial = alg.identity("cube", (a + b)**3, a**3 + 3*a**2*b + 3*a*b**2 + b**3)
```

## Plane geometry

Points live in the Euclidean plane ℝ². Only `=` and `≠` make sense between points.

```python
A, B, C = geo.points("A B C")
triangle = pl.Theorem("triangle_inequality", [A, B, C],
                      conclusion=geo.dist(A, C) <= geo.dist(A, B) + geo.dist(B, C),
                      proof=pl.exact(geo.dist_triangle(A, B, C)))

angle_sum = pl.Theorem(
    "angle_sum", [A, B, C], assumptions={"h": B != A},
    conclusion=geo.angle(A, B, C) + geo.angle(B, C, A) + geo.angle(C, A, B) == pl.pi(),
    proof=pl.exact(geo.angle_add_angle_add_angle_eq_pi(C, pl.hyp("h"))))
```

`pl.hyp("h")` refers to the assumption named `h`.

```python
results = pl.verify_all([trig, exp_bound, cauchy_schwarz, am_gm, binomial, triangle,
                         angle_sum], timeout=1800)
for r in results:
    print(r.summary())
assert all(r.verified for r in results)
```

## Every Mathlib name, no module paths

`pl.mathlib` gives access to every declaration of Lean core, Batteries and the pinned
Mathlib by its Lean name. PyLeanX finds the module that defines it and imports exactly
that module:

```python
M = pl.mathlib
y = pl.var("y", pl.Real)
sqrt_ok = pl.Theorem("sqrt_nonneg_demo", [y], conclusion=pl.Le(0, M.Real.sqrt(y)),
                     proof=pl.exact(M.Real.sqrt_nonneg(y)))
print(sqrt_ok.to_lean().splitlines()[0])        # import Mathlib.Analysis.Real.Sqrt
print(M.find("Finset.sum_range_succ"))          # ('Mathlib.Algebra.BigOperators…', 'theorem')
print(M.search("sqrt le sqrt")[:3])
assert sqrt_ok.verify().verified
```

- theorems are citable lemmas (`M.Real.sqrt_nonneg(y)`), definitions are functions
  (`M.Real.sqrt(y)`), types are sorts (`pl.var("v", M.EuclideanSpace(pl.Real, pl.Fin(3)))`);
- a mistyped name raises an error with suggestions;
- from the shell: `pyleanx mathlib find NAME`, `pyleanx mathlib search WORDS`.

The name index is built once per Mathlib revision from the local sources (about a minute,
no Lean run) and cached. It records *where* names live; Lean checks every use.

## Any Mathlib declaration by module path

Outside the catalogs, cite a declaration by name and give the module it lives in:

```python
abs_triangle = pl.ref("abs_add_le", imports=["Mathlib.Algebra.Order.Group.Unbundled.Abs"])
t = pl.Theorem("abs_triangle", [a, b], conclusion=abs(a + b) <= abs(a) + abs(b),
               proof=pl.exact(abs_triangle(a, b)))
assert t.verify().verified
```

If you do not know the module, `imports=["Mathlib"]` always works (it loads all of Mathlib,
which is slower). Mathlib's [documentation](https://leanprover-community.github.io/mathlib4_docs/)
shows each declaration's module.

## Seeing a theorem as Lean states it

`pl.infoview` shows a declaration like the Lean editor's infoview, straight from Lean, with
nothing restated:

```python
view = pl.infoview(alg.abs_add_le)
print(view)
assert view.conclusion == "|a + b| ≤ |a| + |b|"
```

```text
α : Type u_1
inst✝ : Lattice α
inst✝ : AddCommGroup α
inst✝ : AddLeftMono α
a b : α
⊢ |a + b| ≤ |a| + |b|
```

Mathlib states results in general structures (here any lattice-ordered additive group);
PyLeanX instantiates them at ℝ. From the shell:
`pyleanx infoview abs_add_le --import Mathlib.Algebra.Order.Group.Unbundled.Abs`.

## Searching: the theorem bank

The bank indexes the catalogs with the statements Lean reports, searches them, and stores
your own verified theorems with their evidence:

```bash
pyleanx bank index                       # once: asks Lean for every catalog statement
pyleanx bank search "triangle inequality"
pyleanx bank show geometry.dist_triangle
```

```python
bank = pl.TheoremBank()                  # in memory; TheoremBank.open() uses ~/.pyleanx/bank.json
bank.add_theorem(cauchy_schwarz, results[2], id="mine.cauchy_schwarz_2d",
                 aliases=["cauchy schwarz in the plane"])
print(bank.search("cauchy schwarz")[0].entry.summary())
```

A bank entry is a pointer, never a proof: reusing it means Lean checks it again. Entries
record the Lean and Mathlib versions and refuse to be used with others.
