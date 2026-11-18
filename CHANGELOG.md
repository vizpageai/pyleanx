# Changelog

All notable changes are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and the project uses
[semantic versioning](https://semver.org/) (while in 0.x, minor versions may break the API;
see [docs/stability.md](docs/stability.md)).

## [Unreleased]

### Added
- [Citable facts](docs/facts.md): a generated page listing all 390 facts of the domain
  modules with the label that selects each one in `because=`.
- A step that cites a hypothesis no part of the proof defines (`because="hz"` where only `hx`
  exists) is refused when the theorem is built, with the closest names, instead of failing
  later in Lean as an unknown identifier.

- `pyleanx check SCRIPT --watch`: re-checks on every save, with Lean kept loaded, after a
  numeric sanity check; prints each proof with its verdict.
- The first `check()` of a session says what it is doing while Lean loads its imports and
  checks the shipped facts (on stderr; `PYLEANX_QUIET=1` silences it).
- `sanity_check` draws isosceles figures: for a hypothesis |AB| = |AC| it places C on the circle
  about A through B, so isosceles-triangle proofs are tried on samples instead of skipped;
  likewise right angles (∠ACB = 90°: B on the perpendicular to CA at C), e.g. Pythagoras, and
  parallels (a parallelogram's fourth vertex), equilateral triangles (two circles) and vertical
  angles; parallel/perpendicular lines and points on a line are evaluated. Of the 72
  benchmark proofs, 28 are now tried on samples (18 before), with no finding on any of them.

### Changed
- The gap filler tries "lemma applied to a cited fact" only when a step cites at most about a
  dozen facts; a step citing dozens of facts hit Lean's per-declaration time limit.
- CI runs the Lean integration tests, every example script and the naturalness benchmark as
  three parallel jobs; failures are reported as annotations, and a written proof that Lean
  rejects now fails the benchmark job.

### Fixed
- A one-word label (`because="SSS"`, `"SAS"`) cites its fact; it was taken as a Lean name.
  Citing the CPCTC family by its label is now checked by Lean in `examples/euclid_book1.py`.
- `TheoremBank.index_catalogs` asks Lean only for Mathlib declarations; it failed on the
  facts PyLeanX proves itself (`geo.altitude`, …), which exist only in files that include
  their proofs. Found by running `examples/theorem_bank.py`.
- Tutorial excerpts of example files are shown as fragments, so the documentation test runs
  every page to the end.

## [0.1.0] - 2026-11-17

First public release. Pinned to Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

### Added: core
- Typed, immutable expression IR with operator overloading (`pl.symbols`, `==`/`<=` build
  propositions, `pl.And/Or/Not/Implies/Iff/Forall/Exists`), exact literals, explicit casts.
- `pl.Theorem` and the `@pl.theorem` decorator; typed tactics (`ring`, `positivity`,
  `linarith`, `nlinarith`, `simp`, `omega`, `norm_num`, `intro`, `exact`, `apply`, `rw`, `use`,
  `constructor`, …) and gated `raw_tactic` for model-generated text.
- Deterministic Lean rendering with a source map; Python file:line origins in diagnostics.
- Batch verification (`verify`, `verify_all`) with a position-checked `#print axioms` audit,
  `AxiomPolicy` (rejects `sorryAx`, non-standard axioms and native evaluation by default),
  reproducibility fingerprint, verified-only result cache, stable JSON schema.
- CLI: `init`, `doctor`, `show-lean`, `compile`, `check`, `cache`, `bank`, `agent`, `infoview`.
- Interactive proof sessions on a persistent Lean REPL (`thm.session()`, `apply/peek/undo`).
- Jupyter display: typeset statements, results and goal states; `pl.latex`; Greek and
  subscript identifiers; `ℝ ℕ ℤ ℚ` output option.
- Domain modules `pl.algebra`, `pl.analysis` (sin, cos, π), `pl.geometry` (points of ℝ²,
  distance, angle) with lemma catalogs checked against the pinned Mathlib.
- `pl.TheoremBank`: Lean-indexed, versioned theorem bank with search and evidence.
- `pyleanx.agent`: `ProofEnv` with JSON tool schemas, proof search, proposers, a 13-problem
  benchmark (baseline 9/13) and a JSON-lines server.
- `pl.infoview`: Mathlib declarations displayed as Lean states them.

### Added: written proofs, domain libraries, natural proofs
- Open Lean types: `pl.Type("…")`, `pl.Fn`, `pl.Prod`, `pl.Fin`, `pl.EuclideanSpace`;
  terms of these types are checked by Lean (built-in sorts keep their Python checks).
- General terms: `pl.var`, `pl.const`, `pl.app`, `pl.fun`, `pl.sum`, `pl.prod`, `pl.integral`,
  `pl.pair`, `pl.field`, `pl.ascribe`, `pl.smul`, `pl.norm`; structure fields as attributes.
- Definitions: `@pl.define`, `pl.define_type`, `@pl.structure`, `pl.mk`.
- Structured proofs: `pl.have`, `pl.calc`, `pl.show`, `pl.obtain`, `pl.cases`, `pl.induction`,
  `pl.unfold`, `pl.ext`, `pl.proof`, `pl.auto`; `Theorem.auto_prove`.
- External libraries: `pyleanx add/libs/build-lib/remove` (`pl.add_library`, …).
- Generated bindings: `pl.lib.use(module)`, `pl.lib.search`, `pyleanx bindings`.
- Faithfulness: `Theorem.same_statement_as(name)`.
- `pl.mathlib.<any Lean name>`: all Lean core, Batteries and Mathlib declarations by name, with
  the defining module found automatically (index of the pinned sources);
  `pl.mathlib.find/search`, `pyleanx mathlib find|search|index`.
- `pl.proof_graph(...)` / `pyleanx proof-graph NAME`: the lemmas, definitions and types a
  theorem rests on, as computed by Lean, down to its axioms, with statistics of the full
  dependency closure. Shown as a text tree, Mermaid (Jupyter), DOT, JSON or HTML.
- `pl.explain(...)` / `pyleanx explain NAME`: a library proof step by step: its exact
  source, the goal before and after each tactic and rewrite, the lemmas each step used, and
  their statements. Lean re-elaborates the pinned source. The result is marked `exact` only
  if the proof term and statement match the compiled ones Lean verified. It also accepts
  your own `pl.Theorem`; Lean then replays exactly the source `verify()` checks.
- Written proofs: `pl.claim(P, because=…, note=…)`, `pl.conclude(…)` and `pl.let(f, …)`
  write a proof as statements with reasons; Lean fills routine gaps with standard
  automation and checks every step. `thm.prose(result)` prints the proof as numbered
  steps (text or typeset in Jupyter).
- `Theorem(…, avoid=[lemmas])`: the proof must not use these lemmas. Gap-filling
  automation excludes them and a Lean check fails verification if the proof term refers to
  them (catches circular proofs, e.g. `simp` proving sin²+cos²=1 with that very lemma).
- Vocabulary for written proofs: `an.deriv`, `an.differentiable` and calculus facts;
  `geo.line`, `geo.parallel`, `geo.on_segment`, `geo.collinear`, `geo.triangle`,
  `geo.similar`, `geo.similar_AA`. Facts Mathlib lacks in citable form
  (`geo.corresponding_angles`, `geo.similar_sides`) ship as Lean theorems with proofs,
  checked in every file that cites them.
- Written proofs across mathematics: `pl.fix`/`pl.assume` (let x be arbitrary, assume P),
  `pl.take` (witness), `pl.choose` (obtain from an existence fact), `pl.suppose_not`
  (contradiction), `pl.cases_on`/`pl.case`, `pl.induction_on`, `pl.chain` (a = b ≤ c with a
  reason per link) and `pl.suffices`; nested blocks print as numbered sub-steps (6.1, 6.2)
  that match the Lean step names (`step6_1`). The gap filler also uses one half of a cited
  `∧`/`↔`, `omega`, `push_cast` and splitting `∧`.
- `pl.type_param("G", "Group", label="group")` and `alg.group`/`ring`/`field`/…: theorems
  about every group (Lean `{G : Type*} [Group G]`).
- `pyleanx.numbers`: divisibility, parity, primes, factorials. `an.tendsto` with the ε–N
  definition `an.tendsto_iff` (shipped with its proof), `an.triangle_inequality`.
- Examples: Euclid's infinitely many primes, n(n+1) even by cases, limit of a sum (ε–N),
  groups with x² = 1 are abelian, Bernoulli's inequality by induction.
- `pyleanx.complex_analysis`: ℂ, discs and circles, holomorphy, `circle_integral`, Cauchy's
  theorem for a disc and the integral ∮ dz/(z − w) = 2πi. Example
  `readable_cauchy_integral.py`: Cauchy's integral formula from Cauchy's theorem, avoiding
  Mathlib's own formula.
- Citing proved theorems: `because=thm` / `pl.cite(thm)` carries the theorem with its proof;
  it is emitted before the citing theorem and re-checked by Lean in every run. Citing a
  theorem without a proof is an error, and a failed cited proof rejects exactly the theorems
  that cite it. The bank records citations as dependencies and makes loaded theorems
  citable. Example `using_cauchy_integral.py`: ∮_{|z|=2} z²/(z − 1) dz = 2πi.
- The Hilbert kernel away from its singularity (`examples/hilbert_kernel.py`): smoothness
  |1/(x−y) − 1/(x−y₀)| ≤ 2|y−y₀|/|x−y₀|², cancellation against a mean-zero b on
  I = [y₀ − t, y₀ + t], and the decay |∫_I b(y)/(x−y) dy| ≤ (2t/|x−y₀|²)∫_I|b| for
  |x − y₀| > 2t, and Hörmander's estimate ∫_{|x−y₀|>2t} |∫_I b(y)/(x−y) dy| dx ≤ 2∫_I|b|
  — written proofs verified by Lean. Shipped facts ∫_{|x−y₀|>s} dx/(x − y₀)² = 2/s.
- The gap filler tries `field_simp` alone; prose brackets denominators like 2t.
- Natural proofs (`docs/tutorials/natural-proofs.md`): `thm.check()` / `pl.check_all` check in
  a persistent Lean REPL (seconds after the first run; same audit as `verify`, not archived);
  `thm.sanity_check()` finds false steps on random numbers; `pl.explain_failure` and the prose
  explain rejections step by step; reasons may be descriptions (`because="AA similarity"`,
  `pl.search_facts`, `pl.fact`); `pl.similarly(step, exchange=(A, B))`; a sturdier gap filler
  (cheap matching first, either orientation, two-fact applications, notation symmetry).
- Every catalogue fact has a textbook label; a description equal to a label selects that
  fact, or a whole family sharing the label ("CPCTC"), whose members Lean tries.
- CLI: `pyleanx sanity script.py` (numeric check of every step, no Lean) and
  `pyleanx facts <description>` (search the citable facts). The sanity check constructs
  points the hypotheses determine (a point between two others, `M = midpoint(A, B)`).
- Euclid Book I propositions as written proofs (`examples/euclid_book1.py`) and a naturalness
  benchmark over the examples (`benchmarks/naturalness.py`, `docs/benchmark.md`).
- Pythagoras' theorem from similar triangles, as in a textbook (`examples/pythagoras_similar.py`):
  the leg rule AC² = AD·AB (△ABC ∼ △ACD by AA, 2 steps) and Pythagoras (drop the altitude,
  the leg rule at A and at B, add; 5 steps), both verified by Lean without Mathlib's
  Pythagoras. Geometry: `geo.perpendicular(l₁, l₂)`, `geo.on_line`, `geo.altitude` (every
  triangle), `geo.foot_right_angles`, `geo.foot_between`, `geo.right_triangle_acute`,
  `geo.altitude_to_hypotenuse`, `geo.common_angle`, `geo.proportional_sides`. The gap filler
  treats ∠ACB/∠BCA, "between A and B"/"between B and A" and the vertex order of a triangle as
  the same, as a textbook does.
- The intervals of an open set and the Calderón–Zygmund intervals (`examples/cz_intervals.py`):
  endpoints sup{y ≤ x : y ∉ U} and inf{y ≥ x : y ∉ U}, intervals that meet coincide, and every
  x ∈ {Mf > α} lies in an interval (a, b) ⊆ {Mf > α} with a, b ∉ {Mf > α} and
  ∫_[a,b]|f| ≤ 2α(b − a) — written proofs verified by Lean. The gap filler builds ⟨h₁, …, hₙ⟩.
- The Calderón–Zygmund decomposition on ℝ (`examples/calderon_zygmund.py`): with
  Ω = {Mf > α}, Ω is open, |Ω| ≤ 8‖f·1{|f|>α/2}‖₁/α, |f| ≤ α a.e. off Ω, and every interval
  meeting ℝ ∖ Ω has average ≤ 2α — written proofs verified by Lean. Lebesgue's
  differentiation theorem in textbook form ships in `pyleanx.realvar`, with its Lean proof.
- The Hilbert transform on L²(ℝ) (`pyleanx.hilbert`, `examples/hilbert_transform.py`):
  Hf = 𝓕⁻(−i sgn ξ·𝓕f) as a shipped definition; written proofs, verified by Lean, that
  ‖Hf‖₂ = ‖f‖₂ and H(Hf) = −f (via Plancherel and the a.e. calculus of L²).
- The Lᵖ bound for the Hardy–Littlewood maximal function (`examples/marcinkiewicz.py`):
  p∫₀^∞ t^{p−1}μ{Mf > t} dt ≤ (8p·2^{p−1}/(p−1))∫|f|^p, from the weak-type bound by the
  calculus lemmas 9a–9e, a measurability argument on (0,∞)×ℝ and Tonelli — all written
  proofs verified by Lean. Real exponents, [0, ∞]-valued integrals, intervals, indicators,
  pairs and product measures in `pyleanx.realvar`.
- Real-variable methods (`pyleanx.realvar`) and `examples/singular_integrals.py`: the Vitali
  covering lemma for finite families, integrals over disjoint intervals, and the covering
  bound behind the Hardy–Littlewood maximal inequality, and the maximal inequality itself
  on compact sets and its weak type (1,1) form on measurable sets of finite measure
  (α|{Mf > α}| ≤ 4‖f‖₁), all as PyLeanX written proofs verified by Lean; lecture notebook
  `examples/lecture_singular_integrals.ipynb`. `pl.union`, `pl.integral(within=…)`, and `⊆` as an infix relation.
- Harmonic analysis (`pyleanx.harmonic`, conventions of Stein–Shakarchi): Fourier
  coefficients on [−π, π], Fourier transform and inverse on ℝ, L²/L¹, the two sides of
  Parseval, and 18 shipped facts (Parseval, Bessel, Riemann–Lebesgue for coefficients and
  for the transform, (f′)^(n) = in f̂(n), the Gaussian, Fourier inversion, the integral
  formulas). Shipped *definitions* used in statements are now emitted into the Lean file.
  Lecture notebook `examples/lecture_harmonic_analysis.ipynb` (partial sums and the Gibbs
  phenomenon, decay, Riemann–Lebesgue, Gaussian dilation; three worked examples, a wrong
  step, three exercises); helpers in `examples/harmonic_lecture.py`. Plain-text prose shows
  f̂, ξ and ‖z‖.
- Real analysis as in a textbook: `pyleanx.analysis` gains definitions with ε–N / ε–δ
  unfoldings (`continuous_at`, `cauchy`, `uniformly_continuous_on`, `continuous_on`,
  `differentiable_on`, `increasing`, `bounded`, …) and 29 shipped theorems under textbook
  names (IVT, EVT, Rolle, MVT, Bolzano–Weierstrass, monotone convergence, Heine–Cantor,
  completeness, limit algebra, squeeze, Archimedean property), plus absolute-value facts.
  `pl.take(w, such_that=P, because=…)` ("take δ = ε/3 > 0"). Sequences given by a formula
  print as the formula; written proofs show casts `(n : ℝ)` as `n`; `choose … names=` quotes
  each part of a conjunction. Gap filler: substitute a cited equation, then algebra (also
  inside |…|). Lecture notebook `examples/lecture_real_analysis.ipynb` for mathematicians
  (phrasebook, catalogue, five worked examples, a rejected wrong proof, four exercises),
  helpers in `examples/analysis_lecture.py`; `examples/lecture_tools.py` holds the shared
  `check` (names the failing step from Lean's own step tags).
- Interactive lecture notebook `examples/lecture_congruent_triangles.ipynb` (congruent
  triangles: SSS, SAS, ASA, CPCTC) with SVG figures, slider explorers, worked examples, a
  rejected wrong proof, and four exercises checked by Lean via `check(...)`, which names the
  step Lean could not justify; helpers and verified solutions in `examples/geometry_lecture.py`.
- High-school plane geometry catalogue in `geo` (64 citable facts by chapter): SSS/SAS/ASA/
  AAS/HL congruence and CPCTC, similarity, alternate and co-interior angles, angle sum,
  exterior angle, isosceles triangles, Pythagoras, laws of sines and cosines, midpoints and
  the midsegment theorem, perpendicular bisectors, Thales, intersecting chords, parallelogram
  diagonals; 17 are shipped with Lean proofs. New vocabulary: `congruent`, `midpoint`,
  `is_midpoint`, `right_angle`, `opposite_sides`, `same_side`, `on_circle`, `concyclic`,
  `parallelogram`. Example `textbook_geometry.py` (five textbook proofs). The gap filler also
  uses a part of a cited conjunction, a cited fact with its points in another order, and a
  cited rewrite rule applied everywhere (e.g. `geo.angle_comm`).
- Auxiliary constructions in geometry: `geo.extend_beyond`, `geo.strictly_between`, shipped
  construction facts (`geo.extension_between/length/triangle`, `geo.bisector_parallel`,
  `geo.componendo`, …). Example `readable_angle_bisector.py`: the angle bisector theorem by
  extending BA and citing the proved side-splitter theorem. The gap filler also uses a
  cited equation reversed (`exact h.symm`).
- `avoid=` also checks inside cited PyLeanX facts and theorems, and imports avoided lemmas' modules. The gap
  filler also applies a cited lemma to a cited fact and rewrites with cited equations.

- Examples `readable_trig.py` (sin²+cos²=1 by derivatives), `readable_side_splitter.py`
  (similar triangles), `readable_am_gm.py`; `side_splitter.py`, `side_splitter_vectors.py`.

### Fixed
- Interactive sessions build and run the Lean REPL with the pinned toolchain's `lake`, so they
  work when elan has no default toolchain (as on CI) and never use a different Lean version.

### Changed
- `geo.corresponding_angles` now states both pairs of equal angles; cite it for either one
  (`geo.corresponding_angles_2` is removed). Written-proof steps are named by position among
  all steps (`step2` is printed step 2), not among claims only.
- The default time limit per Lean run is 900 s (was 300 s): a cold load of larger Mathlib
  modules (e.g. trigonometry) can exceed 300 s on a slow or memory-starved machine. The
  timeout diagnostic now says how to raise the limit.

### Security
- Raw tactic text nested inside structured proof steps is gated like top-level raw text.
- Lean type text is validated so it cannot escape its binder or add commands.
- A definition that fails to elaborate rejects every theorem in its Lean file.
