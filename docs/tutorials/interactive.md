# Interactive proving

Writing a whole proof blind is hard. A *session* keeps Lean running and shows you the goals
after each tactic, like the goal view in a Lean editor. Requires
`pip install "pyleanx[interactive]"`. All code on this page runs in order.

```python
import pyleanx as pl

a, x = pl.symbols("a x", pl.Real)
thm = pl.Theorem("scaled_square_pos", [a, x],
                 assumptions={"ha": a > 0},
                 conclusion=a * x**2 + a > 0)

s = thm.session()        # Lean loads Mathlib once (seconds to a minute)
print(s.goals)
```

```text
a x : ℝ
ha : 0 < a
⊢ 0 < a * x ^ 2 + a
```

## Trying tactics

`apply` runs a tactic and records it if it succeeds. A failed tactic leaves the state
unchanged and tells you why:

```python
step = s.apply(pl.linarith())
print(step.ok, step.error.splitlines()[0] if step.error else "")
```

`linarith` only does *linear* arithmetic, and `a * x²` is not linear. `peek` tries a tactic
without recording it:

```python
print(s.peek(pl.positivity()).goals)        # () : would close the goal
```

```python
s.apply(pl.positivity())
assert s.is_complete
print([str(t) for t in s.history])          # ['positivity']
```

`s.undo()` steps back; `s.reset()` starts over.

## Verifying

The REPL saying "no goals" is a convenience, not a verdict. `verify()` turns the recorded
tactics into a proof and runs the normal batch check with the axiom audit:

```python
result = s.verify()
print(result.summary())
assert result.verified
pl.shutdown_sessions()                       # stop the background Lean process
```

## Multi-step proofs

```python
P, Q = pl.prop_symbol("P"), pl.prop_symbol("Q")
comm = pl.Theorem("and_swap", [P, Q], conclusion=pl.Implies(pl.And(P, Q), pl.And(Q, P)))
s = comm.session()
s.apply(pl.intro("h"))
s.apply(pl.constructor())
print(len(s.goals), "goals")                 # 2 goals: Q and P
s.apply(pl.exact(pl.ref("h.right")))
s.apply(pl.exact(pl.ref("h.left")))
assert s.verify().verified
pl.shutdown_sessions()
```

## In Jupyter

Sessions, goals and step results render as formatted output: goal states as Lean blocks,
failed steps with ❌ and Lean's message. Theorems render as typeset statements with the
Lean source in a collapsible block.

## How sessions relate to verification

- Sessions share one Lean REPL per project (much faster after the first statement).
- Imports needed by later tactics are added automatically.
- On managed Windows machines where the REPL binary is blocked, PyLeanX runs it through
  `lean --run` instead (slower start, same results).
- `verify()` always runs a fresh batch Lean process; the REPL's opinion is never evidence.
