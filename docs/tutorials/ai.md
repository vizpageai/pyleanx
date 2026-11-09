# Proof agents (for AI and ML researchers)

PyLeanX gives learning systems a sound oracle: models propose, Lean disposes. This page
covers the environment, search, batch checking and the benchmark. Code blocks run in order
(sessions need `pip install "pyleanx[interactive]"`).

## Soundness first

However a proof was found (by a model, by search, or typed by hand), `verified` comes only
from a fresh batch Lean run plus the `#print axioms` audit. The integration tests include
"lying" agents that close goals with `sorry` or `native_decide`; the REPL accepts their
steps and the final audit rejects them.

## A gym-like environment

```python
import pyleanx as pl
from pyleanx import agent

x = pl.symbol("x", pl.Real)
env = agent.ProofEnv(pl.Theorem("sq_plus_one_pos", [x], conclusion=pl.Lt(0, x**2 + 1)))

obs = env.observe()                    # {"goals": [...], "steps": 0, ...}
print(obs["goals"])
out = env.act("positivity")            # tactic text, a pl tactic, or canonical JSON
print(out["ok"], out["goals"])
result = env.verify()                  # batch Lean + audit (None if goals remain)
print(result.summary())
assert result is not None and result.verified
```

Tactic text is parsed into PyLeanX's typed tactics where possible. Anything else is raw
text, which is refused unless the environment is created with `allow_raw=True` (then
screened and audited). `env.transcript_jsonl()` returns the whole episode as JSON lines.

## Tool calling

`agent.TOOLS` are JSON schemas (`get_state`, `apply_tactic`, `undo`, `verify`) in the format
LLM tool-calling APIs accept. Route the model's calls to `env.call_tool`:

```python
print([t["name"] for t in agent.TOOLS])
print(env.call_tool("get_state", {}))
pl.shutdown_sessions()
```

## Search with a proposer

A proposer is any callable from an observation to candidate tactics; an LLM wrapped in a
function is a proposer. `search_proof` runs a depth-first search with backtracking and a
budget:

```python
a, b = pl.symbols("a b", pl.Real)
thm = pl.Theorem("am_gm_two", [a, b], conclusion=2*a*b <= a**2 + b**2)

def my_model(obs):                     # replace with a call to your model
    return ["linarith", "nlinarith [sq_nonneg (a - b)]"]

attempt = agent.search_proof(thm, agent.ChainProposer(my_model, agent.AutomationProposer()),
                             allow_raw=True)
print(attempt.status, attempt.script)
assert attempt.verified
pl.shutdown_sessions()
```

`agent.RetrievalProposer(bank)` proposes lemmas from a [theorem bank](mathlib.md).

## Batch checking without a REPL

To score many complete candidate proofs (e.g. samples from a model), check them in one Lean
process:

```python
candidates = [pl.ring(), pl.positivity(), pl.nlinarith(pl.ref("sq_nonneg")(a - b))]
best = agent.try_proofs(thm, candidates)
print(best.status, best.script)
assert best.verified
```

`pl.verify_all` does the same for many different theorems; every result has its own
status, diagnostics and audit, and `to_json()` gives a stable schema for datasets.

## Benchmark

```bash
pyleanx agent bench                  # 13 problems, session search with the baseline proposer
pyleanx agent bench --mode batch     # REPL-free baseline
pyleanx agent export -o basic.jsonl  # statements only, for your own harness
```

The automation-only baseline verifies 9 of 13. The four it misses need a witness (`use`),
a structural step (`constructor`), a hinted `nlinarith`, or a named lemma: the gap a
model or retrieval should close. `agent.run_benchmark(proposer=...)` scores your proposer.

## Agents in other languages

`pyleanx agent serve` speaks JSON lines over stdio (`open`, `tools`, `call`, `transcript`,
`close`). A client cannot enable raw tactics; the operator decides with `--allow-raw`.
It runs Lean on client-supplied statements: use it only with trusted clients and never
expose it to a network (see [Trust model](../security.md)).
