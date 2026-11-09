"""Proof agents: baseline search, a custom proposer, and the LLM tool interface.

Run: python examples/agent_search.py   (needs pip install -e ".[interactive]")
"""

import json

import pyleanx as pl
from pyleanx import agent

a, b = pl.symbols("a b", pl.Real)
thm = pl.Theorem("am_gm_two", [a, b], conclusion=2 * a * b <= a**2 + b**2)


# 1. Any callable `observation -> candidate tactics` is a proposer. An LLM is one too:
#    send obs["goals"] to the model and return its suggested tactic strings.
def my_proposer(obs):
    return ["linarith", "positivity", "nlinarith [sq_nonneg (a - b)]"]


attempt = agent.search_proof(thm, agent.ChainProposer(my_proposer, agent.AutomationProposer()),
                             allow_raw=True)  # free-form text: screened, then audited
print(attempt.status, attempt.script)
print(attempt.result.summary() if attempt.result else "no complete script found")

# 2. Tool-calling models: give them agent.TOOLS and route their calls to env.call_tool.
print("\ntools offered to a model:", [t["name"] for t in agent.TOOLS])
x = pl.symbol("x", pl.Real)
env = agent.ProofEnv(pl.Theorem("sq_plus_one_pos", [x], conclusion=pl.Lt(0, x**2 + 1)))
for name, args in [("get_state", {}), ("apply_tactic", {"tactic": "positivity"}),
                   ("verify", {})]:
    print(name, "->", json.dumps(env.call_tool(name, args), ensure_ascii=False)[:160])

pl.shutdown_sessions()
raise SystemExit(0 if attempt.verified else 1)
