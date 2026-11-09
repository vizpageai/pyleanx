"""Proof-agent API (M8): let programs and AI models propose proofs that Lean checks.

    from pyleanx import agent
    env = agent.ProofEnv(thm)                      # observe / act / undo / verify
    attempt = agent.search_proof(thm)              # baseline automation search
    report = agent.run_benchmark(mode="session")   # score a proposer on agent.basic()

Invariant: no suggestion, REPL state or search result ever becomes ``verified``
without the batch backend's fresh Lean run and ``#print axioms`` audit.
"""

from .benchmark import BenchmarkReport, Problem, basic, export_jsonl, run_benchmark
from .env import TOOLS, ProofEnv
from .llm import LLMProposer, parse_tactics
from .parse import TacticParser, tactic_from_text
from .search import (
    CLOSERS,
    AutomationProposer,
    ChainProposer,
    ProofAttempt,
    Proposer,
    RetrievalProposer,
    search_proof,
    try_proofs,
)

__all__ = [
    "ProofEnv", "TOOLS", "TacticParser", "tactic_from_text", "Proposer",
    "AutomationProposer", "RetrievalProposer", "ChainProposer", "CLOSERS", "ProofAttempt",
    "search_proof", "try_proofs", "Problem", "basic", "export_jsonl", "run_benchmark",
    "BenchmarkReport", "LLMProposer", "parse_tactics",
]
