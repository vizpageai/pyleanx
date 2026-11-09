"""Model-agnostic language-model proposer.

PyLeanX bundles no model client. Pass any function that maps a prompt string to the
model's text reply (an API call, a local model, a cached transcript):

    def complete(prompt: str) -> str:
        return my_client.generate(prompt)          # your code

    proposer = agent.LLMProposer(complete, hints=lambda goal: pl.lib.search("norm"))
    attempt = agent.search_proof(thm, agent.ChainProposer(proposer, agent.AutomationProposer()),
                                 allow_raw=True)

Whatever the model says is only a *candidate*: tactic text is parsed into PyLeanX's typed
tactics where possible (anything else is untrusted raw text, gated by ``allow_raw``) and
every finished script is verified by the batch Lean run and the axiom audit.
"""

from __future__ import annotations

import re
from collections.abc import Callable, Iterable
from typing import Any

PROMPT = """You are proving a theorem in Lean 4 with Mathlib.
Propose up to {k} different next tactics for the FIRST goal below.
Reply with one tactic per line, inside a single ```lean code block, and nothing else.
Do not use sorry, admit, native_decide or set_option.

Goals:
{goals}
{hints}{history}"""

_FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide|set_option|axiom)\b")


def parse_tactics(reply: str, k: int = 8) -> list[str]:
    """Tactic candidates from a model reply (code block lines, de-duplicated)."""
    blocks = re.findall(r"```(?:lean4?|)\s*\n(.*?)```", reply, re.S)
    text = "\n".join(blocks) if blocks else reply
    out: list[str] = []
    for line in text.splitlines():
        line = re.sub(r"^\s*(?:[-*•]|\d+[.)])\s+", "", line).strip().rstrip(";")
        if not line or line.startswith(("--", "#", "/-")) or _FORBIDDEN.search(line):
            continue
        if line not in out:
            out.append(line)
        if len(out) >= k:
            break
    return out


class LLMProposer:
    """Ask a language model for next-step tactics.

    ``complete(prompt) -> reply`` is supplied by you. ``hints(goal) -> iterable`` may return
    lemma names or :class:`~pyleanx.bindings.Decl` objects to include in the prompt.
    """

    def __init__(self, complete: Callable[[str], str], *, k: int = 6,
                 hints: Callable[[str], Iterable[Any]] | None = None,
                 template: str = PROMPT) -> None:
        self.complete = complete
        self.k = k
        self.hints = hints
        self.template = template
        self.calls = 0

    def prompt(self, obs: dict[str, Any]) -> str:
        goals = "\n\n".join(obs.get("goals") or [])
        hint_text = ""
        if self.hints is not None and obs.get("goals"):
            lines = []
            for h in list(self.hints(obs["goals"][0]))[:12]:
                sig = h.signature() if hasattr(h, "signature") else str(h)
                lines.append(f"- {sig[:200]}")
            if lines:
                hint_text = "\nPossibly useful lemmas:\n" + "\n".join(lines) + "\n"
        hist = obs.get("history") or []
        history = ("\nTactics applied so far:\n" + "\n".join(hist) + "\n") if hist else ""
        return self.template.format(k=self.k, goals=goals, hints=hint_text, history=history)

    def __call__(self, obs: dict[str, Any]) -> list[str]:
        if not obs.get("goals"):
            return []
        self.calls += 1
        try:
            reply = self.complete(self.prompt(obs))
        except Exception:  # noqa: BLE001 - a failing model must not crash the search
            return []
        return parse_tactics(reply or "", self.k)
