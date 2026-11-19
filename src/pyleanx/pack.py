"""Writing a domain pack: one object for everything a pack contributes to the core.

    import pyleanx as pl

    topo = pl.domain_pack("topology", sorts={"TopSpace"}, symbols=("TopologicalSpace.",))
    topo.facts("mypkg.topology", prefix="top", title="Topology")   # LEMMAS citable by name
    topo.rule("step", 55, lambda s: [f"(simp only [interior_interior] at *; exact{s.h})"],
              name="interior idempotent")                          # justification rule
    topo.sampler("TopSpace", lambda rng: ...)                      # numeric sanity check
    topo.hint(r"failed to synthesize TopologicalSpace", "say which topology the set carries")

A pack's justification rules apply only to theorems whose sorts or Lean symbols belong to
the pack (``sorts``, ``symbols``). The geometry pack (``pyleanx.geometry``) is written
this way. Nothing a pack registers is trusted: Lean checks every proof it helps produce.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class DomainPack:
    """Registration of one domain pack (see :func:`domain_pack`)."""

    name: str

    # --- justification (pyleanx.justify) -------------------------------------------
    def rule(self, slot: str, priority: float, make: Any, *, name: str) -> None:
        """A justification rule: ``slot`` is "step", "close" or "cheap_close"; ``make`` is
        fixed tactic text, a list of them, or a function of the step (``justify.Step``)."""
        from .justify import add_rule

        add_rule(slot, priority, make, pack=self.name, name=name)

    # --- citable facts (pyleanx.fact_search) ----------------------------------------
    def facts(self, module: str, *, prefix: str, title: str = "") -> None:
        """Make the ``LEMMAS`` of ``module`` citable and searchable (``pl.search_facts``)."""
        from .fact_search import register_domain

        register_domain(module, prefix=prefix, title=title or self.name)

    # --- numeric sanity check (pyleanx.numeric) ---------------------------------------
    def function(self, lean_name: str, fn: Any) -> None:
        """Evaluate the function ``lean_name`` on sampled values."""
        from .numeric import register_function

        register_function(lean_name, fn)

    def apply(self, head: str, handler: Any) -> None:
        """Evaluate ``head args…`` with ``handler(args, env)`` (``NotImplemented`` to decline)."""
        from .numeric import register_apply

        register_apply(head, handler)

    def sampler(self, sort_name: str, sampler: Any) -> None:
        """Draw random values of a sort with ``sampler(rng)``."""
        from .numeric import register_sampler

        register_sampler(sort_name, sampler)

    def bigop(self, kind: str, handler: Any) -> None:
        """Evaluate big operators of ``kind`` (e.g. "integral") with ``handler(e, env)``."""
        from .numeric import register_bigop

        register_bigop(kind, handler)

    def construction(self, hook: Any) -> None:
        """Place values the hypotheses determine (see ``numeric.register_construction``)."""
        from .numeric import register_construction

        register_construction(hook, name=self.name)

    # --- explanations (pyleanx.diagnose) ---------------------------------------------
    def hint(self, pattern: str, text: str) -> None:
        """Explain Lean messages matching ``pattern`` with ``text``."""
        from .diagnose import register_hint

        register_hint(pattern, text)


def domain_pack(name: str, *, sorts: Iterable[str] = (), symbols: Iterable[str] = (),
                imports: Iterable[str] = ()) -> DomainPack:
    """Declare a domain pack; its rules apply to theorems using ``sorts`` (sort names) or a
    Lean symbol starting with one of ``symbols``, and ``imports`` (the Lean modules its
    rules need) are imported for them. Declaring it again replaces the declaration (its
    registered rules stay)."""
    from .justify import register_pack

    register_pack(name, sorts=sorts, symbols=symbols, imports=imports)
    return DomainPack(name)


__all__ = ["DomainPack", "domain_pack"]
