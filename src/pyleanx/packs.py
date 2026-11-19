"""The domain packs that ship with PyLeanX.

A domain pack is built on the core (docs/core.md): it declares vocabulary, citable facts
(its ``LEMMAS``), justification rules and numeric constructions. The core knows none of
them by name; this module registers the built-in ones. A third-party pack registers itself
the same way::

    from pyleanx.fact_search import register_domain
    register_domain("mypkg.topology", prefix="top", title="Topology")
"""

from __future__ import annotations

from .fact_search import register_domain

#: (module, prefix used when printing a fact, title), in the order facts are listed
BUILTIN = (
    ("pyleanx.geometry", "geo", "Plane geometry"),
    ("pyleanx.realvar", "rv", "Real-variable methods"),
    ("pyleanx.analysis", "an", "Real analysis"),
    ("pyleanx.algebra", "alg", "Algebra"),
    ("pyleanx.numbers", "nt", "Number theory"),
    ("pyleanx.complex_analysis", "ca", "Complex analysis"),
    ("pyleanx.harmonic", "ha", "Harmonic analysis"),
    ("pyleanx.hilbert", "hil", "The Hilbert transform"),
)

for _module, _prefix, _title in BUILTIN:
    register_domain(_module, prefix=_prefix, title=_title)

#: entry-point group through which installed domain packages announce themselves
PLUGIN_GROUP = "pyleanx.packs"
_LOADED: dict[str, str] = {}   # entry-point name -> module, or the error that stopped it


def load_plugins() -> dict[str, str]:
    """Import every installed domain package (entry points in the ``pyleanx.packs``
    group); importing a package registers its pack. Returns name -> module (or the error).

    A domain package declares, in its ``pyproject.toml``::

        [project.entry-points."pyleanx.packs"]
        topology = "mypkg_topology"
    """
    import importlib
    from importlib.metadata import entry_points

    for ep in entry_points(group=PLUGIN_GROUP):
        if ep.name in _LOADED:
            continue
        try:
            importlib.import_module(ep.value.split(":")[0])
            _LOADED[ep.name] = ep.value
        except Exception as exc:  # noqa: BLE001 - a broken plugin must not break the core
            _LOADED[ep.name] = f"failed to load: {type(exc).__name__}: {exc}"
    return dict(_LOADED)
