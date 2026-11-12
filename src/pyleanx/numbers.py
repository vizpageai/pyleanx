"""Elementary number theory: divisibility, parity, primes, factorials (Mathlib's notions).

    import pyleanx as pl
    from pyleanx import numbers as nt

    n = pl.symbol("n", pl.Nat)
    nt.even(n * (n + 1))          # n(n + 1) is even
    nt.divides(3, n**3 - n)       # 3 ∣ n³ − n   (``Dvd.dvd``)
    nt.prime(p), nt.factorial(n)  # p is prime, n!

Abstractions and limitations
----------------------------
* ``even``/``odd``/``divides`` work for ℕ and ℤ (Lean picks the instance from the
  argument); ``prime`` and ``factorial`` are about natural numbers (``Nat.Prime``,
  ``Nat.factorial``). Natural-number subtraction truncates at 0, as in Mathlib.
* Mathlib's ``Even n`` means ``∃ r, n = r + r``; ``Odd n`` means ``∃ m, n = 2 * m + 1``.
  Cite :data:`even_iff_two_mul` to work with ``n = 2 * k``.
* ``LEMMAS`` reference declarations at :data:`VERIFIED_MATHLIB`; Lean checks every use.
"""

from __future__ import annotations

from typing import Any

from ._domain import CATALOG_VERSION, VERIFIED_MATHLIB, collect_lemmas, lemma
from .expr import Expr
from .types import UNKNOWN, Fn, Nat, Prop

_PARITY = "Mathlib.Algebra.Group.Nat.Even"
_INT_PARITY = "Mathlib.Algebra.Group.Int.Even"
_RING_PARITY = "Mathlib.Algebra.Ring.Parity"
_DVD = "Mathlib.Algebra.Group.Basic"
_NAT_DVD = "Mathlib.Algebra.Order.Group.Nat"
_PRIME = "Mathlib.Data.Nat.Prime.Basic"
_PRIME_DEFS = "Mathlib.Data.Nat.Prime.Defs"
_FACT = "Mathlib.Data.Nat.Factorial.Basic"
_GCD = "Mathlib.Data.Nat.GCD.Basic"


def _c(name: str, imports: tuple[str, ...], latex: str, sort: Any = UNKNOWN) -> Any:
    from .terms import const

    return const(name, sort, imports=imports, latex=latex)


def divides(a: object, b: object) -> Expr:
    """``a ∣ b``: ``a`` divides ``b`` (``Dvd.dvd a b``)."""
    from .terms import apply

    return apply(_c("Dvd.dvd", (_DVD,), r"{0} \mid {1}"), a, b)


def even(n: object) -> Expr:
    """``n`` is even (Mathlib's ``Even n``)."""
    from .terms import apply

    return apply(_c("Even", (_PARITY, _INT_PARITY), r"{0} \text{{ is even}}"), n)


def odd(n: object) -> Expr:
    """``n`` is odd (Mathlib's ``Odd n``: ``∃ m, n = 2 * m + 1``)."""
    from .terms import apply

    return apply(_c("Odd", (_RING_PARITY,), r"{0} \text{{ is odd}}"), n)


def prime(p: object) -> Expr:
    """``p`` is a prime number (``Nat.Prime p``)."""
    from .terms import apply

    return apply(_c("Nat.Prime", (_PRIME_DEFS,), r"{0} \text{{ is prime}}",
                    Fn(Nat, Prop)), p)


def factorial(n: object) -> Expr:
    """``n!`` (``Nat.factorial n``)."""
    from .terms import Lam, apply

    paren = not hasattr(n, "name") or isinstance(n, Lam)
    tex = r"\left({0}\right)!" if paren and not isinstance(n, int) else "{0}!"
    return apply(_c("Nat.factorial", (_FACT,), tex, Fn(Nat, Nat)), n)


def gcd(a: object, b: object) -> Expr:
    """``gcd(a, b)`` of natural numbers (``Nat.gcd a b``)."""
    from .terms import apply

    return apply(_c("Nat.gcd", (_GCD,), r"\gcd({0}, {1})", Fn(Nat, Nat, Nat)), a, b)


# --- parity
even_or_odd = lemma("Nat.even_or_odd", _RING_PARITY,
                    label="every natural number is even or odd")
int_even_or_odd = lemma("Int.even_or_odd", "Mathlib.Algebra.Ring.Int.Parity",
                        label="every integer is even or odd")
even_iff_two_mul = lemma("even_iff_exists_two_mul", _RING_PARITY,
                         label="n is even iff n = 2k for some k")
even_iff_two_dvd = lemma("even_iff_two_dvd", _RING_PARITY, label="n is even iff 2 ∣ n")
# --- divisibility
dvd_refl = lemma("dvd_refl", _DVD, label="a ∣ a")
dvd_trans = lemma("dvd_trans", _DVD, label="divisibility is transitive")
dvd_mul_right = lemma("dvd_mul_right", _DVD, label="a ∣ ab")
dvd_mul_left = lemma("dvd_mul_left", _DVD, label="a ∣ ba")
dvd_add = lemma("dvd_add", _DVD, label="d ∣ a and d ∣ b give d ∣ a + b")
#: ``k ∣ m → (k ∣ m + n ↔ k ∣ n)``.
dvd_add_right = lemma("Nat.dvd_add_right", _NAT_DVD,
                      label="if d ∣ a, then d ∣ a + b exactly when d ∣ b")
# --- primes and factorials
exists_prime_dvd = lemma("Nat.exists_prime_and_dvd", _PRIME,
                         label="every n ≠ 1 has a prime factor")
prime_two_le = lemma("Nat.Prime.two_le", _PRIME_DEFS, label="a prime is at least 2")
prime_pos = lemma("Nat.Prime.pos", _PRIME_DEFS, label="a prime is positive")
prime_not_dvd_one = lemma("Nat.Prime.not_dvd_one", _PRIME_DEFS,
                          label="a prime does not divide 1")
prime_dvd_mul = lemma("Nat.Prime.dvd_mul", _PRIME,
                      label="Euclid's lemma: p ∣ ab iff p ∣ a or p ∣ b")
factorial_pos = lemma("Nat.factorial_pos", _FACT, label="n! > 0")
dvd_factorial = lemma("Nat.dvd_factorial", _FACT, label="m ∣ n! for 0 < m ≤ n")

LEMMAS = collect_lemmas(globals())

__all__ = ["divides", "even", "odd", "prime", "factorial", "gcd", "LEMMAS",
           "VERIFIED_MATHLIB", "CATALOG_VERSION", *LEMMAS]
