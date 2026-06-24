#!/usr/bin/env python3
"""
Computational exploration for Erdos problem 828:

    for each integer a, are there infinitely many n with phi(n) | (n + a) ?

The goal here is modest:
- search all n up to a bound for a few small a values
- print the arithmetic data that suggests candidate infinite families

For the user-requested cases:
- a = -1 has the obvious infinite family n = p (primes), since phi(p) = p - 1
- a = 1 is experimentally matched by products of initial Fermat primes
- a = 2 is experimentally matched by twice those products, and by one short
  Euclid-style chain n = 2m with 2(m+1) = 3 phi(m)
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass


@dataclass(frozen=True)
class Hit:
    a: int
    n: int
    phi: int
    quotient: int
    factors: tuple[tuple[int, int], ...]


def phi_and_spf_sieve(limit: int) -> tuple[list[int], list[int]]:
    """
    Build phi and smallest-prime-factor tables together.

    WHY: problem 828 is about divisibility by phi(n), so a totient sieve gives
    the whole search range in near-linear time, and SPF makes factor display
    cheap without separate trial division.
    """
    phi = list(range(limit + 1))
    spf = list(range(limit + 1))
    if limit >= 1:
        spf[1] = 1

    for p in range(2, limit + 1):
        if phi[p] != p:
            continue
        spf[p] = p
        for multiple in range(p, limit + 1, p):
            phi[multiple] -= phi[multiple] // p
            if spf[multiple] == multiple:
                spf[multiple] = p

    return phi, spf


def factor_with_spf(n: int, spf: list[int]) -> tuple[tuple[int, int], ...]:
    if n <= 1:
        return ()

    out: list[tuple[int, int]] = []
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, e))
    return tuple(out)


def search_hits(limit: int, a_values: list[int], max_hits: int | None) -> list[Hit]:
    phi, spf = phi_and_spf_sieve(limit)
    hits: list[Hit] = []

    for a in a_values:
        found = 0
        for n in range(1, limit + 1):
            ph = phi[n]
            if (n + a) % ph != 0:
                continue
            hits.append(
                Hit(
                    a=a,
                    n=n,
                    phi=ph,
                    quotient=(n + a) // ph,
                    factors=factor_with_spf(n, spf),
                )
            )
            found += 1
            if max_hits is not None and found >= max_hits:
                break

    return hits


def format_factors(factors: tuple[tuple[int, int], ...]) -> str:
    if not factors:
        return "1"
    pieces = []
    for p, e in factors:
        pieces.append(str(p) if e == 1 else f"{p}^{e}")
    return " * ".join(pieces)


def is_prime_64(n: int) -> bool:
    """
    Deterministic Miller-Rabin for 64-bit integers.

    WHY: the experimental families grow past sieve bounds very quickly, so a
    lightweight primality check keeps the family generator standalone.
    """
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
    for p in small_primes:
        if n % p == 0:
            return n == p

    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1

    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def fermat_prime_prefix_family() -> list[dict[str, int | str]]:
    """
    Known explicit examples coming from the known Fermat primes.

    If F_i = 2^(2^i) + 1 is prime for i < k, then
      n = product_{i<k} F_i = F_k - 2
    satisfies n + 1 = 2 phi(n), and 2n satisfies 2n + 2 = 4 phi(2n).
    """
    known_fermat_primes = [3, 5, 17, 257, 65537]
    rows: list[dict[str, int | str]] = []

    running = 1
    running_phi = 1
    for idx, fp in enumerate(known_fermat_primes, start=1):
        running *= fp
        running_phi *= fp - 1
        rows.append(
            {
                "k": idx,
                "family": "a=1 Fermat-prefix",
                "n": running,
                "phi": running_phi,
                "quotient": (running + 1) // running_phi,
                "note": "n+1 = 2 phi(n)",
            }
        )
        rows.append(
            {
                "k": idx,
                "family": "a=2 doubled Fermat-prefix",
                "n": 2 * running,
                "phi": running_phi,
                "quotient": (2 * running + 2) // running_phi,
                "note": "n+2 = 4 phi(n)",
            }
        )

    return rows


def plus_two_chain(max_terms: int) -> list[dict[str, int | str]]:
    """
    Build the Euclid-style chain
      m_{k+1} = m_k (m_k + 2)
    whenever m_k + 2 is prime.

    If 2(m+1) = 3 phi(m) and m+2 is prime, then for m' = m(m+2),
      2(m'+1) = 3 phi(m').
    Therefore n = 2m gives n + 2 = 3 phi(n).
    """
    rows: list[dict[str, int | str]] = []
    m = 5

    for idx in range(1, max_terms + 1):
        rows.append(
            {
                "k": idx,
                "family": "a=2 plus-two chain",
                "n": 2 * m,
                "phi": 2 * (m + 1) // 3,
                "quotient": 3,
                "note": f"next prime check: m+2 = {m + 2}",
            }
        )
        if not is_prime_64(m + 2):
            break
        m *= m + 2

    return rows


def print_search(limit: int, a_values: list[int], max_hits: int | None) -> None:
    hits = search_hits(limit=limit, a_values=a_values, max_hits=max_hits)

    current_a: int | None = None
    for hit in hits:
        if hit.a != current_a:
            current_a = hit.a
            print(f"a = {current_a}")
        print(
            f"  n={hit.n:<10d} phi={hit.phi:<10d} "
            f"q={(hit.quotient):<4d} factors={format_factors(hit.factors)}"
        )


def print_families(terms: int) -> None:
    print("Explicit infinite family for a = -1")
    print("  n = p prime, with phi(p) = p - 1, so phi(n) | (n - 1).")
    print()

    print("Fermat-prime prefix data")
    for row in fermat_prime_prefix_family()[: 2 * terms]:
        print(
            f"  k={row['k']}: {row['family']}: n={row['n']} "
            f"phi={row['phi']} q={row['quotient']}  ({row['note']})"
        )
    print()

    print("Euclid-style plus-two chain for a = 2")
    for row in plus_two_chain(max_terms=terms):
        print(
            f"  k={row['k']}: n={row['n']} phi={row['phi']} "
            f"q={row['quotient']}  ({row['note']})"
        )
    print("  This chain stops as soon as m+2 is composite.")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    p_search = subparsers.add_parser("search", help="search n <= limit")
    p_search.add_argument("--limit", type=int, default=200_000)
    p_search.add_argument("--a", type=int, nargs="+", default=[-1, 1, 2])
    p_search.add_argument(
        "--max-hits",
        type=int,
        default=25,
        help="cap hits per a-value; use 0 to print all hits",
    )

    p_families = subparsers.add_parser("families", help="print candidate families")
    p_families.add_argument("--terms", type=int, default=5)

    args = parser.parse_args()

    if args.command == "search":
        max_hits = None if args.max_hits == 0 else args.max_hits
        print_search(limit=args.limit, a_values=args.a, max_hits=max_hits)
        return

    if args.command == "families":
        print_families(terms=args.terms)
        return

    raise AssertionError("unreachable")


if __name__ == "__main__":
    main()
