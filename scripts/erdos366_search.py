#!/usr/bin/env python3
"""
Erdos 366: search for n such that n is 2-full and n+1 is 3-full.

The practical approach is to enumerate 3-full numbers m = n+1, because they
are much sparser than 2-full numbers. For each candidate m we test whether
m-1 is 2-full.

The script also reports the purely local congruence obstruction. That local
analysis is useful because it shows a limitation up front: residue conditions
checked prime-by-prime cannot settle the problem by themselves, since every
finite prime set leaves CRT survivors.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import reduce
from math import gcd, isqrt
from time import perf_counter


def sieve_primes(limit: int) -> list[int]:
    """Return all primes <= limit."""
    if limit < 2:
        return []

    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
    return [n for n, is_prime in enumerate(sieve) if is_prime]


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def is_square(n: int) -> bool:
    root = isqrt(n)
    return root * root == n


def is_two_full(n: int, primes: list[int]) -> bool:
    """
    Decide whether n is 2-full.

    Trial division is enough here because we only exact-test the much smaller
    candidate set coming from the 3-full enumeration.
    """
    if n < 1:
        return False
    if n == 1:
        return True
    if is_square(n):
        return True

    remaining = n
    for p in primes:
        if p * p > remaining:
            break
        if remaining % p != 0:
            continue

        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1

        if exponent < 2:
            return False

        # After stripping some prime powers, many survivors collapse to a
        # square. Any perfect square is automatically 2-full, so we can stop.
        if remaining == 1 or is_square(remaining):
            return True

    return remaining == 1


def local_ok_for_prime(n: int, p: int) -> bool:
    """Check the p-adic necessary condition for n (2-full) and n+1 (3-full)."""
    if n % p == 0 and n % (p * p) != 0:
        return False
    n1 = n + 1
    if n1 % p == 0 and n1 % (p * p * p) != 0:
        return False
    return True


def local_ok(n: int, primes: list[int]) -> bool:
    return all(local_ok_for_prime(n, p) for p in primes)


def local_survivor_count_for_prime(p: int) -> int:
    """
    Number of residues r mod p^3 satisfying:
      - if p | r then p^2 | r
      - if p | r+1 then p^3 | r+1

    This equals (p-2)p^2 + p + 1 = p^3 - 2p^2 + p + 1:
      - p-2 residue classes mod p are free of both 0 and -1, contributing p^2
        lifts each;
      - p residues are multiples of p^2;
      - one residue is r == -1 mod p^3.
    """
    return p * p * p - 2 * p * p + p + 1


def enumerate_local_survivors(primes: list[int], max_modulus: int) -> tuple[int, list[int]] | None:
    """
    Enumerate the exact surviving residue classes when the combined modulus is
    still small enough to inspect directly.
    """
    modulus = reduce(lcm, (p**3 for p in primes), 1)
    if modulus > max_modulus:
        return None

    survivors = [r for r in range(modulus) if local_ok(r, primes)]
    return modulus, survivors


def generate_three_full(limit: int, primes: list[int]):
    """
    Yield all 3-full numbers in increasing-prime recursion order.

    Each prime is chosen once, with exponent >= 3. Recursing only to larger
    primes gives a unique generation path for every 3-full integer.
    """

    def dfs(start: int, current: int):
        for index in range(start, len(primes)):
            p = primes[index]
            value = current * (p**3)
            if value > limit:
                break

            while value <= limit:
                yield value
                yield from dfs(index + 1, value)
                value *= p

    yield from dfs(0, 1)


@dataclass
class SearchStats:
    limit: int
    total_three_full: int = 0
    local_pass: int = 0
    exact_pass: int = 0
    elapsed_seconds: float = 0.0
    hits: list[int] | None = None


def search(limit: int, local_primes: list[int]) -> SearchStats:
    """
    Search all n <= limit with n+1 3-full by enumerating m = n+1 first.
    """
    if limit < 1:
        raise ValueError("limit must be >= 1")

    t0 = perf_counter()
    search_ceiling = limit + 1
    factor_primes = sieve_primes(isqrt(limit) + 1)
    cube_root = round(search_ceiling ** (1 / 3))
    while (cube_root + 1) ** 3 <= search_ceiling:
        cube_root += 1
    while cube_root**3 > search_ceiling:
        cube_root -= 1
    generation_primes = sieve_primes(cube_root + 1)

    hits: list[int] = []
    total_three_full = 0
    local_pass = 0

    for candidate in generate_three_full(search_ceiling, generation_primes):
        total_three_full += 1
        n = candidate - 1
        if not local_ok(n, local_primes):
            continue

        local_pass += 1
        if is_two_full(n, factor_primes):
            hits.append(n)

    return SearchStats(
        limit=limit,
        total_three_full=total_three_full,
        local_pass=local_pass,
        exact_pass=len(hits),
        elapsed_seconds=perf_counter() - t0,
        hits=hits,
    )


def parse_primes(raw: str) -> list[int]:
    return [int(piece) for piece in raw.split(",") if piece.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--limit",
        type=int,
        default=10**12,
        help="search for solutions n <= limit (default: 10^12)",
    )
    parser.add_argument(
        "--local-primes",
        type=str,
        default="2,3,5,7,11,13",
        help="small primes used for the cheap local prefilter",
    )
    parser.add_argument(
        "--enumerate-local-up-to",
        type=int,
        default=10**6,
        help="enumerate exact local survivors only when the modulus is at most this",
    )
    args = parser.parse_args()

    local_primes = parse_primes(args.local_primes)
    local_modulus = reduce(lcm, (p**3 for p in local_primes), 1)
    local_count = 1
    for p in local_primes:
        local_count *= local_survivor_count_for_prime(p)

    print("Erdos 366: n 2-full and n+1 3-full")
    print(f"Search bound: n <= {args.limit}")
    print(f"Local prefilter primes: {local_primes}")
    print()

    print("Local obstruction analysis")
    for p in local_primes:
        count = local_survivor_count_for_prime(p)
        print(f"  p={p:2d}: {count} survivors mod {p**3} out of {p**3}")
    print(
        "  combined: "
        f"{local_count} survivors mod {local_modulus} "
        f"({local_count / local_modulus:.6%} of all residues)"
    )
    print(
        "  consequence: every finite prime-by-prime local filter still leaves "
        "CRT survivors, so pure residue checks cannot prove nonexistence."
    )
    print()

    enumerated = enumerate_local_survivors(local_primes, args.enumerate_local_up_to)
    if enumerated is None:
        print(
            "Skipping exact local survivor enumeration because the modulus "
            f"{local_modulus} exceeds {args.enumerate_local_up_to}."
        )
    else:
        modulus, survivors = enumerated
        print(f"Exact local survivors mod {modulus}: {len(survivors)}")
        print(f"First survivors: {survivors[:40]}")
    print()

    stats = search(args.limit, local_primes)
    print("Search")
    print(f"  3-full candidates checked: {stats.total_three_full}")
    print(f"  passed local prefilter:   {stats.local_pass}")
    print(f"  exact solutions found:    {stats.exact_pass}")
    print(f"  elapsed:                  {stats.elapsed_seconds:.3f}s")
    if stats.hits:
        print(f"  hits: {stats.hits}")
    else:
        print("  hits: none")


if __name__ == "__main__":
    main()
