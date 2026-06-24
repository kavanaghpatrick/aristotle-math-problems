"""
Verify Erdos Problem 985 for odd primes up to a given bound.

For each odd prime p we search for the smallest prime q < p that is a
primitive root modulo p. The standard criterion is:

  q is a primitive root mod p
  iff q^((p-1)/r) != 1 (mod p) for every prime divisor r of p-1.

WHY this implementation is fast enough up to 10^6:
- one linear sieve gives both the prime list and smallest prime factors,
  so factoring p-1 is cheap for every p;
- the minimal primitive-root prime is usually tiny, so only a few prime
  candidates need to be tested for each p.
"""

from __future__ import annotations

import argparse
import time
from array import array
from collections import Counter


def linear_sieve(limit: int) -> tuple[list[int], array]:
    """Return primes up to limit and smallest prime factors for 0..limit."""
    spf = array("I", [0]) * (limit + 1)
    primes: list[int] = []

    for n in range(2, limit + 1):
        if spf[n] == 0:
            spf[n] = n
            primes.append(n)
        for p in primes:
            m = n * p
            if m > limit:
                break
            spf[m] = p
            if p == spf[n]:
                break

    return primes, spf


def distinct_prime_factors(n: int, spf: array) -> list[int]:
    """Factor n into distinct prime divisors using the sieve."""
    factors: list[int] = []
    while n > 1:
        p = spf[n]
        factors.append(p)
        while n % p == 0:
            n //= p
    return factors


def is_primitive_root(candidate: int, p: int, phi_factors: list[int]) -> bool:
    """Check the standard primitive-root criterion for prime modulus p."""
    phi = p - 1
    for r in phi_factors:
        if pow(candidate, phi // r, p) == 1:
            return False
    return True


def verify(limit: int) -> dict[str, object]:
    primes, spf = linear_sieve(limit)
    counts: Counter[int] = Counter()
    first_examples: dict[int, list[int]] = {}
    record_breakers: list[tuple[int, int]] = []
    max_minimal_q = 0
    max_cases: list[int] = []
    counterexamples: list[int] = []

    odd_primes = 0

    for p in primes:
        if p == 2:
            continue

        odd_primes += 1
        phi_factors = distinct_prime_factors(p - 1, spf)
        minimal_q: int | None = None

        for q in primes:
            if q >= p:
                break
            if is_primitive_root(q, p, phi_factors):
                minimal_q = q
                break

        if minimal_q is None:
            counterexamples.append(p)
            continue

        counts[minimal_q] += 1
        first_examples.setdefault(minimal_q, [])
        if len(first_examples[minimal_q]) < 10:
            first_examples[minimal_q].append(p)

        if minimal_q > max_minimal_q:
            max_minimal_q = minimal_q
            max_cases = [p]
            record_breakers.append((p, minimal_q))
        elif minimal_q == max_minimal_q:
            max_cases.append(p)

    return {
        "limit": limit,
        "odd_primes": odd_primes,
        "counts": counts,
        "first_examples": first_examples,
        "record_breakers": record_breakers,
        "max_minimal_q": max_minimal_q,
        "max_cases": max_cases,
        "counterexamples": counterexamples,
    }


def print_summary(result: dict[str, object]) -> None:
    limit = result["limit"]
    odd_primes = result["odd_primes"]
    counts: Counter[int] = result["counts"]  # type: ignore[assignment]
    first_examples: dict[int, list[int]] = result["first_examples"]  # type: ignore[assignment]
    record_breakers: list[tuple[int, int]] = result["record_breakers"]  # type: ignore[assignment]
    max_minimal_q = result["max_minimal_q"]
    max_cases: list[int] = result["max_cases"]  # type: ignore[assignment]
    counterexamples: list[int] = result["counterexamples"]  # type: ignore[assignment]

    print(f"Checked all odd primes p <= {limit:,}.")
    print(f"Odd primes checked: {odd_primes:,}")
    if counterexamples:
        print(f"Counterexamples found: {len(counterexamples)}")
        print("First counterexamples:", counterexamples[:20])
    else:
        print("Counterexamples found: none")

    print("\nDistribution of the minimal prime primitive root q:")
    for q in sorted(counts):
        count = counts[q]
        share = 100.0 * count / odd_primes
        print(f"  q = {q:>3}: {count:>6} primes ({share:6.2f}%)")

    print(f"\nLargest minimal q encountered: {max_minimal_q}")
    print(f"Number of primes attaining it: {len(max_cases)}")
    print("First primes attaining the maximum:", max_cases[:20])

    print("\nRecord breakers for the minimal prime primitive root:")
    for p, q in record_breakers:
        print(f"  p = {p:>7}, minimal q = {q}")

    print("\nFirst examples for each minimal q:")
    for q in sorted(first_examples):
        examples = ", ".join(str(p) for p in first_examples[q])
        print(f"  q = {q:>3}: {examples}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--limit",
        type=int,
        default=10**6,
        help="check all odd primes p <= LIMIT (default: 10^6)",
    )
    args = parser.parse_args()

    start = time.time()
    result = verify(args.limit)
    elapsed = time.time() - start
    print_summary(result)
    print(f"\nElapsed: {elapsed:.2f}s")


if __name__ == "__main__":
    main()
