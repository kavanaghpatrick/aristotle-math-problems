#!/usr/bin/env python3
"""
Brocard / Erdős 398 verifier for

    n! + 1 = m^2.

The script uses two layers:

1. Sound modular filters modulo several primes q > nmax.
   For n <= nmax, if n! + 1 is a square in Z then it must be a quadratic
   residue modulo every such q. Most n are discarded here.
2. Exact verification with math.isqrt on the small survivor set.

This is deliberately simple. The modular layer is what makes higher bounds
practical without carrying exact factorials at every step.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import isqrt
from time import perf_counter


KNOWN_SOLUTIONS = {4: 5, 5: 11, 7: 71}


def is_probable_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for 64-bit inputs."""
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1

    # Standard deterministic basis for 64-bit integers.
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def next_primes(start: int, count: int) -> list[int]:
    """Return the first count odd primes >= start."""
    primes: list[int] = []
    candidate = max(3, start)
    if candidate % 2 == 0:
        candidate += 1
    while len(primes) < count:
        if is_probable_prime(candidate):
            primes.append(candidate)
        candidate += 2
    return primes


def quadratic_residue_table(p: int) -> bytearray:
    """res[r] = 1 iff r is a square modulo the odd prime p."""
    res = bytearray(p)
    for x in range(p):
        res[(x * x) % p] = 1
    return res


@dataclass
class PrimeFilter:
    prime: int
    residues: bytearray
    fact_mod: int = 1
    rejections: int = 0

    def update(self, n: int) -> None:
        self.fact_mod = (self.fact_mod * n) % self.prime

    def accepts(self) -> bool:
        return bool(self.residues[(self.fact_mod + 1) % self.prime])


def modular_survivors(nmax: int, primes: list[int], report_every: int) -> tuple[list[int], list[PrimeFilter]]:
    filters = [PrimeFilter(p, quadratic_residue_table(p)) for p in primes]
    survivors: list[int] = []

    for n in range(1, nmax + 1):
        for flt in filters:
            flt.update(n)

        for flt in filters:
            if not flt.accepts():
                flt.rejections += 1
                break
        else:
            survivors.append(n)

        if report_every and n % report_every == 0:
            print(f"scanned n={n:,}, survivors so far={len(survivors)}", flush=True)

    return survivors, filters


def exact_square_solutions(candidates: list[int]) -> list[tuple[int, int]]:
    """Exact isqrt test on the candidate list, advancing factorial only as needed."""
    solutions: list[tuple[int, int]] = []
    fact = 1
    last = 0
    for n in candidates:
        for k in range(last + 1, n + 1):
            fact *= k
        last = n
        root = isqrt(fact + 1)
        if root * root == fact + 1:
            solutions.append((n, root))
    return solutions


def verify(nmax: int, filter_count: int, report_every: int, modular_only: bool, print_candidates: bool) -> None:
    t0 = perf_counter()
    primes = next_primes(nmax + 1, filter_count)
    print(f"Using {len(primes)} primes above nmax: {primes}")

    candidates, filters = modular_survivors(nmax, primes, report_every)
    t1 = perf_counter()
    print(f"Modular sieve survivors: {len(candidates)} / {nmax}")
    if print_candidates:
        print(f"Candidates: {candidates}")

    if modular_only:
        print("\nFilter stats:")
        for flt in filters:
            print(f"  p={flt.prime}: first-hit rejections={flt.rejections}")
        print(f"\nTiming: sieve={t1 - t0:.3f}s total={t1 - t0:.3f}s")
        return

    solutions = exact_square_solutions(candidates)
    t2 = perf_counter()

    print(f"Exact solutions found: {solutions}")
    print(f"Expected known solutions within range: {[item for item in KNOWN_SOLUTIONS.items() if item[0] <= nmax]}")

    unexpected = [(n, m) for (n, m) in solutions if KNOWN_SOLUTIONS.get(n) != m]
    missed = [(n, m) for (n, m) in KNOWN_SOLUTIONS.items() if n <= nmax and (n, m) not in solutions]

    if unexpected:
        print(f"UNEXPECTED SOLUTIONS: {unexpected}")
    if missed:
        print(f"MISSED KNOWN SOLUTIONS: {missed}")
    if not unexpected and not missed:
        print(f"Verified: no solutions up to n={nmax:,} beyond n=4,5,7.")

    print("\nFilter stats:")
    for flt in filters:
        print(f"  p={flt.prime}: first-hit rejections={flt.rejections}")

    print(f"\nTiming: sieve={t1 - t0:.3f}s exact={t2 - t1:.3f}s total={t2 - t0:.3f}s")


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify Brocard's problem to a finite bound.")
    parser.add_argument("--nmax", type=int, default=100_000, help="verify 1 <= n <= nmax")
    parser.add_argument(
        "--filters",
        type=int,
        default=8,
        help="number of primes just above nmax used as modular filters",
    )
    parser.add_argument(
        "--report-every",
        type=int,
        default=0,
        help="progress print interval; 0 disables progress output",
    )
    parser.add_argument(
        "--modular-only",
        action="store_true",
        help="stop after the modular sieve and report the survivor set",
    )
    parser.add_argument(
        "--print-candidates",
        action="store_true",
        help="print the modular survivor list",
    )
    args = parser.parse_args()

    if args.nmax < 1:
        raise SystemExit("--nmax must be positive")
    if args.filters < 1:
        raise SystemExit("--filters must be positive")

    verify(args.nmax, args.filters, args.report_every, args.modular_only, args.print_candidates)


if __name__ == "__main__":
    main()
