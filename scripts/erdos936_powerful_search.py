#!/usr/bin/env python3
"""
Search the Erdos 936 families for powerful values.

Target families:
  - 2^n + 1
  - 2^n - 1
  - n! + 1
  - n! - 1

A positive integer is powerful if every prime divisor appears with exponent >= 2.

WHY this script is split into two modes:
  1. For 2^n +/- 1 we can often disprove powerfulness cheaply by finding a small
     prime p with p | (2^n +/- 1) but p^2 not | (2^n +/- 1). That only needs
     modular arithmetic, so it still works for large n.
  2. For n! +/- 1 there is no comparable cheap modular filter built into the
     form, so we fall back to exact integers and factorization. That keeps the
     code simple and honest about what it can actually verify.
"""

from __future__ import annotations

import argparse
import math
import random
from dataclasses import dataclass


SMALL_PRIMES = (
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
)


@dataclass(frozen=True)
class CheckResult:
    family: str
    n: int
    value_bits: int
    powerful: bool | None
    reason: str
    factorization: list[tuple[int, int]] | None = None


def sieve_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            start = p * p
            is_prime[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
    return [p for p in range(2, limit + 1) if is_prime[p]]


def is_probable_prime(n: int, rounds: int = 16) -> bool:
    if n < 2:
        return False
    for p in SMALL_PRIMES:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2

    for _ in range(rounds):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_rho(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3

    while True:
        c = random.randrange(1, n - 1)
        x = random.randrange(2, n - 1)
        y = x
        d = 1

        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)

        if d != n:
            return d


def factorint(n: int) -> list[tuple[int, int]]:
    if n < 2:
        return []

    factors: dict[int, int] = {}

    def add_prime(p: int) -> None:
        factors[p] = factors.get(p, 0) + 1

    def rec(m: int) -> None:
        if m == 1:
            return
        if is_probable_prime(m):
            add_prime(m)
            return
        for p in SMALL_PRIMES:
            if m % p == 0:
                add_prime(p)
                rec(m // p)
                return
        d = pollard_rho(m)
        rec(d)
        rec(m // d)

    rec(n)
    return sorted(factors.items())


def is_powerful_from_factors(factors: list[tuple[int, int]]) -> bool:
    return all(exp >= 2 for _, exp in factors)


def format_factorization(factors: list[tuple[int, int]] | None) -> str:
    if factors is None:
        return "unknown"
    if not factors:
        return "1"
    parts = []
    for p, exp in factors:
        parts.append(str(p) if exp == 1 else f"{p}^{exp}")
    return " * ".join(parts)


def exact_check(family: str, n: int, value: int) -> CheckResult:
    if value <= 0:
        return CheckResult(
            family=family,
            n=n,
            value_bits=0 if value == 0 else value.bit_length(),
            powerful=None,
            reason=f"value={value} is outside the positive-integer definition",
            factorization=None,
        )

    factors = factorint(value)
    powerful = is_powerful_from_factors(factors)
    return CheckResult(
        family=family,
        n=n,
        value_bits=value.bit_length(),
        powerful=powerful,
        reason="exact factorization",
        factorization=factors,
    )


def small_prime_witness_pow2(n: int, delta: int, primes: list[int]) -> int | None:
    for p in primes:
        if p == 2:
            continue

        residue_p = pow(2, n, p)
        residue_p2 = pow(2, n, p * p)

        if delta == 1:
            if residue_p == p - 1 and residue_p2 != p * p - 1:
                return p
        else:
            if residue_p == 1 and residue_p2 != 1:
                return p

    return None


def check_pow2_family(
    family: str,
    n: int,
    delta: int,
    witness_primes: list[int],
    max_exact_bits: int,
) -> CheckResult:
    witness = small_prime_witness_pow2(n, delta, witness_primes)
    value_bits = max(1, n + (1 if delta > 0 else 0))
    if witness is not None:
        return CheckResult(
            family=family,
            n=n,
            value_bits=value_bits,
            powerful=False,
            reason=f"small-prime witness: {witness} divides once modulo {witness}^2",
            factorization=[(witness, 1)],
        )

    if value_bits > max_exact_bits:
        return CheckResult(
            family=family,
            n=n,
            value_bits=value_bits,
            powerful=None,
            reason=f"no witness <= {witness_primes[-1] if witness_primes else 1}, exact value skipped above {max_exact_bits} bits",
            factorization=None,
        )

    value = (1 << n) + delta
    return exact_check(family, n, value)


def search_pow2(
    family: str,
    delta: int,
    n_start: int,
    n_end: int,
    witness_primes: list[int],
    max_exact_bits: int,
    report_every: int,
    verbose: bool,
) -> list[CheckResult]:
    results: list[CheckResult] = []
    for n in range(n_start, n_end + 1):
        result = check_pow2_family(family, n, delta, witness_primes, max_exact_bits)
        results.append(result)

        should_print = verbose or result.powerful is True or result.powerful is None
        if report_every > 0 and (n - n_start + 1) % report_every == 0:
            print(
                f"[{family}] reached n={n}: powerful={sum(r.powerful is True for r in results)}, "
                f"not_powerful={sum(r.powerful is False for r in results)}, unresolved={sum(r.powerful is None for r in results)}"
            )
        if should_print:
            print_result(result)

    return results


def search_factorial(
    family: str,
    delta: int,
    n_start: int,
    n_end: int,
    max_exact_bits: int,
    report_every: int,
    verbose: bool,
) -> list[CheckResult]:
    if n_end < 0:
        return []

    fact = math.factorial(n_start)
    results: list[CheckResult] = []
    for n in range(n_start, n_end + 1):
        if n > n_start:
            fact *= n

        value = fact + delta
        value_bits = value.bit_length() if value > 0 else 0

        if value > 0 and value_bits > max_exact_bits:
            result = CheckResult(
                family=family,
                n=n,
                value_bits=value_bits,
                powerful=None,
                reason=f"exact value skipped above {max_exact_bits} bits",
                factorization=None,
            )
        else:
            result = exact_check(family, n, value)

        results.append(result)
        should_print = verbose or result.powerful is True or result.powerful is None
        if report_every > 0 and (n - n_start + 1) % report_every == 0:
            print(
                f"[{family}] reached n={n}: powerful={sum(r.powerful is True for r in results)}, "
                f"not_powerful={sum(r.powerful is False for r in results)}, unresolved={sum(r.powerful is None for r in results)}"
            )
        if should_print:
            print_result(result)

    return results


def print_result(result: CheckResult) -> None:
    status = (
        "powerful"
        if result.powerful is True
        else "not powerful"
        if result.powerful is False
        else "unresolved"
    )
    line = f"{result.family}: n={result.n}, bits={result.value_bits}, {status}, reason={result.reason}"
    if result.factorization is not None:
        line += f", factors={format_factorization(result.factorization)}"
    print(line)


def summarize(results: list[CheckResult]) -> None:
    if not results:
        return

    family = results[0].family
    powerful_hits = [r for r in results if r.powerful is True]
    unresolved = [r for r in results if r.powerful is None]
    not_powerful = len([r for r in results if r.powerful is False])

    print(f"\nSummary for {family}")
    print(f"  checked:      {len(results)}")
    print(f"  powerful:     {len(powerful_hits)}")
    print(f"  not powerful: {not_powerful}")
    print(f"  unresolved:   {len(unresolved)}")

    if powerful_hits:
        print("  hits:")
        for hit in powerful_hits:
            print(f"    n={hit.n}, factors={format_factorization(hit.factorization)}")
    if unresolved:
        print("  unresolved n:")
        preview = ", ".join(str(r.n) for r in unresolved[:12])
        suffix = "" if len(unresolved) <= 12 else ", ..."
        print(f"    {preview}{suffix}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Search the Erdos 936 powerful-number variants.")
    parser.add_argument(
        "--family",
        choices=("pow2-plus", "pow2-minus", "fact-plus", "fact-minus", "all"),
        default="all",
        help="Which family to search.",
    )
    parser.add_argument("--n-start", type=int, default=1, help="Starting n.")
    parser.add_argument("--n-end", type=int, default=50, help="Ending n.")
    parser.add_argument(
        "--prime-bound",
        type=int,
        default=10_000,
        help="Small-prime witness bound for the 2^n +/- 1 families.",
    )
    parser.add_argument(
        "--max-exact-bits",
        type=int,
        default=128,
        help="Skip exact factorization when the candidate exceeds this bit size.",
    )
    parser.add_argument(
        "--report-every",
        type=int,
        default=0,
        help="Progress report cadence; 0 disables periodic updates.",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print every checked n, not just hits and unresolved cases.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.n_end < args.n_start:
        raise SystemExit("n-end must be >= n-start")

    random.seed(0)
    witness_primes = sieve_primes(args.prime_bound)
    family_results: list[list[CheckResult]] = []

    if args.family in ("pow2-plus", "all"):
        family_results.append(
            search_pow2(
                family="2^n+1",
                delta=1,
                n_start=args.n_start,
                n_end=args.n_end,
                witness_primes=witness_primes,
                max_exact_bits=args.max_exact_bits,
                report_every=args.report_every,
                verbose=args.verbose,
            )
        )

    if args.family in ("pow2-minus", "all"):
        family_results.append(
            search_pow2(
                family="2^n-1",
                delta=-1,
                n_start=args.n_start,
                n_end=args.n_end,
                witness_primes=witness_primes,
                max_exact_bits=args.max_exact_bits,
                report_every=args.report_every,
                verbose=args.verbose,
            )
        )

    if args.family in ("fact-plus", "all"):
        family_results.append(
            search_factorial(
                family="n!+1",
                delta=1,
                n_start=args.n_start,
                n_end=args.n_end,
                max_exact_bits=args.max_exact_bits,
                report_every=args.report_every,
                verbose=args.verbose,
            )
        )

    if args.family in ("fact-minus", "all"):
        family_results.append(
            search_factorial(
                family="n!-1",
                delta=-1,
                n_start=args.n_start,
                n_end=args.n_end,
                max_exact_bits=args.max_exact_bits,
                report_every=args.report_every,
                verbose=args.verbose,
            )
        )

    print()
    for results in family_results:
        summarize(results)


if __name__ == "__main__":
    main()
