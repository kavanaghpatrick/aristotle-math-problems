#!/usr/bin/env python3
"""
Bounded verification for Erdős 672.

For positive integers n, d, k with gcd(n, d) = 1, this script studies

    P(n, d, k) = ∏_{i=0}^{k-1} (n + i d)

and checks whether P(n, d, k) is a perfect l-th power for some l >= 2.

This is only a small-case exploration tool. It uses exact prime-exponent
factorization, so it is mathematically rigorous on the searched range.
"""

from __future__ import annotations

import argparse
import math
from collections import Counter
from dataclasses import dataclass


def build_spf(limit: int) -> list[int]:
    """Smallest-prime-factor sieve for exact factorizations up to `limit`."""
    spf = list(range(limit + 1))
    if limit >= 1:
        spf[1] = 1
    for p in range(2, math.isqrt(limit) + 1):
        if spf[p] != p:
            continue
        for multiple in range(p * p, limit + 1, p):
            if spf[multiple] == multiple:
                spf[multiple] = p
    return spf


def factor_with_spf(n: int, spf: list[int]) -> Counter[int]:
    """Return the prime factorization of `n` as exponent counts."""
    factors: Counter[int] = Counter()
    while n > 1:
        p = spf[n]
        factors[p] += 1
        n //= p
    return factors


def integer_nth_root_if_exact(n: int, power: int) -> int | None:
    """Return y if y**power == n, else None."""
    if n < 0 or power < 1:
        return None
    if n in (0, 1) or power == 1:
        return n

    lo = 1
    hi = 1 << ((n.bit_length() + power - 1) // power)
    while lo <= hi:
        mid = (lo + hi) // 2
        value = mid**power
        if value == n:
            return mid
        if value < n:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


def ap_terms(n: int, d: int, k: int) -> list[int]:
    return [n + i * d for i in range(k)]


def ap_product(n: int, d: int, k: int) -> int:
    product = 1
    for term in ap_terms(n, d, k):
        product *= term
    return product


def factorized_ap_exponents(n: int, d: int, k: int, spf: list[int]) -> Counter[int]:
    """Prime exponents of the AP product, accumulated term-by-term."""
    total: Counter[int] = Counter()
    for term in ap_terms(n, d, k):
        total += factor_with_spf(term, spf)
    return total


def perfect_power_exponent(exponents: Counter[int]) -> int:
    """
    Largest l such that the factored integer is an l-th power.

    This is gcd of all nonzero prime exponents; value 1 means "not a nontrivial
    perfect power".
    """
    gcd_exponent = 0
    for exponent in exponents.values():
        gcd_exponent = math.gcd(gcd_exponent, exponent)
    return gcd_exponent


@dataclass(frozen=True)
class Hit:
    n: int
    d: int
    k: int
    l: int
    root: int
    product: int
    max_power: int


def analyze_case(n: int, d: int, k: int, spf: list[int]) -> tuple[int, int]:
    """
    Return (product, max_power) where max_power is the largest l >= 1 for which
    the product is an l-th power.
    """
    product = ap_product(n, d, k)
    exponents = factorized_ap_exponents(n, d, k, spf)
    return product, perfect_power_exponent(exponents)


def search_hits(
    *,
    min_k: int,
    max_k: int,
    max_d: int,
    max_term: int,
    min_l: int,
    max_l: int,
    max_hits: int,
) -> list[Hit]:
    if min_k < 1 or max_k < min_k:
        raise ValueError("Require 1 <= min_k <= max_k")
    if min_l < 2 or max_l < min_l:
        raise ValueError("Require 2 <= min_l <= max_l")

    spf = build_spf(max_term)
    hits: list[Hit] = []

    for k in range(min_k, max_k + 1):
        if k > max_term:
            break
        d_cap = min(max_d, (max_term - 1) // max(1, k - 1) if k > 1 else max_d)
        for d in range(1, d_cap + 1):
            n_max = max_term - (k - 1) * d
            for n in range(1, n_max + 1):
                if math.gcd(n, d) != 1:
                    continue

                product, max_power = analyze_case(n, d, k, spf)
                if max_power < min_l:
                    continue

                for l in range(min_l, min(max_l, max_power) + 1):
                    if max_power % l != 0:
                        continue
                    root = integer_nth_root_if_exact(product, l)
                    if root is None:
                        raise AssertionError("factorization and root check disagree")
                    hits.append(
                        Hit(
                            n=n,
                            d=d,
                            k=k,
                            l=l,
                            root=root,
                            product=product,
                            max_power=max_power,
                        )
                    )
                    if len(hits) >= max_hits:
                        return hits
    return hits


def format_hit(hit: Hit) -> str:
    terms = " * ".join(str(t) for t in ap_terms(hit.n, hit.d, hit.k))
    return (
        f"k={hit.k} l={hit.l} n={hit.n} d={hit.d}: "
        f"{terms} = {hit.product} = {hit.root}^{hit.l} "
        f"(largest power exponent {hit.max_power})"
    )


def run_check(n: int, d: int, k: int, l: int) -> int:
    if n <= 0 or d <= 0 or k <= 0 or l < 2:
        raise ValueError("Require n,d,k > 0 and l >= 2")
    if math.gcd(n, d) != 1:
        raise ValueError("Require gcd(n, d) = 1")

    max_term = n + (k - 1) * d
    spf = build_spf(max_term)
    product, max_power = analyze_case(n, d, k, spf)
    exact_root = integer_nth_root_if_exact(product, l)

    terms = " * ".join(str(t) for t in ap_terms(n, d, k))
    print(f"terms: {terms}")
    print(f"product: {product}")
    print(f"largest exact perfect-power exponent: {max_power}")
    if exact_root is None:
        print(f"result: not a perfect {l}-th power")
        return 1

    print(f"result: {product} = {exact_root}^{l}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    check = subparsers.add_parser("check", help="check one explicit (n, d, k, l)")
    check.add_argument("--n", type=int, required=True)
    check.add_argument("--d", type=int, required=True)
    check.add_argument("--k", type=int, required=True)
    check.add_argument("--l", type=int, required=True)

    search = subparsers.add_parser("search", help="search bounded ranges")
    search.add_argument("--min-k", type=int, default=3)
    search.add_argument("--max-k", type=int, default=8)
    search.add_argument(
        "--max-d",
        type=int,
        default=50,
        help="upper bound on common difference d",
    )
    search.add_argument(
        "--max-term",
        type=int,
        default=200,
        help="require n + (k-1)d <= max-term",
    )
    search.add_argument("--min-l", type=int, default=2)
    search.add_argument("--max-l", type=int, default=8)
    search.add_argument("--max-hits", type=int, default=20)
    return parser


def main() -> int:
    args = build_parser().parse_args()

    if args.command == "check":
        return run_check(args.n, args.d, args.k, args.l)

    hits = search_hits(
        min_k=args.min_k,
        max_k=args.max_k,
        max_d=args.max_d,
        max_term=args.max_term,
        min_l=args.min_l,
        max_l=args.max_l,
        max_hits=args.max_hits,
    )
    if not hits:
        print("No perfect-power AP products found in the searched range.")
        return 0

    for hit in hits:
        print(format_hit(hit))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
