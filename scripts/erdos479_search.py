#!/usr/bin/env python3
"""
Computational exploration of Erdos problem 479:

    For fixed k > 1, are there infinitely many n with 2^n ≡ k (mod n)?

This script searches all n <= limit for k in a fixed interval and then
summarizes the hits using the odd-part multiplicative order ord_m(2),
where n = 2^a m with m odd.

Core facts used in the analysis:
  1) If n = 2^a m with m odd and 2^n ≡ k (mod n), then a <= v2(k).
  2) The odd part m must be coprime to k.
  3) For gcd(2,m)=1, the congruence modulo m is controlled by ord_m(2):
         2^n ≡ k (mod m)  <=>  k lies in <2> mod m and n is in the
         corresponding exponent class modulo ord_m(2).

The search itself is intentionally simple: one pass over n using Python's
modular exponentiation. The extra work goes into explaining the output.
"""

from __future__ import annotations

import argparse
import math
from collections import Counter


def sieve_spf(limit: int) -> list[int]:
    """Smallest prime factor table for fast factorization up to limit."""
    spf = list(range(limit + 1))
    if limit >= 1:
        spf[1] = 1
    for i in range(2, int(limit**0.5) + 1):
        if spf[i] != i:
            continue
        for j in range(i * i, limit + 1, i):
            if spf[j] == j:
                spf[j] = i
    return spf


def factorize(n: int, spf: list[int]) -> dict[int, int]:
    factors: dict[int, int] = {}
    while n > 1:
        p = spf[n]
        factors[p] = factors.get(p, 0) + 1
        n //= p
    return factors


def is_prime(n: int, spf: list[int]) -> bool:
    return n >= 2 and spf[n] == n


def v2(n: int) -> int:
    return (n & -n).bit_length() - 1


def phi_from_factors(factors: dict[int, int]) -> int:
    out = 1
    for p, e in factors.items():
        out *= (p - 1) * (p ** (e - 1))
    return out


def multiplicative_order_2(modulus: int, spf: list[int]) -> int:
    """ord_modulus(2), assuming modulus is odd and positive."""
    if modulus <= 0 or modulus % 2 == 0:
        raise ValueError("modulus must be a positive odd integer")
    if modulus == 1:
        return 1

    phi = phi_from_factors(factorize(modulus, spf))
    order = phi
    for q in factorize(phi, spf):
        while order % q == 0 and pow(2, order // q, modulus) == 1:
            order //= q
    return order


def prime_family_anchor(a: int) -> int | None:
    """
    Return 2^(2^a) when it is small enough to matter for our search range.

    For a >= 5 this already exceeds 10^6 by a wide margin, so no odd prime
    factor p <= 10^6 can satisfy p > 2^(2^a).
    """
    exp = 1 << a
    if exp > 20:
        return None
    return 1 << exp


def search_hits(limit: int, k_min: int, k_max: int) -> dict[int, list[int]]:
    hits: dict[int, list[int]] = {k: [] for k in range(k_min, k_max + 1)}
    for n in range(2, limit + 1):
        residue = pow(2, n, n)
        if k_min <= residue <= k_max:
            hits[residue].append(n)
    return hits


def analyze_hits_for_k(k: int, values: list[int], spf: list[int], show: int) -> str:
    lines: list[str] = []
    lines.append(f"k={k}: {len(values)} hits")
    if not values:
        return "\n".join(lines)

    first = values[:show]
    lines.append(f"  first hits: {first}")

    prime_hits = sum(1 for n in values if is_prime(n, spf))
    a_counts = Counter(v2(n) for n in values)
    odd_gcd_violations = 0
    v2_violations = 0
    exact_family_tail = 0
    shape_2a_p = 0

    for n in values:
        a = v2(n)
        m = n >> a
        if a > v2(k):
            v2_violations += 1
        if math.gcd(m, k) != 1:
            odd_gcd_violations += 1
        if m > 1 and is_prime(m, spf):
            shape_2a_p += 1
            anchor = prime_family_anchor(a)
            if anchor is not None and m > max(k, anchor):
                exact_family_tail += 1

    lines.append(f"  prime n count: {prime_hits}")
    lines.append(f"  v2(n) distribution: {dict(sorted(a_counts.items()))}")
    lines.append(f"  hits of shape 2^a * p with odd prime p: {shape_2a_p}")
    lines.append(f"  exact 2^(2^a) prime-family tail hits: {exact_family_tail}")
    lines.append(f"  theory checks: v2 violations={v2_violations}, odd-gcd violations={odd_gcd_violations}")

    lines.append("  sample order data:")
    for n in first:
        a = v2(n)
        m = n >> a
        if m == 1:
            lines.append(f"    n={n}: pure power of 2, odd part m=1")
            continue
        order = multiplicative_order_2(m, spf)
        reduced_exp = n % order
        residue_m = k % m
        lines.append(
            "    "
            f"n={n} = 2^{a} * {m}; ord_{m}(2)={order}; "
            f"n mod ord={reduced_exp}; 2^{reduced_exp} mod {m}={pow(2, reduced_exp, m)}; "
            f"k mod {m}={residue_m}"
        )

    return "\n".join(lines)


def global_pattern_summary(hits: dict[int, list[int]], spf: list[int]) -> str:
    lines: list[str] = []
    lines.append("Global pattern summary")

    prime_only_for = []
    for k, values in hits.items():
        if any(is_prime(n, spf) for n in values):
            prime_only_for.append(k)
    lines.append(f"  k with at least one prime solution up to the bound: {prime_only_for}")

    exact_tail_by_k = {}
    for k, values in hits.items():
        total = 0
        for n in values:
            a = v2(n)
            m = n >> a
            anchor = prime_family_anchor(a)
            if m > 1 and is_prime(m, spf) and anchor is not None and m > max(k, anchor):
                total += 1
        exact_tail_by_k[k] = total
    lines.append(f"  exact 2^(2^a) prime-family tail counts by k: {exact_tail_by_k}")

    explained = []
    for k, total in exact_tail_by_k.items():
        if total:
            explained.append(k)
    lines.append(
        "  Only k with a substantial large-prime 2^a*p family can survive this test: "
        f"{explained}"
    )
    lines.append(
        "  For n = 2^a p with odd prime p coprime to k, "
        "2^n ≡ 2^(2^a) (mod p) because ord_p(2) | p-1."
    )
    lines.append(
        "  Combined with the 2-adic condition k ≡ 0 (mod 2^a), this singles out "
        "the obvious families k = 2, 4, 16 when p is large."
    )

    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1_000_000)
    parser.add_argument("--k-min", type=int, default=2)
    parser.add_argument("--k-max", type=int, default=20)
    parser.add_argument("--show", type=int, default=8)
    args = parser.parse_args()

    hits = search_hits(args.limit, args.k_min, args.k_max)
    spf = sieve_spf(args.limit)

    total_hits = sum(len(values) for values in hits.values())
    print(
        f"Searched n <= {args.limit} for residues k in [{args.k_min}, {args.k_max}] "
        f"and found {total_hits} total hits."
    )
    print()

    print(global_pattern_summary(hits, spf))
    print()

    for k in range(args.k_min, args.k_max + 1):
        print(analyze_hits_for_k(k, hits[k], spf, args.show))
        print()


if __name__ == "__main__":
    main()
