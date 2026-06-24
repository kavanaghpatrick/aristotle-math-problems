#!/usr/bin/env python3
"""
Search support for Erdos problem 677.

Question:
  For k > 0 and m >= n+k, must we always have

      lcm(n+1, ..., n+k) != lcm(m+1, ..., m+k) ?

This script searches for counterexamples for fixed k, and also exposes small
"shifted-length" equalities such as:

  lcm(5,6,7)     = lcm(14,15)
  lcm(4,5,6,7)   = lcm(20,21)
  lcm(9,10,11,12)= lcm(44,45)

Core pruning idea (WHY this is fast):
If p is prime and m < p <= m+k, then p divides lcm(m+1,...,m+k). Since
m >= n+k, we also have p > n+k, so p cannot divide lcm(n+1,...,n+k).
Therefore any genuine counterexample must live inside a prime gap of length
at least k. We reject every interval containing a prime before doing any
exact LCM work.
"""

from __future__ import annotations

import argparse
import time
from array import array
from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache


def build_sieve(limit: int) -> tuple[array, array]:
    """
    Return:
      spf[n]   = smallest prime factor of n (spf[1] = 1)
      pi[n]    = number of primes <= n

    A smallest-prime-factor sieve is enough for exact factorization, while
    pi supports the prime-gap obstruction.
    """
    if limit < 1:
        raise ValueError("limit must be >= 1")

    spf = array("I", [0]) * (limit + 1)
    pi = array("I", [0]) * (limit + 1)
    spf[1] = 1

    primes: list[int] = []
    primes_append = primes.append

    prime_count = 0
    for i in range(2, limit + 1):
        if spf[i] == 0:
            spf[i] = i
            primes_append(i)
            prime_count += 1
        pi[i] = prime_count

        for p in primes:
            ip = i * p
            if ip > limit:
                break
            spf[ip] = p
            if p == spf[i]:
                break
    return spf, pi


@lru_cache(maxsize=None)
def _factor_tuple(n: int, spf_key: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    """
    Cached factorization helper.

    The cache key uses a tuple view of spf so the helper stays pure from the
    caller's perspective; callers should pass the same tuple each time.
    """
    spf = spf_key
    factors: list[tuple[int, int]] = []
    x = n
    while x > 1:
        p = spf[x]
        e = 0
        while x % p == 0:
            x //= p
            e += 1
        factors.append((p, e))
    return tuple(factors)


def factor_tuple(n: int, spf_key: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    if n <= 1:
        return ()
    return _factor_tuple(n, spf_key)


def interval_signature(start: int, k: int, spf_key: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    """
    Canonical factorization of lcm(start+1, ..., start+k) as sorted (p, e).

    Using a factor signature avoids constructing enormous Python integers while
    still giving exact equality checks.
    """
    max_exp: dict[int, int] = {}
    for x in range(start + 1, start + k + 1):
        for p, e in factor_tuple(x, spf_key):
            prev = max_exp.get(p, 0)
            if e > prev:
                max_exp[p] = e
    return tuple(sorted(max_exp.items()))


def interval_has_prime(start: int, k: int, prime_pi: array) -> bool:
    return prime_pi[start + k] > prime_pi[start]


def signature_to_lcm(signature: tuple[tuple[int, int], ...]) -> int:
    value = 1
    for p, e in signature:
        value *= p**e
    return value


@dataclass(frozen=True)
class CounterexampleHit:
    k: int
    n: int
    m: int
    gap: int


@dataclass(frozen=True)
class ShiftedHit:
    left_start: int
    left_len: int
    right_start: int
    right_len: int
    lcm_value: int


@dataclass(frozen=True)
class SearchStats:
    starts: int
    prime_free_starts: int
    exact_checks: int


def search_counterexamples(
    *,
    k: int,
    max_start: int,
    max_hits: int,
    progress_every: int,
) -> tuple[list[CounterexampleHit], SearchStats]:
    if k <= 0:
        raise ValueError("k must be positive")
    if max_start < k:
        return ([], SearchStats(starts=max_start + 1, prime_free_starts=0, exact_checks=0))

    limit = max_start + k
    spf, prime_pi = build_sieve(limit)
    spf_key = tuple(spf)

    signatures = [interval_signature(start, k, spf_key) for start in range(max_start + 1)]
    eligible: dict[tuple[tuple[int, int], ...], list[int]] = defaultdict(list)

    hits: list[CounterexampleHit] = []
    prime_free_starts = 0
    exact_checks = 0
    t0 = time.time()

    for m in range(max_start + 1):
        if m - k >= 0:
            eligible[signatures[m - k]].append(m - k)

        if m < k:
            continue

        if interval_has_prime(m, k, prime_pi):
            continue
        prime_free_starts += 1

        same_sig = eligible.get(signatures[m], [])
        if not same_sig:
            continue

        exact_checks += 1
        for n in same_sig:
            hits.append(
                CounterexampleHit(
                    k=k,
                    n=n,
                    m=m,
                    gap=m - n,
                )
            )
            if len(hits) >= max_hits:
                return (
                    hits,
                    SearchStats(
                        starts=max_start + 1,
                        prime_free_starts=prime_free_starts,
                        exact_checks=exact_checks,
                    ),
                )

        if progress_every and m % progress_every == 0:
            elapsed = time.time() - t0
            print(
                f"[m={m}/{max_start}] prime_free={prime_free_starts:,} "
                f"exact_checks={exact_checks:,} hits={len(hits)} elapsed={elapsed:.1f}s"
            )

    return (
        hits,
        SearchStats(
            starts=max_start + 1,
            prime_free_starts=prime_free_starts,
            exact_checks=exact_checks,
        ),
    )


def search_shifted_equalities(
    *,
    left_len: int,
    right_len: int,
    max_start: int,
    min_gap: int,
    disjoint_only: bool,
    max_hits: int,
) -> list[ShiftedHit]:
    if left_len <= 0 or right_len <= 0:
        raise ValueError("interval lengths must be positive")

    limit = max_start + max(left_len, right_len)
    spf, _ = build_sieve(limit)
    spf_key = tuple(spf)

    left_map: dict[tuple[tuple[int, int], ...], list[int]] = defaultdict(list)
    for start in range(max_start + 1):
        sig = interval_signature(start, left_len, spf_key)
        left_map[sig].append(start)

    hits: list[ShiftedHit] = []
    for right_start in range(max_start + 1):
        sig = interval_signature(right_start, right_len, spf_key)
        left_starts = left_map.get(sig, [])
        if not left_starts:
            continue
        for left_start in left_starts:
            if abs(right_start - left_start) < min_gap:
                continue
            left_end = left_start + left_len
            right_end = right_start + right_len
            if disjoint_only and not (left_end < right_start + 1 or right_end < left_start + 1):
                continue
            hits.append(
                ShiftedHit(
                    left_start=left_start,
                    left_len=left_len,
                    right_start=right_start,
                    right_len=right_len,
                    lcm_value=signature_to_lcm(sig),
                )
            )
            if len(hits) >= max_hits:
                return hits
    return hits


def cmd_search(args: argparse.Namespace) -> None:
    hits, stats = search_counterexamples(
        k=args.k,
        max_start=args.max_start,
        max_hits=args.max_hits,
        progress_every=args.progress_every,
    )

    print(
        f"searched k={args.k}, starts=0..{args.max_start}, "
        f"prime_free={stats.prime_free_starts}, exact_checks={stats.exact_checks}"
    )
    if not hits:
        print("No counterexamples found in this range.")
        return

    for hit in hits:
        print(
            f"COUNTEREXAMPLE k={hit.k} n={hit.n} m={hit.m} gap={hit.gap}"
        )


def cmd_range(args: argparse.Namespace) -> None:
    for k in range(args.k_min, args.k_max + 1):
        hits, stats = search_counterexamples(
            k=k,
            max_start=args.max_start,
            max_hits=1,
            progress_every=0,
        )
        print(
            f"k={k}: hits={len(hits)} prime_free={stats.prime_free_starts} exact_checks={stats.exact_checks}"
        )
        if hits:
            hit = hits[0]
            print(f"  first hit: n={hit.n}, m={hit.m}, gap={hit.gap}")


def cmd_shifted(args: argparse.Namespace) -> None:
    hits = search_shifted_equalities(
        left_len=args.left_len,
        right_len=args.right_len,
        max_start=args.max_start,
        min_gap=args.min_gap,
        disjoint_only=args.disjoint_only,
        max_hits=args.max_hits,
    )
    if not hits:
        print("No shifted equalities found in this range.")
        return

    for hit in hits:
        print(
            f"left=lcm({hit.left_start + 1}..{hit.left_start + hit.left_len}) "
            f"right=lcm({hit.right_start + 1}..{hit.right_start + hit.right_len}) "
            f"value={hit.lcm_value}"
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_search = sub.add_parser("search", help="search fixed-k counterexamples")
    p_search.add_argument("--k", type=int, required=True)
    p_search.add_argument("--max-start", type=int, default=50_000)
    p_search.add_argument("--max-hits", type=int, default=20)
    p_search.add_argument("--progress-every", type=int, default=10_000)
    p_search.set_defaults(func=cmd_search)

    p_range = sub.add_parser("range", help="scan a range of k values")
    p_range.add_argument("--k-min", type=int, required=True)
    p_range.add_argument("--k-max", type=int, required=True)
    p_range.add_argument("--max-start", type=int, default=20_000)
    p_range.set_defaults(func=cmd_range)

    p_shifted = sub.add_parser("shifted", help="search equal LCMs with different lengths")
    p_shifted.add_argument("--left-len", type=int, required=True)
    p_shifted.add_argument("--right-len", type=int, required=True)
    p_shifted.add_argument("--max-start", type=int, default=500)
    p_shifted.add_argument("--min-gap", type=int, default=1)
    p_shifted.add_argument("--disjoint-only", action="store_true")
    p_shifted.add_argument("--max-hits", type=int, default=20)
    p_shifted.set_defaults(func=cmd_shifted)

    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
