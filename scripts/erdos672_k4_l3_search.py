#!/usr/bin/env python3
"""
Erdos 672, case (m,k) = (4,3): search for 4-term APs of 3-full numbers.

Question (from Erdős 1975, reformulated by Bajpai-Bennett-Chan 2023):
  Does there exist N, d > 0 such that N, N+d, N+2d, N+3d are all 3-full,
  with gcd(N, d) = 1?

Status: OPEN. Bajpai-Bennett-Chan (2023) construct infinite 3-term APs
of coprime 3-full numbers (starting from the equation X^3+Y^3 = 2*3^4*Z^3
seeded by (X,Y,Z)=(37,17,7)), and prove that under abc, gcd(d,N) >> max(d,N)^{3/7-eps}
for any 4-term AP of 3-full numbers. The case (m=4,k=3) is NOT in the
exceptional set (1.8) of their paper, so abc gives a NONTRIVIAL constraint —
existence/non-existence remains open.

This script enumerates all 3-full numbers up to max_term and searches for any
4-term AP among them. Optionally restricts to coprime APs (gcd(N, d) = 1).

Output format (JSON):
  {
    "max_term": int,
    "num_3full":  int,
    "search_seconds": float,
    "aps_4term": [{"N": ..., "d": ..., "coprime": bool, "terms":[..]}, ...],
    "coprime_aps_4term": [...]  # filtered subset
  }
"""

from __future__ import annotations

import argparse
import bisect
import json
import math
import time
from pathlib import Path


def enumerate_kfull(N: int, k: int = 3) -> list[int]:
    """Return all k-full positive integers ≤ N (sorted)."""
    # Sieve of primes up to N^{1/k}
    p_max = int(N ** (1.0 / k)) + 2
    sieve = bytearray(b"\x01") * (p_max + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(math.isqrt(p_max)) + 1):
        if sieve[i]:
            for j in range(i * i, p_max + 1, i):
                sieve[j] = 0
    primes = [i for i in range(2, p_max + 1) if sieve[i]]

    out: list[int] = []

    def rec(idx: int, partial: int) -> None:
        out.append(partial)
        for j in range(idx, len(primes)):
            p = primes[j]
            pk = p**k
            if partial > N // pk:
                break
            # try exponents e = k, k+1, ...
            e = k
            cur = partial * pk
            while cur <= N:
                rec(j + 1, cur)
                e += 1
                if cur > N // p:
                    break
                cur *= p

    rec(0, 1)
    out.sort()
    return out


def find_4term_aps(kfull: list[int], coprime_only: bool = False) -> list[dict]:
    """
    Search all 4-term APs N, N+d, N+2d, N+3d inside the sorted list `kfull`.

    Strategy: for each pair (a, b) with a < b in kfull, set d = b - a, N = a.
    Then check if N+2d = a + 2(b-a) = 2b-a and N+3d = 3b-2a both lie in kfull.

    Complexity: O(|kfull|^2) membership lookups, each via bisect (log).
    With |kfull|~650 for N ≤ 10^9, this is ~4e5 pairs, trivial.
    """
    s = set(kfull)
    hits = []
    for i, a in enumerate(kfull):
        for j in range(i + 1, len(kfull)):
            b = kfull[j]
            d = b - a
            c = 2 * b - a  # a + 2d
            if c not in s:
                continue
            e = 3 * b - 2 * a  # a + 3d
            if e not in s:
                continue
            coprime = math.gcd(a, d) == 1
            if coprime_only and not coprime:
                continue
            hits.append({
                "N": a,
                "d": d,
                "coprime": coprime,
                "terms": [a, b, c, e],
            })
    return hits


def split_coprime(hits: list[dict]) -> tuple[list[dict], list[dict]]:
    """Return (all, coprime_only)."""
    return hits, [h for h in hits if h["coprime"]]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-term", type=int, default=10**9,
                    help="Enumerate 3-full numbers up to this bound.")
    ap.add_argument("--output", type=str,
                    default="analysis/erdos672_k4_l3_search.json")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    kfull = enumerate_kfull(args.max_term, k=3)
    t_enum = time.time() - t0
    if args.verbose:
        print(f"Enumerated {len(kfull):,} 3-full numbers ≤ {args.max_term:,} "
              f"in {t_enum:.2f}s")
        print(f"First 10:  {kfull[:10]}")
        print(f"Last 5:    {kfull[-5:]}")

    t1 = time.time()
    hits = find_4term_aps(kfull, coprime_only=False)
    t_search = time.time() - t1
    if args.verbose:
        print(f"Found {len(hits)} 4-term APs (incl. non-coprime) in {t_search:.2f}s")

    coprime_hits = [h for h in hits if h["coprime"]]
    if args.verbose:
        print(f"Of those, {len(coprime_hits)} are coprime (gcd(N,d)=1)")

    payload = {
        "max_term": args.max_term,
        "k_fullness": 3,
        "num_3full": len(kfull),
        "enum_seconds": round(t_enum, 4),
        "search_seconds": round(t_search, 4),
        "aps_4term_all": hits,
        "aps_4term_coprime": coprime_hits,
        "first_few_3full": kfull[:50],
        "last_few_3full": kfull[-10:],
    }

    outpath = Path(args.output)
    outpath.parent.mkdir(parents=True, exist_ok=True)
    outpath.write_text(json.dumps(payload, indent=2))
    if args.verbose:
        print(f"Wrote {outpath}")

    # Print a brief summary
    print(f"max_term={args.max_term:,}  num_3full={len(kfull)}  "
          f"aps_all={len(hits)}  aps_coprime={len(coprime_hits)}")
    if hits:
        for h in hits[:10]:
            print(f"  N={h['N']} d={h['d']} coprime={h['coprime']} "
                  f"terms={h['terms']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
