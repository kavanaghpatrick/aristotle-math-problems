#!/usr/bin/env python3
"""
Erdős Problem 389 (original statement):

  For each n >= 1, does there exist k >= 1 such that
    n (n+1) ... (n+k-1)  divides  (n+k) (n+k+1) ... (n+2k-1) ?

This script searches for the *minimal* such k (when found within a cutoff).

Exact check is done by tracking prime-adic valuation differences
  d_p(k) = v_p(R_k) - v_p(L_k),
updated incrementally using smallest-prime-factor (SPF) factorizations.
"""

from __future__ import annotations

import argparse
from array import array
from dataclasses import dataclass


def spf_sieve(limit: int) -> array:
    """Return SPF table for 0..limit (spf[x] = smallest prime factor of x)."""
    if limit < 1:
        return array("I", [0])

    spf = array("I", [0]) * (limit + 1)
    spf[1] = 1
    for i in range(2, limit + 1):
        if spf[i] == 0:  # prime
            spf[i] = i
            if i <= limit // i:
                step = i
                start = i * i
                for j in range(start, limit + 1, step):
                    if spf[j] == 0:
                        spf[j] = i
    return spf


@dataclass
class DiffTracker:
    spf: array
    diff: dict[int, int]
    neg_count: int = 0

    def _bump(self, p: int, delta: int) -> None:
        old = self.diff.get(p, 0)
        new = old + delta

        if old < 0 <= new:
            self.neg_count -= 1
        elif old >= 0 > new:
            self.neg_count += 1

        if new == 0:
            self.diff.pop(p, None)
        else:
            self.diff[p] = new

    def add_factor(self, x: int, mult: int) -> None:
        """Add mult * v_p(x) to diff for each prime p."""
        while x > 1:
            p = int(self.spf[x])
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            self._bump(p, mult * e)


def minimal_k(n: int, k_max: int, spf: array | None = None) -> int | None:
    """
    Return the minimal k in [1, k_max] such that
      prod_{i=0..k-1} (n+i) divides prod_{i=0..k-1} (n+k+i),
    or None if no such k <= k_max is found.
    """
    if n < 1:
        raise ValueError("n must be >= 1")
    if k_max < 1:
        raise ValueError("k_max must be >= 1")

    if spf is None:
        limit = n + 2 * k_max + 1
        spf = spf_sieve(limit)
    elif len(spf) <= n + 2 * k_max + 1:
        raise ValueError("spf table too small for given n,k_max")
    t = DiffTracker(spf=spf, diff={})

    # k = 1: L1 = n, R1 = n+1
    t.add_factor(n + 1, +1)
    t.add_factor(n, -1)
    if t.neg_count == 0:
        return 1

    for k in range(1, k_max):
        # d(k+1) = d(k) + v(n+2k) + v(n+2k+1) - 2*v(n+k)
        t.add_factor(n + 2 * k, +1)
        t.add_factor(n + 2 * k + 1, +1)
        t.add_factor(n + k, -2)
        if t.neg_count == 0:
            return k + 1

    return None


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--nmax", type=int, default=15, help="compute for n=1..nmax")
    p.add_argument("--kmax", type=int, default=8_500_000, help="search k up to kmax")
    args = p.parse_args()

    print(f"Searching minimal k for n=1..{args.nmax} with k<= {args.kmax}")
    spf = spf_sieve(args.nmax + 2 * args.kmax + 1)
    for n in range(1, args.nmax + 1):
        k = minimal_k(n, args.kmax, spf=spf)
        print(f"n={n:2d}: k={k}")


if __name__ == "__main__":
    main()
