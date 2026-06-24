#!/usr/bin/env python3
"""
Erdos 647 — Cunningham-chain residual witness scan.

Slot737 narrowed E647's failure region to exactly the Sophie-Germain Cunningham
chain configurations in [3000, 10^6]:
  n in [3000, 10^6], n ≡ 0 (mod 6), n-1 prime, q=(n-2)/2 prime,
  r=(q-1)/2 prime, p=(2q-1)/3 prime.

The slot737 Boolean exclusion (n-3 or n-4 witness) FAILS in exactly these cases
because both r and p are prime. There are 35 such cases.

GOAL: For each of these 35 n, find an explicit m < n with m + τ(m) > n+2,
i.e., σ₀(m) > n - m + 2. We try small offsets m = n-5, n-6, n-7, n-8, n-9, n-12,
and any other small candidates with high divisor count. Save the witness table.

Erdős 647 target inequality (impossibility direction): for every n > 24,
there exists m < n with m + σ₀(m) > n + 2. Equivalently σ₀(m) ≥ n + 3 - m.

Witness requirement for offset d := n - m: need σ₀(m) ≥ d + 3.
  d=5: σ₀(m) ≥ 8
  d=6: σ₀(m) ≥ 9
  d=7: σ₀(m) ≥ 10
  d=8: σ₀(m) ≥ 11
  d=9: σ₀(m) ≥ 12
  d=10: σ₀(m) ≥ 13
  d=12: σ₀(m) ≥ 15
  d=24: σ₀(m) ≥ 27
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from sympy import isprime, divisor_count


def sieve_primes(n: int):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(math.isqrt(n)) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return s


def tau(m: int) -> int:
    """Divisor count σ₀(m). Use sympy for accuracy."""
    return int(divisor_count(m))


def enumerate_cunningham_cases(bound_n: int = 1_000_000):
    """Return the list of Cunningham residual cases (n, q, r, p) in [3000, bound_n]."""
    sieve = sieve_primes(bound_n + 10)
    cases = []
    for n in range(3000, bound_n + 1, 6):
        if not sieve[n - 1]:
            continue
        q = (n - 2) // 2
        if q >= len(sieve) or not sieve[q]:
            continue
        # Slot737 Boolean exclusion failure case: r=(q-1)/2 prime AND p=(2q-1)/3 prime
        r = (q - 1) // 2
        p = (2 * q - 1) // 3
        if r < 2 or not isprime(r):
            continue
        if p < 2 or not isprime(p):
            continue
        cases.append((n, q, r, p))
    return cases


def find_witness(n: int, max_offset: int = 30):
    """
    Search m < n with m + τ(m) > n+2.
    Tries offsets d = 1..max_offset (m = n - d) and reports the smallest d
    such that σ₀(m) ≥ d + 3 (equivalently m + σ₀(m) ≥ n + 3 > n + 2).
    Returns (best_d, m, tau_m, slack) where slack = (m + τ(m)) - (n + 2) ≥ 1.
    """
    best = None  # tuple (d, m, tau_m, slack)
    for d in range(1, max_offset + 1):
        m = n - d
        if m <= 0:
            break
        t = tau(m)
        # Need m + t > n + 2  iff  t > d + 2  iff  t ≥ d + 3
        slack = (m + t) - (n + 2)
        if slack >= 1:
            if best is None or d < best[0]:
                best = (d, m, t, slack)
                # Note: we take the smallest valid d (closest m to n) for stability
                break
    return best


def main():
    BOUND_N = 1_000_000
    print(f"Enumerating Cunningham-chain Sophie residuals in [3000, {BOUND_N}].\n")
    cases = enumerate_cunningham_cases(BOUND_N)
    total = len(cases)
    print(f"Cunningham residual cases (slot737 Boolean exclusion fails): {total}\n")

    rows = []
    offset_counter: dict[int, int] = {}
    no_witness = []

    for (n, q, r, p) in cases:
        result = find_witness(n, max_offset=30)
        if result is None:
            no_witness.append({"n": n, "q": q, "r": r, "p": p})
            continue
        d, m, t, slack = result
        offset_counter[d] = offset_counter.get(d, 0) + 1
        rows.append({
            "n": n,
            "q": q,
            "r": r,
            "p": p,
            "m": m,
            "offset": d,
            "tau": t,
            "slack": slack,
        })

    print(f"{'n':>9} {'q':>8} {'r':>7} {'p':>8} {'m':>9} {'d':>3} {'tau':>4} {'slack':>5}")
    for row in rows:
        print(
            f"{row['n']:>9} {row['q']:>8} {row['r']:>7} {row['p']:>8} "
            f"{row['m']:>9} {row['offset']:>3} {row['tau']:>4} {row['slack']:>5}"
        )

    print("\n=== Offset histogram ===")
    for d in sorted(offset_counter.keys()):
        print(f"  d = n-{d:>2}: {offset_counter[d]} cases")
    print(f"\nTotal with witness: {len(rows)} / {total}")
    print(f"No witness found in [n-1, n-30]: {len(no_witness)}")
    if no_witness:
        print("  HARD CASES (no witness in offset range):")
        for w in no_witness:
            print(f"    {w}")

    # Save as JSON
    out_path = Path("/Users/patrickkavanagh/math/analysis/erdos647_cunningham_witnesses.json")
    out_path.parent.mkdir(exist_ok=True, parents=True)
    payload = {
        "description": (
            "Witness table for the 35 Cunningham-chain Sophie residuals of "
            "Erdős 647 in [3000, 10^6]. Slot737's Boolean exclusion "
            "¬Prime((q-1)/2) ∨ ¬Prime((2q-1)/3) fails for these n; both r and p are prime. "
            "For each case we provide an explicit witness m = n-d with σ₀(m) > d+2, "
            "so m + σ₀(m) > n+2."
        ),
        "bound_n": BOUND_N,
        "total_cases": total,
        "cases_with_witness": len(rows),
        "cases_without_witness": len(no_witness),
        "offset_histogram": offset_counter,
        "rows": rows,
        "no_witness": no_witness,
    }
    out_path.write_text(json.dumps(payload, indent=2))
    print(f"\nSaved witness table to {out_path}")


if __name__ == "__main__":
    main()
