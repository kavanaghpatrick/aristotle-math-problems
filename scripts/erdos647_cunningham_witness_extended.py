#!/usr/bin/env python3
"""
Erdos 647 Cunningham residual: EXTENDED witness search.

Hedge for agent #3. Agent #3 tries small offsets m = n-3, n-4, ..., n-12.
We extend the search to ALL m < n and find the witness with MAXIMUM tau(m).

Erdos 647 conjecture (Sophie subclass) inequality:
  m + tau(m) > n + 2,  where tau = sigma_0 = #divisors.

Equivalently: tau(m) > n + 2 - m, i.e., tau(m) >= n + 3 - m.

A witness exists iff there exists m < n with tau(m) >= n + 3 - m.

This script enumerates the same 35 Cunningham-chain cases as
scripts/erdos647_sophie_scan2.py, and for each n:
  - records tau(n-k) for k in {5, 6, 8, 9}
  - searches all m < n for the witness with maximum tau(m) and reports it
  - reports max tau(m) - (n+3-m), the "witness slack"; if >= 0, m is a witness
"""

import json
import math
from pathlib import Path

from sympy import isprime, divisor_count


REPO = Path(__file__).resolve().parent.parent
OUT_JSON = REPO / "analysis" / "erdos647_cunningham_extended_table.json"


def sieve_primes(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(math.isqrt(n)) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return s


def tau(m: int) -> int:
    """Number of divisors of m (sigma_0)."""
    return int(divisor_count(m))


def find_cunningham_cases(bound_n=1_000_000):
    """Reproduce scripts/erdos647_sophie_scan2.py case enumeration."""
    sieve = sieve_primes(bound_n + 10)
    cases = []
    for n in range(3000, bound_n + 1, 6):
        if not sieve[n - 1]:
            continue
        q = (n - 2) // 2
        if q >= len(sieve) or not sieve[q]:
            continue
        r = (q - 1) // 2
        p = (2 * q - 1) // 3
        # Cunningham case: r prime AND p prime
        if (r >= 2 and isprime(r)) and (p > 1 and isprime(p)):
            cases.append({"n": n, "q": q, "r": r, "p": p})
    return cases


def max_tau_witness(n: int):
    """
    Search all m in [2, n-1] for max tau(m) and find first m with
    tau(m) >= n + 3 - m (a witness).
    Returns (best_m, best_tau, witness_m, witness_tau) where witness_* are
    None if no witness exists.
    """
    best_m, best_tau = 0, 0
    witness_m, witness_tau = None, None
    # Search downward from n-1 (typically witnesses live near n)
    for m in range(n - 1, 1, -1):
        t = tau(m)
        if t > best_tau:
            best_m, best_tau = m, t
        # Witness check: tau(m) >= n + 3 - m
        if witness_m is None and t >= n + 3 - m:
            witness_m, witness_tau = m, t
        # Early exit: if best_tau is already very high and we're far from n,
        # later m can still beat it but the loop is small enough (n <= 10^6)
        # to just run to completion for accuracy.
    return best_m, best_tau, witness_m, witness_tau


def tau_at(n, k):
    """tau(n - k) and slack (>= 0 means witness)."""
    m = n - k
    if m < 2:
        return None
    t = tau(m)
    needed = k + 3
    return {"m": m, "tau": t, "needed": needed, "slack": t - needed,
            "is_witness": t >= needed}


def main():
    print("Erdos 647 Cunningham residual: extended witness search\n")

    cases = find_cunningham_cases()
    print(f"Cunningham cases found: {len(cases)}\n")

    rows = []
    no_witness_cases = []
    cases_needing_large_offset = []
    cases_covered_by_small_offset = []

    for case in cases:
        n = case["n"]
        row = {
            "n": n,
            "q": case["q"],
            "r": case["r"],
            "p": case["p"],
        }
        # Small offsets (per agent #3's approach)
        for k in (5, 6, 7, 8, 9, 10, 11, 12):
            info = tau_at(n, k)
            row[f"n-{k}"] = info

        # Max tau over all m < n
        bm, bt, wm, wt = max_tau_witness(n)
        row["max_tau"] = {"m": bm, "tau": bt}
        if wm is None:
            row["witness"] = None
            no_witness_cases.append(case)
        else:
            row["witness"] = {"m": wm, "tau": wt, "offset_from_n": n - wm,
                              "slack": wt - (n + 3 - wm)}
            small_offset_covered = any(
                row[f"n-{k}"] and row[f"n-{k}"]["is_witness"]
                for k in (5, 6, 7, 8, 9, 10, 11, 12)
            )
            if small_offset_covered:
                cases_covered_by_small_offset.append(case)
            else:
                cases_needing_large_offset.append({**case, "witness": row["witness"]})

        rows.append(row)
        print(
            f"n={n:>9} q={case['q']:>8} | n-5: tau={row['n-5']['tau']:>3} (witness? {row['n-5']['is_witness']}) | "
            f"n-6: tau={row['n-6']['tau']:>3} ({row['n-6']['is_witness']}) | "
            f"n-8: tau={row['n-8']['tau']:>3} ({row['n-8']['is_witness']}) | "
            f"n-9: tau={row['n-9']['tau']:>3} ({row['n-9']['is_witness']}) | "
            f"witness: m={row['witness']['m'] if row['witness'] else None} "
            f"tau={row['witness']['tau'] if row['witness'] else None} "
            f"offset={(n - row['witness']['m']) if row['witness'] else None}"
        )

    summary = {
        "total_cunningham_cases": len(cases),
        "cases_with_no_witness": len(no_witness_cases),
        "cases_covered_by_small_offset_k_le_12": len(cases_covered_by_small_offset),
        "cases_needing_large_offset_k_gt_12": len(cases_needing_large_offset),
        "max_offset_among_witnesses": max(
            (n - r["witness"]["m"]) for r in rows
            for n in [r["n"]] if r["witness"] is not None
        ) if any(r["witness"] for r in rows) else None,
        "max_tau_among_witnesses": max(
            r["witness"]["tau"] for r in rows if r["witness"]
        ) if any(r["witness"] for r in rows) else None,
    }

    print("\n=== SUMMARY ===")
    for k, v in summary.items():
        print(f"  {k}: {v}")

    if no_witness_cases:
        print("\n=== CASES WITH NO WITNESS (case C: counterexample alert) ===")
        for c in no_witness_cases:
            print(f"  n={c['n']} q={c['q']} r={c['r']} p={c['p']}")

    if cases_needing_large_offset:
        print(f"\n=== CASES NEEDING m < n - 12 (case B) ===")
        for c in cases_needing_large_offset[:10]:
            w = c["witness"]
            print(f"  n={c['n']:>9}  witness m={w['m']} (offset {c['n'] - w['m']}) tau={w['tau']}")

    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    with open(OUT_JSON, "w") as f:
        json.dump({
            "summary": summary,
            "no_witness_cases": no_witness_cases,
            "cases_needing_large_offset": cases_needing_large_offset,
            "rows": rows,
        }, f, indent=2)
    print(f"\nWrote {OUT_JSON}")


if __name__ == "__main__":
    main()
