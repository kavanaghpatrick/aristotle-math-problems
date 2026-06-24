#!/usr/bin/env python3
"""
Erdős 203 — Quotient Lift Analysis from slot740

Slot740 found m = 1579554969991861182625270235031094424159694 such that for every
cell (k,l) in [0,8)^2, some index-1 prime p ≤ 500 divides 2^k · 3^l · m + 1.

The question: does this 8×8 finite witness lift to an infinite Z^2 cover?

Method:
  1. Find all index-1 primes p with 3 < p ≤ 500 (i.e., <2,3> = (Z/pZ)*).
  2. For each such p, identify which (k,l) cells in [0,8)^2 satisfy
     p | 2^k · 3^l · m + 1. The primes that catch at least one cell are
     the "cover primes" — among them Aristotle's greedy cover of 22 lives.
  3. For each cover prime p, compute ord_p(2) and ord_p(3), and the set
     of "shadow cells" (k mod ord_p(2), l mod ord_p(3)) where
     2^k · 3^l · m ≡ -1 (mod p).
  4. Compute K = lcm(ord_p(2)) and L = lcm(ord_p(3)).
  5. Lift each prime's shadow to the K×L quotient grid (the shadow tiles
     by its period). Ask: is the union of lifts equal to ALL of K×L?
       YES => slot740 lifts to infinite Erdős 203 witness.
       NO  => slot740 is a finite-grid artifact.

Author: agent#1 (May 30 2026, June 1-7 batch prep)
"""

import json
import math
from pathlib import Path
from sympy import isprime, primerange, mod_inverse

M = 1579554969991861182625270235031094424159694
GRID = 8  # finite witness verified on [0, GRID)^2


def multiplicative_order(a: int, p: int) -> int:
    """ord_p(a): smallest e ≥ 1 with a^e ≡ 1 (mod p). Requires gcd(a,p)=1."""
    a = a % p
    if a == 0:
        raise ValueError(f"a={a} divisible by p={p}")
    # ord divides p-1
    n = p - 1
    # Find divisors of n in ascending order
    divs = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            divs.append(i)
            if i != n // i:
                divs.append(n // i)
        i += 1
    divs.sort()
    for d in divs:
        if pow(a, d, p) == 1:
            return d
    return n  # safety


def is_index1(p: int) -> bool:
    """Index-1 prime: <2,3> generates (Z/pZ)*, i.e. orders of 2 and 3 in
    (Z/pZ)* together generate the whole group, equivalently the subgroup
    generated has order p-1."""
    if p <= 3:
        return False
    o2 = multiplicative_order(2, p)
    o3 = multiplicative_order(3, p)
    # The subgroup <2,3> in cyclic Z/(p-1)Z has order lcm(o2, o3) ONLY if
    # we're inside a cyclic group: (Z/pZ)* IS cyclic of order p-1.
    return math.lcm(o2, o3) == p - 1


def cells_covered_by(p: int, m_mod_p: int, kmax: int = GRID, lmax: int = GRID):
    """Return list of (k, l) in [0,kmax) x [0,lmax) with 2^k * 3^l * m ≡ -1 (mod p)."""
    target = (-m_mod_p) % p  # we need 2^k * 3^l ≡ -1 / m ≡ -m^{-1} (mod p)
    # Actually: p | 2^k * 3^l * m + 1  <=>  2^k * 3^l * m ≡ -1 (mod p)
    # If gcd(m, p) > 1, p | m, then LHS ≡ 0, not -1 → no cover.
    if m_mod_p == 0:
        return []
    minv = mod_inverse(m_mod_p, p)
    target = (-minv) % p  # we want 2^k * 3^l ≡ -m^{-1} (mod p)
    cells = []
    # Precompute powers
    pow2 = [pow(2, k, p) for k in range(kmax)]
    pow3 = [pow(3, l, p) for l in range(lmax)]
    for k in range(kmax):
        for l in range(lmax):
            if (pow2[k] * pow3[l]) % p == target:
                cells.append((k, l))
    return cells


def shadow_on_period(p: int, m_mod_p: int):
    """For prime p with m mod p = m_mod_p, compute the FULL set of
    (k mod ord_p(2), l mod ord_p(3)) where 2^k * 3^l * m ≡ -1 (mod p).
    Returns (o2, o3, shadow_cells) with shadow_cells a set of (a, b)
    with a in [0,o2), b in [0,o3).
    """
    o2 = multiplicative_order(2, p)
    o3 = multiplicative_order(3, p)
    if m_mod_p == 0:
        return o2, o3, set()
    minv = mod_inverse(m_mod_p, p)
    target = (-minv) % p
    shadow = set()
    pow2 = [pow(2, k, p) for k in range(o2)]
    pow3 = [pow(3, l, p) for l in range(o3)]
    for k in range(o2):
        for l in range(o3):
            if (pow2[k] * pow3[l]) % p == target:
                shadow.add((k, l))
    return o2, o3, shadow


def main():
    print("=" * 70)
    print("Erdős 203 — Quotient Lift Analysis")
    print(f"m = {M}")
    print(f"Grid verified: [0,{GRID})^2")
    print("=" * 70)

    # Step 1: enumerate index-1 primes 3 < p ≤ 500.
    print("\n[1] Enumerating index-1 primes 3 < p ≤ 500 ...")
    index1_primes = []
    for p in primerange(5, 501):
        if is_index1(p):
            index1_primes.append(p)
    print(f"  Found {len(index1_primes)} index-1 primes ≤ 500")

    # Step 2: for each index-1 prime, find which 8×8 cells it catches.
    print("\n[2] Identifying cover primes (those that catch ≥1 cell on 8×8) ...")
    cover_primes = []  # list of (p, m_mod_p, cells_caught)
    for p in index1_primes:
        mp = M % p
        cells = cells_covered_by(p, mp, GRID, GRID)
        if cells:
            cover_primes.append((p, mp, cells))

    print(f"  Cover primes that catch ≥1 cell: {len(cover_primes)}")
    print("  Primes used as cover witnesses:")
    primes_only = sorted({p for p, _, _ in cover_primes})
    for p in primes_only:
        print(f"    p = {p}")

    # Verify the 8×8 grid is fully covered.
    covered_cells = set()
    for p, mp, cells in cover_primes:
        covered_cells.update(cells)
    full_grid = {(k, l) for k in range(GRID) for l in range(GRID)}
    missing = full_grid - covered_cells
    print(f"\n  8×8 cells covered: {len(covered_cells)}/64")
    if missing:
        print(f"  MISSING: {sorted(missing)}")
    else:
        print("  ✓ Full 8×8 grid covered (matches slot740 native_decide).")

    # Step 3: compute periodic shadows
    print(f"\n[3] Computing periodic shadows on quotient (Z/ord_p(2)) × (Z/ord_p(3)) ...")
    cover_data = []
    for p, mp, cells8 in cover_primes:
        o2, o3, shadow = shadow_on_period(p, mp)
        cover_data.append({
            "p": p,
            "m_mod_p": mp,
            "ord2": o2,
            "ord3": o3,
            "shadow_cells_on_period": sorted(shadow),
            "shadow_size": len(shadow),
            "period_size": o2 * o3,
            "cells_on_8x8": sorted(cells8),
        })
        print(f"  p={p:>3d}: ord_p(2)={o2:>4d}, ord_p(3)={o3:>4d}, "
              f"shadow size={len(shadow):>3d}/{o2*o3} on period")

    # Step 4: compute K, L
    K = 1
    L = 1
    for d in cover_data:
        K = math.lcm(K, d["ord2"])
        L = math.lcm(L, d["ord3"])
    print(f"\n[4] Quotient periods:")
    print(f"    K = lcm(ord_p(2)) = {K}")
    print(f"    L = lcm(ord_p(3)) = {L}")
    print(f"    K × L = {K*L}")

    # Step 5: lift each shadow to the K×L quotient grid (or determine if too big)
    # The cover in K×L is the union over p of:
    #   {(k, l) : 0 ≤ k < K, 0 ≤ l < L, (k mod ord_p(2), l mod ord_p(3)) ∈ shadow_p}
    # If K×L is too large to enumerate, we check via inclusion-exclusion of complements,
    # or we directly bound from below by uncovered residues.
    print(f"\n[5] Testing quotient cover ...")

    KL = K * L
    LIFT_LIMIT = 50_000_000  # safe enumeration ceiling
    result = {
        "m": str(M),
        "grid_size": GRID,
        "num_index1_primes_le_500": len(index1_primes),
        "cover_primes": primes_only,
        "num_cover_primes": len(primes_only),
        "K": K,
        "L": L,
        "KL": KL,
        "cover_data": cover_data,
    }

    if KL <= LIFT_LIMIT:
        # Enumerate.
        covered_on_KL_count = 0
        # For efficiency, for each (k,l) in K×L, test each prime's shadow membership.
        # Total work: K*L*|cover_primes|.
        # 50M * 22 ≈ 1.1B; too slow in Python.
        # Better: compute the UNION incrementally.
        # Use a bytearray bitmap.
        covered_bitmap = bytearray((KL + 7) // 8)

        def setbit(idx):
            covered_bitmap[idx >> 3] |= (1 << (idx & 7))

        def getbit(idx):
            return (covered_bitmap[idx >> 3] >> (idx & 7)) & 1

        for d in cover_data:
            o2 = d["ord2"]
            o3 = d["ord3"]
            for (a, b) in d["shadow_cells_on_period"]:
                # Lift: all (k, l) in K×L with k ≡ a (mod o2), l ≡ b (mod o3).
                # k loop: a, a+o2, a+2*o2, ..., < K
                k = a
                while k < K:
                    l = b
                    base = k * L
                    while l < L:
                        setbit(base + l)
                        l += o3
                    k += o2

        # Count uncovered
        covered_count = 0
        for byte in covered_bitmap:
            covered_count += bin(byte).count("1")
        uncovered_count = KL - covered_count
        print(f"    Covered: {covered_count}/{KL}")
        print(f"    Uncovered: {uncovered_count}")

        result["covered_count"] = covered_count
        result["uncovered_count"] = uncovered_count
        result["full_cover"] = (uncovered_count == 0)

        if uncovered_count == 0:
            print("    ✓✓✓ FULL QUOTIENT COVERED — slot740 LIFTS to infinite witness!")
            result["verdict"] = "YES_LIFTS"
        else:
            print("    ✗ NOT covered — slot740 is a finite-grid artifact.")
            # Sample some uncovered cells
            uncovered_samples = []
            for idx in range(KL):
                if not getbit(idx) and len(uncovered_samples) < 20:
                    uncovered_samples.append([idx // L, idx % L])
                if len(uncovered_samples) >= 20:
                    break
            result["uncovered_samples"] = uncovered_samples
            print(f"    Sample uncovered (k,l): {uncovered_samples[:10]}")
            result["verdict"] = "NO_FINITE_ARTIFACT"
    else:
        print(f"    K×L = {KL} too large to enumerate (>{LIFT_LIMIT}).")
        # Lower-bound check: count UNIQUE shadow density.
        # For a prime p, its lift to K×L covers exactly |shadow_p| * (K/o2) * (L/o3)
        # = |shadow_p| * K*L / (o2*o3) cells.
        # But these overlap with other primes' lifts, so the union is at most sum.
        total_density = 0.0
        for d in cover_data:
            density = d["shadow_size"] / d["period_size"]
            total_density += density
            print(f"      p={d['p']:>3d}: shadow density = {density:.6f}")
        print(f"    Upper bound on coverage fraction: {total_density:.4f}")
        result["total_shadow_density_upper_bound"] = total_density
        result["full_cover"] = total_density >= 1.0  # necessary condition
        if total_density < 1.0:
            print("    ✗ DENSITY UPPER BOUND < 1 — slot740 CANNOT lift; finite-grid artifact.")
            result["verdict"] = "NO_FINITE_ARTIFACT_DENSITY"
        else:
            print("    ? Density sum ≥ 1, but K×L too big to confirm full cover.")
            result["verdict"] = "INCONCLUSIVE_TOO_LARGE"

    # Save JSON
    out_json = Path("/Users/patrickkavanagh/math/analysis/erdos203_quotient_lift_may30.json")
    out_json.parent.mkdir(parents=True, exist_ok=True)
    with open(out_json, "w") as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\n[6] JSON written: {out_json}")

    return result


if __name__ == "__main__":
    main()
