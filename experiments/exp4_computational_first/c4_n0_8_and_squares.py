"""
EXP4 C4: Dive into the striking patterns from C3:
(a) n0=8 appears repeatedly as a starting point
(b) 30% of 3-APs have n1 as a perfect square
(c) Patterns within these special families

We're chasing the question: is there a hidden algebraic family for "many 3-APs start at 8"?
"""

import json
import bisect
import time
from math import gcd, isqrt
from collections import defaultdict, Counter

def factor(n):
    f = {}; m = n; p = 2
    while p*p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
        if p > 2 and p % 2 == 0: p += 1
    if m > 1: f[m] = f.get(m, 0) + 1
    return f

def fmt(n):
    return " * ".join(f"{p}^{e}" for p, e in sorted(factor(n).items()))

def golomb(n):
    f = factor(n); a, b = 1, 1
    for p, e in f.items():
        if e % 2 == 0: a *= p**(e//2)
        else: b *= p; a *= p**((e-3)//2)
    return (a, b)

# Load 3-APs
print("Loading 3-APs...")
all_3aps = []
with open("/Users/patrickkavanagh/math/experiments/exp4_computational_first/c2_all_3aps.txt") as f:
    for line in f:
        if line.startswith("#"): continue
        parts = line.strip().split()
        if len(parts) == 3:
            all_3aps.append(tuple(int(x) for x in parts))

# ============================================================
# A: Show all 3-APs starting at n0 = 8
# ============================================================
print("\n=== A: All 3-APs starting at n0=8 ===")
n0_8 = [ap for ap in all_3aps if ap[0] == 8]
print(f"Total: {len(n0_8)}")
for ap in n0_8[:50]:
    n0, n1, n2 = ap
    g0 = golomb(n0); g1 = golomb(n1); g2 = golomb(n2)
    print(f"  ({n0:>10}, {n1:>10}, {n2:>10})  d={n1-n0:>8}  fac1={fmt(n1)}  fac2={fmt(n2)}  golomb=(({g0[0]},{g0[1]}),({g1[0]},{g1[1]}),({g2[0]},{g2[1]}))")

# Pattern: when n0=8 and ... what relationship between n1 and n2?
# 8 + 2d = n2 means 2(n1-n0) = n2-n0, n1 = 4 + n2/2. Since n0=8 = 2^3, all 3-APs with n0=8 have n2 = 2(n1-4)
# Are these all in a Pell-like family?

# Look at n0=8 case: 2*n1 = 8 + n2, so n2 = 2n1 - 8.
# We need n1 powerful, n2 = 2n1-8 powerful.

# Let's collect ALL n1 such that both n1 and 2n1-8 are powerful, n1 > 8, n1 <= 10^11
print("\n--- For n0=8: list of (n1, n2=2n1-8) pairs where both are powerful ---")
print("    (also show n1 as a^2 b^3 and n2 factorization)")
for n1, n2 in [(p1, p2) for (p0, p1, p2) in n0_8]:
    g1 = golomb(n1); g2 = golomb(n2)
    print(f"    n1={n1} = {g1[0]}^2 * {g1[1]}^3 = {fmt(n1)}")
    print(f"    n2={n2} = {g2[0]}^2 * {g2[1]}^3 = {fmt(n2)}  (= 2*n1-8)")

# Bigger: also include up to 10^11 (we have full list up to 10^11)
import struct
print("\n--- Full search for n0=8 case up to n2 <= 10^11 ---")
DATA = "/Users/patrickkavanagh/math/experiments/exp4_computational_first/powerful_1e11.bin"
with open(DATA, "rb") as f:
    N_BOUND, count = struct.unpack("<QQ", f.read(16))
    powerful = list(struct.unpack(f"<{count}Q", f.read(count * 8)))
powerful_set = set(powerful)

# For each powerful n1 > 8, check if 2*n1 - 8 is powerful
n0_8_full = []
for n1 in powerful:
    if n1 < 9: continue
    n2 = 2*n1 - 8
    if n2 > N_BOUND: break
    if n2 in powerful_set:
        n0_8_full.append((8, n1, n2))
print(f"Total 3-APs starting at n0=8 with n2 <= 10^11: {len(n0_8_full)}")
print("\n--- The first 30 (sorted by n1) ---")
for ap in n0_8_full[:30]:
    n0, n1, n2 = ap
    g1 = golomb(n1); g2 = golomb(n2)
    s1 = "SQ" if isqrt(n1)**2 == n1 else "  "
    s2 = "SQ" if isqrt(n2)**2 == n2 else "  "
    print(f"  n1={n1:>14} [{s1}] = {g1[0]:>10}^2 * {g1[1]:>4}^3  || n2={n2:>14} [{s2}] = {g2[0]:>10}^2 * {g2[1]:>4}^3  || fac(n1)={fmt(n1)}  fac(n2)={fmt(n2)}")

# Key question: are these of the form (8, k^2 * something, 2*k^2*something-8)?
# Or is there a parametric family?

# Note: 2n1 - n2 = 8. Equivalent: n2 = 2n1 - 8.
# If n1 = a^2 * b^3, n2 = 2*a^2*b^3 - 8 must be powerful.

# Let's look at the multiplicative structure: is n2/4 = (n1-4)/2 always powerful or interesting?
print("\n--- Structural analysis: gcd(n0=8, n1, n2) and (n0/g, n1/g, n2/g) for n0=8 case ---")
gcd_dist = Counter()
norm_triples = Counter()
for ap in n0_8_full:
    g = gcd(gcd(ap[0], ap[1]), ap[2])
    gcd_dist[g] += 1
    norm = (ap[0]//g, ap[1]//g, ap[2]//g)
    norm_triples[norm] += 1
print(f"  gcd distribution: {dict(gcd_dist)}")
print(f"  Top 10 normalized triples: {norm_triples.most_common(10)}")

# Common normalized triples: are these all in known scaling families?
print("\n--- For each distinct normalized triple, count members ---")
for norm, count in norm_triples.most_common(30):
    print(f"    {norm}: {count} members")

# ============================================================
# B: Cases where n1 is a perfect square (largest pattern: 30% of all)
# ============================================================
print("\n\n=== B: 3-APs where n1 is a perfect square ===")
mid_sq = [ap for ap in all_3aps if isqrt(ap[1])**2 == ap[1]]
print(f"Total: {len(mid_sq)} of {len(all_3aps)} = {100*len(mid_sq)/len(all_3aps):.2f}%")

# In these cases, n1 = m^2 for some m. Then n0, n2 powerful and n0 + n2 = 2m^2.
# This is the SUM-OF-TWO-POWERFULS-EQUALS-2m^2 problem!
# This is closely related to the equation: x + y = 2m^2 where x, y are powerful.
# Famous: known to be solvable in many ways. The question is when n0, n2 are CONSECUTIVE.

# Compute: when n1 = m^2, distribution of (n0, n2) = (m^2 - d, m^2 + d) where both powerful.
print("\n--- For each (n1=m^2), how many d's give a valid 3-AP? ---")
m1_to_count = defaultdict(int)
for ap in mid_sq:
    m1 = isqrt(ap[1])
    m1_to_count[m1] += 1

# Sort by count
print("  Top 30 m values (n1 = m^2) by number of valid 3-APs:")
for m, count in sorted(m1_to_count.items(), key=lambda x: -x[1])[:30]:
    n1 = m*m
    fac1 = fmt(n1)
    print(f"    m={m}: n1={n1} = {fac1}, {count} valid (n0, n2) pairs")

# These m values: what's special about them? Check if m is heavily composite
print("\n--- For top m values, factor them ---")
for m, count in sorted(m1_to_count.items(), key=lambda x: -x[1])[:30]:
    print(f"    m={m}: factor(m) = {fmt(m) if m > 1 else '1'}, count = {count}")

# ============================================================
# C: When n0 = m^2 (perfect square) and n2 is something interesting
# ============================================================
print("\n\n=== C: 3-APs where n0 is a perfect square ===")
sq0 = [ap for ap in all_3aps if isqrt(ap[0])**2 == ap[0]]
print(f"Total: {len(sq0)} ({100*len(sq0)/len(all_3aps):.2f}%)")

# Show first 30 with their structure
print("\n--- First 30 with n0 = a^2 ---")
for ap in sq0[:30]:
    n0, n1, n2 = ap
    a0 = isqrt(n0)
    print(f"  ({n0}={a0}^2, {n1}={fmt(n1)}, {n2}={fmt(n2)})  d={n1-n0}")

# ============================================================
# D: When kernel triple is (1, 1, 1) — i.e. all three are perfect squares
# ============================================================
print("\n\n=== D: All three perfect squares (kernel (1,1,1)) ===")
all_sq = [ap for ap in all_3aps if all(isqrt(x)**2 == x for x in ap)]
print(f"Total: {len(all_sq)}")
print("\n--- All-square 3-APs are squares in AP. Show first 30 ---")
for ap in all_sq[:30]:
    n0, n1, n2 = ap
    a, b, c = isqrt(n0), isqrt(n1), isqrt(n2)
    print(f"  ({a}^2, {b}^2, {c}^2) = ({n0}, {n1}, {n2})  -- so {a}^2 + {c}^2 = 2*{b}^2")

# This is the classical "three squares in AP" problem!
# n0 = a^2, n1 = b^2, n2 = c^2 with a^2 + c^2 = 2*b^2.
# Solution: (a,b,c) = (b-k, b, b+k) where 2b^2 = (b-k)^2 + (b+k)^2 = 2b^2 + 2k^2... wait.
# a^2 + c^2 = 2b^2 means (b-a)(b+a) + (b-c)(b+c) = 2b^2 - ...
# Standard: a^2, b^2, c^2 in AP iff (a, b, c) = ... gives Pythagorean-like
# In fact, b^2 - a^2 = c^2 - b^2 means (b-a)(b+a) = (c-b)(c+b)
# Classical: there are infinitely many; parametrized by Pell-like equation x^2 - 2y^2 = -1 etc.

# ============================================================
# Save summary
# ============================================================
summary = {
    "n0_eq_8_count_total": len(n0_8_full),
    "n0_eq_8_first_30": n0_8_full[:30],
    "n0_eq_8_gcd_dist": dict(gcd_dist),
    "n0_eq_8_top_normalized_triples": [(str(k), v) for k, v in norm_triples.most_common(20)],
    "middle_square_count": len(mid_sq),
    "middle_square_pct": 100*len(mid_sq)/len(all_3aps),
    "first_square_count": len(sq0),
    "all_squares_count": len(all_sq),
    "all_squares_first_30": [(isqrt(ap[0]), isqrt(ap[1]), isqrt(ap[2])) for ap in all_sq[:30]],
}
with open("/Users/patrickkavanagh/math/experiments/exp4_computational_first/c4_results.json", "w") as f:
    json.dump(summary, f, indent=2, default=str)
print("\nSaved c4_results.json")
