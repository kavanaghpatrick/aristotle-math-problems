"""
EXP4 C7: EFFICIENT Pell classification of consecutive 3-APs.

KEY FINDING from c4-c6: All 6 consecutive 3-APs reduce to 2 normalized triples:
  F1 normalized: (48, 49, 50) — but 48, 50 not powerful; only the SCALED versions are.
  F2 normalized: (182250, 182329, 182408) where:
    182250 = 2 * 3^6 * 5^3
    182329 = 7^2 * 61^2 = (7 * 61)^2 = 427^2
    182408 = 2^3 * 151^2
    Identity: 427^2 - 302^2 = (7*61)^2 - (2*151)^2 = 5^3 * 3^6 = 91125

NEW INSIGHT: F1 base (48, 49, 50): 49 = 7^2, AP gap = 1. The "powerful 3-AP" only emerges
when scaled by 36 = 6^2 (or 144 = 12^2 = 4*36). So F1 needs the GCD to be 36 to satisfy
"all three are powerful".

GENERAL SCHEMA: A powerful 3-AP comes from scaling an AP of integers (a, b, c) by some k^2.
The CONSECUTIVENESS condition is then much more restrictive.

CONJECTURE FROM DATA:
Every consecutive powerful 3-AP in F1 family has n0 = (6m)^2 * 48 for some m,
i.e. n0 = 1728 m^2 (since 6^2 * 48 = 36*48 = 1728), and m must satisfy a sparse condition.

Test: F1 instances are (1728, 1764, 1800) and (6912, 7056, 7200).
1728 = 1728 * 1, so m=1.
6912 = 1728 * 4 = 1728 * 2^2, so m=2.

ALL OTHER MULTIPLES (m^2 * 1728 for m in 3, 4, 5, ...): are these consecutive? Let's check m=3, 4, 5.
m=3: (15552, 15876, 16200). Check consecutiveness.
m=4: (27648, 28224, 28800). Check consecutiveness.
m=5: (43200, 44100, 45000). Check consecutiveness.

These should all be powerful 3-APs but NOT consecutive (intervening powerfuls).

Then ask: for what M values is m^2 * 1728 (or m^2 * 729000) consecutive?

This is the SHARPEST data-derived conjecture: characterize the set M = {m : F1 scaled by m^2 is consecutive}.
"""

import struct
import bisect
import time
from math import gcd, isqrt
from collections import defaultdict, Counter

DATA = "/Users/patrickkavanagh/math/experiments/exp4_computational_first/powerful_1e11.bin"
with open(DATA, "rb") as f:
    N_BOUND, count = struct.unpack("<QQ", f.read(16))
    powerful = list(struct.unpack(f"<{count}Q", f.read(count * 8)))
powerful_set = set(powerful)
powerful_sorted = sorted(powerful)

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
    return " * ".join(f"{p}^{e}" for p, e in sorted(factor(n).items())) if n > 1 else "1"

def is_powerful(n):
    if n < 1: return False
    return n in powerful_set or all(e >= 2 for e in factor(n).values())

def num_intervening(n0, n2, n1=None):
    """Count powerful numbers strictly between n0 and n2, excluding n1 if given."""
    if n2 > N_BOUND:
        return -1  # out of range
    lo = bisect.bisect_right(powerful_sorted, n0)
    hi = bisect.bisect_left(powerful_sorted, n2)
    inter = hi - lo
    if n1 is not None and lo <= bisect.bisect_left(powerful_sorted, n1) < hi:
        inter -= 1
    return inter

# ============================================================
# A: Test F1 family: (1728*m^2, 1764*m^2, 1800*m^2) for m=1..50
# ============================================================
print("=== A: F1 family (1728*m^2, 1764*m^2, 1800*m^2) ===")
print(f"  m | n_0      | n_1     | n_2      | intervening | consecutive?")
print(f"  --+----------+---------+----------+-------------+--------------")
for m in range(1, 50):
    n0 = 1728 * m * m
    n1 = 1764 * m * m
    n2 = 1800 * m * m
    if n2 > N_BOUND:
        break
    # First check all three are powerful
    if n0 not in powerful_set or n1 not in powerful_set or n2 not in powerful_set:
        # Some might fall out of powerful (e.g. m=3 gives 1728*9 = 15552 = 2^6 * 3^5 -- check)
        # 1728 * 9 = 15552 = 2^6 * 3^5. Both 2 (exp 6 >= 2) and 3 (exp 5 >= 2) powerful. So it IS powerful.
        # Hmm maybe 1764*9 = 15876 = ? 1764 = 2^2 * 3^2 * 7^2. * 9 = 2^2 * 3^4 * 7^2. Powerful.
        # 1800*9 = 16200 = 2^3 * 3^4 * 5^2. Powerful.
        # So we should be fine for prime m. But wait, m=2: 1728*4 = 6912 = 2^8 * 3^3 ✓.
        # Let me just check whether the triple is in our powerful set.
        print(f"  {m:3} | {n0:>10} | {n1:>10} | {n2:>10} | NOT IN P-SET")
        continue
    inter = num_intervening(n0, n2, n1)
    print(f"  {m:3} | {n0:>10} | {n1:>10} | {n2:>10} | {inter:>11} | {'YES' if inter == 0 else 'no'}")

# ============================================================
# B: Test F2 family: (729000*m, 729316*m, 729632*m) for m=1..50
# (Note: F2 SCALES BY m, not m^2 — because F2 base is already powerful)
# ============================================================
print("\n=== B: F2 family (729000*m, 729316*m, 729632*m) ===")
print(f"  m | n_0           | n_1           | n_2           | powerful? | intervening")
print(f"  --+---------------+---------------+---------------+-----------+------------")
for m in range(1, 50):
    n0 = 729000 * m
    n1 = 729316 * m
    n2 = 729632 * m
    if n2 > N_BOUND:
        break
    pow_check = (n0 in powerful_set, n1 in powerful_set, n2 in powerful_set)
    if not all(pow_check):
        print(f"  {m:3} | {n0:>13} | {n1:>13} | {n2:>13} | {pow_check} | -")
        continue
    inter = num_intervening(n0, n2, n1)
    print(f"  {m:3} | {n0:>13} | {n1:>13} | {n2:>13} | YES       | {inter}")

# ============================================================
# C: For F1, characterize which m give consecutive
# F1 instances are (1728*1, 1728*4) consecutive. Others non-consecutive.
# Hypothesis: consecutive iff m is a power of 2 less than some bound?
# Check: m=1, m=2, m=4, m=8, m=16, m=32, ...
# Actually F1 = (1728*1, 1764*1, 1800*1) and (1728*4, 1764*4, 1800*4) = (6912, 7056, 7200).
# m=4 was given. Is m=16 consecutive? 1728*16 = 27648, ..., would have n2 = 28800. Was this in the consec list?
# No -- our consec list is only the 6 above. So m=16 is NOT consecutive.
# So F1 is consecutive only for m=1 and m=2 (square scaling m^2 with m=1 → 1 and m=2 → 4).
# Wait, our parameterization is n0 = 1728*m^2 where 1728 = 48 * 6^2 = 48 * 36. So if m=1 we get 1728*1 = 1728. If m=2 we get 1728*4 = 6912.

print("\n=== C: F1 detailed check for m in {1, 2, 3, 4, 5} ===")
for m in [1, 2, 3, 4, 5]:
    n0 = 1728 * m * m
    n1 = 1764 * m * m
    n2 = 1800 * m * m
    if n2 > N_BOUND:
        break
    inter = num_intervening(n0, n2, n1)
    # Show intervening powerfuls
    lo = bisect.bisect_right(powerful_sorted, n0)
    hi = bisect.bisect_left(powerful_sorted, n2)
    p_list = powerful_sorted[lo:hi]
    inter_list = [p for p in p_list if p != n1]
    print(f"  m={m}: ({n0}, {n1}, {n2}), intervening = {inter_list[:20]}{'...' if len(inter_list)>20 else ''}")

# ============================================================
# D: Search for OTHER "base" powerful 3-APs (not F1, not F2) that have consec descendants
# ============================================================
# For each base powerful 3-AP B = (b0, b1, b2), check if k^2*B has consec descendants
# Take small base 3-APs (n0 < 1000) and check
print("\n=== D: All 'base' powerful 3-APs with n0 <= 1000 ===")
small_3aps = []
with open("/Users/patrickkavanagh/math/experiments/exp4_computational_first/c2_all_3aps.txt") as f:
    for line in f:
        if line.startswith("#"): continue
        parts = line.strip().split()
        if len(parts) == 3:
            ap = tuple(int(x) for x in parts)
            if ap[0] <= 1000:
                small_3aps.append(ap)

print(f"  {len(small_3aps)} small 3-APs with n0 <= 1000")
# For each, look up scaled descendants in our 3-AP set
import json
all_3aps = []
with open("/Users/patrickkavanagh/math/experiments/exp4_computational_first/c2_all_3aps.txt") as f:
    for line in f:
        if line.startswith("#"): continue
        parts = line.strip().split()
        if len(parts) == 3:
            all_3aps.append(tuple(int(x) for x in parts))
all_3aps_set = set(all_3aps)

# For each consecutive 3-AP, find its "primitive" base
consec = [
    (1728, 1764, 1800),
    (6912, 7056, 7200),
    (729000, 729316, 729632),
    (1458000, 1458632, 1459264),
    (2916000, 2917264, 2918528),
    (11664000, 11669056, 11674112),
]

# For each consec, find the smallest (n0', n1', n2') such that (n0, n1, n2) = k * (n0', n1', n2') for rational k.
print("\n=== E: 'Most primitive' base for each consecutive 3-AP ===")
for n0, n1, n2 in consec:
    g = gcd(gcd(n0, n1), n2)
    p0, p1, p2 = n0 // g, n1 // g, n2 // g
    print(f"  Original: ({n0}, {n1}, {n2})")
    print(f"  GCD: {g} = {fmt(g)}")
    print(f"  Primitive: ({p0}, {p1}, {p2}) — sum check: {p0+p2} == 2*{p1} = {2*p1}")
    print(f"    {p0} = {fmt(p0)}, {p1} = {fmt(p1)}, {p2} = {fmt(p2)}")

# ============================================================
# F: Search for OTHER base triples (p0, p1, p2) primitive (gcd=1) such that p0+p2=2p1 and EACH ki * (p0, p1, p2) for some k forms a powerful 3-AP that is consecutive.
# ============================================================
print("\n=== F: Search for 'primitive bases' that generate ANY consec descendants ===")
# Find all (a, b, c) primitive with a < b < c, b = (a+c)/2, gcd(a,b,c)=1, and EXISTS k s.t. (ka, kb, kc) is a consecutive powerful 3-AP.

# From the data above:
# F1 primitive: (48, 49, 50), but 48 and 50 are NOT powerful. So k must "powerify" them.
#   k * 48 powerful: 48 = 2^4 * 3. So k must absorb the lone 3. So k must contain 3 to odd power... no wait, 3 has exp 1, so k * 48 has v_3 = v_3(k) + 1. Need this >= 2, so v_3(k) >= 1.
#   k * 50 powerful: 50 = 2 * 5^2. So k must have v_2(k) + 1 >= 2, i.e., v_2(k) >= 1.
#   k * 49 powerful: 49 = 7^2 already powerful. Need v_7(k) != 1 (so v_7(k) = 0 or >= 2).
#   So k must be a multiple of 6 (containing 2 and 3 to power >= 1).
#   In fact: k = 6 * j^2 might work for some j; or k = 36, etc.
#   Check k=6: 6*48=288=2^5*3^2 powerful ✓; 6*49=294=2*3*7^2 NOT powerful (2 and 3 have exp 1).
#     So k=6 fails on n1=49 scaling.
#   k=36: 36*48=1728=2^6*3^3 ✓; 36*49=1764=2^2*3^2*7^2 ✓; 36*50=1800=2^3*3^2*5^2 ✓.
#   So k=36 works. And k=144 (=4*36) works. What about k=36*9 = 324?
#     324*48=15552=2^6*3^5 ✓; 324*49=15876=2^2*3^4*7^2 ✓; 324*50=16200=2^3*3^4*5^2 ✓.
#     So (15552, 15876, 16200) is a powerful 3-AP! Is it consecutive?
n0, n1, n2 = 15552, 15876, 16200
inter = num_intervening(n0, n2, n1)
print(f"  F1 with k=324: ({n0}, {n1}, {n2}), intervening = {inter}")
# Show what's in between
lo = bisect.bisect_right(powerful_sorted, n0)
hi = bisect.bisect_left(powerful_sorted, n2)
p_list = [p for p in powerful_sorted[lo:hi] if p != n1]
print(f"    intervening list: {p_list[:20]}")

# k=36*16=576: 576*48 = 27648, 576*49 = 28224, 576*50 = 28800.
n0, n1, n2 = 27648, 28224, 28800
inter = num_intervening(n0, n2, n1)
print(f"  F1 with k=576: ({n0}, {n1}, {n2}), intervening = {inter}")
lo = bisect.bisect_right(powerful_sorted, n0)
hi = bisect.bisect_left(powerful_sorted, n2)
p_list = [p for p in powerful_sorted[lo:hi] if p != n1]
print(f"    intervening list: {p_list[:20]}")

# ============================================================
# G: Final classification: all consec from F1 and F2 ONLY, where k matches very specific form
# F1: k = 36 * j^2 for j in {1, 2}.  Why only 1, 2 and not 3, 4, ...?
# F2: k = m for m in {1, 2, 4, 16}.  Why only these?
# ============================================================
# Let me list all F2 scalings up to bound and check intervening counts
print("\n=== G: F2 scaled by all m up to 200, full intervening counts ===")
f2_base = (729000, 729316, 729632)
f2_results = []
for m in range(1, 200):
    n0, n1, n2 = (m*x for x in f2_base)
    if n2 > N_BOUND:
        break
    # all powerful?
    all_pow = all(p in powerful_set for p in (n0, n1, n2))
    if not all_pow:
        f2_results.append((m, n0, n1, n2, None, "not all powerful"))
        continue
    inter = num_intervening(n0, n2, n1)
    f2_results.append((m, n0, n1, n2, inter, "ok"))

print("  m | n0 (=729000m) | n1 (=729316m) | n2 (=729632m) | intervening | note")
for m, n0, n1, n2, inter, note in f2_results[:50]:
    if inter == 0:
        marker = "*** CONSEC ***"
    elif inter is None:
        marker = "BAD"
    else:
        marker = ""
    print(f"  {m:>3} | {n0:>13} | {n1:>13} | {n2:>13} | {str(inter):>11} | {note} {marker}")

# m=1, 2, 4, 16 consec (per our data) -- verify
# Are there OTHER m's that give consec?

# Save consec subset of F2
f2_consec = [r for r in f2_results if r[4] == 0]
print(f"\nF2 m values yielding consecutive: {[r[0] for r in f2_consec]}")
