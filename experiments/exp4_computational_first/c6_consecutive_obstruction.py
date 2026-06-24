"""
EXP4 C6: For the 6 consecutive powerful 3-APs we found, analyze why they're SPECIAL.

Six consecutive 3-APs up to 10^11:
  (1728, 1764, 1800)    d=36
  (6912, 7056, 7200)    d=144
  (729000, 729316, 729632)   d=316
  (1458000, 1458632, 1459264) d=632
  (2916000, 2917264, 2918528) d=1264
  (11664000, 11669056, 11674112) d=5056

What's the structural common factor?

Goal: identify the smallest set of NECESSARY conditions for a powerful 3-AP to be consecutive.
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

# 6 consecutive 3-APs
consec = [
    (1728, 1764, 1800),
    (6912, 7056, 7200),
    (729000, 729316, 729632),
    (1458000, 1458632, 1459264),
    (2916000, 2917264, 2918528),
    (11664000, 11669056, 11674112),
]

# Verify they're consecutive
print("=== Verifying consecutiveness ===")
for n0, n1, n2 in consec:
    lo = bisect.bisect_right(powerful_sorted, n0)
    hi = bisect.bisect_left(powerful_sorted, n2)
    inter = hi - lo - 1
    print(f"  ({n0}, {n1}, {n2}): {inter} intervening (should be 0)")

# ============================================================
# A: Factorization signatures
# ============================================================
print("\n=== A: Factorization signatures ===")
for n0, n1, n2 in consec:
    print(f"  AP ({n0}, {n1}, {n2}):")
    print(f"    {n0} = {fmt(n0)}")
    print(f"    {n1} = {fmt(n1)}")
    print(f"    {n2} = {fmt(n2)}")
    g = gcd(gcd(n0, n1), n2)
    print(f"    GCD = {g} = {fmt(g)}")
    print(f"    Normalized: ({n0//g}, {n1//g}, {n2//g})")
    print(f"    sum of primes in n0, n1, n2: 2-exps={tuple(factor(x).get(2, 0) for x in (n0,n1,n2))}, 3-exps={tuple(factor(x).get(3, 0) for x in (n0,n1,n2))}, 5-exps={tuple(factor(x).get(5, 0) for x in (n0,n1,n2))}, 7-exps={tuple(factor(x).get(7, 0) for x in (n0,n1,n2))}, 11-exps={tuple(factor(x).get(11, 0) for x in (n0,n1,n2))}")
    print()

# ============================================================
# B: Two known families
# F1: based on (48, 49, 50) scaled by k^2 (Walker 1976)
# F2: based on (729000, 729316, 729632) scaled by m
# ============================================================
print("\n=== B: Family analysis ===")
# F1 base: (48, 49, 50) — is this a powerful 3-AP base?
# 48 = 2^4 * 3, NOT powerful (3 has exp 1).
# 49 = 7^2, powerful.
# 50 = 2 * 5^2, NOT powerful (2 has exp 1).
# So (48, 49, 50) is NOT a powerful 3-AP. Walker's "base" is (1728, 1764, 1800) = (48*36, 49*36, 50*36).
# This is multiplying by 36 = 6^2 (a square), and 36 is NOT a "kernel adjustment" but a perfect square multiplier.

print(f"F1 base check: 48 = {fmt(48)}, 49 = {fmt(49)}, 50 = {fmt(50)}")
print(f"  These are NOT all powerful, but they form an AP (49^2 = 48*50 + 1)")
print(f"  Scaled by 36 = 6^2: (1728, 1764, 1800) = (2^6*3^3, 2^2*3^2*7^2, 2^3*3^2*5^2)")
print(f"  Scaled by 144 = 12^2: (6912, 7056, 7200) = (2^8*3^3, 2^4*3^2*7^2, 2^5*3^2*5^2)")

# F2 base: (729000, 729316, 729632)
# 729000 = 2^3 * 3^6 * 5^3 = 8 * 729 * 125 = 729 * 1000
# 729316 = 2^2 * 7^2 * 61^2 -- 729316 / 4 = 182329 = 7 * 26047 = ? Let's verify.
print(f"\nF2 base check:")
for x in [729000, 729316, 729632]:
    print(f"  {x} = {fmt(x)}")
# 729000 = 2^3 * 3^6 * 5^3  (since 2^3=8, 3^6=729, 5^3=125, product = 8*729*125 = 729000 ✓)
# 729316 = ? Let me verify by factoring:
n = 729316
print(f"  729316 factored: ", end="")
f = factor(n)
for p, e in sorted(f.items()):
    print(f"{p}^{e}", end=" * ")
print()
# 729632 = ?
n = 729632
print(f"  729632 factored: ", end="")
f = factor(n)
for p, e in sorted(f.items()):
    print(f"{p}^{e}", end=" * ")
print()

# So F2 base = (2^3 * 3^6 * 5^3, 2^2 * (something)^2, 2^5 * ...)
# Connection to Pell: 729316 = 854^2, 729632 = 8 * 91204 = 2^5 * 22801 = 2^5 * 151^2
# So 729316 / 729632 = 854^2 / (32 * 151^2) = (854/151)^2 / 32 = ...
# The Pell equation: x^2 - 2y^2 = ? for (x, y) = (854, 151) gives 854^2 - 2*151^2 = 729316 - 45602 = 683714. Not -1.
# Let's try (x, y) = (854, ?): 854^2 - 729000 = 316, so 854^2 = 729316 = 729000 + 316.
# Note: gap d = 316. Coincidence? 854^2 = 729316.  And 729000 = 2^3 * 3^6 * 5^3.  Hmm.
# 2 * 854^2 = 1458632 = n1 of F2 doubled = 729316 * 2 = 1458632. So 2 * 854^2 = 1458632 ✓.
# And 729000 + 729632 = 1458632 = 2*729316 = 2 * 854^2 ✓ (AP check).

# So the Pell relation in F2: 854^2 = (729000 + 729632)/2 = 2^2 * 3^6 * 5^3 + 2^4 * 151^2 ... no this is messy.

# Cleaner: 729000 = 2*3^6*5^3 * 2^2 = ... let me try u = 729000/4 = 182250 = 2 * 3^6 * 5^3.
# Or: u = 729000 / 8 = 91125 = 3^6 * 5^3 = 729 * 125 = 91125. Yes.
# So n0 / 8 = 91125 = 3^6 * 5^3 (the MEGA-7 finding!).
# And n2 = 729632 / 8 = 91204 = 151^2. (Wait, 91204 / 4 = 22801, and 151^2 = 22801. So 729632 = 32 * 151^2 = 2^5 * 151^2.)
# Hmm: 729632 / 8 = 91204, and 91204 = 4 * 22801 = 4 * 151^2 = (2*151)^2 = 302^2. YES, 302^2 = 91204.
# Wait: 729632 / 4 = 182408, not 91204. Let me recompute. 729632 / 8 = 91204. 302^2 = 91204. Yes.
# So 729632 = 8 * 302^2 = 2^3 * 302^2 = 2^3 * (2*151)^2 = 2^3 * 4 * 151^2 = 2^5 * 151^2. CHECK.

# So:
#  n0 = 729000 = 8 * 91125 = 8 * 3^6 * 5^3
#  n1 = 729316 = 4 * 182329 = 4 * 427^2 = (2*427)^2 = 854^2. Hmm. So n1 is a perfect square.
#     427^2 = 182329. Then n1 = 4 * 427^2 = 854^2. So 854^2 / 8 = 91204/8 wait.
#     854^2 = 729316. So n1/4 = 182329 = 427^2.  Or n1 = 854^2.  Either way it's a square.
#  n2 = 729632 = 8 * 91204 = 8 * 302^2 = (sqrt(8) * 302)^2 = ... = 2^3 * 302^2 = 2^3 * 4 * 151^2 = 2^5 * 151^2.

# AP relation: 2 * 854^2 = 729000 + 729632 ⟹ 2 * 854^2 - 729632 = 729000
#  854^2 - 729632/2 = 729000/2 ⟹ 854^2 - 364816 = 364500.
#  Hmm. Try: 854^2 - 8 * 151^2 = 729316 - 8*22801 = 729316 - 182408 = 546908. Nope.
#  2 * 854^2 - 8 * 302^2 = 2*729316 - 8*91204 = 1458632 - 729632 = 729000. ⟹ 854^2 - 4*302^2 = 364500/... ugh

# Try the cleaner form: 854^2 = 4*427^2 → so n1 = 854^2 = 4*427^2.
#   Then n0 = 2*854^2 - n2 = 2*4*427^2 - 8*302^2 = 8*(427^2 - 302^2) = 8*(427-302)(427+302) = 8*125*729 = 8*5^3*3^6 ✓✓✓
#
# THE PELL DECOMPOSITION:  427^2 - 302^2 = 125 * 729 = 5^3 * 3^6.
#
# So the key identity is: there exist integers (a, b, c, d) with c^2 - d^2 = 5^3 * 3^6, here (c, d) = (427, 302).
# (c+d)(c-d) = 5^3 * 3^6 = 91125.
# 427 + 302 = 729 = 3^6.
# 427 - 302 = 125 = 5^3.
# So c+d = 3^6 and c-d = 5^3, hence c = (3^6 + 5^3)/2 = (729+125)/2 = 427 (integer iff 3^6+5^3 is even ⟹ both odd? 729 odd, 125 odd → sum even).
# And d = (3^6 - 5^3)/2 = (729 - 125)/2 = 302.

# THIS IS THE MEGA-7 FINDING! Verified independently from computational data alone.

print("\n=== F2 Pell decomposition (MEGA-7 finding re-derived from data) ===")
print(f"  n0 = 729000 = 8 * 5^3 * 3^6")
print(f"  n1 = 729316 = 4 * 427^2 = 854^2")
print(f"  n2 = 729632 = 8 * 302^2")
print(f"  Identity: 427^2 - 302^2 = 5^3 * 3^6 = 91125")
print(f"  Factorization: (427-302)(427+302) = 125 * 729 = 5^3 * 3^6")

# ============================================================
# C: Replicate the search for OTHER (powerful, m^2, powerful) consecutive 3-APs
# Looking for the same structure: n1 = m^2, n0 = 8 * powerful_form, n2 = 8 * powerful_form
# ============================================================
print("\n=== C: Generalized Pell search for consecutive 3-APs (n1 = square) ===")
print("We seek (a*x^2, m^2, a*y^2) consecutive powerful 3-APs.")
print("From the F2 structure: gcd constraint is unusual; n0/n2 ratio shows 3^6 * 5^3 structure.\n")
# Each consec_3AP, what is the gcd(n0, n2)?
for ap in consec:
    n0, n1, n2 = ap
    g_02 = gcd(n0, n2)
    g_01 = gcd(n0, n1)
    g_12 = gcd(n1, n2)
    print(f"  AP {ap}: gcd(n0,n2)={g_02}={fmt(g_02)}, gcd(n0,n1)={g_01}={fmt(g_01)}, gcd(n1,n2)={g_12}={fmt(g_12)}")
    # n0 - n2 = -2d, n0+n2 = 2n1, n0*n2 = ?
    print(f"    n0+n2 = {n0+n2} = 2*n1 = {2*n1}")
    print(f"    n2-n0 = {n2-n0} = 2*d = {2*(n1-n0)}")
    print(f"    n0*n2 = {n0*n2}")
    # difference of two squares
    sq_n1 = isqrt(n1)
    if sq_n1 * sq_n1 == n1:
        print(f"    n1 = {sq_n1}^2 -- so n0, n2 sum to 2*{sq_n1}^2")
        # Try to write n2 - n0 = 2d as factor structure
        # n0 = sq_n1^2 - d, n2 = sq_n1^2 + d
        # If n0, n2 both powerful, what's d?

print("\n=== D: Is n1 always a perfect square for consecutive 3-APs? ===")
for ap in consec:
    n1 = ap[1]
    s = isqrt(n1)
    print(f"  n1 = {n1}, sqrt = {s}, is square? {s*s == n1}")

# F1 = (1728, 1764, 1800) → n1=1764=42^2. YES.
# F1 = (6912, 7056, 7200) → n1=7056=84^2. YES.
# F2 = (729000, 729316, 729632) → n1=729316=854^2. YES.
# F2 = (1458000, 1458632, 1459264) → n1=1458632 = ? sqrt(1458632) = 1207.7... NOT square.
# But wait, F2's middle terms should be... let me check.

# Actually: F2's second member is (1458000, 1458632, 1459264).
# n1 = 1458632. isqrt = 1207. 1207^2 = 1456849. NO.
# Hmm, so this consecutive 3-AP does NOT have n1 a perfect square!

# Re-verify factorization
n = 1458632
print(f"\n  {n} factored: {fmt(n)}")
n = 1458000
print(f"  {n} factored: {fmt(n)}")
n = 1459264
print(f"  {n} factored: {fmt(n)}")
# 1458632 = 2^3 * 7^2 * 61^2 ? or 2^3 * 182329 = 8 * 182329 = 8 * 427^2  -- so 1458632 = 8 * 427^2

# Yes: 1458632 / 8 = 182329 = 427^2. So 1458632 = 2 * 729316 = 2 * 854^2. NOT a square.

print(f"\nSo F2 scaling by m=2: 729316 * 2 = 1458632 = 2 * 854^2. NOT a perfect square.")
print(f"So not all consecutive APs have square middle term.")
