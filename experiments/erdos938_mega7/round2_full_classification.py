"""
MEGA-7 Round 2: Classify ALL consecutive powerful 3-APs by their structural family.

Sieve up to 10^10, identify all consecutive powerful 3-APs, then for each one:
1. Compute its "primitive base" (reduce by gcd structure)
2. Check if it's a scaling of a known smaller AP
3. Identify the underlying Pell equation (if any)
"""

import math
from math import gcd, isqrt
import time

def is_powerful(n: int) -> bool:
    if n < 1: return False
    if n == 1: return True
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if e < 2:
                return False
        p += 1
    return m == 1

def factor(n: int) -> dict:
    if n <= 1: return {}
    f = {}
    m = n
    p = 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def fmt_factor(n):
    return " * ".join(f"{p}^{e}" for p, e in sorted(factor(n).items()))

def is_square(n):
    if n < 0: return False
    r = isqrt(n)
    return r*r == n

def golomb(n: int):
    """Write powerful n = a^2 * b^3 with b squarefree.
       For each prime p, exponent e_p: e_p mod 3 determines power of p in b, then quotient gives a's contribution."""
    f = factor(n)
    a_pow = {}
    b_pow = {}
    for p, e in f.items():
        # b absorbs 3*floor((e_p - 2)/2 / 3)?  Actually Golomb: b = product p^(e_p mod 2) ... need rad-divisibility.
        # Standard Golomb: write n = a^2 b^3 with rad(b) | rad(a). So for each prime p with e_p:
        # if e_p is even, b contributes 0 (or rad-divisible), a contributes e_p / 2.
        # if e_p is odd, b contributes 1, a contributes (e_p - 3)/2.
        # But e_p >= 2 (powerful), so e_p in {2, 3, 4, 5, ...}.
        if e % 2 == 0:
            b_pow[p] = 0
            a_pow[p] = e // 2
        else:
            b_pow[p] = 1
            a_pow[p] = (e - 3) // 2
    a = 1
    for p, e in a_pow.items():
        a *= p ** e
    b = 1
    for p, e in b_pow.items():
        b *= p ** e
    assert a * a * b * b * b == n, f"Golomb failed for {n}: a={a}, b={b}"
    return (a, b)

def powerful_sieve(N: int):
    powerful = set([1])
    b = 1
    while b * b * b <= N:
        a = 1
        while (a * a) * (b * b * b) <= N:
            n = (a * a) * (b * b * b)
            if is_powerful(n):
                powerful.add(n)
            a += 1
        b += 1
    return sorted(powerful)

N_BOUND = 10**10
print(f"Building powerful sieve up to {N_BOUND}...")
t0 = time.time()
powerful = powerful_sieve(N_BOUND)
t1 = time.time()
print(f"  {len(powerful)} powerful numbers, in {t1-t0:.1f}s")
powerful_set = set(powerful)

# Find all consecutive powerful 3-APs
print("\nSearching for consecutive powerful 3-APs...")
consec_3aps = []
for i in range(len(powerful) - 2):
    n0, n1, n2 = powerful[i], powerful[i+1], powerful[i+2]
    if 2 * n1 == n0 + n2:
        consec_3aps.append((n0, n1, n2))

print(f"  Found {len(consec_3aps)} consecutive powerful 3-APs up to {N_BOUND}.")

# Classify
print("\n" + "=" * 80)
print("CLASSIFICATION OF CONSECUTIVE POWERFUL 3-APs")
print("=" * 80)

for i, ap in enumerate(consec_3aps):
    n0, n1, n2 = ap
    d = n1 - n0
    g = gcd(gcd(n0, n1), n2)
    nm = (n0//g, n1//g, n2//g)
    print(f"\nAP{i+1}: ({n0}, {n1}, {n2}) gap={d}")
    print(f"  Factorizations:")
    print(f"    n_k   = {fmt_factor(n0)}")
    print(f"    n_k+1 = {fmt_factor(n1)}")
    print(f"    n_k+2 = {fmt_factor(n2)}")
    print(f"  Golomb forms: (a, b):")
    a0, b0 = golomb(n0); print(f"    n_k:   a={a0}, b={b0}  (n = a^2 * b^3 = {a0**2 * b0**3})")
    a1, b1 = golomb(n1); print(f"    n_k+1: a={a1}, b={b1}  (n = a^2 * b^3 = {a1**2 * b1**3})")
    a2, b2 = golomb(n2); print(f"    n_k+2: a={a2}, b={b2}  (n = a^2 * b^3 = {a2**2 * b2**3})")
    print(f"  Kernel triple (b0, b1, b2) = ({b0}, {b1}, {b2})")
    is_sq = [is_square(n0), is_square(n1), is_square(n2)]
    print(f"  Square pattern: {is_sq}")
    print(f"  GCD={g}, normalized: ({nm[0]}, {nm[1]}, {nm[2]})")

# Now identify scaling families
print("\n" + "=" * 80)
print("FAMILY CLUSTERING")
print("=" * 80)

# Two APs (A0, A1, A2) and (B0, B1, B2) are in same family if (A0, A1, A2) = k * (B0, B1, B2)
# for some rational k. Equivalent: A0/B0 = A1/B1 = A2/B2 as rationals.
# i.e., A0 * B1 = A1 * B0 etc. Actually, we want to know if there's a scale factor.

families = []  # list of (representative_ap, list_of_aps_in_family)
for ap in consec_3aps:
    matched = False
    for fam_idx, (rep, members) in enumerate(families):
        # Check if ap is rational scaling of rep
        # ap[i] = rep[i] * (p/q) for fixed p, q
        # equivalently: ap[0] * rep[1] == ap[1] * rep[0] AND ap[0] * rep[2] == ap[2] * rep[0]
        if ap[0] * rep[1] == ap[1] * rep[0] and ap[0] * rep[2] == ap[2] * rep[0]:
            members.append(ap)
            matched = True
            break
    if not matched:
        families.append((ap, [ap]))

print(f"\nNumber of distinct families: {len(families)}")
for i, (rep, members) in enumerate(families):
    print(f"\nFamily {i+1}: representative {rep}")
    print(f"  Members ({len(members)}):")
    for m in members:
        scale_n = m[0]
        scale_d = rep[0]
        # Reduce
        g = gcd(scale_n, scale_d)
        sn, sd = scale_n // g, scale_d // g
        print(f"    {m}  (scale = {sn}/{sd})")
