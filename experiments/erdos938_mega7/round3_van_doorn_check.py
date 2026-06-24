"""
MEGA-7 Round 3: Test van Doorn's Pell family x^2 - 7^3 * y^2 = 2 and find its triples.

Van Doorn 2026 (arXiv:2605.06697) claims this Pell family produces infinitely many
powerful 3-APs of consecutive structure. The first triple: (130530625, 130553476, 130576327).

Let's verify:
- Find Pell solutions (x, y) to x^2 - 343*y^2 = 2
- For each, compute the triple ((x-1)^2, ?, 7^3 * y^2) or similar
- Check consecutiveness against full powerful sieve
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

def is_square(n):
    if n < 0: return False
    r = isqrt(n)
    return r*r == n

# Find Pell solutions to x^2 - 343*y^2 = 2 with x, y >= 1
print("Finding Pell solutions x^2 - 343*y^2 = 2 ...")
D = 343
c = 2
sols = []
y = 1
while y < 10**7:
    rhs = D * y * y + c
    x = isqrt(rhs)
    if x * x == rhs:
        sols.append((x, y))
        print(f"  Solution: x={x}, y={y}; x^2 = {x*x}, 7^3*y^2 = {D*y*y}, x^2 - 7^3*y^2 = {x*x - D*y*y}")
        if len(sols) >= 6:
            break
    y += 1

# Now also check x^2 - 7^3 y^2 = -2 (perhaps van Doorn uses negative)
print("\nFinding Pell solutions x^2 - 343*y^2 = -2 ...")
sols_neg = []
y = 1
while y < 10**6:
    rhs = D * y * y - 2
    x = isqrt(rhs)
    if x > 0 and x * x == rhs:
        sols_neg.append((x, y))
        print(f"  Solution: x={x}, y={y}; x^2 = {x*x}, 7^3*y^2 = {D*y*y}")
        if len(sols_neg) >= 6:
            break
    y += 1

print("\n--- Analysis of first van Doorn triple (130530625, 130553476, 130576327) ---")
t = (130530625, 130553476, 130576327)
for n in t:
    f = factor(n)
    fact_str = " * ".join(f"{p}^{e}" for p, e in sorted(f.items()))
    sqrt_n = isqrt(n)
    is_sq = sqrt_n * sqrt_n == n
    print(f"  {n} = {fact_str}  square: {is_sq}  sqrt={sqrt_n} (squared = {sqrt_n*sqrt_n})")

# Decompose: 130530625 = ? square check
n0 = 130530625
print(f"\n130530625 / 7^3 = {n0 / 343}")
print(f"isqrt(130530625) = {isqrt(n0)}, squared = {isqrt(n0)**2}")
# Sigh, 130530625 = 11425^2 ? let me check
for k in [11425, 11427, 11500]:
    print(f"  {k}^2 = {k*k}")
# 11427^2 = 130576329 (the LAST element 130576327 is 2 less... so the LAST element is NOT a perfect square)
# 11425^2 = 130530625 — YES, the FIRST element is a perfect square!
# So van Doorn's family has (x^2, ?, 7^3*y^2) structure but FIRST is the square, not middle.

# Let me check: 130576327 / 343 = ?
print(f"\n130576327 / 343 = {130576327 / 343}")
# 130576327 / 343 = 380689 = 617^2 (617 is prime? 617 is prime, yes). So 130576327 = 7^3 * 617^2. ✓
# Pell-like check:
# 11425^2 - 7^3 * 617^2 = 130530625 - 130576327 = -45702. Not = 2.
# Hmm, what is 130530625 - 7^3*617^2?
print(f"11425^2 = {11425**2}, 7^3 * 617^2 = {7**3 * 617**2}, diff = {11425**2 - 7**3 * 617**2}")

# So 11425^2 - 7^3 * 617^2 = -45702, NOT 2. Let me look at the structure differently.
# 130530625 = 11425^2, 130576327 = 7^3 * 617^2. Their average is (130530625+130576327)/2 = 130553476 = ?
print(f"\n(130530625 + 130576327)/2 = {(130530625 + 130576327)//2}")
print(f"130553476 = {factor(130553476)}")
# 130553476 = 2^2 * ? Let me check: 130553476/4 = 32638369. isqrt = 5713, 5713^2 = 32638369?
print(f"isqrt(32638369) = {isqrt(32638369)}, sq = {isqrt(32638369)**2}")
# 5713^2 = 32638369 → 130553476 = (2*5713)^2 = 11426^2! ✓
print(f"11426^2 = {11426**2}")
# YES, 130553476 = 11426^2.

# So the actual van Doorn structure for THIS triple is:
#   n_k     = 11425^2 = (a-1)^2  where a = 11426
#   n_{k+1} = 11426^2 = a^2
#   n_{k+2} = 7^3 * 617^2 = a^2 + 22851
# Gap = 22851. Indeed 11426^2 - 11425^2 = 22851 = (11426+11425)(11426-11425) = 22851 * 1 = 22851. ✓
# And 11426^2 + 22851 = 130553476 + 22851 = 130576327 = 7^3 * 617^2. ✓

# So 22851 = 11426 + 11425 = 22851. And we need 7^3 * 617^2 - 11426^2 = 22851.
# Substituting: 7^3 * 617^2 = 11426^2 + 22851 = 11426^2 + (11426 + 11425)
#                          = 11426^2 + 11426 + 11425
# Equivalently: (11426)^2 + (11426 - 1) + 11426 = 11426^2 + 2*11426 - 1 = (11426+1)^2 - 2 = 11427^2 - 2.
# Let's check: 11427^2 = 130576329. Indeed 130576329 - 2 = 130576327 = 7^3 * 617^2. ✓
# So Pell: 11427^2 - 7^3 * 617^2 = 2. ← VAN DOORN'S PELL FAMILY!

print(f"\n*** Van Doorn Pell verified: 11427^2 - 7^3 * 617^2 = {11427**2 - 7**3 * 617**2} ***")
print(f"   So x=11427, y=617 IS A SOLUTION of x^2 - 343*y^2 = 2 ***")

# Now let me find ALL solutions of x^2 - 343 y^2 = 2 in a more systematic way.
print("\n--- Finding all (x, y) with x^2 - 343*y^2 = 2, y <= 10^7 ---")
sols2 = []
y = 1
LIM_Y = 10**7
t0 = time.time()
while y <= LIM_Y:
    rhs = D * y * y + 2
    x = isqrt(rhs)
    if x * x == rhs:
        sols2.append((x, y))
        # Compute triple
        n0 = (x - 2)**2
        n1 = (x - 1)**2
        n2 = D * y * y  # = x^2 - 2
        # Verify AP: 2*n1 = n0 + n2?
        if 2 * n1 == n0 + n2:
            n2_pf = is_powerful(n2)
            n0_pf = is_powerful(n0)
            n1_pf = is_powerful(n1)  # always true (perfect square)
            all_pf = n0_pf and n1_pf and n2_pf
            print(f"  y={y}, x={x}: triple = ((x-2)^2, (x-1)^2, 7^3*y^2) = ({n0}, {n1}, {n2})")
            print(f"    All powerful: {all_pf} (n0={n0_pf}, n1={n1_pf}, n2={n2_pf})")
            print(f"    Factors: n0 = {factor(n0)}; n2 = {factor(n2)}")
            print(f"    Gap = {n1 - n0}")
        if len(sols2) >= 4:
            break
    y += 1
t1 = time.time()
print(f"  (Search to y={LIM_Y}: {t1-t0:.1f}s)")
print(f"  Found {len(sols2)} solutions.")
