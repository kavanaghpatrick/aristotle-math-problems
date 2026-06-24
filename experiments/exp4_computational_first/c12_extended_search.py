"""
EXP4 C12: Extended Mordell search up to n2 = 10^16 (PURE arithmetic, no sieve).

We don't need the powerful sieve for the (a, b) → (w, x, y) generation.
We just need to verify that the resulting (8w^3, 4y^2, 8x^2) is a valid powerful 3-AP
(automatic for Mordell solutions) and CONJECTURE whether it's consecutive.

For VERY large n, we can't directly check consecutiveness, but we can ESTIMATE.

The KEY metric: x^2 - w^3 (the "gap deficit"). Smaller = more likely consecutive.
Type A (5, 9): x^2 - w^3 = 91204 - 91125 = 79.
Type C (1, 6): x^2 - w^3 = 225 - 216 = 9.

Strong CONJECTURE FROM DATA:
For Mordell (a, b) of Type A or Type C with x^2 - w^3 small, consecutive may occur.

For Type A (a, b) odd coprime: w = ab, x = (b^3-a^3)/2, y = (b^3+a^3)/2.
x^2 - w^3 = ((b^3-a^3)/2)^2 - (ab)^3 = (b^6 - 2a^3b^3 + a^6)/4 - a^3 b^3
         = (b^6 - 2a^3b^3 + a^6 - 4a^3b^3)/4
         = (b^6 - 6a^3b^3 + a^6)/4
         = ((b^3 - a^3)^2 - 4a^3b^3 - ... ) hmm.
Let u = a^3, v = b^3. Then x = (v-u)/2, y = (v+u)/2, w = ab = (uv)^(1/3).
x^2 - w^3 = (v-u)^2/4 - uv = (v^2 - 2uv + u^2 - 4uv)/4 = (v^2 - 6uv + u^2)/4 = ((v-u)^2 - 4uv)/4
         Hmm. Maybe compute directly:
For (5, 9): a=5, b=9, u=125, v=729. (v-u)^2 = 604^2 = 364816. 4uv = 4*125*729 = 364500. Diff = 316. /4 = 79. ✓
For (3, 7): a=3, b=7, u=27, v=343. (v-u)^2 = 316^2 = 99856. 4uv = 4*27*343 = 37044. Diff = 62812. /4 = 15703.
For (5, 7): a=5, b=7, u=125, v=343. (v-u)^2 = 218^2 = 47524. 4uv = 4*125*343 = 171500. Diff = -123976. NEGATIVE — means x^2 < w^3. So (5,7) doesn't satisfy our ordering.

So for Type A, x^2 - w^3 = ((b^3 - a^3)^2 - (2ab)^3) / 4? Let me re-derive.
Wait: x^2 - w^3 with x = (v-u)/2, w = (uv)^(1/3). w^3 = uv. So x^2 - w^3 = (v-u)^2/4 - uv.
(v-u)^2 - 4uv = v^2 - 2uv + u^2 - 4uv = v^2 - 6uv + u^2.
For (5, 9): 729^2 - 6*125*729 + 125^2 = 531441 - 546750 + 15625 = 316. /4 = 79. ✓

So x^2 - w^3 = (v^2 - 6uv + u^2)/4 for Type A.
For this to be SMALL relative to w^3 = uv, need v^2 - 6uv + u^2 small compared to uv.
i.e., v/u + u/v small compared to 6. Setting r = v/u, need r + 1/r close to 6, i.e., r near 3+2sqrt(2) ≈ 5.828 or r near 3-2sqrt(2) ≈ 0.172.

For (5, 9): r = v/u = 729/125 = 5.832 — VERY close to 3+2√2 = 5.828!

This is the GOLDEN RATIO of the Mordell parameter. r = b^3/a^3 ≈ (3+2√2) for Type A near-consecutive.
So b/a ≈ (3+2√2)^(1/3) ≈ 1.7989.

What are integer (a, b) with b/a ≈ 1.7989?
(5, 9): 9/5 = 1.8 ✓
(11, 20): 20/11 ≈ 1.818
(17, 31): 31/17 ≈ 1.824 (further off)
(23, 41): 41/23 ≈ 1.783

Let me check (5, 9), (11, 19), (17, 31), etc:
"""

import math
from math import gcd, isqrt
from collections import defaultdict

def is_powerful(n):
    if n < 1: return False
    if n == 1: return True
    m = n; p = 2
    while p*p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p; e += 1
            if e < 2:
                return False
        p += 1
    return True

print("=== Type A: Mordell (a, b) odd coprime, find x^2 - w^3 small ===")
print(f"  Target: b^3 / a^3 ≈ 3 + 2√2 ≈ {3 + 2*math.sqrt(2):.6f}")
print(f"  Equivalently: b / a ≈ (3+2√2)^(1/3) ≈ {(3+2*math.sqrt(2))**(1/3):.6f}")

# Enumerate (a, b) coprime odd, compute deficit = x^2 - w^3
# We want deficit small (positive)
results = []
for a in range(1, 200, 2):
    for b in range(a + 2, 500, 2):
        if gcd(a, b) != 1: continue
        u, v = a**3, b**3
        deficit_num = v*v - 6*u*v + u*u
        deficit = deficit_num // 4
        if deficit_num % 4 != 0:
            # shouldn't happen for our (a, b) odd
            continue
        if deficit <= 0: continue
        w = a*b
        x = (v - u) // 2
        y = (v + u) // 2
        n0 = 8 * w**3
        n2 = 8 * x*x
        n1 = 4 * y*y
        # ratio = deficit / w^3 = deficit / (uv)
        ratio = deficit / (u*v)
        results.append((a, b, deficit, ratio, w, x, y, n0, n1, n2))

# Sort by ratio
results.sort(key=lambda r: r[3])
print(f"\n  Top 30 by SMALLEST ratio (x^2-w^3)/w^3:")
print(f"  {'(a,b)':<10} {'deficit':<15} {'ratio':<15} {'n0':<20}")
for r in results[:30]:
    a, b, deficit, ratio, w, x, y, n0, n1, n2 = r
    print(f"  ({a:>3}, {b:>3})  {deficit:<15} {ratio:.8f}  n0={n0}")

# Check which of these are actually Mordell (we know they are by construction) and which we predict to be consecutive.
# For our 10^11 range, the smaller deficit ones with smaller w are more likely consecutive.

# Now compute Poisson-prediction: P(consec) = e^{-rate}, rate = (n2-n0) / (2 sqrt(n0)) approx
print("\n  Top 30 by Poisson-rate (lowest expected intervening):")
def poisson_rate(n0, n2):
    return (n2 - n0) / (2 * math.sqrt(n0))

results_with_rate = [(r, poisson_rate(r[7], r[9])) for r in results]
results_with_rate.sort(key=lambda x: x[1])
for (a, b, deficit, ratio, w, x, y, n0, n1, n2), rate in results_with_rate[:30]:
    p_consec = math.exp(-rate)
    print(f"  ({a:>3}, {b:>3}): n0={n0:>20}, n2={n2:>20}, rate={rate:.4f}, P(consec) ≈ {p_consec:.4f}")

# Compare to F2 (5, 9): n0=729000, rate ≈ 0.370, P(consec) ≈ 0.69. ✓
# (11, 20): a=11, b=20 — but b even, not Type A.
# Let me restrict to a,b both odd:
print("\n  Cases with b/a near (3+2√2)^(1/3) ≈ 1.799:")
target = (3 + 2*math.sqrt(2))**(1/3)
candidates = []
for r in results:
    a, b = r[0], r[1]
    ratio = b/a
    if abs(ratio - target) < 0.1:
        candidates.append((abs(ratio - target), r))
candidates.sort()
for diff, r in candidates[:20]:
    a, b, deficit, ratio, w, x, y, n0, n1, n2 = r
    rate = poisson_rate(n0, n2)
    print(f"  (a={a}, b={b}): b/a={b/a:.4f} (off by {diff:.4f}), deficit={deficit}, n0={n0}, rate={rate:.4f}")

# ============================================================
# Type C revisited with the new lens
# ============================================================
print("\n=== Type C: w=ab, x=w(b-a)/2, y=w(a+b)/2 ===")
print(f"  x^2 - w^3 = w^2 (b-a)^2/4 - w^3 = w^2 ((b-a)^2/4 - w) = w^2 ((b-a)^2/4 - ab)")
# For x^2 > w^3: (b-a)^2/4 > ab ⟹ (b-a)^2 > 4ab ⟹ b^2 - 2ab + a^2 > 4ab ⟹ b^2 - 6ab + a^2 > 0
# Same condition as Type A! (b/a + a/b > 6 ⟺ b/a > 3+2sqrt(2) or b/a < 3-2sqrt(2))
# So Type C's deficit ratio = ((b-a)^2/4 - ab) / (ab) = (b-a)^2/(4ab) - 1
# For F1 (1, 6): (6-1)^2/4 = 25/4 = 6.25. ab = 6. Ratio = (6.25 - 6) / 6 = 0.041666. Yes very small.

# Find Type C with smallest deficit ratio (b-a)^2 - 4ab small
print("  (a, b) coprime Type C with smallest deficit (b-a)^2 - 4ab > 0:")
C_results = []
for a in range(1, 200):
    for b in range(a + 1, 500):
        if gcd(a, b) != 1: continue
        deficit_factor = (b-a)**2 - 4*a*b  # times w^2/4 gives x^2 - w^3
        if deficit_factor <= 0: continue
        w = a*b
        x = w*(b-a) // 2
        y = w*(a+b) // 2
        if x*w % 2 != 0:
            # need (b-a) and (a+b) both even or both odd to make w*(b-a)/2 integer
            # If a, b same parity: a+b and a-b both even. Both work.
            # If a, b different parity: a+b, a-b both odd. So x = w*(b-a)/2 needs w even (i.e., w=ab even, so one of a, b even). Then (b-a) odd, w even, w*(b-a)/2 integer iff w/2 integer i.e. w even.
            # If a even, b odd: w = ab even. x integer ✓.
            # If a odd, b even: w even. x integer ✓.
            # Both odd: (b-a) even. x = w*even/2 integer.
            # Both even: gcd issue, but they could be coprime if... they can't both be even and coprime.
            # Actually gcd(a,b)=1 means at most one is even.
            # In all cases x integer ✓.
            pass
        deficit = w**2 * deficit_factor // 4
        ratio = deficit / w**3
        n0 = 8 * w**3
        n2 = 8 * x*x
        n1 = 4 * y*y
        C_results.append((a, b, deficit, ratio, w, x, y, n0, n1, n2))

C_results.sort(key=lambda r: r[3])
print(f"  Top 30 by ratio:")
for r in C_results[:30]:
    a, b, deficit, ratio, w, x, y, n0, n1, n2 = r
    rate = poisson_rate(n0, n2)
    print(f"  ({a:>3}, {b:>3}): w={w}, deficit={deficit}, ratio={ratio:.6f}, n0={n0}, rate={rate:.4f}")

# ============================================================
# Key claim: as a, b grow, deficit ratio → ? for Type A and Type C
# Type A: deficit / w^3 = (v^2 - 6uv + u^2)/(4uv) = ((v/u) + (u/v))/4 - 3/2
#   For r = v/u >> 1: ≈ r/4 → ∞.
#   For r near 3+2√2: minimum is 0 (limit). So deficit → 0 as r → 3+2√2.

# Wait actually deficit ratio = (v^2 - 6uv + u^2) / (4 uv) → (r/4 + 1/(4r)) - 3/2
#   At r = 3+2√2: (3+2√2)/4 + 1/(4(3+2√2)) - 3/2.
#   1/(3+2√2) = 3-2√2 (rationalize).
#   So sum = (3+2√2)/4 + (3-2√2)/4 = 6/4 = 1.5. Minus 3/2 = 0. ✓
# So deficit ratio → 0 at r = 3+2√2. Theoretical minimum is 0 (not attained for integer u, v).

# For integer u, v, what's the smallest possible ratio?
# (a, b) = (5, 9): u/v = 5^3/9^3 = 125/729. v/u = 5.832. ratio = (5.832/4 + 0.04287) - 1.5 = 1.458 + 0.04287 - 1.5 = 0.0008685.
# (a, b) = (29, 47)? gcd(29, 47) = 1. b/a = 47/29 = 1.6207. b^3/a^3 = 103823/24389 = 4.257.
#   ratio = (4.257/4 + 1/(4*4.257)) - 1.5 = 1.064 + 0.0588 - 1.5 = -0.378. NEGATIVE.
# Hmm that means b/a too small. Try larger b/a:
# (5, 9): b/a = 1.8. v/u = 5.832. We've seen ratio = 0.0009 (very small).
# Closest convergents of (3+2√2)^(1/3) ≈ 1.79885...
# Continued fraction: [1; 1, 3, 1, 33, 1, 1, ...]. Convergents: 1, 2, 7/4=1.75, 9/5=1.8, 304/169=1.7988, 313/174=1.7989...
# So (5, 9) is the SECOND convergent, giving b/a = 1.8.
# (169, 304): b/a = 1.7988. Are they coprime? gcd(169, 304) = gcd(13^2, 16*19) = 1. ✓.
# (304, 547): 547 = ? 313 = ? Let me compute more convergents.

# (3+2√2)^(1/3) ≈ 1.7988585611...
target_cube_root = (3 + 2*math.sqrt(2))**(1/3)
print(f"\n=== Continued fraction convergents of (3+2√2)^(1/3) ≈ {target_cube_root} ===")

# Compute continued fraction
x = target_cube_root
cf = []
for _ in range(20):
    a_i = int(x)
    cf.append(a_i)
    if x == a_i: break
    x = 1 / (x - a_i)

print(f"  CF: {cf}")

# Compute convergents
def convergents(cf):
    p0, p1 = 0, 1
    q0, q1 = 1, 0
    res = []
    for a in cf:
        p2 = a * p1 + p0
        q2 = a * q1 + q0
        res.append((p2, q2))
        p0, p1 = p1, p2
        q0, q1 = q1, q2
    return res

convs = convergents(cf)
print(f"  Convergents (p, q) for p/q ≈ {target_cube_root}:")
for p, q in convs[:12]:
    val = p / q
    diff = abs(val - target_cube_root)
    # Check if (q, p) is a valid Type A pair (both odd, coprime)
    parity_ok = (q % 2 == 1 and p % 2 == 1)
    coprime = gcd(q, p) == 1
    # Compute deficit if valid
    if coprime and p > q:
        if parity_ok:
            a, b = q, p
            u, v = a**3, b**3
            deficit_num = v*v - 6*u*v + u*u
            if deficit_num > 0:
                deficit = deficit_num // 4
                w = a*b
                x_val = (v - u) // 2
                ratio = deficit / (u*v)
                print(f"    (a={a:>5}, b={p:>5}): b/a={val:.6f}, diff={diff:.2e}, Type A: deficit={deficit}, n0=8w^3={8*w**3:.4g}, ratio={ratio:.4g}")
        # Also Type C (a, b coprime, w=ab)
        a, b = q, p
        if (b - a) >= 0:
            x_val = a*b*(b-a) // 2  # times w / 2
            w = a*b
            n0 = 8 * w**3
            print(f"    (a={a:>5}, b={p:>5}): Type C w=ab={w}, n0=8w^3={n0:.4g}")
    elif coprime:
        print(f"    p, q = ({p}, {q})  (coprime: {coprime}, b/a={val:.6f})")
