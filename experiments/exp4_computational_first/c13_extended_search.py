"""
C13 (ADVERSARIAL VERIFICATION): Extend consecutive-powerful-3-AP search beyond 10^11.

Reuses the validated Golomb sieve (confirmed correct vs brute force up to 10^6).
Pushes to N = 10^13.

Outputs:
  (a) count of CONSECUTIVE powerful 3-APs up to N
  (b) for each, whether it fits the Mordell form (8w^3, 4y^2, 8x^2)
  (c) primitive Mordell bases (after dividing out the multiplier k)
"""

import time
from math import isqrt, gcd

N_BOUND = 10**13

def squarefree_sieve(M):
    mu = bytearray([1]) * (M + 1)
    p = 2
    while p * p <= M:
        if mu[p]:
            for j in range(p * p, M + 1, p * p):
                mu[j] = 0
        p += 1
    return mu

B_BOUND = int(round(N_BOUND ** (1.0 / 3.0))) + 3
print(f"N = {N_BOUND}, B_BOUND = {B_BOUND}", flush=True)

t0 = time.time()
mu = squarefree_sieve(B_BOUND)
print(f"  squarefree sieve to {B_BOUND} done in {time.time()-t0:.1f}s", flush=True)

# Generate powerful numbers via unique Golomb (a^2 * b^3, b squarefree)
t0 = time.time()
powerful = []
ap = powerful.append
for b in range(1, B_BOUND + 1):
    if not mu[b]:
        continue
    b3 = b * b * b
    if b3 > N_BOUND:
        break
    a_max = isqrt(N_BOUND // b3)
    b3a = b3
    a = 1
    while a <= a_max:
        ap(a * a * b3a)
        a += 1
print(f"  generated {len(powerful)} powerful numbers in {time.time()-t0:.1f}s (pre-sort)", flush=True)

t0 = time.time()
powerful.sort()
print(f"  sorted in {time.time()-t0:.1f}s", flush=True)
print(f"  |P(N)|/sqrt(N) = {len(powerful)/N_BOUND**0.5:.4f} (expected ~2.1732)", flush=True)

# Uniqueness check
t0 = time.time()
dup = 0
for i in range(1, len(powerful)):
    if powerful[i] == powerful[i-1]:
        dup += 1
print(f"  duplicate adjacent count: {dup} (should be 0) in {time.time()-t0:.1f}s", flush=True)

# ============================================================
# CONSECUTIVE powerful 3-APs up to N
# ============================================================
print("\n=== CONSECUTIVE powerful 3-APs up to 1e13 ===", flush=True)
t0 = time.time()
P = powerful
consec = []
for i in range(len(P) - 2):
    if 2 * P[i+1] == P[i] + P[i+2]:
        consec.append((P[i], P[i+1], P[i+2]))
print(f"  found {len(consec)} consecutive 3-APs in {time.time()-t0:.1f}s", flush=True)


def fits_mordell(n0, n1, n2):
    """Check if (n0,n1,n2) == (8 w^3 k, 4 y^2 k, 8 x^2 k) for some integer k>=1
    and (w,x,y) with x^2 + w^3 = y^2.
    Returns (k, w, x, y) if it fits, else None.
    Approach: the claim is n0=8 k w^3, n2 = 8 k x^2, n1 = 4 k y^2.
    Given the actual triple, we DON'T know k. But the *primitive* test is:
    divide the whole triple by its gcd g; then we need the EXACT structural form.
    Instead, test the forward map directly across all (k,w): expensive.
    Cleaner: the Mordell form says n0/8 must be k*w^3 and n2/8 = k*x^2 and n1/4 = k*y^2.
    So 2*n1 = n0+n2 (AP, already true). Necessary: 8 | n0, 8 | n2, 4 | n1.
    Then with m0=n0/8, m1=n1/4, m2=n2/8: need m0 = k w^3, m2 = k x^2, m1 = k y^2
    with x^2+w^3=y^2, i.e. m2 + (m0/k)*?... Let's just verify the *identity*:
      The Mordell form forces n0 = 8 k w^3, n1 = 4 k y^2, n2 = 8 k x^2 with y^2 = x^2 ...
      Actually the AP condition: 2 n1 = n0 + n2 => 8 k y^2 = 8 k w^3 + 8 k x^2 => y^2 = w^3 + x^2. GOOD.
    So the form is equivalent to:
      8 | n0, 8 | n2, 4 | n1, AND n0/8, n2/8, n1/4 share a common factor k such that
      (n0/8)/k is a perfect cube w^3, (n2/8)/k is a perfect square x^2, (n1/4)/k a perfect square y^2.
    We search k over divisors of gcd(n0/8, n2/8, n1/4)? Not all k work. Instead, since w^3=(n0/8)/k,
    x^2=(n2/8)/k, y^2=(n1/4)/k, and the AP gives y^2=w^3+x^2 automatically once the three hold,
    we just need to find ANY k making all three perfect (cube,square,square)."""
    if n0 % 8 != 0 or n2 % 8 != 0 or n1 % 4 != 0:
        return None
    m0 = n0 // 8   # = k w^3
    m2 = n2 // 8   # = k x^2
    m1 = n1 // 4   # = k y^2
    g = gcd(gcd(m0, m2), m1)
    # k must divide g. Enumerate divisors of g.
    divs = []
    d = 1
    while d * d <= g:
        if g % d == 0:
            divs.append(d)
            if d != g // d:
                divs.append(g // d)
        d += 1
    for k in sorted(divs):
        c0 = m0 // k
        c2 = m2 // k
        c1 = m1 // k
        # c0 must be a perfect cube, c2 & c1 perfect squares
        w = round(c0 ** (1.0/3.0))
        wfound = None
        for ww in (w-1, w, w+1):
            if ww >= 0 and ww*ww*ww == c0:
                wfound = ww
                break
        if wfound is None:
            continue
        sx = isqrt(c2)
        if sx*sx != c2:
            continue
        sy = isqrt(c1)
        if sy*sy != c1:
            continue
        # verify Mordell: sx^2 + wfound^3 == sy^2
        if sx*sx + wfound**3 == sy*sy:
            return (k, wfound, sx, sy)
    return None


print("\n=== Mordell-form fit per consecutive 3-AP ===", flush=True)
primitive_bases = {}
for ap in consec:
    fit = fits_mordell(*ap)
    if fit is None:
        print(f"  *** {ap} gap={ap[1]-ap[0]}  DOES NOT FIT MORDELL FORM ***", flush=True)
    else:
        k, w, x, y = fit
        # primitive base = the (w,x,y) when k makes triple smallest; record base AP
        base = (8*w**3, 4*y*y, 8*x*x)
        primitive_bases.setdefault((w, x, y), []).append((ap, k))
        print(f"  {ap} gap={ap[1]-ap[0]}  =>  k={k}, (w,x,y)=({w},{x},{y}), base={base}, deficit={x*x-w**3}, delta/w^3={(x*x-w**3)/w**3:.6g}", flush=True)

print("\n=== Distinct primitive Mordell bases ===", flush=True)
for (w, x, y), aps in sorted(primitive_bases.items()):
    ks = sorted(k for (_, k) in aps)
    print(f"  (w,x,y)=({w},{x},{y})  base_AP=({8*w**3},{4*y*y},{8*x*x})  multipliers k={ks}", flush=True)
print(f"\nTOTAL consecutive: {len(consec)} | distinct primitive Mordell bases: {len(primitive_bases)}", flush=True)
print(f"GRAND TOTAL elapsed across script visible above.", flush=True)
