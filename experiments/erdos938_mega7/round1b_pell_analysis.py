"""
MEGA-7 Round 1b: Analyze the structure of the 6 consecutive powerful 3-APs found.

KEY OBSERVATION:
  AP1: (1728, 1764, 1800)         d=36
  AP2: (6912, 7056, 7200)         d=144 = 4*36
  AP3: (729000, 729316, 729632)   d=316
  AP4: (1458000, 1458632, 1459264) d=632 = 2*316
  AP5: (2916000, 2917264, 2918528) d=1264 = 4*316
  AP6: (11664000, 11669056, 11674112) d=5056 = 16*316

These come in TWO FAMILIES:
  Family F1: (1728, 1764, 1800) and scalings by 2^k
  Family F2: (729000, 729316, 729632) and scalings by 2^k

Each AP scales: if (a, b, c) is consecutive powerful 3-AP, then (m^k * a, m^k * b, m^k * c) is
a powerful 3-AP (not consecutive in general!). But these ARE all consecutive?

Let's verify scaling. AP2 = 4 * AP1: 1728 * 4 = 6912 yes. 1764 * 4 = 7056 yes. 1800 * 4 = 7200 yes.
AP2 / AP1 = 4 = 2^2. AP3 = 8 * AP1? 1728 * 8 = 13824, not 729000. So AP3 is NEW.
AP4 = 2 * AP3. AP5 = 4 * AP3. AP6 = 16 * AP3.

So FAMILY structure is via integer scaling by 2 (or rather: scaling preserves powerful).

KEY: (a, b, c) consecutive ⟹ (4a, 4b, 4c) consecutive? Only if no powerful in between, i.e.,
no powerful x with 4a < x < 4c that isn't 4b. This requires checking.

Actually for these 6 APs the SCALING IS BY 4 not by 2: AP1 -> AP2 (x4), AP3 -> AP5 (x4),
AP3 -> AP4 (x2), AP3 -> AP6 (x16). Hmm.

Let me work out the underlying Pell structure for AP1 = (1728, 1764, 1800).

  1728 = 12^3 = 2^6 * 3^3
  1764 = 42^2 = (2*3*7)^2 = 2^2 * 3^2 * 7^2
  1800 = 2^3 * 3^2 * 5^2

Common gcd: 4 (since 1728 = 4*432, 1764 = 4*441, 1800 = 4*450).
Dividing: (432, 441, 450). 432 = 2^4 * 3^3, 441 = 21^2, 450 = 2 * 3^2 * 5^2.
But 450 is NOT powerful! 450 = 2 * 3^2 * 5^2 has 2 to power 1.

So the "smallest representative" of the family is (1728, 1764, 1800) since the gcd-divided
version isn't all powerful.

Let me look at the next family. AP3 = (729000, 729316, 729632):
  729000 = 2^3 * 3^6 * 5^3
  729316 = 854^2 = 2^2 * 7^2 * 61^2
  729632 = 2^5 * 151^2

This time the "middle" is exactly a perfect square, like AP1.

Let me check: in BOTH families, the middle is a perfect square!
  AP1 middle: 1764 = 42^2 ✓
  AP3 middle: 729316 = 854^2 ✓

This is the structural pattern.

The general structural pattern:
  n_k = a*b^3 (powerful)
  n_{k+1} = M^2 (perfect square, also powerful)
  n_{k+2} = c*d^3 (powerful)
  M^2 = (n_k + n_{k+2})/2
  Equivalently, n_k + n_{k+2} = 2M^2.

This is a TERNARY QUADRATIC FORM!  We need:
  a * b^3 + c * d^3 = 2 * M^2
  M^2 - a*b^3 = M^2 - n_k = d = gap
  c * d^3 - M^2 = c * d^3 - n_{k+1} = d = gap
  So a*b^3 = M^2 - d and c*d^3 = M^2 + d.

Let me focus on Walker Type A_1: middle = perfect square, outer two are non-square powerful.

This corresponds to the Pell-like equation:
  a*X^2 + c*Z^2 = 2*M^2 where X, Z are integers with rad-divisibility constraints.
  Or: M^2 - a*X^2 = d and c*Z^2 - M^2 = d (so a*X^2 - c*Z^2 = -2d ... but d depends on M).

Cleaner: M^2 = (n_k + n_{k+2})/2 with n_k = a*b^3, n_{k+2} = c*d^3.

Let's check: in AP1, M=42, n_k = 1728 = 12^3, n_{k+2} = 1800 = 2*30^2 wait...
  1800 = 2^3 * 3^2 * 5^2. Write 1800 = 2 * (2 * 3 * 5)^2 = 2 * 30^2. So n_{k+2} = 2 * 30^2.
  1728 = 12^3.

So  M^2 - X^3 = d and (M+gap-distance)^2... actually let me re-examine.

For AP1: 42^2 - 12^3 = 1764 - 1728 = 36 ✓ (gap)
         2 * 30^2 - 42^2 = 1800 - 1764 = 36 ✓ (gap)
So: 42^2 - 12^3 = 2 * 30^2 - 42^2 = 36
⟺ 2 * 42^2 = 12^3 + 2 * 30^2  ⟺  2 * 42^2 - 2 * 30^2 = 12^3
⟺ 2 * (42^2 - 30^2) = 12^3
⟺ 2 * (42-30) * (42+30) = 12^3
⟺ 2 * 12 * 72 = 12^3
⟺ 24 * 72 = 1728
⟺ 1728 = 1728 ✓

For AP3: M = 854, n_k = 2^3 * 3^6 * 5^3, n_{k+2} = 2^5 * 151^2.
  854^2 - 2^3 * 3^6 * 5^3 = 729316 - 729000 = 316
  2^5 * 151^2 - 854^2 = 729632 - 729316 = 316
  So 2 * 854^2 = 2^3 * 3^6 * 5^3 + 2^5 * 151^2.

Are there underlying Pell-like equations? Let me try.

Write n_k = 2*A^2 with A = 30 for AP1 (so n_{k+2} = 2 * 30^2 ✓).
Then n_k = 2*A^2 requires a*b^3 = 2*A^2 → for AP1, 1728 = 1728? but 2*30^2 = 1800, not 1728.
So I confused n_k and n_{k+2}. Let me redo.

For AP1:
  n_k = 1728 = 12^3 = 2^6 * 3^3
  n_{k+1} = 1764 = 42^2
  n_{k+2} = 1800 = 2 * 30^2

  2 * 1764 = 1728 + 1800: 2 * 42^2 = 12^3 + 2 * 30^2.
  → 2 * (42-30) * (42+30) = 12^3
  → 2 * 12 * 72 = 1728 ✓

For AP3:
  n_k = 729000 = 2^3 * 3^6 * 5^3 = (2 * 3^2 * 5)^3 / (something)... actually
       729000 = 90^3 / ... let me factor: 90^3 = 729000 ✓ (since 90 = 2*3^2*5, 90^3 = 8*729*125 = 729000)
  n_{k+1} = 729316 = 854^2
  n_{k+2} = 729632 = 2^5 * 151^2 = 32 * 151^2

  2 * 854^2 = 90^3 + 32 * 151^2
  854^2 - 90^3 = 316  →  854^2 = 90^3 + 316
  32 * 151^2 - 854^2 = 316  →  854^2 = 32*151^2 - 316
  Combining: 2*854^2 = 90^3 + 32*151^2  →  90^3 = 2*854^2 - 32*151^2 = 2*(854^2 - 16*151^2)
  So 854^2 - 16*151^2 = 90^3 / 2 = 364500.

Hmm. Let me try Pell-style: 854^2 - 4*151^2 = ... 854 = 2*427. 854^2 = 4 * 427^2. So
4*427^2 - 16*151^2 = 364500. Divide by 4: 427^2 - 4*151^2 = 91125 = 90^3 / 8 = 364500/4.
Hmm, 91125 = 3^6 * 5^3 = (3^2)^3 * 5^3 = ... = 45^3 / ... 45^3 = 91125 ✓ (45^2 = 2025, 45^3 = 91125)

So 427^2 - 4*151^2 = 45^3.  (Pell-like with cube RHS.)
Also: 854 = 2 * 427, 30 * (...) hmm.

CONCLUSION: AP3's structure is 854^2 - 4*151^2 = ... a Pell-like form.

But the discriminant here is 4. The Pell equation X^2 - 4*Y^2 = (X-2Y)(X+2Y) factors,
so it's not a "real" Pell. The form is degenerate.

Maybe the underlying structure isn't a single Pell but a SYSTEM of Pell-like equations
constrained by powerfulness.

Let me look at AP1 differently:
  1728 = 12^3 (a cube)
  1764 = 42^2 (a square)
  1800 = 2 * 30^2 (twice a square)

Differences: 12^3, 42^2, 2*30^2 in arithmetic progression with gap 36.
36 = 6^2 = 2^2 * 3^2.
12 = 2*6, 42 = 7*6, 30 = 5*6. So all multiples of 6.
Divide by 6^3 = 216: 1728/216 = 8 = 2^3, 1764/216 = 8.166... not integer.

Try gcd: gcd(1728, 1764, 1800) = 12 (since 1728 = 12*144, 1764 = 12*147, 1800 = 12*150,
and gcd(144, 147, 150) = 3, so gcd is 12*3 = 36). Wait gcd(144,147,150): 144=16*9, 147=3*49, 150=6*25;
common factor 3: yes. gcd(144/3, 147/3, 150/3) = gcd(48, 49, 50) = 1. So gcd = 36.

Divide AP1 by 36: (48, 49, 50). 48 = 2^4*3, 49 = 7^2, 50 = 2*5^2. Only 49 is powerful here.
So the "reduced form" of AP1 is the triple (48, 49, 50) but only middle is powerful in the reduced form.
The factor 36 = 2^2 * 3^2 multiplies each, and since 48*36 = 1728 = 2^6 * 3^3 is powerful,
49*36 = 1764 = 2^2*3^2*7^2 is powerful, 50*36 = 1800 = 2^3*3^2*5^2 is powerful.

KEY INSIGHT: 36 = 2^2 * 3^2 is a "powerful multiplier" that fills in the gaps:
- 48 = 2^4 * 3: multiplied by 36 gives 2^6 * 3^3, which is powerful (since 3 had power 1, gets to power 3).
- 50 = 2 * 5^2: multiplied by 36 gives 2^3 * 3^2 * 5^2, which is powerful.

So the family is: (48*k^2, 49*k^2, 50*k^2) where k^2 supplies the "missing primes" to make everything powerful.

For k = 6: (48*36, 49*36, 50*36) = (1728, 1764, 1800). YES, this is AP1.
For k = 12: (48*144, 49*144, 50*144) = (6912, 7056, 7200). YES, this is AP2.
For k = 24: (48*576, 49*576, 50*576) = (27648, 28224, 28800).

But wait, AP2 is at gap 144 = 4*36. Let me check: is (27648, 28224, 28800) consecutive?
gap = 576. Are there other powerful numbers in (27648, 28800)?

So MEGA-7 hypothesis: the "48, 49, 50" base triple generates an INFINITE FAMILY of
powerful 3-APs via scaling by suitable k^2. The question is: are infinitely many CONSECUTIVE?

This is precisely the falsification-vs-finiteness question!

Let me investigate. The reduced form of AP3:
  AP3 = (729000, 729316, 729632), gcd?
  gcd(729000, 729316, 729632) = gcd(2^3*3^6*5^3, 2^2*7^2*61^2, 2^5*151^2) = 2^2 = 4.
  729000/4 = 182250 = 2 * 3^6 * 5^3
  729316/4 = 182329 = 7^2 * 61^2 = 427^2
  729632/4 = 182408 = 2^3 * 151^2 (= 8 * 22801)
  Reduced: (182250, 182329, 182408), gap = 79.
  But 182250 = 2 * 3^6 * 5^3, 182408 = 2^3 * 151^2 — only middle is powerful in reduced form.

So MEGA-7 hypothesis generalized:
  Each consecutive 3-AP family has a "primitive base" (a, b, c) with middle square and
  outer two NOT individually powerful, and a "scaling factor" k^2 such that (a*k^2, b*k^2, c*k^2)
  is all powerful (and possibly consecutive).

For the (48, 49, 50) family, k^2 must be: divisible by 3 (to lift the 3 in 48 to 3^3),
must absorb the 2 in 50 to 2^3 (so k must be divisible by 2).
Required: k = 6m, m arbitrary. Then k^2 = 36 m^2.
For m=1: k=6, triple = (1728, 1764, 1800) ← AP1
For m=2: k=12, triple = (6912, 7056, 7200) ← AP2
For m=3: k=18, triple = (15552, 15876, 16200) — IS THIS CONSECUTIVE POWERFUL?
For m=4: k=24, triple = (27648, 28224, 28800) — IS THIS CONSECUTIVE POWERFUL?

Let me check these against my sieve!
"""

import math
from math import gcd, isqrt

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

# Larger sieve
N_BOUND = 10**9
print(f"Building powerful sieve up to {N_BOUND}...")
powerful = powerful_sieve(N_BOUND)
print(f"  {len(powerful)} powerful numbers")
powerful_set = set(powerful)

# Check the (48, 49, 50) family
print("\n=== Family F1: (48, 49, 50) scaled ===")
for m in range(1, 200):
    k = 6 * m
    k2 = k * k
    triple = (48 * k2, 49 * k2, 50 * k2)
    if max(triple) > N_BOUND:
        break
    all_pow = all(is_powerful(x) for x in triple)
    if all_pow:
        # Check consecutive: any powerful between?
        intermediates = [n for n in powerful if triple[0] < n < triple[2] and n != triple[1]]
        consec = len(intermediates) == 0
        marker = "** CONSECUTIVE **" if consec else f"(intermediates: {len(intermediates)})"
        print(f"  m={m:3d}, k={k:4d}: triple=({triple[0]}, {triple[1]}, {triple[2]}) d={49*k2 - 48*k2}={k2} {marker}")

print("\n=== Family F2: (n_k/4, 854^2/4, n_{k+2}/4) base from AP3 ===")
# AP3 base: (182250, 182329, 182408). Reduced gcd is 1, gap = 79.
# Reduced powerfulness: 182250 = 2 * 3^6 * 5^3, 182329 = 7^2 * 61^2, 182408 = 2^3 * 151^2.
# Need k^2 to lift: 2 in 182250 needs to become 2^2+ (k must be even),
# Actually wait — 182250 = 2 * 3^6 * 5^3 already has 3^6 * 5^3 powerful, only 2 is "loose".
# So we need k to contribute the missing 2.
# Similarly 182408 = 2^3 * 151^2: already powerful! Hmm.
# So the base is (2 * 3^6 * 5^3, 7^2 * 61^2, 2^3 * 151^2) — only 182250 needs k to be even.
# k = 2m → k^2 = 4m^2 → triple = (4m^2 * 182250, 4m^2 * 182329, 4m^2 * 182408)
# For m=1: k=2, k^2 = 4 → (729000, 729316, 729632) ← AP3 (this is m=1)
# For m=2: k=4, k^2 = 16 → (4 * 182250 * 16, ...) wait that's (m=2 means k=4, k^2=16, so 16 * 182250 = 2916000)
# That matches AP5! And m=2 means we'd skip AP4 (which had factor 2 not 4 in scaling).

# Let me re-look. AP3 → AP4: factor 2, AP3 → AP5: factor 4, AP3 → AP6: factor 16.
# So actually scaling AP3 by 2 = k=sqrt(2)? No, scaling AP3 by m: triple = (m*729000, m*729316, m*729632).
# m=2: (1458000, 1458632, 1459264) ✓ AP4.
# m=4: (2916000, 2917264, 2918528) ✓ AP5.
# m=16: (11664000, 11669056, 11674112) ✓ AP6.
# So the scaling is by m DIRECTLY (not k^2), and we need m * each component to be powerful.

# When does m * (2 * 3^6 * 5^3) = 2m * 3^6 * 5^3 remain powerful? Need m's contribution to '2' to make it ≥ 2.
# If m has v_2(m) >= 1, then v_2(m * 182250) >= 2, OK. If m has v_2(m) = 0, fail.
# Similarly m * (7^2 * 61^2): need m's exponents to make powerful, so m itself must be powerful.
# m * (2^3 * 151^2): same constraint.

# So we need m powerful AND v_2(m) >= 1. I.e., m = 2 * (any powerful), or m = 4 * (any powerful), etc.

# m = 2: 2 = 2^1 → not powerful! But AP4 is consecutive!
# So our parametric model isn't quite right.

# Actually let me re-check: is m=2 case all powerful?
# 2 * 729000 = 1458000 = 2^4 * 3^6 * 5^3 ✓
# 2 * 729316 = 1458632 = 2^3 * 7^2 * 61^2 ✓ — wait, that's 2^3 not 2^2, why powerful? Because all primes appear >= 2. ✓
# 2 * 729632 = 1459264 = 2^6 * 151^2 ✓

# So m=2 works for AP3 even though m=2 itself isn't powerful. The scaling lifts the loose 2 from middle/right.
# Specifically: 729316 had v_2 = 2, multiplying by 2 → v_2 = 3, still powerful.

# General rule for m * (a^2 * b^3 type powerful): multiplying preserves powerful iff for each prime p|m,
# either p|n (then exponent grows) or p doesn't divide n and we need v_p(m) >= 2.
# So m * n is powerful for ALL powerful n iff m is powerful.
# But for SPECIFIC n, m * n can be powerful even when m is not.

# Hmm, this is getting complex. Let me just sweep.

print("\n=== Sweep: AP3 scaled by all m=1..1000 ===")
base = (729000, 729316, 729632)
hits = []
for m in range(1, 1500):
    triple = (base[0]*m, base[1]*m, base[2]*m)
    if max(triple) > N_BOUND:
        break
    if all(is_powerful(x) for x in triple):
        # Check consecutive
        intermediates = [n for n in powerful if triple[0] < n < triple[2] and n != triple[1]]
        consec = len(intermediates) == 0
        marker = "** CONSECUTIVE **" if consec else f"(int: {len(intermediates)})"
        hits.append((m, triple, consec, len(intermediates)))
        if consec or m <= 30:
            print(f"  m={m:4d}: ({triple[0]}, {triple[1]}, {triple[2]}) gap={triple[1]-triple[0]} {marker}")

print(f"\nTotal m where all 3 are powerful: {len(hits)}")
print(f"Total m where CONSECUTIVE: {sum(1 for h in hits if h[2])}")
