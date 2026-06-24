"""
EXP4 C8: Investigate the UNIQUENESS of F1 and F2 base 3-APs.

Question: Up to 10^11, the only consecutive powerful 3-APs are scalings of (48, 49, 50) and (182250, 182329, 182408).
Is this an artifact of the bound, or a structural fact?

Approach:
(A) Run F2 scalings up to m=10^4 (so n2 = 729632 * 10^4 = 7.3e9), record all consecutive ones.
(B) Search for OTHER "primitive base triples" (a, b, c) with a+c=2b, gcd(a,b,c)=1, where SOME scaling produces a powerful 3-AP. We need to characterize WHICH primitive (a, b, c) admit such scaling.
(C) For each candidate primitive, check if its powerful-scaling has consecutive examples.
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
    return n in powerful_set if n <= N_BOUND else all(e >= 2 for e in factor(n).values())

def num_intervening(n0, n2, n1):
    if n2 > N_BOUND:
        return -1
    lo = bisect.bisect_right(powerful_sorted, n0)
    hi = bisect.bisect_left(powerful_sorted, n2)
    inter = hi - lo
    if lo <= bisect.bisect_left(powerful_sorted, n1) < hi:
        inter -= 1
    return inter

# ============================================================
# A: F2 scalings up to maximum
# ============================================================
print("=== A: F2 family scalings — full list of consecutive descendants ===")
F2_BASE = (729000, 729316, 729632)
m_max = N_BOUND // F2_BASE[2]
print(f"  m_max = {m_max}")
consec_f2 = []
all_pow_count = 0
for m in range(1, m_max + 1):
    n0, n1, n2 = (m*x for x in F2_BASE)
    if n2 > N_BOUND:
        break
    if n0 not in powerful_set or n1 not in powerful_set or n2 not in powerful_set:
        continue
    all_pow_count += 1
    inter = num_intervening(n0, n2, n1)
    if inter == 0:
        consec_f2.append((m, n0, n1, n2))

print(f"  Total m with all-three-powerful in F2-scaling: {all_pow_count}")
print(f"  Consecutive F2-scalings: {[c[0] for c in consec_f2]}")
print(f"  Count: {len(consec_f2)}")

# So among all m up to floor(10^11 / 729632), all consec F2 are: 1, 2, 4, 16.

# ============================================================
# B: F1 scalings — note F1 uses m^2 scaling (since base is "almost powerful")
# ============================================================
print("\n=== B: F1 family scalings (m^2 form) up to bound ===")
F1_BASE = (1728, 1764, 1800)  # = 36 * (48, 49, 50)
consec_f1 = []
m_max_f1 = isqrt(N_BOUND // F1_BASE[2]) + 1
print(f"  m_max_f1 = {m_max_f1}")
all_pow_count_f1 = 0
for m in range(1, m_max_f1):
    k = m * m
    n0 = F1_BASE[0] * k
    n1 = F1_BASE[1] * k
    n2 = F1_BASE[2] * k
    if n2 > N_BOUND:
        break
    if n0 not in powerful_set or n1 not in powerful_set or n2 not in powerful_set:
        continue
    all_pow_count_f1 += 1
    inter = num_intervening(n0, n2, n1)
    if inter == 0:
        consec_f1.append((m, n0, n1, n2))

print(f"  Total m^2 scalings with all-three-powerful: {all_pow_count_f1}")
print(f"  Consecutive F1-scalings: {[c[0] for c in consec_f1]}")

# Also F1 with m being a more general powerful multiplier (not just m^2)
print("\n=== B': F1 scalings with general k (k * (48,49,50)) ===")
# 48k powerful: v_p(k * 48) >= 2 for all p in k or 48 = 2^4 * 3
# 50k powerful: v_p(k * 50) >= 2 for all p in k or 50 = 2 * 5^2
# 49k powerful: 49 = 7^2 already; v_7(k) != 1
# So we need v_3(k) >= 1 (to fix 50 -- wait 50 doesn't have 3, so 3-adic only from k)
# Actually 48 = 2^4 * 3^1: need v_3(48k) >= 2 (if v_3(k) > 0) OR v_3(48k) = 0 (impossible since v_3(48)=1).
#   So 48k powerful iff v_3(k) >= 1. AND v_2(48k) >= 2, fine since v_2(48)=4 >= 2.
# 50k = 2*5^2 * k: v_2(50k) >= 2 requires v_2(k) >= 1.
#   v_5(50k) = 2 + v_5(k) >= 2 always.
# 49k = 7^2 * k: v_7(49k) = 2 + v_7(k) must be >= 2, OK.
#   For other primes p in k: v_p(49k) = v_p(k) >= 2 if k is "powerful or k=2^a * 3^b * (powerful with primes != 2,3)"
# So the condition: k = 2^a * 3^b * c, c powerful, a >= 1, b >= 1.
# The minimum such k is 2 * 3 = 6, but check 48k = 288 = 2^5 * 3^2 ✓, 49k = 294 = 2*3*7^2: v_2 = 1, NOT powerful.
# So k=6 fails. Need v_2(49k) >= 2 too, but 49 has v_2=0, so need v_2(k) >= 2.
# Adjust: v_2(k) >= 2 AND v_3(k) >= 1 (or both adjusted to "min 2" for safety).
# Actually for 49k powerful: 49k must be powerful. 49 = 7^2 alone is powerful. For p | k, p != 7, we need v_p(49k) = v_p(k) >= 2.
# So k must be powerful AND 2,3 | k (with v_2(k) >= 1 to fix 50, v_3(k) >= 1 to fix 48).
# But 50k needs v_2 >= 2 in 50k = 2*5^2 * k, so v_2(50k) = 1 + v_2(k) >= 2, so v_2(k) >= 1. OK.
# 48k needs v_3(48k) = 1 + v_3(k) >= 2, so v_3(k) >= 1.
# 49k requires k powerful (excluding adjustment by 49).
# So k = 2^a * 3^b * c with c powerful & coprime to {2,3,7?} & a >= 1 & b >= 1 — but for ALL primes in k that aren't 2,3 we need v_p(k) >= 2.

# Minimal such k: a=2, b=2, c=1 → k = 4*9 = 36. ✓
# Next: a=2, b=3, c=1 → k = 4*27 = 108. Check: 48*108 = 5184 = 2^6 * 3^4 ✓; 49*108 = 5292 = 2^2*3^3*7^2 ✓; 50*108 = 5400 = 2^3*3^3*5^2 ✓. Powerful 3-AP!
# Is (5184, 5292, 5400) consecutive? Check.
n0, n1, n2 = 5184, 5292, 5400
if n0 in powerful_set and n1 in powerful_set and n2 in powerful_set:
    inter = num_intervening(n0, n2, n1)
    print(f"  k=108: ({n0}, {n1}, {n2}) intervening={inter}")
else:
    print(f"  k=108: not all powerful")

# Iterate k = 2^a * 3^b * c with c powerful & coprime to 2,3 (and c=1 or c <= bound)
print("\n=== B'': All F1 generalized scalings up to bound ===")
generalized_f1 = []
small_powerful_23coprime = [1]  # powerful & coprime to 2,3 from our set
for p in powerful_sorted:
    if p > 10**6:
        break
    if p % 2 != 0 and p % 3 != 0:
        small_powerful_23coprime.append(p)
print(f"  {len(small_powerful_23coprime)} powerful integers coprime to 6 (up to 10^6)")

for c in small_powerful_23coprime[:100]:
    a = 2
    while True:
        b = 2
        n0_base = c * (1 << (2*a))  # 2^(2a)
        if n0_base > N_BOUND:
            break
        while True:
            three_part = 3 ** b
            k = (1 << a) * three_part * c
            # Wait this is getting confused. Let me reformulate.
            # k = 2^a * 3^b * c, with c powerful & coprime to 6, a >= 1, b >= 1.
            # For 48k powerful: 48 = 2^4*3, so 48k = 2^(4+a) * 3^(1+b) * c.
            #   Need every exponent >= 2. 4+a >= 2 ✓; 1+b >= 2 ⟺ b >= 1; for p in c: v_p(48k) = v_p(c) >= 2 ✓ since c powerful.
            # For 50k powerful: 50 = 2*5^2, so 50k = 2^(1+a) * 5^2 * c if gcd(c,10)=1; need 1+a >= 2 ⟺ a >= 1.
            # For 49k powerful: 49 = 7^2, so 49k = 7^2 * 2^a * 3^b * c if gcd(c,7)=1; need a >= 2 (for 2^a >= 2^2 standalone)? NO.
            #   Wait: 49k = 7^2 * 2^a * 3^b * c. For powerfulness, v_2(49k) = a must be >= 2 (since 49 has no 2).
            #   So a >= 2.
            # OK so a >= 2, b >= 1, c powerful & coprime to {2, 3, 7?}.
            # If 7 | c, then v_7(49k) = 2 + v_7(c) >= 2 ✓; but c powerful means v_7(c) >= 2 if 7 | c.
            n0 = 48 * (1 << a) * three_part * c
            n1 = 49 * (1 << a) * three_part * c
            n2 = 50 * (1 << a) * three_part * c
            if n2 > N_BOUND:
                break
            # Check
            if a >= 2 and b >= 1:
                if n0 in powerful_set and n1 in powerful_set and n2 in powerful_set:
                    inter = num_intervening(n0, n2, n1)
                    generalized_f1.append((a, b, c, n0, n1, n2, inter))
            b += 1
            if 3 ** b * c * (1 << a) > N_BOUND // 50:
                break
        a += 1
        if (1 << a) * c > N_BOUND // 50:
            break

consec_gen = [r for r in generalized_f1 if r[6] == 0]
print(f"  Total generalized F1 powerful 3-APs found: {len(generalized_f1)}")
print(f"  Consecutive: {len(consec_gen)}")
for a, b, c, n0, n1, n2, inter in consec_gen:
    k = (1 << a) * 3**b * c
    print(f"    a={a}, b={b}, c={c}: k={k}, ({n0}, {n1}, {n2}), inter={inter}")

# Show first 30 of the F1-generalized (not consec)
print("\n  First 30 (k, n0, intervening) for F1 generalized:")
for r in generalized_f1[:30]:
    a, b, c, n0, n1, n2, inter = r
    k = (1 << a) * 3**b * c
    print(f"    a={a}, b={b}, c={c}: k={k}, ({n0}, {n1}, {n2}), inter={inter}")

print(f"\n  Distribution of intervening counts (F1 generalized):")
intervening_counts = Counter(r[6] for r in generalized_f1)
for k in sorted(intervening_counts):
    print(f"    {k}: {intervening_counts[k]}")

# ============================================================
# C: F2 has primitive (2*3^6*5^3, 7^2*61^2, 2^3*151^2). What's the "generalized scaling"?
#
# For F2 to scale by k while remaining powerful 3-AP:
#   k * 182250 = k * 2 * 3^6 * 5^3 powerful needs v_2(k) + 1 >= 2 ⟹ v_2(k) >= 1
#   k * 182329 = k * 7^2 * 61^2 powerful needs v_p(k) >= 2 for p ∉ {7, 61}, and v_7(k), v_61(k) any (since 7, 61 already powered)
#   k * 182408 = k * 2^3 * 151^2 powerful: v_2(k) any (since 2 already powered), v_p(k) >= 2 for p != 2, 151
#
# Combined: k must have v_2(k) >= 1 AND every other prime in k has v_p(k) >= 2 (except possibly p in {7, 61, 151} where any v is fine since those are already at exp 2 or 3 in the base).
#
# Wait: k * 182329 needs each prime in 7^2 * 61^2 * k to have exponent >= 2 in product.
#   For 7: v_7(k * 7^2 * 61^2) = 2 + v_7(k) >= 2 ✓ always.
#   For 61: similarly always.
#   For 2: v_2(k * 7^2 * 61^2) = v_2(k). If 2 | k, need v_2(k) >= 2.
#   For p in k, p ∉ {7, 61, 2}: need v_p(k) >= 2.
#
# So k must be either 1 (no factors) or have v_2(k) >= 2 AND every other prime to >= 2.
# That means k is either 1 or k is powerful with EVEN 2-adic valuation? No, just v_2(k) >= 2 or v_2(k) = 0... wait:
# v_2(k) = 0: 2 ∤ k. Then v_2(k * 182250) = 1 (the 2 from 182250). 1 < 2, NOT powerful. So 2 | k.
# v_2(k) = 1: k * 182250 = 2^2 * ..., 1+1=2 ✓. k * 182329 has v_2 = 1, NOT powerful.
# v_2(k) >= 2: k * 182329 has v_2 = v_2(k) >= 2 ✓. k * 182250 has v_2 = 1 + v_2(k) >= 3 ✓. k * 182408 has v_2 = 3 + v_2(k) ≥ 5 ✓.

# WAIT: Actually m=1, 2 give consec, and m=2 means v_2(k)=1 (k=2). And we said v_2(k)=1 makes 182329*2=364658 NOT powerful.
# Let me check: 729316 = 182329 * 4. Is 729316 powerful? Yes (we verified). So 4 * 182329 = 4 * (7*61)^2 = (2*7*61)^2 = 854^2. Powerful (it's a square).
# So 4 * 182329 = 854^2 -- powerful. So k=4 works.

# The "scaling by m" in F2 is M = m * BASE where BASE = (182250, 182329, 182408), m is the multiplier on the WHOLE triple
# but we originally wrote F2 = (729000, 729316, 729632) = 4 * BASE. So m=1 in F2 form means k=4 in BASE form.
# m=2 in F2 form: k = 8 in BASE form. m=4: k=16. m=16: k=64.
# So F2-consec corresponds to k = 4, 8, 16, 64 = 2^2, 2^3, 2^4, 2^6 -- all powers of 2!
# k = 2^a with a in {2, 3, 4, 6} works. a=5 (k=32)?  k * 182329 = 32 * 7^2 * 61^2 -- v_2 = 5 >= 2 ✓; 32 * 182250 = 2^5 * 2 * 3^6 * 5^3 = 2^6 * 3^6 * 5^3 ✓; 32 * 182408 = 32 * 2^3 * 151^2 = 2^8 * 151^2 ✓.
# So k=32 (= F2 m=8): n2 = 5837056 -- we saw m=8 gives intervening=1, NOT consec.

print("\n=== C: F2 scalings k = 2^a only, all a values ===")
F2_PRIM = (182250, 182329, 182408)
print(f"  Primitive F2 base: ({F2_PRIM[0]}, {F2_PRIM[1]}, {F2_PRIM[2]})")
for a in range(1, 30):
    k = 1 << a
    n0, n1, n2 = (k * x for x in F2_PRIM)
    if n2 > N_BOUND:
        break
    if n0 in powerful_set and n1 in powerful_set and n2 in powerful_set:
        inter = num_intervening(n0, n2, n1)
        marker = "*** CONSEC ***" if inter == 0 else ""
        print(f"  a={a}: k=2^{a}={k}, ({n0}, {n1}, {n2}), inter={inter} {marker}")
    else:
        print(f"  a={a}: k=2^{a}={k}, ({n0}, {n1}, {n2}), NOT ALL POWERFUL")

# So F2 with k = 2^a: 4 (m=1) ✓, 8 (m=2) ✓, 16 (m=4) ✓, 32 (m=8): inter=1, 64 (m=16) ✓, 128 (m=32): inter=2, 256 (m=64): probably inter > 0, etc.
# Conjecture: F2 with k=2^a is consecutive ONLY for a in {2, 3, 4, 6}?
# This is a STRIKING pattern in the data.

# Also F2 with non-power-of-2 multipliers — these were m=9 (k=36 in base form), m=18, m=25, m=27, m=32 (k=128), etc.
# Let's check m=25 (k = 25*4 = 100):
# 100 * 182329 = 18232900. v_2(100) = 2, v_5(100) = 2. So OK powerful. 100 * 182250 = 18225000. 100 * 182408 = 18240800. All powerful.

# Generalized: F2 multiplied by k = 4 * j^2 ? Let me check what the consecutive m correspond to in different form.
# Actually a slick parametrization: let's write k_eff = 4 * j where j powerful or j=1...
# k=4: j=1. k=8: j=2. k=16: j=4. k=64: j=16. So j = 1, 2, 4, 16.
# F2 in m-form: m = 1, 2, 4, 16. SAME pattern.

# Conjecture from data: F2 is consecutive iff m ∈ {1, 2, 4, 16}.

# We can also ask: do F1 and F2 share a structural identity?
# F1 base = (48, 49, 50). Pell-like: 49^2 - 48*50 = 2401 - 2400 = 1. So 49^2 = 48*50 + 1 (Pell-like).
# F2 base = (182250, 182329, 182408). 182329^2 - 182250*182408 = ?
val = 182329**2 - 182250 * 182408
print(f"\n  F2: 182329^2 - 182250 * 182408 = {val}")
# Let's compute: 182329^2 = 33243864241. 182250 * 182408 = 33243363720. Diff = 500521.
# Hmm not 1. Different relationship.

# But: F2 has the Pell decomposition 427^2 - 302^2 = 3^6 * 5^3.
# Where does 302 = 2*151, 427 = 7*61 come from?
# Notice: 7 * 61 = 427, 2 * 151 = 302. And primes: 2, 7, 61, 151. 151 = ?
# 151 is prime. 61 prime. 7 prime. So F2 involves primes 2, 3, 5, 7, 61, 151.
# Is 151 special? 151 = ? Hmm.

print("\n=== D: Pell-like decompositions for known consecutive APs ===")
# F1: 49^2 - 48*50 = 1, classic Pell-like (m^2 = (m-1)(m+1) + 1).
# F2: looking for identity. 729316 = 854^2 = (2*427)^2. And n0+n2 = 2*n1.
# 729000 = 2*3^6*5^3, 729632 = 2^3*151^2. d = 316.
# (n2-n1)*(n2+n1) = n2^2 - n1^2 = ?
# Or maybe: sqrt(n1) = 854. n0 = 854^2 - 316, n2 = 854^2 + 316. So n0*n2 = 854^4 - 316^2.
# 854^4 - 316^2 = (854^2 - 316)(854^2 + 316) = 729000 * 729632.

# n0*n2 = 729000 * 729632 = 531901728000. And n1^2 = 729316^2 = 531829717856 = 729316^2.
# Hmm wait: n1^2 - n0*n2 = 729316^2 - 729000 * 729632 = d^2 = 316^2 = 99856. Always true for AP.
# So that's not interesting.

# But the SHARP identity in F2: 854^2 = 4 * 427^2. And 729000 = 8 * 91125 = 8 * 3^6 * 5^3.
# 854 = 2 * 427 = 2 * 7 * 61. And 729000^(1/3) = 90. Hmm 90^3 = 729000. YES, 90 = 2*3^2*5.
# So 729000 = 90^3 (since 90 = 2*3^2*5, 90^3 = 2^3 * 3^6 * 5^3 ✓).
# Interesting: n0 of F2 is a perfect CUBE.
# 729632: 729632^(1/3) ~ 90.013. Not a cube.

# But n0 = 90^3, n1 = 854^2, n2 = 8 * 302^2. Or n1/4 = 427^2, n2/8 = 302^2.

# A CLEANER pell-like identity: 427^2 - 302^2 = 5^3 * 3^6, where 5^3 * 3^6 = (5 * 3^2)^3 / 5^... no.
# 5^3 * 3^6 = 5^3 * (3^2)^3 = (5 * 3^2)^3 / ... no, 5^3 * 9^3 = 45^3 = 91125. Yes! 45^3 = 91125.
# So: 427^2 - 302^2 = 45^3.
# This is the identity at the heart of F2.

print("  F2 sharp identity: 427^2 - 302^2 = 45^3 = 91125 = 5^3 * 3^6")
print("  Or: (7*61)^2 - (2*151)^2 = (3^2 * 5)^3")
print("  Factorization: (427-302)(427+302) = 125 * 729 = 5^3 * 3^6")
print("  i.e., 427 + 302 = 729 = 3^6 and 427 - 302 = 125 = 5^3")

# So the Pell-like identity y^2 - z^2 = w^3 with y+z = 3^6 and y-z = 5^3 gives F2.
# This is the (cubically-paired Pell) identity!

# What if we look for OTHER y, z with y^2 - z^2 = some cube?
# Specifically: y - z = a^3, y + z = b^3 for some a, b coprime. Then y = (a^3+b^3)/2, z = (b^3-a^3)/2.
# For integer y, z: a^3 + b^3 even, i.e., a, b same parity. If both even, then gcd at least 2, so primitive needs both ODD.
# So: (a, b) coprime, both odd. y = (a^3+b^3)/2, z = (b^3-a^3)/2.
# (a, b) = (5, 9): y = (125+729)/2 = 427, z = (729-125)/2 = 302. THIS IS F2's structure!
# So F2 corresponds to (a, b) = (5, 9) -- both odd, coprime.

# Other (a, b) odd coprime?
# (1, 3): y = (1+27)/2 = 14, z = (27-1)/2 = 13. So y^2 - z^2 = 196 - 169 = 27 = 3^3. ✓
# (1, 5): y = (1+125)/2 = 63, z = (125-1)/2 = 62. y^2-z^2 = 125 = 5^3.
# (1, 7): y = (1+343)/2 = 172, z = (343-1)/2 = 171. y^2-z^2 = 343 = 7^3.
# (1, 9): y = (1+729)/2 = 365, z = (729-1)/2 = 364. y^2-z^2 = 729 = 3^6 = 9^3.
# (3, 5): y = (27+125)/2 = 76, z = (125-27)/2 = 49. y^2-z^2 = 27*5^2 ... wait, 76^2-49^2 = 5776 - 2401 = 3375 = 5^3 * 27. ✓
# (3, 7): y = (27+343)/2 = 185, z = (343-27)/2 = 158. y^2-z^2 = 27*7^3+... actually 27 * 7^3?
#   = (185-158)(185+158) = 27 * 343 = 9261. So 27 * 343 = 9261. Check: 185^2-158^2 = 34225-24964 = 9261. ✓ = 3^3 * 7^3 = 21^3. Cube!
# (3, 11): y=(27+1331)/2=679, z=(1331-27)/2=652. y^2-z^2 = 27 * 1331 = 35937 = 33^3. ✓
# (5, 7): y=(125+343)/2=234, z=(343-125)/2=109. y^2-z^2 = 125*343 = 42875 = 35^3. ✓
# (5, 9): y=427, z=302. → F2. ✓
# (5, 11): y=(125+1331)/2=728, z=(1331-125)/2=603. y^2-z^2 = 125*1331 = 166375 = 55^3. ✓
# (7, 9): y=(343+729)/2=536, z=(729-343)/2=193. y^2-z^2 = 343*729 = 250047 = 63^3. ✓
# (7, 11): y=(343+1331)/2=837, z=(1331-343)/2=494. y^2-z^2 = 343*1331 = 456533 = 77^3. ✓
# (9, 11): y=(729+1331)/2=1030, z=(1331-729)/2=301. y^2-z^2 = 729*1331 = 970299 = 99^3. ✓

# Now: for each (a, b) coprime odd with a<b, we have y = (a^3+b^3)/2, z = (b^3-a^3)/2.
# Then form a candidate F2-like 3-AP:
#   n0 = 2 * a^3 * b^3 (or similar)
#   n1 = 4 * y^2 = (a^3 + b^3)^2
#   n2 = 8 * z^2 = 2 * (b^3 - a^3)^2
#
# Wait, this needs to be checked. For F2: y = 427, z = 302.
#   n1 = 4 * 427^2 = 729316 ✓
#   n2 = 8 * 302^2 = 729632 ✓
#   n0 = n1 - d = 729316 - 316 = 729000. Or 2*n1 - n2 = 1458632 - 729632 = 729000.
#   d = (n2 - n0)/2 = 316. And we expect d = z?, d = 316 = z? z = 302, no. Hmm.
#   d = 729316 - 729000 = 316.
#   Or: d = (8*z^2 - 729000)/2? Let me compute 8*z^2 - 729000 = 729632 - 729000 = 632. Then /2 = 316. d = 316.
#   Try: n0 = 4*y^2 - d = 4*427^2 - 316 = 729316 - 316 = 729000.
#     For arbitrary (a, b), what is d? It must satisfy n0 = 2 * (3^6 * 5^3) = 2 * a^3 * b^3 (since y^2 - z^2 = a^3 b^3).
#     2*n1 = n0 + n2 ⟹ 8y^2 = 2(a^3b^3) + 8z^2 ⟹ 8(y^2 - z^2) = 2(a^3 b^3) ⟹ 4(y^2-z^2) = a^3b^3.
#     But y^2 - z^2 = a^3 b^3 (since y-z = a^3, y+z = b^3, (y-z)(y+z) = a^3 b^3). So 4 a^3 b^3 = a^3 b^3 requires 4 = 1. FALSE.
#     So this clean parametrization works for F2 only because of the SPECIFIC scaling.
#
# Let me re-examine F2:
#   n0 = 729000 = 8 * 91125 = 8 * 45^3 = 8 * (3^2 * 5)^3 = 8 * 3^6 * 5^3.
#   n1 = 729316 = 4 * 427^2 (verified).
#   n2 = 729632 = 8 * 302^2 (verified).
# AP: n0 + n2 = 2 * n1
#   8 * 45^3 + 8 * 302^2 = 8 * (45^3 + 302^2) =? 2 * 4 * 427^2 = 8 * 427^2
#   45^3 + 302^2 = 427^2?
#   91125 + 91204 = 182329. And 427^2 = 182329. YES!
# So the identity is: 45^3 + 302^2 = 427^2, i.e., 302^2 + 45^3 = 427^2.
# Equivalently: 427^2 - 302^2 = 45^3. SAME identity as before.

# Now to GENERALIZE F2: seek (x, y, w) with w^3 + x^2 = y^2 and x, y, w coprime appropriately (Mordell curve!).
# Then n0 = 8 * w^3, n1 = 4 * y^2, n2 = 8 * x^2. Check: n0+n2 = 8(w^3 + x^2) = 8*y^2 = 2 * (4*y^2) = 2*n1 ✓.
# And the AP step is d = (n2-n0)/2 = 4*x^2 - 4*w^3 = 4(x^2 - w^3) = 4 * (y^2 - 2*w^3 - ... hmm)

# So GENERAL F2-LIKE FAMILY: any (w, x, y) with x^2 + w^3 = y^2, gcd conditions, gives a powerful 3-AP candidate.
# This is the MORDELL EQUATION x^2 + w^3 = y^2 (a special form: difference of squares is a cube).
# The Mordell equation y^2 = x^3 + k has finitely many integer solutions for each fixed k... but here k = w^3 varies.

# Let me search for all (w, x, y) with x^2 + w^3 = y^2 and y^2 <= 10^11/4 (so n1 <= 10^11).
# This gives candidate (n0, n1, n2) = (8w^3, 4y^2, 8x^2) which is automatically an AP!

# But which of these are POWERFUL 3-APs? We need n0, n1, n2 each powerful.
# n0 = 8 w^3 = 2^3 * w^3: powerful iff 2^3 has each prime ≥2 (which it does for prime 2), AND w^3 has every prime ≥2 (it does, cube). So n0 powerful iff gcd(2, w) handled.
#   If w even: w = 2u, then 8w^3 = 8 * 8 * u^3 = 64 u^3 = 2^6 * u^3. Powerful iff u^3 powerful, which it is. So n0 powerful for w even.
#   If w odd: 8w^3 = 2^3 * w^3, where w^3 odd. Each prime exp: 2 has exp 3, w's primes have exp 3 each. POWERFUL.
#   So n0 = 8w^3 is ALWAYS powerful.
# n1 = 4y^2 = (2y)^2 — perfect square, always powerful.
# n2 = 8x^2 = 2^3 * x^2: powerful iff every prime in x has exp ≥ 1 (yes, x^2 has 2*v_p(x)), AND 2 has exp 3 ≥ 2 ✓.
#   Wait but x might be odd, then x^2 has no 2, and v_2(n2) = 3 ≥ 2 ✓. If x even, x = 2v, n2 = 8 * 4v^2 = 32 v^2, OK.
#   So n2 = 8x^2 ALWAYS powerful.
# Excellent! So for ANY (w, x, y) with x^2 + w^3 = y^2, n0=8w^3, n1=4y^2, n2=8x^2 is a powerful 3-AP.

# THIS IS A NEW INFINITE FAMILY of powerful 3-APs!

# Verify with F2: w=45, x=302, y=427. 302^2 + 45^3 = 91204 + 91125 = 182329 = 427^2 ✓.
#   n0 = 8 * 45^3 = 8 * 91125 = 729000 ✓.
#   n1 = 4 * 427^2 = 729316 ✓.
#   n2 = 8 * 302^2 = 729632 ✓.

# Verify with (a, b) = (3, 5): y_3,5 = 76, z_3,5 = 49. y^2-z^2 = 76^2 - 49^2 = 5776 - 2401 = 3375 = 15^3.
#   So w = 15, x = 49, y = 76. n0 = 8*15^3 = 27000, n1 = 4*76^2 = 23104, n2 = 8*49^2 = 19208.
#   Wait: order? n0 should be < n1 < n2 for AP. 27000 > 23104. So this is REVERSED. Need to swap.
#   Or: the AP is actually (8x^2, 4y^2, 8w^3) with 8x^2 < 4y^2 < 8w^3 if x^2 < y^2/2 < w^3.
#   Hmm. Let's recompute: y^2 = x^2 + w^3 ⟹ y^2 > x^2 AND y^2 > w^3. So 4y^2 > 4x^2 and 4y^2 > 4w^3.
#   But 8x^2 vs 4y^2: 8x^2 vs 4(x^2+w^3) = 4x^2+4w^3. So 8x^2 - 4y^2 = 4x^2 - 4w^3.
#   If x^2 > w^3: 8x^2 > 4y^2 → n2 > n1.
#   If x^2 < w^3: 8x^2 < 4y^2 → n2 < n1.
#   AP means n0 = 8w^3 must satisfy 2*n1 = n0+n2, i.e. 8y^2 = 8w^3 + 8x^2, ✓.
#   But for the AP to be n0 < n1 < n2 (increasing), need n0 < n1 < n2.
#   n0 = 8w^3, n1 = 4y^2 = 4(x^2+w^3) = 4x^2 + 4w^3. So n1 > n0 iff 4w^3 < 4x^2+4w^3 i.e. 0 < 4x^2. Always.
#   n2 = 8x^2, so n2 > n1 iff 8x^2 > 4x^2 + 4w^3 iff x^2 > w^3.
#   So we need x^2 > w^3 for proper AP order!
#   For (w, x, y) = (45, 302, 427): 302^2 = 91204, 45^3 = 91125. 91204 > 91125 ✓.

print("\n=== E: Mordell-derived powerful 3-AP family ===")
print("For (w, x, y) with x^2 + w^3 = y^2 and x^2 > w^3 (proper AP order):")
print("  n0 = 8 w^3, n1 = 4 y^2, n2 = 8 x^2 forms a powerful 3-AP automatically.")

# Search systematically: for each w, for each x with x > w^(3/2), check if x^2 + w^3 is a square.
def mordell_search(W_max, N2_max=N_BOUND):
    results = []
    for w in range(1, W_max + 1):
        w3 = w**3
        x = isqrt(w3) + 1  # x > w^(3/2)
        while True:
            x2 = x*x
            y2 = x2 + w3
            y = isqrt(y2)
            if y*y == y2:
                # Found
                n0 = 8 * w3
                n1 = 4 * y2
                n2 = 8 * x2
                if n2 > N2_max:
                    break
                results.append((w, x, y, n0, n1, n2))
            x += 1
            if 8 * x*x > N2_max:
                break
    return results

print("\n  Searching for w in [1, 1000], x^2 <= 10^11 / 8 ...")
t0 = time.time()
mordell_results = mordell_search(1000, N_BOUND)
print(f"  Found {len(mordell_results)} (w, x, y) triples in {time.time()-t0:.1f}s")

# For each, check if all three are powerful AND if the 3-AP is consecutive
consec_mordell = []
for w, x, y, n0, n1, n2 in mordell_results:
    if n2 > N_BOUND:
        continue
    if n0 in powerful_set and n1 in powerful_set and n2 in powerful_set:
        inter = num_intervening(n0, n2, n1)
        if inter == 0:
            consec_mordell.append((w, x, y, n0, n1, n2, inter))

print(f"\n  Of these, {len(consec_mordell)} are CONSECUTIVE powerful 3-APs")
for r in consec_mordell:
    print(f"    w={r[0]}, x={r[1]}, y={r[2]}: ({r[3]}, {r[4]}, {r[5]})")

# Also list the ones with small intervening (1, 2, 3) — "near-consecutive"
print(f"\n  First 30 Mordell-derived 3-APs (any consecutiveness):")
for r in mordell_results[:30]:
    w, x, y, n0, n1, n2 = r
    if n2 > N_BOUND: continue
    inter = num_intervening(n0, n2, n1) if n0 in powerful_set else "n/a"
    print(f"    w={w}, x={x}, y={y}: ({n0}, {n1}, {n2}), inter={inter}")
