"""
EXP4 C5: The n0=8 family looks like a Pell-derived sequence.

OBSERVATION from C4:
n0=8 case, sorted by n1:
  (8, 36, 64)   normalized (2, 9, 16)
  (8, 200, 392) normalized (1, 25, 49) -- 25=5^2, 49=7^2
  (8, 972, 1936) normalized (2, 243, 484)
  ...
  (8, 1156, 2304) normalized (2, 289, 576) -- 289=17^2, 576=24^2
  (8, 5400)  ...

Specifically, the (2, k^2, j^2) and (1, k^2, j^2) subfamilies look Pell-derived.

Let's verify: are these all in the family 2*x^2 - y^2 = -1 (or similar)?

(1, 25, 49): 2*25 - 1 - 49 = 50 - 50 = 0  AP check OK; n0=1, n1=25=5^2, n2=49=7^2.
  Relation: 7^2 - 5^2 = 24 = (7-5)(7+5) and 5^2 - 1 = 24.  d=24.
  So 5^2 - 1 = 7^2 - 5^2 = 24. Equivalently: 2*5^2 = 1 + 7^2, i.e., 7^2 - 2*5^2 = -1.
  This is the Pell equation y^2 - 2x^2 = -1!

(1, 841, 1681): 841 = 29^2, 1681 = 41^2. 41^2 - 2*29^2 = 1681 - 1682 = -1.  YES!
(1, 28561, 57121): 28561 = 169^2, 57121 = 239^2. 239^2 - 2*169^2 = 57121 - 57122 = -1. YES!
(1, 970225, 1940449): 985^2 - hmm 970225 = 985^2. 1940449 = 1393^2. 1393^2 - 2*985^2 = ?
  1393^2 = 1940449.  2*985^2 = 2*970225 = 1940450.  So 1393^2 - 2*985^2 = -1. YES!

CONJECTURE FROM DATA: The 3-APs (1, k^2, j^2) where (j, k) satisfies j^2 - 2k^2 = -1 are
infinitely many! This is the NEGATIVE PELL equation with D=2, which has solutions:
(k, j) = (5, 7), (29, 41), (169, 239), (985, 1393), (5741, 8119), ...

These are the solutions to the NSW-like recurrence!

But wait: the 3-AP (1, k^2, j^2) has n0=1 which is powerful (trivially), but n1=k^2 and n2=j^2 are
both powerful (squares). And 2*k^2 = 1 + j^2 means n1, n2 form an AP with n0=1.

This is the SOLUTION TO 2x^2 - y^2 = 1 (or y^2 - 2x^2 = -1), the negative Pell equation
for D=2. THIS HAS INFINITELY MANY SOLUTIONS. So there are infinitely many powerful 3-APs (1, k^2, j^2)!

Now: are any of these CONSECUTIVE powerful 3-APs? The intervening question.

Let's check: is (1, 25, 49) consecutive? Between 1 and 49, the powerful numbers are: 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, ...
So 1, 4, 8, ... 25 has many intervening. NOT consecutive.

But this gives a HUGE family of powerful 3-APs (not consecutive). The reason E938 is hard
is because consecutiveness is very restrictive.

Let me investigate: what is the EXACT condition for (1, k^2, j^2) to be consecutive?
That means NO powerful m with 1 < m < 49 (for k=5, j=7), m ≠ 25.
But 4, 8, 9, 16, 25, 27, 32, 36 are powerful — clearly NOT consecutive.

So the negative Pell family doesn't give consecutive 3-APs.

But what about scaled versions? (8, 200, 392) is (1, 25, 49) * 8.
The 3-AP (8, 200, 392) — is this near consecutiveness? Between 8 and 392 are MANY powerful numbers.

Let me explore the SCALING that makes any of these consecutive.
"""

import struct
import time
from math import gcd, isqrt
from collections import defaultdict, Counter

DATA = "/Users/patrickkavanagh/math/experiments/exp4_computational_first/powerful_1e11.bin"
with open(DATA, "rb") as f:
    N_BOUND, count = struct.unpack("<QQ", f.read(16))
    powerful = list(struct.unpack(f"<{count}Q", f.read(count * 8)))
powerful_set = set(powerful)

# ============================================================
# A: Verify the negative Pell family (1, k^2, j^2) with j^2 - 2k^2 = -1
# ============================================================
print("=== A: Negative Pell family verification ===")
# Recurrence: (k_{n+1}, j_{n+1}) = (3k_n + 2j_n, 4k_n + 3j_n) -- fundamental solution (k,j)=(1,1) trivial,
# then (k,j) = (5, 7), and recurrence k' = 3k + 2j, j' = 4k + 3j
k, j = 1, 1  # Trivial sol: 1^2 - 2*1^2 = -1
sols = []
for _ in range(20):
    sols.append((k, j))
    k, j = 3*k + 2*j, 4*k + 3*j

print(f"Solutions to j^2 - 2k^2 = -1 (first 20):")
for k, j in sols[:20]:
    print(f"  k={k:>20}, j={j:>20}, j^2 - 2k^2 = {j*j - 2*k*k}, (1, k^2={k*k}, j^2={j*j})")

# Check which fit in [1, 10^11]
print(f"\nWhich (1, k^2, j^2) have j^2 <= 10^11?")
for k, j in sols:
    if j*j <= N_BOUND:
        # Check that (1, k^2, j^2) is in our 3-AP set
        if 1 in powerful_set and k*k in powerful_set and j*j in powerful_set:
            print(f"  ({1}, {k*k}, {j*j}): YES, all powerful  -- 2*{k}^2 - {j}^2 = {2*k*k - j*j}")

# ============================================================
# B: General scaling: for each unit c, (c, c*k^2, c*j^2) where c*k^2, c*j^2 powerful
# ============================================================
print("\n=== B: Scaling the family (c, c*k^2, c*j^2) ===")
# For (c, c*k^2, c*j^2) to be a powerful 3-AP, need c powerful AND c*k^2 powerful AND c*j^2 powerful.
# Note c*k^2: since k^2 is a square (powerful), c*k^2 is powerful iff c is powerful (?? actually no -- c*k^2 powerful requires
# every prime in c*k^2 to have exponent >= 2. If p | c with v_p(c) = 1 and p ∤ k, then v_p(c*k^2) = 1, not powerful.
# So we need: for every prime p | c, either v_p(c) >= 2 OR p | k.
# Simplest: c powerful AND gcd(c, k) such that... actually c powerful suffices.

# Try c = 8 = 2^3 (powerful). Then 8*k^2 powerful iff every p | 8 has v_p(8*k^2) >= 2.
# v_2(8*k^2) = 3 + 2*v_2(k) >= 3 >= 2. OK.  So c=8 works for any k.
# Similarly c = 4, 9, 16, 25, 27, ...

# For each powerful c, count how many Pell solutions (k, j) give (c, c*k^2, c*j^2) a valid 3-AP up to 10^11
print(f"For each powerful c <= 100, count Pell solutions (k, j) with c*j^2 <= 10^11:")
small_powerful = [p for p in powerful if p <= 100]
for c in small_powerful[:20]:
    count_full = 0
    for k, j in sols:
        if c * j * j > N_BOUND:
            break
        # Check all powerful
        if c*k*k in powerful_set and c*j*j in powerful_set:
            count_full += 1
    if count_full > 0:
        print(f"  c={c}: {count_full} valid (k, j)")

# ============================================================
# C: Same for (c, c*k^2, c*j^2) where j^2 - 2k^2 = +1 (positive Pell)
# ============================================================
print("\n=== C: Positive Pell family j^2 - 2k^2 = +1 ===")
# Standard Pell with D=2: solutions (k, j) = (2, 3), (12, 17), (70, 99), ...
# Recurrence: k_{n+1} = 3k_n + 2j_n, j_{n+1} = 4k_n + 3j_n; fundamental (3,2) with j=3, k=2.
sols_pos = []
k, j = 2, 3
for _ in range(15):
    sols_pos.append((k, j))
    k, j = 3*k + 2*j, 4*k + 3*j

print(f"Solutions to j^2 - 2k^2 = +1 (first 15):")
for k, j in sols_pos:
    val = j*j - 2*k*k
    print(f"  k={k}, j={j}, j^2 - 2k^2 = {val}")

# These have j^2 = 2k^2 + 1, so 2k^2 - j^2 = -1; AP check: 1 + j^2 = 2k^2 means n0=1, n1=k^2, n2=j^2 gives 2n1 = 2k^2 = 1 + j^2 = n0 + n2.  YES, AP!
# Wait but that's wrong: 2k^2 = 1 + j^2 means j^2 = 2k^2 - 1, j^2 - 2k^2 = -1. That's the NEGATIVE Pell case.
# Positive Pell j^2 - 2k^2 = +1 means 2k^2 = j^2 - 1, so 2k^2 < j^2, NOT an AP with n0=1.

# OK so only negative Pell family gives (1, k^2, j^2).

# ============================================================
# D: More general: (a^2, b^2, c^2) with a^2 + c^2 = 2*b^2 — squares in AP
# ============================================================
print("\n=== D: Squares in AP. Classify by parametric family. ===")
# (a^2, b^2, c^2) is an AP iff c^2 - b^2 = b^2 - a^2, equivalent (c-b)(c+b) = (b-a)(b+a)
# These are classified by primitive Pythagorean-like parametrization:
# (a, b, c) = (|m^2 - 2mn - n^2|, m^2 + n^2, m^2 + 2mn - n^2) for some integers m, n.
# Or: a = b - kd_a, c = b + kd_c. The standard parametrization is:
# All "three squares in AP" come from a = u - v, b = u, c = u + v with some condition.
# Actually a^2, b^2, c^2 in AP iff b^2 = (a^2 + c^2)/2, so (c-a)(c+a) = 2(b^2-a^2)...
# Wait: 2b^2 = a^2 + c^2 with a < b < c. This is the equation Hardy & Wright discuss.
# Parametric: a = m^2 - 2mn - n^2, b = m^2 + n^2, c = m^2 + 2mn - n^2 with gcd(m,n)=1, m,n opposite parity.
# Or more cleanly: (a + c, c - a) = (2u, 2v) with u^2 + v^2 = ... hmm.

# Anyway: from C4 we see lots of patterns:
# (1, 5, 7), (1, 29, 41), (1, 169, 239), (1, 985, 1393), (1, 5741, 8119)
# (2, 10, 14), (2, 58, 82), (2, 338, 478), (2, 1970, 2786)
# (3, 15, 21), (3, 87, 123), (3, 507, 717), (3, 2955, 4179)
# (4, 20, 28), (4, 116, 164), ...

# Let's check: (1, 5, 7): is 5^2 - 1^2 = 7^2 - 5^2 = 24?  25-1=24, 49-25=24. YES.
# (1, 29, 41): 29^2 - 1 = 840 = 41^2 - 29^2? 1681 - 841 = 840. YES.

# The (a, b, c) sequences for a=1: 1, 5, 29, 169, 985, 5741, ... -- this is the central terms in solutions of j^2 - 2k^2 = -1!
# Recurrence: 6*prev - prev_prev (NSW recurrence)
# Check: 6*5 - 1 = 29. 6*29 - 5 = 169. 6*169 - 29 = 985. YES!

# For a=2: 2, 10, 58, 338, 1970. Ratios: 10/2=5, 58/10=5.8, 338/58=5.83, 1970/338=5.83.
# Hmm, also recurrence b_{n+1} = 6 b_n - b_{n-1}: 6*10-2=58, 6*58-10=338, 6*338-58=1970. YES!
# For a=3: 3, 15, 87, 507, 2955. 6*15-3=87, 6*87-15=507, 6*507-87=2955. YES.
# For a=4: 4, 20, 116, 676, 3940. 6*20-4=116, 6*116-20=676, 6*676-116=3940. YES.
# For a=5: 5, 25, 145, 845, 4925. 6*25-5=145, 6*145-25=845, 6*845-145=4925. YES.
# For a=7: 49, 169, 289... 7,13,17,23,35,73,97,103... Let's recompute:
# (49, 169, 289): a=7, b=13, c=17. 6*13-7 = 71, not 17. So NOT the standard NSW sequence here.
# But (49, 289, 529): a=7, b=17, c=23. 6*17-7 = 95, not 23.
# So a=7 starts a NEW orbit: (7, 13, 17, ...) — recurrence might be different.
# 6*13-7 = 71. 17 != 71. So 17 starts a separate orbit. Hmm.

# Better claim: the (a, b, c) with a^2+c^2=2b^2 forms an orbit under T(a,b,c) = (b, 2b+c-a, b+2c-a)?
# Actually, the GROUP action on Pell-like solutions:
# (a, b, c) → (a, 3b+2c-3a, c+2(3b+2c-3a-c)/2 ...) is messy.

# Let me skip parametric classification and just empirically find ALL distinct "first" terms:
sq_aps = []  # (a, b, c) where a^2, b^2, c^2 is a powerful 3-AP and a^2 <= N_BOUND, c^2 <= N_BOUND
for n in powerful:
    if n * n > N_BOUND:
        break

# Wait, this is the wrong loop. We want (a, b, c) with a^2 + c^2 = 2b^2.
# Iterate a, b, find c if exists.

max_a = int((N_BOUND ** 0.5) ** 0.5) + 1
print(f"max_a for c^2 <= {N_BOUND}: c <= sqrt(N) ~ {int(N_BOUND**0.5)}, so a <= ...")

# For each a in [1, sqrt(N)], for each b in [a, sqrt(N)]:
#   2b^2 - a^2 = c^2
#   c = sqrt(2b^2 - a^2) must be integer
# Count
sq_ap_count = 0
sq_aps = []
t0 = time.time()
sqrt_N = isqrt(N_BOUND)
for a in range(1, sqrt_N + 1):
    if a * a > N_BOUND:
        break
    # Iterate b from a (need b > a since 2b^2 = a^2 + c^2 with c > b > a means c^2 > b^2 > 0)
    # Also c^2 = 2b^2 - a^2 <= N_BOUND
    b_max = isqrt((N_BOUND + a*a) // 2)
    for b in range(a + 1, b_max + 1):
        c2 = 2*b*b - a*a
        c = isqrt(c2)
        if c * c == c2 and c > b:
            sq_aps.append((a, b, c))
            sq_ap_count += 1
    if a % 1000 == 0:
        print(f"  a={a}/{sqrt_N}, count={sq_ap_count}, t={time.time()-t0:.1f}s")
print(f"\nTotal (a,b,c) with a^2 + c^2 = 2b^2 and c^2 <= 10^11: {sq_ap_count}")
print(f"Time: {time.time()-t0:.1f}s")

# Save first 30
print(f"\nFirst 30 with a <= 7:")
for a, b, c in sq_aps[:50]:
    if a <= 7:
        print(f"  ({a}, {b}, {c}): a^2={a*a}, b^2={b*b}, c^2={c*c}")
