"""
EXP4 C10: Analyze the NEAR-MISS Mordell-derived 3-APs with intervening = 1.

From C9: (w=140, x=1657, y=2343) gives (21952000, 21958596, 21965192) with inter=1.
What is the intervening powerful?

Also: are there hidden patterns in the (w, x, y) values that give low intervening counts?

Generalization: the parametric (w, x, y) form gives an INFINITE family of powerful 3-APs.
For each, the intervening count can be modeled probabilistically:
  Expected intervening ~ count(powerful in (n0, n2)) - 1
  Width of (n0, n2) = 16(x^2 - w^3) for the Mordell form. Actually n2 - n0 = 8x^2 - 8w^3.
  For x^2 > w^3, this width is positive.
  Density of powerful near n ~ 1/(2 sqrt(n)).
  So expected intervening ~ width / (2 sqrt(n0)) ~ 8(x^2 - w^3) / (2 * sqrt(8 w^3))
                          ~ 8(x^2 - w^3) / (4 sqrt(2) w^(3/2))
                          ~ 2(x^2 - w^3) / (sqrt(2) w^(3/2))
  For (w, x) = (45, 302): x^2 - w^3 = 91204 - 91125 = 79.
    Expected ~ 2*79 / (sqrt(2) * 45^1.5) ~ 158 / (1.414 * 301.87) ~ 158/426.84 ~ 0.37.
  Poisson rate λ = 0.37, P(exactly 0 intervening) = e^{-λ} ~ 0.69. Consistent with consec ✓.

  For (w, x) = (140, 1657): x^2 - w^3 = 2745649 - 2744000 = 1649.
    Expected ~ 2*1649 / (sqrt(2) * 140^1.5) ~ 3298 / (1.414 * 1656) ~ 3298 / 2342 ~ 1.408.
    P(0) = e^{-1.408} ~ 0.245. So 24.5% chance of being consecutive. Why was it 1?

  These match data well — the actual data shows ~ 1-2 intervening near this.
"""

import struct
import bisect
import time
import math
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

# Near-miss analysis
print("=== Near-miss Mordell triple (w=140, x=1657, y=2343) ===")
w, x, y = 140, 1657, 2343
n0 = 8 * w**3; n1 = 4*y*y; n2 = 8*x*x
print(f"  ({n0}, {n1}, {n2})")
print(f"  factor n0 = {fmt(n0)}")
print(f"  factor n1 = {fmt(n1)}")
print(f"  factor n2 = {fmt(n2)}")
print(f"  factor w=140 = {fmt(140)} = 2^2 * 5 * 7")
print(f"  factor x=1657 = {fmt(1657)}")
print(f"  factor y=2343 = {fmt(2343)}")
# Look at intervening powerful
lo = bisect.bisect_right(powerful_sorted, n0)
hi = bisect.bisect_left(powerful_sorted, n2)
inter_list = [p for p in powerful_sorted[lo:hi] if p != n1]
print(f"  Intervening powerful(s): {inter_list}")
for p in inter_list:
    print(f"    {p} = {fmt(p)}")

# So one intervening: what is it?
# Let me also check the (w=180, x=2416) and (w=210, x=3045) examples
for w, x, y, name in [(180, 2416, 3416, "(180, 2416, 3416)"), (210, 3045, 4305, "(210, 3045, 4305)"),
                       (560, 13256, 18744, "(560, 13256, 18744)"), (180, 2416, 3416, "(180, 2416, 3416)")]:
    n0 = 8*w**3; n1 = 4*y*y; n2 = 8*x*x
    if n2 > N_BOUND: continue
    print(f"\n=== {name}: ({n0}, {n1}, {n2}) ===")
    print(f"  factor w={w} = {fmt(w)}")
    print(f"  factor x={x} = {fmt(x)}")
    print(f"  factor y={y} = {fmt(y)}")
    print(f"  factor n0 = {fmt(n0)}")
    print(f"  factor n1 = {fmt(n1)}")
    print(f"  factor n2 = {fmt(n2)}")
    lo = bisect.bisect_right(powerful_sorted, n0)
    hi = bisect.bisect_left(powerful_sorted, n2)
    inter_list = [p for p in powerful_sorted[lo:hi] if p != n1]
    print(f"  {len(inter_list)} intervening")
    if len(inter_list) <= 15:
        for p in inter_list:
            print(f"    {p} = {fmt(p)}")

# ============================================================
# Common structure analysis: w, x, y for consec and near-consec triples
# ============================================================
print("\n\n=== Structural pattern for low-intervening Mordell triples ===")
# Re-enumerate Mordell and compute intervening for all
N_BOUND = 10**11
W_MAX = int((N_BOUND // 8) ** (1/3)) + 1
X_MAX = isqrt(N_BOUND // 8) + 1
print(f"  Enumerating Mordell (w, x, y) up to x={X_MAX}, w={W_MAX}...")
mordell = []
for w in range(1, W_MAX + 1):
    w3 = w**3
    if 8 * w3 > N_BOUND: break
    x_lo = isqrt(w3) + 1
    if (x_lo - 1)**2 > w3: x_lo -= 1
    while x_lo * x_lo <= w3: x_lo += 1
    x = x_lo
    while 8 * x * x <= N_BOUND:
        x2 = x*x
        y2 = x2 + w3
        y = isqrt(y2)
        if y*y == y2:
            mordell.append((w, x, y))
        x += 1

print(f"  {len(mordell)} Mordell triples")

# For each, compute intervening
def num_intervening(n0, n2, n1):
    lo = bisect.bisect_right(powerful_sorted, n0)
    hi = bisect.bisect_left(powerful_sorted, n2)
    inter = hi - lo
    pos = bisect.bisect_left(powerful_sorted, n1)
    if lo <= pos < hi:
        inter -= 1
    return inter

mordell_with_inter = []
for w, x, y in mordell:
    n0 = 8 * w**3
    n1 = 4 * y * y
    n2 = 8 * x * x
    if n2 > N_BOUND: continue
    inter = num_intervening(n0, n2, n1)
    # Also compute Poisson rate estimate
    width = n2 - n0
    rate = width / (2 * math.sqrt(n0)) if n0 > 0 else 0
    mordell_with_inter.append((w, x, y, n0, n1, n2, inter, rate))

# Top 30 lowest intervening
mordell_with_inter.sort(key=lambda r: (r[6], -r[7]))  # lowest inter, then lowest rate

print(f"\n  Top 30 (lowest intervening, expected Poisson rate λ):")
print(f"  {'w':<8} {'x':<8} {'y':<8} {'n0':<15} {'n2':<15} {'inter':<6} {'λ_pred':<8}")
for w, x, y, n0, n1, n2, inter, rate in mordell_with_inter[:30]:
    print(f"  {w:<8} {x:<8} {y:<8} {n0:<15} {n2:<15} {inter:<6} {rate:.3f}")

# Distribution of inter vs rate
print(f"\n  Distribution of (inter, rate-bucket):")
rate_buckets = defaultdict(lambda: defaultdict(int))
for w, x, y, n0, n1, n2, inter, rate in mordell_with_inter:
    rb = int(rate)
    if rb > 20: rb = 21
    rate_buckets[rb][inter] += 1
for rb in sorted(rate_buckets):
    row = rate_buckets[rb]
    print(f"  rate~{rb}: {dict(sorted(row.items())[:6])}")

# ============================================================
# Key question: What characterizes (w, x, y) giving (1728, 1764, 1800) and (729000, 729316, 729632) specifically?
# ============================================================
print("\n\n=== Factor structure of F1 and F2 Mordell parameters ===")
print(f"  F1 base: (w, x, y) = (6, 15, 21)")
print(f"    w = 6 = 2 * 3")
print(f"    x = 15 = 3 * 5")
print(f"    y = 21 = 3 * 7")
print(f"    gcd(w,x) = 3, gcd(x,y) = 3, gcd(w,y) = 3")
print(f"    All three multiples of 3!")

print(f"\n  F2 base: (w, x, y) = (45, 302, 427)")
print(f"    w = 45 = 3^2 * 5")
print(f"    x = 302 = 2 * 151")
print(f"    y = 427 = 7 * 61")
print(f"    gcd(w, x) = 1, gcd(x, y) = 1, gcd(w, y) = 1")
print(f"    All three coprime!")

# Why these specific (w, x, y)? Let's parametrize Mordell solutions.
# Pythagorean-like for x^2 + w^3 = y^2: (y-x)(y+x) = w^3.
# Let d_1 = gcd(y-x, y+x). Then d_1 | 2x and d_1 | 2y. If y, x coprime, d_1 | 2.
# Case 1: d_1 = 1 (when x, y both odd?). Then y-x = a^3, y+x = b^3 with ab = w, gcd(a,b)=1.
#   F1: w=6=2*3, x=15, y=21. y-x=6, y+x=36. d_1 = gcd(6, 36) = 6.
#     Hmm 6 isn't 1 or 2 either. So this case doesn't apply.
#   F2: w=45, x=302, y=427. y-x=125=5^3, y+x=729=3^6=(3^2)^3=9^3.
#     d_1 = gcd(125, 729) = 1. So y-x = 5^3, y+x = 9^3, with gcd(5, 9) = 1.
#     Then w = 5*9 = 45 ✓.
# Case 1 applies to F2 with (a, b) = (5, 9).
#
# Case 2: d_1 = 2 (when y, x both odd would make d_1 = 2).
#   Then y-x = 2a^3, y+x = 2b^3 → y = a^3 + b^3, x = b^3 - a^3, w = 2ab.
# F1: w=6, x=15, y=21. y = 21 = a^3 + b^3? a^3 + b^3 = 21. (1, 2) gives 1+8=9, (2,?)... no. (1, ?)
#   Try (1, 2): w = 2*1*2 = 4 ≠ 6. (a,b)=(? ?)...
#   Actually a^3 + b^3 = 21 has no small integer solution. So Case 2 doesn't apply either.
#   F1 has y-x = 6 = 2*3, y+x = 36 = 4*9 = 2^2*3^2. gcd(y-x, y+x) = 6.
#   So d_1 = 6 = 2*3, not 1 or 2. Tells us gcd(x,y) > 1 (both divisible by 3).
#   Indeed: gcd(15, 21) = 3. So this is the NON-PRIMITIVE Mordell case.

# Conclusion: F1 = 3 * (primitive Mordell with w'/3 = 2, etc.)
# Let me normalize F1 by 3: F1 base (6,15,21) divided by gcd(15,21)=3: (6, 5, 7).
# Check Mordell: 5^2 + 6^3 = 25 + 216 = 241 ≠ 7^2 = 49. NOT Mordell.
# But the AP form: 8 * 6^3 = 1728, 4 * 21^2 = 1764, 8 * 15^2 = 1800.
# If we tried (w', x', y') = (6, 5, 7): n0 = 8*216 = 1728, n1 = 4*49 = 196, n2 = 8*25 = 200.
# (1728, 196, 200)? Not AP.

# So F1 (6, 15, 21) doesn't reduce easily.

# OK let me look at primitive Mordell triples directly to find structure.
print("\n=== All primitive Mordell triples (gcd(w, x, y) = 1) ===")
print("  Looking for further structure...")
prim_mordell = [(w, x, y) for (w, x, y) in mordell if gcd(gcd(w, x), y) == 1]
print(f"  {len(prim_mordell)} primitive triples")

# For each primitive, parametrize: y^2 - x^2 = w^3, so (y-x)(y+x) = w^3
# If gcd(y-x, y+x) = 1: y-x = a^3, y+x = b^3, w = ab, gcd(a,b)=1.
# If gcd = 2: y-x = 2a^3, y+x = 2b^3 (both y, x odd impossibility unless...).
#   Actually y+x and y-x differ by 2x, so their gcd divides 2x. If gcd(y-x, y+x) = 2 then y, x both odd? Let's see: if y, x same parity, y±x both even; if opposite parity, y±x both odd.
#   So gcd(y-x, y+x) is 1 (both odd) or 2 (both even? No, then y, x same parity and gcd >= 2).
#   For Mordell-primitive, x, y coprime ⟹ at most one even.

# Let me just check parametrization on first 20 primitive triples
print("\n  First 20 primitive Mordell triples, parametrization check:")
for w, x, y in prim_mordell[:20]:
    yx_minus = y - x
    yx_plus = y + x
    g = gcd(yx_minus, yx_plus)
    parity = (x % 2, y % 2)
    # Try y-x = a^3, y+x = b^3
    a3 = yx_minus
    b3 = yx_plus
    a = round(a3 ** (1/3))
    b = round(b3 ** (1/3))
    a_match = a**3 == a3
    b_match = b**3 == b3
    print(f"  w={w}, x={x}, y={y}: y-x={yx_minus}, y+x={yx_plus}, gcd={g}, parity(x,y)={parity}")
    print(f"    Parametric: a={a} (a^3={a**3}, match={a_match}), b={b} (b^3={b**3}, match={b_match})")
    if a_match and b_match:
        print(f"    ✓ Gives w = a*b = {a*b}, check = {a*b == w}")
