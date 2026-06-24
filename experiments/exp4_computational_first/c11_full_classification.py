"""
EXP4 C11: FULL classification of Mordell solutions and powerful 3-AP base triples.

Findings so far:
- Mordell x^2 + w^3 = y^2 has TWO families:
  Type A: y - x = a^3, y + x = b^3, w = ab, gcd(a, b) = 1, ab same parity ratio.
    Result: w = ab, x = (b^3 - a^3)/2, y = (b^3 + a^3)/2.
    Need a^3, b^3 same parity for x, y integers; so a, b same parity (both odd if gcd=1).
  Type B: y - x = 2a^3, y + x = 2b^3, w = 2ab, gcd(a, b) = 1.
    Result: w = 2ab, x = b^3 - a^3, y = b^3 + a^3.

  - F2 (w=45, x=302, y=427): Type A with (a, b) = (5, 9).
  - F1 (w=6, x=15, y=21): NOT primitive (gcd(15, 21) = 3). After dividing out gcd:
    Actually let me re-examine F1.
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

# ============================================================
# A: Enumerate via PARAMETRIC families
# Type A: (a, b) coprime, same parity (both odd or one of them 1)
#   If both odd: w = ab, x = (b^3-a^3)/2, y = (b^3+a^3)/2 (need a^3+b^3 even, so a, b same parity; coprime forces both odd)
#   Actually if both even, gcd >= 2 not coprime. So both odd.
# Type B: (a, b) coprime, not both odd (one even). w = 2ab, x = b^3-a^3, y = b^3+a^3.
# ============================================================
print("=== Type A: a^3+b^3 = 2y, b^3-a^3 = 2x, w = ab; both a, b odd coprime ===")
print(f"  {'(a, b)':<15} {'w':<10} {'x':<12} {'y':<12} {'(8w^3, 4y^2, 8x^2)':<40} {'inter'}")
A_results = []
for a in range(1, 50, 2):  # both odd
    for b in range(a + 2, 200, 2):  # b > a, both odd
        if gcd(a, b) != 1:
            continue
        a3 = a**3
        b3 = b**3
        w = a * b
        x = (b3 - a3) // 2
        y = (b3 + a3) // 2
        n0 = 8 * w**3
        n1 = 4 * y * y
        n2 = 8 * x * x
        if n2 > N_BOUND:
            continue
        # Check x^2 > w^3 for proper AP order
        if x*x <= w**3:
            continue
        # check all powerful (automatic by Mordell construction)
        # check consecutive
        lo = bisect.bisect_right(powerful_sorted, n0)
        hi = bisect.bisect_left(powerful_sorted, n2)
        pos = bisect.bisect_left(powerful_sorted, n1)
        inter = hi - lo
        if lo <= pos < hi:
            inter -= 1
        A_results.append((a, b, w, x, y, n0, n1, n2, inter))

# Sort by n0
A_results.sort(key=lambda r: r[5])
for r in A_results[:40]:
    a, b, w, x, y, n0, n1, n2, inter = r
    marker = "*** CONSEC ***" if inter == 0 else ""
    print(f"  ({a}, {b}):       {w:<10} {x:<12} {y:<12} ({n0}, {n1}, {n2})  inter={inter} {marker}")

print(f"\n  Type A: {len(A_results)} triples found")
print(f"  Type A consecutive: {sum(1 for r in A_results if r[8] == 0)}")
print(f"  Type A near-consecutive (inter <= 5): {sum(1 for r in A_results if 0 <= r[8] <= 5)}")

# ============================================================
# B: Type B (a, b) coprime not both odd, w = 2ab
# ============================================================
print("\n=== Type B: w = 2ab, x = b^3 - a^3, y = b^3 + a^3; a, b coprime not both odd ===")
print(f"  {'(a, b)':<15} {'w':<10} {'x':<12} {'y':<12} {'(n0, n1, n2)':<40} {'inter'}")
B_results = []
for a in range(1, 50):
    for b in range(a + 1, 200):
        if gcd(a, b) != 1:
            continue
        if a % 2 == 1 and b % 2 == 1:
            continue  # skip both odd (covered by Type A)
        a3 = a**3
        b3 = b**3
        w = 2 * a * b
        x = b3 - a3
        y = b3 + a3
        if x % 2 != 0 and y % 2 != 0:
            # x, y both odd, OK
            pass
        n0 = 8 * w**3
        n1 = 4 * y * y
        n2 = 8 * x * x
        if n2 > N_BOUND:
            continue
        if x*x <= w**3:
            continue
        lo = bisect.bisect_right(powerful_sorted, n0)
        hi = bisect.bisect_left(powerful_sorted, n2)
        pos = bisect.bisect_left(powerful_sorted, n1)
        inter = hi - lo
        if lo <= pos < hi:
            inter -= 1
        B_results.append((a, b, w, x, y, n0, n1, n2, inter))

B_results.sort(key=lambda r: r[5])
for r in B_results[:40]:
    a, b, w, x, y, n0, n1, n2, inter = r
    marker = "*** CONSEC ***" if inter == 0 else ""
    print(f"  ({a}, {b}):       {w:<10} {x:<12} {y:<12} ({n0}, {n1}, {n2})  inter={inter} {marker}")

print(f"\n  Type B: {len(B_results)} triples found")
print(f"  Type B consecutive: {sum(1 for r in B_results if r[8] == 0)}")

# ============================================================
# C: F1 case revisited
# F1 (w, x, y) = (6, 15, 21). gcd(w, x, y) = 3. Divide by 3:
# (w/3, x/3, y/3) = (2, 5, 7). Check Mordell: 5^2 + 2^3 = 25 + 8 = 33 ≠ 7^2 = 49. NOT Mordell.
# So F1 is NOT a scaling of a primitive Mordell.
# Rather: F1 is (6, 15, 21) with the relation 15^2 + 6^3 = 225 + 216 = 441 = 21^2. Yes Mordell.
# gcd(6, 15, 21) = 3, but Mordell uses different scaling.
# If (w, x, y) all multiples of 3: w=3W, x=3X, y=3Y, then x^2 + w^3 = y^2 becomes 9X^2 + 27W^3 = 9Y^2 ⟹ X^2 + 3W^3 = Y^2. NOT Mordell.
# So scaling isn't multiplicative for w^3 vs x^2, y^2.
# This means F1 is a "DIFFERENT" Mordell solution, not a scaling of a smaller one.

# It does fit Type A with (a, b) = ? Let's check:
# w = ab = 6, x = (b^3-a^3)/2 = 15, y = (b^3+a^3)/2 = 21.
# y^2 = 441 = (b^6 + 2a^3b^3 + a^6)/4. And b^3 + a^3 = 42, so y = 21.
# Then b^3 + a^3 = 42. And a, b odd coprime: (a, b) = (1, ?), or (3, ?).
# a=1: b^3 = 41 (no integer b). a=3: b^3 = 15 (no). a=5: b^3 = -83 (no).
# So Type A doesn't fit.

# Type B: w = 2ab, x = b^3 - a^3, y = b^3 + a^3.
# w = 6 = 2ab ⟹ ab = 3. So (a, b) = (1, 3) (a odd, b odd — NOT type B condition).
# Or (a, b) = (3, 1), but a < b.
# But type B says "not both odd". (1, 3) is both odd. So Type B doesn't fit (1, 3).
# Type A with (a, b) = (1, 3): w = 1*3 = 3 (NOT 6). x = (27-1)/2 = 13. y = (27+1)/2 = 14.
# That's the (3, 13, 14) triple, not F1.

# So F1 is in NEITHER Type A nor Type B in the simple parametrization!
# F1 must be from a NON-PRIMITIVE Mordell where the parametrization is different.

# Let me check: gcd(y-x, y+x) for F1: y-x = 6, y+x = 36. gcd = 6.
# So (y-x)(y+x) = 216 = w^3 = 6^3 ✓.
# But the gcd is 6, so we can't simply factor into cubes.

# Write: y - x = 6 = 2*3, y + x = 36 = 4*9. Their product is 216 = 6^3.
# The factorization into UNIT × CUBE×CUBE:
#   y - x = 2 * 3 (factors with multiplicities)
#   y + x = 2^2 * 3^2
#   gcd(y-x, y+x) = 2 * 3 = 6.
# So y - x = d * a^3' (modified), y + x = d * b^3' where d = gcd.
# (y-x)/d * (y+x)/d = w^3 / d^2 = 216/36 = 6.
# So u * v = 6 where u = (y-x)/6 = 1, v = (y+x)/6 = 6. uv = 6, not a cube anymore.
# This means the standard "cubic" parametrization doesn't apply.

# Let me check if (1, 6) factors into cubes after multiplying by gcd:
# u = 1 = 1^3, v = 6 = 2*3 — not a cube. So this doesn't fit "two cubes" form.

# But Mordell x^2 + w^3 = y^2 always has SOME solution structure. The fundamental theorem
# (for the curve E_k: y^2 = x^3 + k) says finite rank, finite torsion. So solutions are finite up to torsion + finite rank.

# But for w VARIABLE (not just fixed k), the set is infinite. The parametric Type A and Type B
# give ALL coprime solutions, and non-coprime are scalings — but scaling is messy because of x^2 vs w^3.

# Actually: if (w, x, y) is a solution and d | w, x, y, write w = dw', x = dx', y = dy'.
# Then d^2 x'^2 + d^3 w'^3 = d^2 y'^2 ⟹ x'^2 + d w'^3 = y'^2.
# This isn't Mordell anymore — it's Mordell only if d = 1.
# So scalings don't preserve Mordell.

# But (6, 15, 21) with gcd 3: 15^2 + 6^3 = 21^2. Divide by 9: 25 + 24 = 49. So 25 + 24 = 49, but 24 = 6^3/9 = 24, not a cube.
# So (6, 15, 21) is NOT a scaling of any primitive Mordell solution. It's its own primitive structure.

# Let me see if it fits a MIXED type:
# (y - x)(y + x) = w^3. With gcd(y-x, y+x) = 6 = w.
# So write y - x = w * a (where a = (y-x)/w = 1), y + x = w * b (where b = (y+x)/w = 6).
# Then w^2 * a * b = w^3 ⟹ a * b = w ⟹ 1 * 6 = 6 ✓.
# So F1 has the form: y - x = w * a, y + x = w * b, a * b = w.
# (a, b) = (1, 6). a, b coprime? gcd(1, 6) = 1 ✓.
# And w = a*b means w = ab. So this is consistent!
# General formula: y = w(a+b)/2, x = w(b-a)/2.
# For F1: w=6, a=1, b=6, y = 6*7/2 = 21, x = 6*5/2 = 15 ✓✓.

# So this is a NEW TYPE: Type C — "self-similar" Mordell where w = a*b with gcd(a,b) = 1.
# Then the solution is (w, x, y) = (ab, ab(b-a)/2, ab(a+b)/2).
# Valid iff a+b even (i.e., a, b same parity) since (a+b)/2 must be integer.
# Or if a, b mixed parity AND ab is even — then ab(b-a)/2 might still be integer.

# Type C with (a, b) = (1, 6): w = 6, x = 15, y = 21. But a=1 odd, b=6 even — mixed parity.
# w(b-a) = 6*5 = 30, w(a+b)=6*7=42. Divide by 2: x=15, y=21. Integer because 30, 42 even (since w=6 even).
# So when w is even, mixed parity (a, b) works.

# Type C with (a, b) = (1, 2): w = 2, x = 1*(2-1) = 1, y = 1*(1+2)/2 ... wait formula: x = w(b-a)/2 = 2*1/2 = 1. y = w(a+b)/2 = 2*3/2 = 3.
# Check: x^2 + w^3 = 1 + 8 = 9 = y^2 ✓.
# So (w, x, y) = (2, 1, 3). But x^2 > w^3 needs 1 > 8, FALSE. So not a proper AP.
# Skip.

# Type C with (a, b) = (1, 4): w = 4, x = 4*3/2 = 6, y = 4*5/2 = 10. 6^2 + 4^3 = 36+64 = 100 = 10^2 ✓.
# x^2 > w^3? 36 > 64 NO. Skip.

# Type C with (a, b) = (1, 8): w = 8, x = 8*7/2 = 28, y = 8*9/2 = 36. 28^2 + 8^3 = 784 + 512 = 1296 = 36^2 ✓.
# x^2 > w^3? 784 > 512 ✓. So (w, x, y) = (8, 28, 36) is valid.
# n0 = 8*512 = 4096, n1 = 4*1296 = 5184, n2 = 8*784 = 6272. We saw this in c9 with inter=28.

# Type C with (a, b) = (2, 3): w = 6, x = 6*1/2 = 3, y = 6*5/2 = 15. 3^2 + 6^3 = 9 + 216 = 225 = 15^2 ✓.
# x^2 > w^3? 9 > 216 NO. Skip.

# Type C with (a, b) = (3, 4): w = 12, x = 12*1/2 = 6, y = 12*7/2 = 42. 6^2 + 12^3 = 36+1728 = 1764 = 42^2 ✓.
# x^2 > w^3? 36 > 1728 NO. Skip.

# Type C with (a, b) = (1, 6): w=6, x=15, y=21 → F1 ✓ (with x^2 = 225 > 216 = w^3 ✓).

# Hmm, so F1 is a SPECIAL Type C solution with x^2 just barely greater than w^3 (225 vs 216, ratio 1.04).
# This is what makes F1 a candidate for CONSECUTIVENESS: the gap n2 - n0 = 8(x^2-w^3) is SMALL relative to n0.

# CONJECTURE: Consecutive 3-APs require x^2 - w^3 SMALL relative to w^3.
# In F1: x^2 - w^3 = 225 - 216 = 9, ratio 9/216 = 0.04 ≈ 1/24.
# In F2: x^2 - w^3 = 91204 - 91125 = 79, ratio 79/91125 ≈ 0.00087.
# In the near-miss (140, 1657, 2343): x^2 - w^3 = 2745649 - 2744000 = 1649, ratio 1649/2744000 ≈ 0.0006.
# In other near-miss (180, 2416, 3416): x^2 - w^3 = 5837056 - 5832000 = 5056, ratio 5056/5832000 ≈ 0.00087.

# Pattern: the consecutive ones have x^2 - w^3 EXTREMELY small relative to w^3.

print("\n=== Type C: y±x = wab/wba ===")
# Type C with (a, b) coprime, w = ab (so a*b = w), x = w(b-a)/2, y = w(a+b)/2.
# Iterate (a, b) with a < b, gcd = 1, ab small enough.
print(f"  Searching Type C (a, b) coprime, w=ab, x=w(b-a)/2, y=w(a+b)/2 ...")
C_results = []
for a in range(1, 100):
    for b in range(a + 1, 1000):
        if gcd(a, b) != 1:
            continue
        w = a * b
        # x and y must be integers
        if (b - a) * w % 2 != 0:
            continue
        x = w * (b - a) // 2
        y = w * (a + b) // 2
        if x*x <= w**3:
            continue
        n0 = 8 * w**3
        n1 = 4 * y * y
        n2 = 8 * x * x
        if n2 > N_BOUND:
            break
        # Verify Mordell
        assert x*x + w**3 == y*y, f"Type C failed: {a}, {b}, x={x}, w={w}, y={y}: {x*x + w**3} != {y*y}"
        # Compute intervening
        lo = bisect.bisect_right(powerful_sorted, n0)
        hi = bisect.bisect_left(powerful_sorted, n2)
        pos = bisect.bisect_left(powerful_sorted, n1)
        inter = hi - lo
        if lo <= pos < hi:
            inter -= 1
        C_results.append((a, b, w, x, y, n0, n1, n2, inter))

C_results.sort(key=lambda r: (r[8], r[5]))  # by inter ascending, then n0
print(f"\n  Type C results (sorted by intervening count, top 40):")
print(f"  {'(a, b)':<15} {'w':<8} {'x':<12} {'y':<12} {'n0':<15} {'inter'}")
for r in C_results[:40]:
    a, b, w, x, y, n0, n1, n2, inter = r
    marker = "*** CONSEC ***" if inter == 0 else ""
    print(f"  ({a:<3}, {b:<3})        {w:<8} {x:<12} {y:<12} {n0:<15} {inter} {marker}")

print(f"\n  Type C: {len(C_results)} triples")
print(f"  Type C consecutive: {sum(1 for r in C_results if r[8] == 0)}")

# Now compare to ALL Mordell solutions
print("\n\n=== Summary ===")
total_A = len(A_results)
total_B = len(B_results)
total_C = len(C_results)
print(f"  Type A: {total_A} (odd-odd coprime)")
print(f"  Type B: {total_B} (mixed parity coprime)")
print(f"  Type C: {total_C} (a, b coprime, w = a*b)")

consec_A = [r for r in A_results if r[8] == 0]
consec_B = [r for r in B_results if r[8] == 0]
consec_C = [r for r in C_results if r[8] == 0]

print(f"\n  Consecutive Type A: {len(consec_A)} -- {consec_A}")
print(f"  Consecutive Type B: {len(consec_B)}")
print(f"  Consecutive Type C: {len(consec_C)} -- {consec_C}")

# Cross-check: does Type C with (1, 6) match F1?
for r in C_results:
    a, b, w, x, y, n0, n1, n2, inter = r
    if (a, b) == (1, 6):
        print(f"\n  Type C (1, 6) → (w={w}, x={x}, y={y}) = ({n0}, {n1}, {n2}), inter={inter} -- F1 base ✓ {'(consec ✓)' if inter == 0 else ''}")
# And Type A with (5, 9):
for r in A_results:
    a, b, w, x, y, n0, n1, n2, inter = r
    if (a, b) == (5, 9):
        print(f"  Type A (5, 9) → (w={w}, x={x}, y={y}) = ({n0}, {n1}, {n2}), inter={inter} -- F2 base ✓ {'(consec ✓)' if inter == 0 else ''}")
