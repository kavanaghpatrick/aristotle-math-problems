"""
EXP4 C9: FOCUSED Mordell equation analysis for powerful 3-APs.

KEY INSIGHT (data-derived):
F2's structure: 302^2 + 45^3 = 427^2, i.e., x^2 + w^3 = y^2 with (w, x, y) = (45, 302, 427).

GENERALIZATION: For ANY (w, x, y) with x^2 + w^3 = y^2 AND x^2 > w^3, the triple
  (8w^3, 4y^2, 8x^2)
is automatically a powerful 3-AP!  (Proof: 8w^3 = 2^3 * w^3 powerful; 4y^2 square = powerful;
8x^2 = 2^3 * x^2 powerful; AP because 2*4y^2 = 8(x^2 + w^3) = 8x^2 + 8w^3.)

This is the "Mordell-powerful family" — a NEW INFINITE FAMILY of powerful 3-APs derived purely
from solutions to x^2 + w^3 = y^2.

CONJECTURE: Up to scaling, the consecutive powerful 3-APs come ONLY from:
(a) The F1 family: (1728, 1764, 1800) and (6912, 7056, 7200).
(b) The Mordell family with very specific (w, x, y).

Let's enumerate ALL Mordell solutions (w, x, y) with y^2 <= 10^11 / 4 (so n1 <= 10^11)
and check which give consecutive powerful 3-APs.
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
print(f"Loaded {len(powerful)} powerful numbers up to {N_BOUND}")

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
# Mordell search: enumerate all (w, x, y) with x^2 + w^3 = y^2
# such that n2 = 8 x^2 <= N_BOUND.
# Then x <= sqrt(N_BOUND / 8) ~ sqrt(1.25e10) ~ 1.118e5.
# w can range from 1 to (N_BOUND / 8)^(1/3) ~ 23208 (so 8w^3 <= N_BOUND).
# But we need x^2 > w^3 (proper AP order), so w < x^(2/3).
# ============================================================
print("\n=== Mordell search for (w, x, y) with x^2 + w^3 = y^2 ===")
N1_MAX = N_BOUND // 4  # since n1 = 4y^2 <= N_BOUND ⟹ y^2 <= N_BOUND/4
X_MAX = isqrt(N_BOUND // 8) + 1  # n2 = 8x^2 <= N_BOUND ⟹ x^2 <= N_BOUND/8

mordell = []  # list of (w, x, y)
t0 = time.time()
# Iterate w from 1 to W_MAX where W_MAX = max w with w^3 <= x^2 for some x <= X_MAX
# i.e., w^3 <= X_MAX^2
W_MAX = int(X_MAX ** (2/3)) + 1
print(f"  Searching w in [1, {W_MAX}], x in [w^(3/2)+1, {X_MAX}]")

for w in range(1, W_MAX + 1):
    w3 = w**3
    if 8 * w3 > N_BOUND:
        break
    # x > w^(3/2): x >= ceil(sqrt(w^3) + 1) ... but really we need x^2 > w^3.
    # If w^3 is a perfect square (i.e., w is a square), x can be sqrt(w^3) + 1; else ceil(sqrt(w^3))+0.
    x_lo = isqrt(w3)
    if x_lo * x_lo <= w3:
        x_lo += 1  # ensure x^2 > w^3
    x = x_lo
    while True:
        x2 = x * x
        if 8 * x2 > N_BOUND:
            break
        y2 = x2 + w3
        y = isqrt(y2)
        if y * y == y2:
            mordell.append((w, x, y))
        x += 1

print(f"  Found {len(mordell)} (w, x, y) solutions to x^2 + w^3 = y^2 with 8x^2 <= 10^11, x^2 > w^3")
print(f"  Time: {time.time()-t0:.1f}s")

# Now check which are CONSECUTIVE powerful 3-APs
consec_mordell = []
all_mordell_3aps = []
for w, x, y in mordell:
    n0 = 8 * w**3
    n1 = 4 * y * y
    n2 = 8 * x * x
    if n2 > N_BOUND:
        continue
    # All powerful (we proved this) — verify just to be safe
    if not all(n in powerful_set for n in [n0, n1, n2]):
        # Sanity: this shouldn't happen
        print(f"  WARN: (w={w}, x={x}, y={y}) gives ({n0}, {n1}, {n2}) — at least one not in our set!")
        continue
    inter = num_intervening(n0, n2, n1)
    all_mordell_3aps.append((w, x, y, n0, n1, n2, inter))
    if inter == 0:
        consec_mordell.append((w, x, y, n0, n1, n2))

print(f"\n  Of {len(all_mordell_3aps)} Mordell-derived powerful 3-APs:")
print(f"    Consecutive: {len(consec_mordell)}")

print("\n  ALL CONSECUTIVE Mordell-derived:")
for w, x, y, n0, n1, n2 in consec_mordell:
    print(f"    (w={w}, x={x}, y={y}): ({n0}, {n1}, {n2})")
    print(f"      n0 = 8 * {w}^3 = {fmt(n0)}")
    print(f"      n1 = 4 * {y}^2 = {fmt(n1)}")
    print(f"      n2 = 8 * {x}^2 = {fmt(n2)}")

# Show histogram of intervening counts
inter_dist = Counter(r[6] for r in all_mordell_3aps)
print(f"\n  Intervening count distribution (all Mordell 3-APs):")
for k in sorted(inter_dist)[:20]:
    print(f"    inter={k}: {inter_dist[k]} APs")

# Show 30 smallest-intervening Mordell 3-APs
print("\n  30 lowest-intervening Mordell 3-APs:")
all_mordell_3aps.sort(key=lambda r: (r[6], r[5]))
for r in all_mordell_3aps[:30]:
    w, x, y, n0, n1, n2, inter = r
    print(f"    (w={w}, x={x}, y={y}): ({n0}, {n1}, {n2}), inter={inter}")

# ============================================================
# Now: do ALL 6 consec 3-APs lie in either F1 (1728, 6912) or the Mordell family?
# Let's check: each consec 3-AP, can it be written as (8w^3, 4y^2, 8x^2)?
# ============================================================
print("\n=== Cross-check: are F2 consecutives in Mordell family? ===")
known_consec = [
    (1728, 1764, 1800),
    (6912, 7056, 7200),
    (729000, 729316, 729632),
    (1458000, 1458632, 1459264),
    (2916000, 2917264, 2918528),
    (11664000, 11669056, 11674112),
]
for n0, n1, n2 in known_consec:
    # Try to write n0 = 8w^3, n1 = 4y^2, n2 = 8x^2
    n0_8 = n0 / 8
    n1_4 = n1 / 4
    n2_8 = n2 / 8
    w_cube_root = n0_8 ** (1/3)
    y_sqrt = n1_4 ** 0.5
    x_sqrt = n2_8 ** 0.5
    w = round(w_cube_root)
    y = round(y_sqrt)
    x = round(x_sqrt)
    print(f"  ({n0}, {n1}, {n2}):")
    print(f"    n0/8 = {n0/8}, sup-fit w={w} (w^3 = {w**3}, match={w**3 == n0//8})")
    print(f"    n1/4 = {n1/4}, sup-fit y={y} (y^2 = {y**2}, match={y*y == n1//4})")
    print(f"    n2/8 = {n2/8}, sup-fit x={x} (x^2 = {x**2}, match={x*x == n2//8})")
    in_family = (w**3 == n0//8) and (y*y == n1//4) and (x*x == n2//8)
    if in_family:
        # Verify x^2 + w^3 = y^2
        print(f"    IN MORDELL FAMILY: x^2 + w^3 = {x*x} + {w**3} = {x*x + w**3} =? y^2 = {y*y}, match={x*x + w**3 == y*y}")

# F1 instances: 1728 = 8 * 216 = 8 * 6^3. Yes!
# So 1728 = 8 * 6^3. And 1764 = 4 * 441 = 4 * 21^2. And 1800 = 8 * 225 = 8 * 15^2.
# Check Mordell: x^2 + w^3 = y^2 with (w, x, y) = (6, 15, 21): 15^2 + 6^3 = 225 + 216 = 441 = 21^2. YES!
# But wait: x^2 = 225, w^3 = 216, so x^2 > w^3 ✓ (proper AP order).

# 6912 = 8 * 864 = 8 * ?  864 = 2^5 * 3^3. 864^(1/3) ~ 9.52. So 864 is NOT a cube. So 6912 is NOT in 8w^3 form.
# Hmm. But 6912 = 1728 * 4 = 2^2 * 1728 = 4 * (8 * 6^3) = 32 * 6^3 ≠ 8 * something^3.
# Actually 6912 / 8 = 864 — not a cube. So (6912, 7056, 7200) is NOT in the Mordell form 8w^3.

# So we need to GENERALIZE: maybe Mordell-form is 4 * w^3 or k * w^3?
# (6912, 7056, 7200): n0 = 2^8 * 3^3 = 256 * 27. So n0 = 256 * 27 = 6912. Equivalently 32 * 6^3 (since 6^3=216, 32*216=6912).
# Or 2^8 * 3^3 = (2^4)^2 * 27 = 256 * 27. Mordell-like: 4 * w^3 needs w^3 = 1728, w=12; then n0=4*12^3=4*1728=6912 ✓.
# So with k=4 (instead of 8): n0=4*12^3=6912, n1=?·12·12 = ?
# n1 = 7056 = 2^4 * 3^2 * 7^2 = (2^2 * 3 * 7)^2 = 84^2. So n1 = 84^2, not 4*y^2 form unless y=42, then 4*42^2=7056 ✓.
# n2 = 7200 = 2^5 * 3^2 * 5^2 = 4 * 2^3 * 3^2 * 5^2 = 4 * 1800 = 4 * (2^3 * 225). Or 8 * 30^2 (8*900 = 7200, 30^2=900). So n2=8*30^2.
# So (6912, 7056, 7200): trying n0=4w^3, n1=4y^2, n2=8x^2 gives w=12, y=42, x=30. Check AP: 4*12^3 + 8*30^2 = 6912 + 7200 = 14112; 2*4*42^2 = 14112 ✓. AP holds.
# But the Mordell identity: x^2 + (k/4)w^3 = y^2? Hmm. 30^2 + 12^3 = 900 + 1728 = 2628 ≠ 42^2 = 1764. NOT same Mordell.

# So (6912, 7056, 7200) is a DIFFERENT family: maybe a "scaled" version of (1728, 1764, 1800) by 4.
# Let me check (6912, 7056, 7200) = 4 * (1728, 1764, 1800). YES, exactly.

# So (1728, 1764, 1800) is the F1 base from Mordell (6, 15, 21).
# And (6912, 7056, 7200) = 4 * F1.
# F2 base (729000, 729316, 729632) from Mordell (45, 302, 427).
# F2 m=2: (1458000, ...) = 2 * F2.
# F2 m=4: (2916000, ...) = 4 * F2.
# F2 m=16: (11664000, ...) = 16 * F2.

# So all 6 are: F1, 4*F1, F2, 2*F2, 4*F2, 16*F2.
# Both F1 and F2 are in the (8w^3, 4y^2, 8x^2) form from Mordell.

# SHARP CONJECTURE FROM DATA:
# Every consecutive powerful 3-AP is of the form k * (8w^3, 4y^2, 8x^2)
# where k is a "consecutiveness-preserving multiplier" and (w, x, y) satisfies x^2 + w^3 = y^2.
# Moreover, (w, x, y) must be "primitive" (gcd considerations).

# What primitive Mordell triples (w, x, y) exist?
print("\n=== Primitive Mordell triples ===")
prim_mordell = []
for w, x, y in mordell:
    if gcd(gcd(w, x), y) == 1:
        prim_mordell.append((w, x, y))

print(f"  {len(prim_mordell)} primitive Mordell triples (gcd(w,x,y)=1) up to x^2 <= 10^11/8")
print("  First 30:")
for w, x, y in prim_mordell[:30]:
    n0 = 8 * w**3
    n1 = 4 * y*y
    n2 = 8 * x*x
    inter = num_intervening(n0, n2, n1)
    print(f"    (w={w:>5}, x={x:>8}, y={y:>8}): ({n0}, {n1}, {n2}), inter={inter}")
