"""
EXP4 C2: Find ALL powerful 3-APs (consecutive AND non-consecutive) up to 10^11.

For each pair (n_i, n_j) with n_i < n_j powerful, check whether 2*n_j - n_i is also powerful.
This is O(P^2) but we can do better: for each n_i, iterate gap d=n_j-n_i over a controlled
range, check if both n_i+d and n_i+2d are in the powerful set.

But the consecutiveness check requires us to know the local neighborhood of powerful numbers.

Strategy:
1. Load all powerful up to 10^11 into a sorted array
2. For consecutive 3-APs: check (P[i], P[i+1], P[i+2]) and 2*P[i+1] == P[i] + P[i+2]
3. For ALL 3-APs (any gap): O(P^2). Since P ~ 7*10^5, this is ~5*10^11 ops -- too slow naive.
   Use HASH-based approach: for each pair (n_i, n_j) with j < some bound, check n_i+2(j-i) in set.

We'll do up to 10^9 for non-consecutive (still gives ~70K powerful, 5*10^9 ops, ~minutes).
And consecutive scan over the full 10^11 set.
"""

import struct
import time
import json
from math import gcd, isqrt
from collections import defaultdict

DATA = "/Users/patrickkavanagh/math/experiments/exp4_computational_first/powerful_1e11.bin"
print(f"Loading powerful numbers from {DATA}...")
t0 = time.time()
with open(DATA, "rb") as f:
    N_BOUND, count = struct.unpack("<QQ", f.read(16))
    powerful = list(struct.unpack(f"<{count}Q", f.read(count * 8)))
print(f"  loaded {len(powerful)} numbers in {time.time()-t0:.1f}s")
powerful_set = set(powerful)
P = powerful

# ============================================================
# PART A: All consecutive powerful 3-APs up to 10^11
# ============================================================
print("\n=== PART A: Consecutive powerful 3-APs up to 10^11 ===")
consec = []
t0 = time.time()
for i in range(len(P) - 2):
    if 2 * P[i+1] == P[i] + P[i+2]:
        consec.append((P[i], P[i+1], P[i+2]))
print(f"  found {len(consec)} consecutive 3-APs in {time.time()-t0:.1f}s")
for ap in consec:
    print(f"    {ap}  gap={ap[1]-ap[0]}")

# ============================================================
# PART B: All powerful 3-APs (any gap) with n0 <= 10^8
# ============================================================
print("\n=== PART B: All powerful 3-APs with n_0 <= 10^8 ===")
N_3AP_BOUND = 10**8
all_3aps = []
t0 = time.time()
# Use the powerful list filtered
P_small = [p for p in P if p <= N_3AP_BOUND]
P_small_set = set(P_small)
print(f"  {len(P_small)} powerful with n_0 <= {N_3AP_BOUND}")
# For each i, j with i<j: check if 2*P[j]-P[i] is powerful and <= 10^11
for i in range(len(P_small)):
    n0 = P_small[i]
    for j in range(i+1, len(P_small)):
        n1 = P_small[j]
        d = n1 - n0
        n2 = n1 + d
        if n2 > N_BOUND:
            break
        if n2 in powerful_set:
            all_3aps.append((n0, n1, n2))
    if i % 5000 == 0:
        print(f"  i={i}/{len(P_small)}, |3aps|={len(all_3aps)}, t={time.time()-t0:.1f}s")
print(f"  total: {len(all_3aps)} powerful 3-APs with n_0 <= 10^8 in {time.time()-t0:.1f}s")

# ============================================================
# PART C: Distributional analysis - histogram of 3-AP counts
# ============================================================
print("\n=== PART C: Distribution analysis ===")
# Histogram by log10(n_0)
bins = defaultdict(int)
for (n0, n1, n2) in all_3aps:
    log_bin = int(math_log10(n0)) if (math_log10 := lambda x: __import__('math').log10(x)) else 0
import math
bins = defaultdict(int)
for (n0, n1, n2) in all_3aps:
    log_bin = int(math.log10(n0))
    bins[log_bin] += 1
print("  3-AP counts by log10(n_0) bin:")
for b in sorted(bins):
    print(f"    [10^{b}, 10^{b+1}): {bins[b]} 3-APs")

# ============================================================
# PART D: Consecutive vs non-consecutive ratio
# ============================================================
print("\n=== PART D: For each non-consecutive 3-AP, count intervening powerfuls ===")
# Build sorted P_small for binary search
import bisect
sorted_P = sorted(P)
intervening_counts = []
for (n0, n1, n2) in all_3aps:
    # count powerfuls m with n0 < m < n2, m != n1
    lo = bisect.bisect_right(sorted_P, n0)
    hi = bisect.bisect_left(sorted_P, n2)
    inter = hi - lo - 1  # subtract n1 itself
    intervening_counts.append(inter)

from collections import Counter
inter_hist = Counter(intervening_counts)
print(f"  intervening powerful count histogram (over {len(all_3aps)} 3-APs):")
for k in sorted(inter_hist)[:20]:
    print(f"    {k} intervening: {inter_hist[k]} 3-APs")
print(f"  3-APs with 0 intervening (= consecutive): {inter_hist[0]}")

# ============================================================
# Save results
# ============================================================
result = {
    "N_bound": N_BOUND,
    "n0_bound_for_all_3aps": N_3AP_BOUND,
    "consecutive_3aps": consec,
    "all_3aps_count": len(all_3aps),
    "intervening_histogram": dict(inter_hist),
    "distribution_by_log10": dict(bins),
}
out = "/Users/patrickkavanagh/math/experiments/exp4_computational_first/c2_results.json"
with open(out, "w") as f:
    json.dump(result, f, indent=2)
print(f"\nSaved to {out}")

# Also save the full 3-AP list (could be large)
with open("/Users/patrickkavanagh/math/experiments/exp4_computational_first/c2_all_3aps.txt", "w") as f:
    f.write(f"# All powerful 3-APs (n0, n1, n2) with n0 <= {N_3AP_BOUND}, n2 <= {N_BOUND}\n")
    for ap in all_3aps:
        f.write(f"{ap[0]} {ap[1]} {ap[2]}\n")
print(f"  all 3-APs saved to c2_all_3aps.txt ({len(all_3aps)} entries)")
