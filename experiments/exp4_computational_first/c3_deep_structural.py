"""
EXP4 C3: Deep structural analysis of ALL 246,812 powerful 3-APs.

We're looking for any structural pattern that might give us a sharper conjecture.
We DON'T look at prior theory. We just dump the data.

For each 3-AP, compute:
1. Full prime factorization of n0, n1, n2
2. Golomb form (a, b) with n = a^2*b^3, b squarefree
3. gcd patterns
4. The diff structure: n1-n0 = d, common factor structure
5. The product n0*n1*n2 factorization
6. The identity n1^2 - n0*n2 = ? (since they're in AP, this should be d^2 - ... wait, if 2n1=n0+n2, then (n1-n0)(n2-n1) = d^2 = n1^2 - n0n2)
7. Mod patterns: mod 4, 9, 7, 11, 25, 27, 49, 5, 8, 16, 36, 72, 144
8. Prime exponent vectors
"""

import time
import json
import bisect
from collections import defaultdict, Counter
from math import gcd, isqrt
from itertools import combinations

def factor(n):
    f = {}
    m = n
    p = 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
        if p > 2 and p % 2 == 0:
            p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def golomb(n):
    """Unique decomp n = a^2 b^3 with b squarefree."""
    f = factor(n)
    a, b = 1, 1
    for p, e in f.items():
        if e % 2 == 0:
            a *= p ** (e // 2)
        else:
            b *= p
            a *= p ** ((e - 3) // 2)
    assert a*a*b*b*b == n, f"golomb failed for {n}"
    return (a, b)

# Load 3-APs
print("Loading 3-APs from c2_all_3aps.txt...")
all_3aps = []
with open("/Users/patrickkavanagh/math/experiments/exp4_computational_first/c2_all_3aps.txt") as f:
    for line in f:
        if line.startswith("#"): continue
        parts = line.strip().split()
        if len(parts) == 3:
            all_3aps.append(tuple(int(x) for x in parts))
print(f"  loaded {len(all_3aps)} 3-APs")

# Compute structural records
print("\nComputing structural data for all 3-APs (this may take 5-10 min)...")
t0 = time.time()
records = []
for idx, (n0, n1, n2) in enumerate(all_3aps):
    if idx % 5000 == 0:
        print(f"  {idx}/{len(all_3aps)}  t={time.time()-t0:.1f}s")
    d = n1 - n0
    g = gcd(gcd(n0, n1), n2)
    rec = {
        "n0": n0, "n1": n1, "n2": n2, "d": d, "gcd3": g,
        "f0": factor(n0), "f1": factor(n1), "f2": factor(n2),
    }
    rec["g0"] = golomb(n0)
    rec["g1"] = golomb(n1)
    rec["g2"] = golomb(n2)
    rec["m4"] = (n0 % 4, n1 % 4, n2 % 4)
    rec["m9"] = (n0 % 9, n1 % 9, n2 % 9)
    rec["m8"] = (n0 % 8, n1 % 8, n2 % 8)
    rec["m25"] = (n0 % 25, n1 % 25, n2 % 25)
    rec["m27"] = (n0 % 27, n1 % 27, n2 % 27)
    rec["m7"] = (n0 % 7, n1 % 7, n2 % 7)
    rec["m11"] = (n0 % 11, n1 % 11, n2 % 11)
    rec["m36"] = (n0 % 36, n1 % 36, n2 % 36)
    rec["m72"] = (n0 % 72, n1 % 72, n2 % 72)
    rec["m144"] = (n0 % 144, n1 % 144, n2 % 144)
    # Square check
    s0 = isqrt(n0); rec["sq0"] = (s0*s0 == n0)
    s1 = isqrt(n1); rec["sq1"] = (s1*s1 == n1)
    s2 = isqrt(n2); rec["sq2"] = (s2*s2 == n2)
    rec["sq_pattern"] = (rec["sq0"], rec["sq1"], rec["sq2"])
    records.append(rec)
print(f"  computed {len(records)} records in {time.time()-t0:.1f}s")

# ============================================================
# ANALYSIS A: Mod-N signatures
# ============================================================
print("\n=== ANALYSIS A: Modular signatures ===")
for mod_name in ["m4", "m9", "m8", "m25", "m27", "m7", "m11", "m36", "m72"]:
    sigs = Counter(r[mod_name] for r in records)
    print(f"\n  {mod_name} signatures (top 20 of {len(sigs)}):")
    for sig, count in sigs.most_common(20):
        pct = 100 * count / len(records)
        print(f"    {sig}: {count} ({pct:.2f}%)")

# ============================================================
# ANALYSIS B: Common difference d - is there a hidden structure?
# ============================================================
print("\n=== ANALYSIS B: Common difference d structure ===")
d_factors = Counter()
for r in records:
    f = factor(r["d"])
    # Just record the small prime exponents
    sig = tuple(sorted((p, e) for p, e in f.items() if p <= 7))
    d_factors[sig] += 1
print(f"\n  Most common (small-prime) d-factorization signatures (top 30):")
for sig, count in d_factors.most_common(30):
    print(f"    {sig}: {count} ({100*count/len(records):.2f}%)")

# Is d ALWAYS divisible by 36? By 12? By 4?
d_mod_results = defaultdict(int)
for r in records:
    for m in [2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 36, 72, 144]:
        if r["d"] % m == 0:
            d_mod_results[m] += 1
print(f"\n  How often is d divisible by m?")
for m in sorted(d_mod_results):
    print(f"    d divisible by {m}: {d_mod_results[m]}/{len(records)} = {100*d_mod_results[m]/len(records):.2f}%")

# ============================================================
# ANALYSIS C: Square patterns
# ============================================================
print("\n=== ANALYSIS C: Square pattern in (sq0, sq1, sq2) ===")
sq_pats = Counter(r["sq_pattern"] for r in records)
for pat, count in sq_pats.most_common(10):
    print(f"  {pat}: {count} ({100*count/len(records):.2f}%)")

# ============================================================
# ANALYSIS D: Golomb (b0, b1, b2) kernel triples
# ============================================================
print("\n=== ANALYSIS D: Golomb kernel triples (b0, b1, b2) ===")
ker_triples = Counter((r["g0"][1], r["g1"][1], r["g2"][1]) for r in records)
print(f"  Total distinct kernel triples: {len(ker_triples)}")
print(f"  Most common 30 kernel triples:")
for ker, count in ker_triples.most_common(30):
    print(f"    {ker}: {count}")

# Special: when is the middle kernel = 1 (i.e. n1 is a perfect square)?
mid_kernel_1 = sum(1 for r in records if r["g1"][1] == 1)
print(f"\n  3-APs where middle term n1 is a perfect square (b1=1): {mid_kernel_1} ({100*mid_kernel_1/len(records):.2f}%)")

# Special: when are all three kernels = 1 (all three squares)?
all_sq = sum(1 for r in records if r["g0"][1] == 1 and r["g1"][1] == 1 and r["g2"][1] == 1)
print(f"  All three perfect squares: {all_sq}")

# ============================================================
# ANALYSIS E: Diophantine identity (n1)^2 - n0*n2 = d^2 - 2*d*0...
# Actually: n1^2 - n0*n2 = ?  Since n0 = n1-d, n2 = n1+d:
# n1^2 - n0*n2 = n1^2 - (n1-d)(n1+d) = n1^2 - n1^2 + d^2 = d^2
# So d^2 = n1^2 - n0*n2 always. Fine.
# But: is gcd(n0, n1, n2)/d^2 telling us anything?
# ============================================================
print("\n=== ANALYSIS E: gcd(n0, n1, n2) relationships ===")
gcd_d2_ratios = Counter()
for r in records:
    # Note: d^2 = n1^2 - n0*n2, so let's see d^2 / gcd^2
    if r["gcd3"] > 0:
        ratio = r["d"] * r["d"] // (r["gcd3"] * r["gcd3"]) if r["gcd3"]**2 != 0 else 0
        ratio_log = ratio  # round to 4 sig figs
    gcd_d2_ratios[r["d"] % r["gcd3"] if r["gcd3"] > 0 else -1] += 1

# Better: distribution of gcd-as-fraction-of-n0
import math
gcd_log_distrib = Counter()
for r in records:
    gn = r["gcd3"] / r["n0"]
    bucket = round(math.log2(gn) if gn > 0 else 0)
    gcd_log_distrib[bucket] += 1
print(f"  log2(gcd/n0) distribution:")
for k in sorted(gcd_log_distrib):
    print(f"    log2={k} : {gcd_log_distrib[k]}")

# ============================================================
# ANALYSIS F: Is d always divisible by gcd(n0, n2)?
# ============================================================
print("\n=== ANALYSIS F: Is d divisible by gcd(n0, n2)? ===")
divides_count = sum(1 for r in records if r["d"] % gcd(r["n0"], r["n2"]) == 0)
print(f"  d divisible by gcd(n0, n2): {divides_count}/{len(records)} = {100*divides_count/len(records):.2f}%")

# Show counterexamples
print(f"\n  First 10 cases where gcd(n0, n2) does NOT divide d:")
shown = 0
for r in records:
    if shown >= 10:
        break
    g = gcd(r["n0"], r["n2"])
    if r["d"] % g != 0:
        print(f"    ({r['n0']}, {r['n1']}, {r['n2']}): d={r['d']}, gcd(n0,n2)={g}")
        shown += 1

# ============================================================
# Save summary
# ============================================================
summary = {
    "total_3aps": len(records),
    "n_consecutive": sum(1 for r in records if r["n0"] in [1728, 6912, 729000, 1458000, 2916000, 11664000]),
    "mod4_most_common": [(str(k), v) for k, v in Counter(r["m4"] for r in records).most_common(20)],
    "mod9_most_common": [(str(k), v) for k, v in Counter(r["m9"] for r in records).most_common(20)],
    "mod36_most_common": [(str(k), v) for k, v in Counter(r["m36"] for r in records).most_common(30)],
    "kernel_triple_most_common": [(str(k), v) for k, v in Counter((r["g0"][1], r["g1"][1], r["g2"][1]) for r in records).most_common(20)],
    "sq_pattern_distribution": [(str(k), v) for k, v in Counter(r["sq_pattern"] for r in records).most_common(10)],
    "d_divisibility": dict(d_mod_results),
}
import json as _json
with open("/Users/patrickkavanagh/math/experiments/exp4_computational_first/c3_structural.json", "w") as f:
    _json.dump(summary, f, indent=2, default=str)
print("\nSaved c3_structural.json")
