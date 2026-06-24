#!/usr/bin/env python3
"""
Erdős 203 — Lift Retry With Different Prime Sets (May 30 2026)

Background: slot740 found explicit m for the 8x8 grid using 22 index-1 primes
<= 500. A1 showed those 22 primes cover only ~69.4% of the full Z^2 quotient
lattice (K*L ~ 5.5e49). The cover does NOT lift to an infinite witness.

This script tests whether LARGER prime sets (B up to 10000) — including the
11 index-2 primes from slot724 — can achieve >95% / 100% Monte-Carlo coverage
of the quotient.

Algorithm (efficient version):
  For each B in {2000, 5000, 10000}:
    1. Enumerate index-1 and index-2 primes p with 3 < p <= B.
    2. For each prime p:
       - The "shadow density" of p is independent of m (the number of (a,b)
         pairs in [0,o2) x [0,o3) with 2^a 3^b ≡ target (mod p)). For a given p,
         the shadow size is the same as |⟨2,3⟩| / lcm(o2, o3) ... actually it
         depends on target.
       - We pick a representative m_mod ∈ (Z/pZ)* uniformly; shadow size
         distribution is uniform over residues.
    3. For each prime, fix shadow_p = shadow_for_m=1(p) as proxy (any m_mod
       gives same SHAPE, just translated). Pool of primes' shadows.
    4. Monte-Carlo: sample N=200,000 points (k,l) ∈ K_eff x L_eff; for each
       sample, test all primes (small set). Report coverage.
    5. Greedy SET COVER on the sample: select primes one at a time maximizing
       additional samples covered. Stop when target_fraction reached or no gain.

Key shortcut: since the shadow of p on its OWN period is the same UP TO
TRANSLATION for any m_mod, the question of "does the quotient cover" with a
specific choice of m's per p is equivalent (up to a CRT translation) to: do
the shadow SHAPES collectively cover the quotient.

So for each prime p, we compute ONE representative shadow (using m_mod=1)
and run set-cover.

Author: agent#5 (May 30 2026)
"""

import json
import math
import random
import time
from pathlib import Path
from sympy import isprime, primerange, mod_inverse

random.seed(42)
BASE_OUT_JSON = Path("/Users/patrickkavanagh/math/analysis/erdos203_lift_retry_may30.json")
BUDGET_SECONDS = 360  # 6 min hard cap


def multiplicative_order(a: int, p: int) -> int:
    a = a % p
    if a == 0:
        raise ValueError("a divisible by p")
    n = p - 1
    divs = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            divs.append(i)
            if i != n // i:
                divs.append(n // i)
        i += 1
    divs.sort()
    for d in divs:
        if pow(a, d, p) == 1:
            return d
    return n


def classify_prime(p: int):
    if p <= 3 or not isprime(p):
        return None, 0, 0
    o2 = multiplicative_order(2, p)
    o3 = multiplicative_order(3, p)
    lcm23 = math.lcm(o2, o3)
    if (p - 1) % lcm23 != 0:
        return None, o2, o3
    idx = (p - 1) // lcm23
    if idx == 1:
        return "index_1", o2, o3
    elif idx == 2:
        return "index_2", o2, o3
    return None, o2, o3


def enumerate_index_primes(B: int):
    idx1 = []
    idx2 = []
    for p in primerange(5, B + 1):
        kind, o2, o3 = classify_prime(p)
        if kind == "index_1":
            idx1.append((p, o2, o3))
        elif kind == "index_2":
            idx2.append((p, o2, o3))
    return idx1, idx2


def shadow_canonical(p: int, o2: int, o3: int):
    """Return shadow set for m_mod_p = 1 (canonical representative).
    Each cell (a,b) is in shadow iff 2^a 3^b ≡ -1 (mod p)."""
    target = (p - 1) % p  # -1 mod p
    shadow = set()
    pow2 = [pow(2, a, p) for a in range(o2)]
    pow3 = [pow(3, b, p) for b in range(o3)]
    for a in range(o2):
        for b in range(o3):
            if (pow2[a] * pow3[b]) % p == target:
                shadow.add((a, b))
    return frozenset(shadow)


def covered_by_prime(k: int, l: int, p: int, o2: int, o3: int, shadow):
    return (k % o2, l % o3) in shadow


def run_scenario(prime_pool, K, L, N_samples=200_000, target=1.0, time_left=600):
    """Greedy set-cover over prime_pool = list of (p, o2, o3, shadow)."""
    rng = random.Random(42)
    K_eff = max(K, 1)
    L_eff = max(L, 1)

    # Generate sample
    samples = []
    for _ in range(N_samples):
        samples.append((rng.randrange(K_eff), rng.randrange(L_eff)))

    # Precompute: for each prime, the bitmap of sample indices it covers.
    # Use integer bitmask for fast OR; 200_000 bits = 25kb per prime.
    print(f"      precomputing prime bitmasks ({len(prime_pool)} primes, {N_samples} samples)...")
    t0 = time.time()
    bitmasks = []
    for p, o2, o3, sh in prime_pool:
        mask = 0
        for idx, (k, l) in enumerate(samples):
            if (k % o2, l % o3) in sh:
                mask |= (1 << idx)
        bitmasks.append((p, o2, o3, sh, mask))
        if time.time() - t0 > time_left * 0.5:
            print(f"        TIME WARN: precompute slow, stopped at {len(bitmasks)}/{len(prime_pool)}")
            break
    print(f"      precompute done in {time.time() - t0:.1f}s")

    # Greedy
    chosen = []
    union_mask = 0
    target_count = int(N_samples * target)
    full_mask = (1 << N_samples) - 1

    t1 = time.time()
    while bin(union_mask).count("1") < target_count and time.time() - t1 < time_left * 0.5:
        best_gain = 0
        best_idx = -1
        for i, (p, o2, o3, sh, mask) in enumerate(bitmasks):
            if i in {c[0] for c in chosen}:
                continue
            new_mask = union_mask | mask
            gain = bin(new_mask).count("1") - bin(union_mask).count("1")
            if gain > best_gain:
                best_gain = gain
                best_idx = i
        if best_idx == -1 or best_gain == 0:
            break
        chosen.append((best_idx, bitmasks[best_idx]))
        union_mask |= bitmasks[best_idx][4]

    coverage = bin(union_mask).count("1") / N_samples
    return chosen, coverage


def run_scenario_fast(prime_pool, K, L, N_samples=100_000, target=1.0):
    """Faster: per-sample set cover. Avoid bitmask of 200k bits (which would be
    huge memory). Use list of sets per sample."""
    rng = random.Random(42)
    K_eff = max(K, 1)
    L_eff = max(L, 1)
    samples = [(rng.randrange(K_eff), rng.randrange(L_eff)) for _ in range(N_samples)]

    # For each prime, compute the set of sample indices it covers (sparse if shadow rare).
    print(f"      computing coverage sets for {len(prime_pool)} primes...")
    t0 = time.time()
    prime_coverage = []  # list of (p_data, frozenset of sample indices)
    for p, o2, o3, sh in prime_pool:
        covered = set()
        for idx, (k, l) in enumerate(samples):
            if (k % o2, l % o3) in sh:
                covered.add(idx)
        prime_coverage.append(((p, o2, o3, sh), frozenset(covered)))
    print(f"      done in {time.time() - t0:.1f}s")

    # Greedy: choose prime with max marginal gain
    chosen = []
    uncovered = set(range(N_samples))
    target_count = int(N_samples * (1 - target))  # stop when uncovered <= target_count

    iters = 0
    while len(uncovered) > target_count and iters < len(prime_pool):
        best_gain = 0
        best_i = -1
        for i, ((p, o2, o3, sh), cov) in enumerate(prime_coverage):
            if any(c[1] == i for c in chosen):
                continue
            gain = len(cov & uncovered)
            if gain > best_gain:
                best_gain = gain
                best_i = i
        if best_i == -1 or best_gain == 0:
            break
        chosen.append((prime_coverage[best_i][0], best_i))
        uncovered = uncovered - prime_coverage[best_i][1]
        iters += 1

    coverage = 1 - len(uncovered) / N_samples
    return chosen, coverage


def main():
    start = time.time()
    print("=" * 70)
    print("Erdős 203 — Lift Retry (efficient version)")
    print("=" * 70)

    results = {
        "budget_seconds": BUDGET_SECONDS,
        "bounds_tested": [],
        "best_partial_coverage": 0.0,
        "no_full_cover": True,
    }

    bounds = [2000, 5000, 10000]
    best_overall = (0.0, 0, None)

    for B in bounds:
        elapsed = time.time() - start
        if elapsed > BUDGET_SECONDS * 0.9:
            print(f"\n[BUDGET] {elapsed:.0f}s — skipping B={B}")
            break
        print(f"\n----- B = {B} -----", flush=True)
        idx1, idx2 = enumerate_index_primes(B)
        print(f"  index-1 primes: {len(idx1)}, index-2 primes: {len(idx2)}", flush=True)

        # Compute K, L for both pools
        for scenario_name, prime_list in [("index1", idx1), ("idx1_plus_idx2", idx1 + idx2)]:
            elapsed = time.time() - start
            if elapsed > BUDGET_SECONDS * 0.9:
                break

            # Filter: skip primes with huge period (would blow up shadow enumeration).
            # o2*o3 <= 100k keeps shadow enumeration fast.
            filtered = [(p, o2, o3) for (p, o2, o3) in prime_list if o2 * o3 <= 100_000]
            print(f"\n  Scenario {scenario_name}: {len(filtered)}/{len(prime_list)} primes with period <= 100k", flush=True)

            # Compute K and L (over all filtered primes — bound by ~25-50 digits)
            K = 1
            L = 1
            for p, o2, o3 in filtered:
                K = math.lcm(K, o2)
                L = math.lcm(L, o3)
            print(f"    K ~ {K.bit_length()} bits, L ~ {L.bit_length()} bits", flush=True)

            # Compute shadows
            t_sh = time.time()
            prime_pool = []
            for p, o2, o3 in filtered:
                sh = shadow_canonical(p, o2, o3)
                if sh:
                    prime_pool.append((p, o2, o3, sh))
            print(f"    {len(prime_pool)} primes with non-empty shadow, computed in {time.time()-t_sh:.1f}s", flush=True)

            # Sort by shadow density (large shadows first → faster greedy)
            prime_pool.sort(key=lambda x: -(len(x[3]) / (x[1] * x[2])))

            elapsed = time.time() - start
            time_left = BUDGET_SECONDS - elapsed
            if time_left < 30:
                print(f"    [BUDGET] only {time_left:.0f}s left, skipping", flush=True)
                break
            # Cap pool size to keep search tractable
            POOL_CAP = 200
            if len(prime_pool) > POOL_CAP:
                print(f"    Capping pool to top-{POOL_CAP} by shadow density", flush=True)
                prime_pool = prime_pool[:POOL_CAP]

            # Run set cover
            N_samples = 50_000 if len(prime_pool) > 100 else 100_000
            print(f"    Running greedy set cover with {N_samples} samples...", flush=True)
            chosen, coverage = run_scenario_fast(prime_pool, K, L, N_samples=N_samples, target=1.0)
            print(f"    -> |chosen|={len(chosen)}, coverage={coverage:.4f}", flush=True)

            entry = {
                "B": B,
                "scenario": scenario_name,
                "n_filtered_primes": len(filtered),
                "n_prime_pool": len(prime_pool),
                "MC_samples": N_samples,
                "chosen_count": len(chosen),
                "coverage": coverage,
                "K_bits": K.bit_length(),
                "L_bits": L.bit_length(),
                "chosen_primes": [c[0][0] for c in chosen][:50],
                "elapsed_s": time.time() - start,
            }
            results["bounds_tested"].append(entry)

            if coverage > best_overall[0]:
                best_overall = (coverage, len(chosen), entry)

            if coverage >= 0.9999:
                print(f"    ✓✓✓ FULL COVERAGE in {scenario_name} at B={B}", flush=True)
                results["no_full_cover"] = False
                results["best_found"] = entry
                break

        if not results["no_full_cover"]:
            break

    results["best_partial_coverage"] = best_overall[0]
    results["best_partial_prime_count"] = best_overall[1]
    if best_overall[2]:
        results["best_partial_entry"] = best_overall[2]
    results["total_duration_s"] = time.time() - start

    BASE_OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    with open(BASE_OUT_JSON, "w") as f:
        json.dump(results, f, indent=2, default=str)

    print(f"\n----- Summary -----")
    print(f"  Runtime: {results['total_duration_s']:.0f}s")
    print(f"  Best coverage: {best_overall[0]:.4f} ({best_overall[1]} primes)")
    print(f"  Full cover: {'YES' if not results['no_full_cover'] else 'NO'}")
    print(f"  JSON: {BASE_OUT_JSON}")
    return results


if __name__ == "__main__":
    main()
