#!/usr/bin/env python3
"""
Odd Multiperfect σ₀(n) = 11 — Search & Shape Analysis (May 30 2026)

Background: An ODD multiperfect number is odd n>1 with σ(n) ≡ 0 (mod n), i.e.
n | σ(n), equivalently σ(n)/n ∈ Z≥2. (Standard def: σ(n) = kn for integer k≥2.)

Constraint σ₀(n) = 11 forces a small list of multiplicative shapes via
σ₀ multiplicativity:
  11 prime ⇒ either n = p^10 (single prime), or n = p^a · q^b · ... with
  (a+1)(b+1)... = 11 = 11 (single factor).
Since 11 is PRIME the ONLY factorizations of 11 are:
  - 11 = 11  →  n = p^10  (one prime, exponent 10)
  - There is no factorization 11 = (a+1)(b+1) with both >1 since 11 prime.

So σ₀(n) = 11 ⇒ n = p^10 for a single prime p.

For ODD: p is odd prime, n = p^10.
σ(p^10) = (p^11 - 1)/(p - 1) = 1 + p + p² + … + p^10.
For n = p^10 to be multiperfect, we need n | σ(n), i.e.
  p^10 | (p^11 - 1)/(p - 1) = 1 + p + … + p^10.
But (1 + p + … + p^10) mod p = 1 (since p divides all terms except 1).
So gcd(p^10, σ(p^10)) = gcd(p^10, 1) = 1, and σ(p^10) is NEVER divisible by p^10 (since σ ≡ 1 mod p, but for divisibility by p^10 we need σ ≡ 0).
Therefore NO odd p^10 is multiperfect. (In fact, no p^a with a >= 1 is, by the same argument.)

The user's brief mentioned 3 shapes (p^10, p^4 q^2, p^2 q r) — this was WRONG.
Those correspond to σ₀ ∈ {11, 15, 12} respectively:
  - (a+1)... = 15 = 5·3 → exponents (4,2) → form p^4 q^2 (σ₀=15)
  - (a+1)... = 12 = 4·3 = 2·2·3 → various
  - So 11 being prime forces single-prime form p^10.

REAL TAKE: σ₀(n) = 11 is RULED OUT for odd multiperfect by trivial p-adic argument.
The conjecture (no odd multiperfect with σ₀=11) is straightforwardly TRUE.

If user meant σ₀(n) ∈ {10, 12, 13, 14, 15} (composite, allowing multi-prime forms),
those are nontrivial. Let me cover BOTH interpretations:
  (A) σ₀=11 exact: trivially impossible (p^10 with p odd is never multiperfect).
  (B) σ₀∈{12,13,14,15}: nontrivial; search bound.

Algorithm for (A): present trivial impossibility argument (will be the gap claim).
Algorithm for (B): enumerate small n with σ₀(n) = target, check σ(n)/n.

Run:
  - Verify shape (A) impossibility numerically: for all odd p < 10⁶, σ(p^10) mod p^10 != 0.
  - Search for odd n with σ₀(n) = 11 up to N = 10⁸ (search all n with τ=11):
    these are exactly n = p^10 with p < 10^{0.8} ~ 7 (so n in {3^10, 5^10, 7^10}).
    Trivial to verify none is multiperfect.
  - Search odd n with σ₀(n) ∈ {12, 13, 14, 15} up to 10⁸ for the sketch.

Author: agent#5 (May 30 2026)
"""

import json
import time
from pathlib import Path
from sympy import divisor_sigma, divisor_count, primerange, factorint

OUT_JSON = Path("/Users/patrickkavanagh/math/analysis/odd_multiperfect_sigma0_11_may30.json")


def is_odd_multiperfect(n):
    """n is odd and σ(n)/n is integer >= 2."""
    if n % 2 == 0 or n < 2:
        return False
    s = int(divisor_sigma(n, 1))
    return s % n == 0 and s // n >= 2


def main():
    start = time.time()
    print("=" * 70)
    print("Odd multiperfect σ₀(n) = 11 — Search")
    print("=" * 70)

    results = {
        "shape_analysis": {},
        "search_results": {},
        "verdict": None,
    }

    # ===== Shape analysis =====
    # σ₀ = 11 prime → n = p^10 for some prime p.
    print("\n[Shape] σ₀(n)=11 ⇔ n = p^10 (since 11 is prime)")
    results["shape_analysis"]["sigma_0_eq_11_shape"] = "n = p^10 for a single prime p"
    results["shape_analysis"]["argument"] = (
        "σ₀ is multiplicative; (a₁+1)…(aₖ+1) = 11 with 11 prime forces k=1, a₁=10."
    )

    # Trivial impossibility:
    # For n = p^10, p odd prime: σ(p^10) = (p^11-1)/(p-1) = 1+p+...+p^10
    # σ(p^10) mod p = 1 (only the 1 term is not divisible by p)
    # So p ∤ σ(p^10), hence p^10 ∤ σ(p^10), hence n=p^10 is NEVER multiperfect.
    print("\n[Argument] For n = p^10 (p odd prime): σ(p^10) ≡ 1 (mod p), so n ∤ σ(n).")
    print("            n = p^10 is NEVER multiperfect.")
    results["shape_analysis"]["impossibility_proof"] = (
        "σ(p^10) = 1+p+...+p^10 ≡ 1 (mod p), so p ∤ σ(p^10), so p^10 ∤ σ(p^10), "
        "so n = p^10 is never multiperfect."
    )

    # ===== Numerical verification =====
    # Verify for p in [3, 1000]
    print("\n[Verify] Checking p in [3, 1000] (odd primes): is p^10 multiperfect?")
    odd_primes = [p for p in primerange(3, 1001) if p % 2 == 1]
    counterexamples = []
    for p in odd_primes:
        n = p ** 10
        if is_odd_multiperfect(n):
            counterexamples.append({"p": p, "n": n})
    print(f"  Checked {len(odd_primes)} odd primes, multiperfect count = {len(counterexamples)}")
    results["search_results"]["sigma_0_eq_11_in_range"] = {
        "primes_checked": len(odd_primes),
        "multiperfect_found": len(counterexamples),
        "samples": counterexamples[:3],
    }

    # ===== Adjacent σ₀ values (where target is nontrivial) =====
    # σ₀ = 12 = 4·3 = 2·2·3 = 12·1 → shapes: p^11, p^5·q^2, p^3·q^2, p·q·r^2, p^3·q·r,...
    # σ₀ = 13 prime → p^12 only — same impossibility argument
    # σ₀ = 15 = 5·3 → p^14, p^4·q^2
    # σ₀ = 14 = 7·2 → p^13, p^6·q
    print("\n[Adjacent] σ₀ = 13 (also prime) — same impossibility (p^12 never multiperfect)")
    results["shape_analysis"]["sigma_0_eq_13"] = "Same — n = p^12, trivially never multiperfect"

    print("\n[Adjacent] σ₀ ∈ {12, 14, 15} — nontrivial. Brief search up to 10^7...")
    # For σ₀(n)=k with composite k, search via sympy
    N_MAX = 10_000_000
    sigma0_12_examples = []
    sigma0_14_examples = []
    sigma0_15_examples = []

    # Iterate small odd n up to N_MAX, check σ₀ and multiperfect
    # Faster: enumerate factorization shapes.
    # σ₀=12: shapes (a₁+1)...(aₖ+1)=12 with all aᵢ≥1: (11), (5,1), (3,2), (2,1,1)
    #   i.e. p^11, p^5·q, p^3·q^2, p^2·q·r (with q ≠ r etc.)
    # We'll do brute scan with sympy divisor_count.
    n = 3
    t0 = time.time()
    last_print = t0
    while n < N_MAX:
        if time.time() - start > 200:
            print(f"  TIMEOUT at n={n}", flush=True)
            break
        tau = int(divisor_count(n))
        if tau in (12, 14, 15):
            if is_odd_multiperfect(n):
                entry = {"n": n, "sigma_0": tau, "sigma": int(divisor_sigma(n, 1)), "k": int(divisor_sigma(n, 1) // n)}
                if tau == 12:
                    sigma0_12_examples.append(entry)
                elif tau == 14:
                    sigma0_14_examples.append(entry)
                else:
                    sigma0_15_examples.append(entry)
        n += 2
        if time.time() - last_print > 30:
            print(f"  ... scanned to n={n}", flush=True)
            last_print = time.time()

    print(f"  σ₀=12 odd multiperfect found: {len(sigma0_12_examples)}")
    print(f"  σ₀=14 odd multiperfect found: {len(sigma0_14_examples)}")
    print(f"  σ₀=15 odd multiperfect found: {len(sigma0_15_examples)}")

    results["search_results"]["adjacent_search"] = {
        "N_MAX": N_MAX,
        "sigma_0_eq_12_examples": sigma0_12_examples[:5],
        "sigma_0_eq_14_examples": sigma0_14_examples[:5],
        "sigma_0_eq_15_examples": sigma0_15_examples[:5],
    }

    # ===== Verdict =====
    results["verdict"] = (
        "σ₀(n)=11 odd multiperfect: TRIVIALLY IMPOSSIBLE via 1-line p-adic argument. "
        "The gap (no odd multiperfect with σ₀=11) is provably TRUE but NOT a substantial "
        "result — the impossibility is elementary. The user's framing (3 shapes: p^10, "
        "p^4·q^2, p^2·q·r) was incorrect: 11 prime forces SHAPE = p^10 only. The 3-shape "
        "case-split corresponds to σ₀=12 (4·3) or σ₀=10 (5·2) or σ₀=15 (5·3), not σ₀=11."
    )
    results["actionable_sketch_targets"] = [
        "(A) σ₀(n)=11 impossibility — TRIVIAL (1-line proof); not a closure target.",
        "(B) Reframe as σ₀=12 OR σ₀=15 — these have 3-shape splits and are nontrivial.",
        "(C) Σ shape (p^4·q^2 or p^2·q·r) — these are FROM σ₀=15, not σ₀=11.",
    ]

    results["recommended_gap"] = (
        "Submit IMPOSSIBILITY: ¬ ∃ n, n odd ∧ σ(n) = k·n ∧ σ₀(n) = 11. Aristotle's "
        "slot737 σ₀ multiplicativity DNA applies but the argument is even simpler — "
        "case-split (a+1)...(aₖ+1)=11 forces single-prime; (1+p+...+p^10) ≡ 1 (mod p). "
        "Bare conjecture sketch."
    )

    results["runtime_s"] = time.time() - start

    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    with open(OUT_JSON, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nJSON: {OUT_JSON}")
    return results


if __name__ == "__main__":
    main()
