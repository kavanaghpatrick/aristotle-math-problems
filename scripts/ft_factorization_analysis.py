#!/usr/bin/env python3
"""
Feit-Thompson p=3 factorization analysis.

For primes q ≡ 71 mod 72 with A = q² + q + 1 prime, explores the
factorization 3 = (1-q)(2+q) mod A and its consequences.

KEY FINDINGS:
  1. (1-q)/(2+q) = -q mod A  [PROVEN: (2+q)(-q) = 1-q]
  2. (-q)^{q+1} = 1 since q³=1 and 3|(q+1)
  3. Therefore (1-q)^{q+1} = (2+q)^{q+1}  [equal projections to Sylow_q]
  4. sqrt(-3) = ±(1+2q) mod A  [PROVEN: (1+2q)² = -3]
  5. (1-q)/(1+2q) = q² mod A  (has order 3, lives in Sylow 3-subgroup)
  6. ord_A(q+1) = 6 always  [PROVEN: cycle q+1, q, -1, -(q+1), -q, 1]
  7. (q+1)^q = -q always  [PROVEN: since q ≡ 5 mod 6]
  8. The Frobenius claim x→x^q swapping (1-q)↔(2+q) is FALSE
  9. 3^q ≠ 3 in general  (3^q varies nontrivially with q)
  10. q | ord_A(3) and q | ord_A(2) always  (empirical, expected by density)

The factorization creates nice algebraic identities but they all collapse
to tautologies. The "square in Sylow_q" property is trivially true since
every element of a cyclic group of odd order is a square.
"""

from sympy import isprime, factorint, sqrt_mod
from math import gcd, lcm
import time

def multiplicative_order(a, n):
    """Compute ord_n(a) for a coprime to n (n prime)."""
    if a % n == 0:
        return None
    phi = n - 1
    factors = factorint(phi)
    order = phi
    for p, e in factors.items():
        while order % p == 0 and pow(a, order // p, n) == 1:
            order //= p
    return order

def main():
    start = time.time()

    print("=" * 80)
    print("Feit-Thompson p=3 Factorization Analysis")
    print("=" * 80)
    print()

    # Collect eligible primes
    eligible = []
    q = 71
    while q < 50000:
        if isprime(q):
            A = q * q + q + 1
            if isprime(A):
                eligible.append((q, A))
        q += 72

    print(f"Setting: q ≡ 71 mod 72 prime, A = q²+q+1 prime")
    print(f"Found {len(eligible)} eligible primes q < 50000")
    print()

    # =========================================================================
    # PART 1: Algebraically proven facts
    # =========================================================================
    print("=" * 80)
    print("PART 1: ALGEBRAICALLY PROVEN IDENTITIES")
    print("=" * 80)
    print()
    print("In Z/AZ where A = q²+q+1:")
    print()
    print("  (a) q³ ≡ 1,  q² ≡ -q-1,  q(q+1) ≡ -1  mod A")
    print("  (b) 3 = (1-q)(2+q) mod A")
    print("  (c) (1-q)² = -3q,  (2+q)² = 3(q+1) mod A")
    print("  (d) (1-q)/(2+q) = -q  [proof: (2+q)(-q) = -2q-q² = -2q+q+1 = 1-q]")
    print("  (e) (-q)^{q+1} = 1    [proof: q³=1, (q+1)≡0 mod 3, so q^{q+1}=1,")
    print("       (-1)^{q+1}=1 since q+1 even]")
    print("  (f) Therefore (1-q)^{q+1} = (2+q)^{q+1}")
    print("  (g) sqrt(-3) = ±(1+2q)  [proof: (1+2q)² = 1+4q+4q² = 1+4q+4(-q-1) = -3]")
    print("  (h) (1+2q)+(1+2q²) = 2+2q+2q² = 2(q²+q+1)/1... = 0 mod A")
    print("  (i) (1-q)/(1+2q) = (2q+1)(q-1)/3 = q² mod A (order 3)")
    print("  (j) ord_A(q+1) = 6 (cycle: q+1, q, -1, -(q+1), -q, 1)")
    print("  (k) (q+1)^q = -q (since q ≡ 5 mod 6)")
    print()

    # Verify all identities
    print("Verification across all eligible primes:")
    all_ok = True
    for q, A in eligible:
        v1 = (1 - q) % A
        v2 = (2 + q) % A

        # (b) 3 = (1-q)(2+q)
        assert (v1 * v2) % A == 3

        # (c) squares
        assert pow(v1, 2, A) == (-3 * q) % A
        assert pow(v2, 2, A) == (3 * (q + 1)) % A

        # (d) ratio = -q
        v2_inv = pow(v2, A - 2, A)
        assert (v1 * v2_inv) % A == (A - q) % A

        # (f) equal (q+1)-th powers
        assert pow(v1, q + 1, A) == pow(v2, q + 1, A)

        # (g) sqrt(-3)
        assert pow(1 + 2 * q, 2, A) == (-3) % A

        # (h) sum = 0
        assert ((1 + 2 * q) + (1 + 2 * q * q)) % A == 0

        # (i) ratio = q²
        s = (1 + 2 * q) % A
        s_inv = pow(s, A - 2, A)
        assert (v1 * s_inv) % A == (q * q) % A

        # (j) ord(q+1) = 6
        assert pow(q + 1, 6, A) == 1
        assert pow(q + 1, 3, A) == A - 1  # = -1
        assert pow(q + 1, 2, A) == q % A

        # (k) (q+1)^q = -q
        assert pow(q + 1, q, A) == (A - q) % A

    print(f"  All identities verified for {len(eligible)}/{len(eligible)} primes  ✓")
    print()

    # =========================================================================
    # PART 2: Frobenius claim is FALSE
    # =========================================================================
    print("=" * 80)
    print("PART 2: THE FROBENIUS CLAIM IS FALSE")
    print("=" * 80)
    print()
    print("CLAIM (FALSE): x→x^q is a ring homomorphism swapping (1-q)↔(2+q)")
    print("REALITY: x→x^q is NOT a ring hom in Z/AZ (char = A ≠ q)")
    print()

    swap_count = 0
    for q, A in eligible:
        v1 = (1 - q) % A
        v2 = (2 + q) % A
        if pow(v1, q, A) == v2 and pow(v2, q, A) == v1:
            swap_count += 1

    print(f"  (1-q)^q = (2+q) AND (2+q)^q = (1-q): {swap_count}/{len(eligible)} cases")
    print()

    three_eq_three = sum(1 for q, A in eligible if pow(3, q, A) == 3)
    print(f"  3^q ≡ 3 mod A: {three_eq_three}/{len(eligible)} cases")
    print("  (Would be all if Frobenius were correct)")
    print()

    # =========================================================================
    # PART 3: Order structure
    # =========================================================================
    print("=" * 80)
    print("PART 3: ORDER STRUCTURE")
    print("=" * 80)
    print()

    print(f"{'q':>7} {'ord(3)':>10} {'ord/q':>8} {'(q+1)/d':>8} "
          f"{'ord(2)':>10} {'q|ord(2)':>9} {'ord(1-q)':>10} {'ord(2+q)':>10}")
    print("-" * 80)

    for q, A in eligible:
        o3 = multiplicative_order(3, A)
        o2 = multiplicative_order(2, A)
        o1q = multiplicative_order((1 - q) % A, A)
        o2q = multiplicative_order((2 + q) % A, A)
        d = o3 // q if o3 % q == 0 else None
        ratio = (q + 1) // d if d and (q + 1) % d == 0 else "N/A"
        q_div_o2 = "YES" if o2 % q == 0 else "no"

        print(f"{q:>7} {o3:>10} {str(d):>8} {str(ratio):>8} "
              f"{o2:>10} {q_div_o2:>9} {o1q:>10} {o2q:>10}")

    print()

    # =========================================================================
    # PART 4: q-th power residue analysis
    # =========================================================================
    print("=" * 80)
    print("PART 4: q-th POWER RESIDUE ANALYSIS")
    print("=" * 80)
    print()
    print("(A-1)/q = q+1. So p^{q+1} ≡ 1 iff p is a q-th power residue.")
    print()

    small_primes = [2, 3, 5, 7, 11, 13]
    counts = {p: 0 for p in small_primes}
    for q, A in eligible:
        for p in small_primes:
            if pow(p, q + 1, A) != 1:
                counts[p] += 1

    print(f"  {'p':>4}  q | ord_A(p)")
    print(f"  {'---':>4}  ----------")
    for p in small_primes:
        print(f"  {p:>4}  {counts[p]}/{len(eligible)} "
              f"({'ALWAYS' if counts[p] == len(eligible) else 'sometimes'})")

    print()
    print("  Expected: ~(q-1)/q of elements have q | ord (density argument).")
    print("  For q ≥ 71, this is ≥ 98.6%, so 'always' for small primes is expected.")
    print()

    # =========================================================================
    # PART 5: The projection to Sylow_q
    # =========================================================================
    print("=" * 80)
    print("PART 5: PROJECTION TO SYLOW q-SUBGROUP")
    print("=" * 80)
    print()
    print("π: (Z/AZ)* → Sylow_q  via  x ↦ x^{q+1}")
    print()
    print("Key result: π(1-q) = π(2+q), so π(3) = π(1-q)²")
    print("But Sylow_q has odd order q, so every element is a square.")
    print("The 'square' property is TRIVIALLY TRUE — no constraint!")
    print()

    print(f"{'q':>7} {'π(1-q)':>14} {'π(2+q)':>14} {'equal':>6} {'π(3)':>14} {'=π(1-q)²':>10}")
    print("-" * 65)
    for q, A in eligible[:10]:
        p1 = pow((1 - q) % A, q + 1, A)
        p2 = pow((2 + q) % A, q + 1, A)
        p3 = pow(3, q + 1, A)
        p1sq = pow(p1, 2, A)
        print(f"{q:>7} {p1:>14} {p2:>14} {'✓' if p1==p2 else '✗':>6} "
              f"{p3:>14} {'✓' if p3==p1sq else '✗':>10}")

    print()

    # =========================================================================
    # PART 6: Relationship to Eisenstein integers
    # =========================================================================
    print("=" * 80)
    print("PART 6: EISENSTEIN INTEGER STRUCTURE")
    print("=" * 80)
    print()
    print("Z[ω] where ω = (-1+√(-3))/2 is an Eisenstein integer.")
    print("In Z/AZ: ω corresponds to q (cube root of unity).")
    print("  √(-3) = 2ω+1 corresponds to 2q+1 = 1+2q  ✓")
    print()
    print("Key elements in Eisenstein language:")
    print("  1-q  = 1-ω  (an Eisenstein prime above 3)")
    print("  2+q  = 1-ω² = 1-ω̄  (its conjugate)")
    print("  3    = (1-ω)(1-ω̄) = N(1-ω)  (the norm)")
    print("  1+2q = 2ω+1 = √(-3)  (related to the different)")
    print()
    print("The factorization 3 = (1-q)(2+q) is just the norm factorization")
    print("of 3 in Z[ω]. All identities follow from the Eisenstein structure.")
    print()

    # =========================================================================
    # PART 7: What 3^q actually is
    # =========================================================================
    print("=" * 80)
    print("PART 7: WHAT IS 3^q mod A?")
    print("=" * 80)
    print()

    print(f"{'q':>7} {'3^q mod A':>14} {'ord(3^q)':>10} {'3^q as N(?)':>14}")
    print("-" * 50)
    for q, A in eligible[:15]:
        v = pow(3, q, A)
        d = multiplicative_order(3, A) // q if multiplicative_order(3, A) % q == 0 else "?"
        # 3^q = ((1-q)(2+q))^q = (1-q)^q · (2+q)^q
        # These individual factors have no simple closed form
        print(f"{q:>7} {v:>14} {str(d):>10}")

    print()
    print("3^q has no simple algebraic expression — it depends on the full")
    print("multiplicative structure of (Z/AZ)*, not just the cubic substructure.")
    print()

    # =========================================================================
    # FINAL SUMMARY
    # =========================================================================
    print("=" * 80)
    print("FINAL SUMMARY")
    print("=" * 80)
    print()
    print("The factorization 3 = (1-q)(2+q) mod A = q²+q+1 is the norm")
    print("factorization of 3 in Z[ω] (Eisenstein integers). It yields:")
    print()
    print("  PROVEN IDENTITIES (non-trivial but algebraic):")
    print("    (1-q)/(2+q) = -q  ←  the two factors are 'conjugate' via -q")
    print("    (1-q)^{q+1} = (2+q)^{q+1}  ←  their Sylow_q projections agree")
    print("    sqrt(-3) = ±(1+2q)  ←  Eisenstein structure")
    print("    (1-q)/(1+2q) = q²  ←  ratio is a cube root of unity")
    print()
    print("  WHAT DOESN'T WORK:")
    print("    - Frobenius claim (x→x^q swaps factors): FALSE")
    print("    - 3^q = 3: FALSE (3^q varies nontrivially)")
    print("    - 'Square in Sylow_q' constraint: TRIVIALLY TRUE (odd order group)")
    print("    - All norm-based identities: CIRCULAR (collapse to 3^k = 3^k)")
    print()
    print("  WHAT REMAINS OPEN:")
    print("    - ord_A(3) = q·d where d | (q+1), d varies: WHY?")
    print("    - Can cubic reciprocity in Z[ω] determine d?")
    print("    - The Eisenstein factorization 3 = -ω²(1-ω)² gives")
    print("      3 as associate of (1-ω)² — does this help via higher reciprocity?")
    print()

    elapsed = time.time() - start
    print(f"[Completed in {elapsed:.1f}s]")


if __name__ == "__main__":
    main()
