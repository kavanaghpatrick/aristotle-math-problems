#!/usr/bin/env python3
"""
Scan q ≡ 71 (mod 72) primes for q ≤ 10000 to verify that the slot720
Fermat-reduction mechanism continues to find a SMALL prime divisor p > 3
of A(q) = q^2 + q + 1 with 3^(q mod (p-1)) ≢ 1 (mod p).

CRITICAL: "small" means p such that native_decide is tractable.
slot720 used p ∈ {7, 7, 13, 211, 487, 7} for q ∈ {359, 431, 503, 647, 719, 863}.
Max p in slot720 was 487. We adopt p ≤ 1000 (similar order of magnitude as slot720) as the
"small enough for native_decide" threshold; ≤ 5000 as a stretch threshold.

For p large (A(q) itself prime), 3^(q mod (p-1)) requires native_decide on huge moduli — slow but
sometimes works. For very large p (≥ 10^6), we expect Aristotle to time out.
"""
from sympy import isprime, factorint

def small_prime_divisor_with_fermat(q, p_cap=10**6):
    """
    Find the SMALLEST prime p > 3 such that:
      p | A(q) = q^2 + q + 1
      3^(q mod (p-1)) != 1 (mod p)
    AND p ≤ p_cap (to keep native_decide tractable).

    Returns (p, q % (p-1), 3^(q%(p-1)) % p, A(q)) on success.
    Returns None on failure.
    """
    A = q*q + q + 1
    factors = factorint(A)
    candidates = sorted(factors.keys())
    for p in candidates:
        if p <= 3:
            continue
        if p > p_cap:
            return None
        r = q % (p - 1)
        val = pow(3, r, p)
        if val != 1:
            return (p, r, val, A, p in candidates and len(candidates) == 1)
    return None

def main():
    bound = 10000
    qs = []
    q = 71
    while q <= bound:
        if isprime(q):
            qs.append(q)
        q += 72
    print(f"Primes q ≡ 71 (mod 72), q ≤ {bound}: {len(qs)} total\n")

    # Thresholds Aristotle could plausibly handle via native_decide.
    # slot720 ceiling was p=487, so we use that as the realistic ceiling.
    for p_cap in [500, 1000, 5000, 10000, 100000, 10**6]:
        pass_count = 0
        fail_qs = []
        for q in qs:
            result = small_prime_divisor_with_fermat(q, p_cap=p_cap)
            if result is None:
                fail_qs.append(q)
            else:
                pass_count += 1
        print(f"  p_cap = {p_cap:>9}: {pass_count:>3}/{len(qs)} pass; fail at q = {fail_qs[:10]}{'...' if len(fail_qs)>10 else ''}")

    # Now decide: pick a bound where Aristotle WOULD plausibly succeed.
    # slot720 worked up to p=487. Stretch: p ≤ 2000 maybe.
    # Find the largest q-bound such that ALL primes q ≡ 71 mod 72 in [71, q_bound]
    # have a small prime divisor p ≤ 1000.
    print("\nLargest q_bound such that all q ≡ 71 mod 72 in [71, q_bound] have small Fermat-compatible divisor:")
    for p_cap in [500, 1000, 2000, 5000]:
        last_q = None
        for q in qs:
            r = small_prime_divisor_with_fermat(q, p_cap=p_cap)
            if r is None:
                break
            last_q = q
        print(f"  p_cap = {p_cap}: max q where ALL prior pass = {last_q}")

    # Detailed list at the slot720 ceiling p_cap = 500.
    print("\n=== Detail: each q, smallest Fermat-compatible p, where p ≤ 1000 ===")
    for q in qs:
        r = small_prime_divisor_with_fermat(q, p_cap=10**8)  # no cap, just show smallest
        if r is None:
            print(f"  q = {q:>5}: NONE (A(q) = {q*q+q+1} has no Fermat-compatible factor)")
        else:
            p, res, val, A, isprime_A = r
            marker = " <-- A(q) prime" if isprime_A else ""
            print(f"  q = {q:>5}: p = {p:>9}, q mod (p-1) = {res:>5}, 3^r mod p = {val:>5}, A(q) = {A}{marker}")

if __name__ == "__main__":
    main()
