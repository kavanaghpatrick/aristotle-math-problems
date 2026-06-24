#!/usr/bin/env python3
"""
Erdos 647 Sophie-Germain residue scan.

Slot723 (Erdos 647) left ONE sorry. The remaining case:
  n ≡ 0 (mod 6), n ≥ 3000, n-1 prime, (n-2)/2 = q prime (Sophie Germain pair).

Aristotle suggested witness m = n-3 = 4r+1 where r = (n-4)/4.
Then n-3 ≡ 3 (mod 6) so 3 | (n-3). For τ(n-3) ≥ 6, need (n-3)/3 = (4r+1)/3
composite, equivalently (2q-1)/3 composite (since q = 2r+1).

GOAL: identify residue classes of q (mod small modulus M) where (2q-1)/3
is FORCED composite by a small prime divisor — purely modular obstruction,
provable by native_decide over a finite check.

KEY OBSERVATION: in the Sophie Germain configuration:
  n ≡ 0 (mod 6),  n-1 prime,  q = (n-2)/2 prime,  r = (n-4)/4
  3 | (n-3), so we look at p = (n-3)/3 = (2q-1)/3 ; want p composite.

If l is a small prime and l ≠ 3, then l | (2q-1)/3  iff  l | 2q-1
iff  q ≡ (l+1)/2 (mod l).  This gives a forced small divisor.

We scan q ∈ [1499, BOUND], Sophie Germain pairs in our regime,
and ask: what fraction is covered by  q ≡ a_l (mod l)  for small l?
"""

import math
from sympy import isprime
from collections import defaultdict


def sieve_primes(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(math.isqrt(n)) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return s


def main():
    BOUND_N = 200000  # scan n in [3000, BOUND_N], n ≡ 0 mod 6
    print(f"Scanning Sophie Germain pairs with n ∈ [3000, {BOUND_N}], n ≡ 0 mod 6")
    print(f"Equivalently q ∈ [1499, {BOUND_N//2 - 1}].\n")

    sieve = sieve_primes(BOUND_N)

    # Enumerate Sophie Germain pairs from the slot723 sorry case:
    # n ≡ 0 mod 6, n ≥ 3000, n-1 prime, q=(n-2)/2 prime.
    sophie_pairs = []   # list of (n, q, r) where r = (n-4)/4 = (q-1)/2
    val_p = []          # (2q-1)/3 values
    for n in range(3000, BOUND_N + 1, 6):
        if not sieve[n - 1]:
            continue
        q = (n - 2) // 2
        if not sieve[q]:
            continue
        # In slot723 sorry, we want τ(n-3) ≥ 6 to win; n-3 = 4r+1 with r=(q-1)/2.
        # n-3 ≡ 3 (mod 6), so 3 | n-3. Let p = (n-3)/3 = (2q-1)/3.
        twoq_minus_1 = 2 * q - 1
        if twoq_minus_1 % 3 != 0:
            # Sanity check: with n ≡ 0 (mod 6) and q = (n-2)/2 ≡ 2 (mod 3) (must verify)
            # n=6k, q=3k-1, 2q-1 = 6k-3 = 3(2k-1) -> always divisible by 3. Good.
            print(f"WARN: 2q-1 not div 3 for q={q}, n={n}")
            continue
        p = twoq_minus_1 // 3
        sophie_pairs.append((n, q, p))
        val_p.append(p)

    total = len(sophie_pairs)
    print(f"Total Sophie pairs in range: {total}\n")

    # Check compositeness of p = (2q-1)/3 across these
    composite_count = 0
    prime_count = 0
    for (n, q, p) in sophie_pairs:
        if p <= 1:
            continue
        if isprime(p):
            prime_count += 1
        else:
            composite_count += 1
    print(f"(2q-1)/3 composite: {composite_count}  prime: {prime_count}")
    if prime_count > 0:
        print(f"  Fraction prime (bad for us): {prime_count/total:.4f}\n")
    else:
        print()

    # MAIN SCAN: for each small prime l ∈ {5,7,11,13,17,19,23,29,31,37,41,43},
    # find residue a such that q ≡ a (mod l) forces l | (2q-1)/3.
    # i.e. 2q-1 ≡ 0 (mod 3l), q ≡ (3l+1)/2 ≡ (l+1)/2 (mod l) [if gcd(2,l)=1]
    # Then l | (2q-1)/3 provided (2q-1)/3 > l (i.e. p > l), which holds for q ≥ ~3l.
    print("Per-prime residue analysis (l | (2q-1)/3 forces compositeness if p > l):\n")
    print(f"{'l':>4} {'a (q mod l)':>14} {'count':>8} {'frac':>8} {'cum_frac':>10}")
    covered = set()
    cumulative = 0
    small_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
    for l in small_primes:
        # q ≡ a (mod l) with 2a ≡ 1 (mod l) -> a = (l+1)/2 mod l
        if l == 2 or l == 3:
            continue
        a = ((l + 1) // 2) % l  # so 2a ≡ 1 (mod l)
        cnt = 0
        new_covered = set()
        for i, (n, q, p) in enumerate(sophie_pairs):
            if i in covered:
                continue
            if p > l and (p % l == 0):
                # Equivalent: q % l == a
                assert q % l == a, f"q={q} l={l} a={a} but q%l={q%l}"
                new_covered.add(i)
                cnt += 1
        covered |= new_covered
        cumulative = len(covered)
        cum_frac = cumulative / total if total else 0
        print(f"{l:>4} {a:>14} {cnt:>8} {cnt/total:>8.4f} {cum_frac:>10.4f}")

    print(f"\nTotal covered by l ∈ {small_primes}: {len(covered)} / {total}  ({len(covered)/total:.4f})")
    uncovered = total - len(covered)
    print(f"Uncovered Sophie pairs (no small l divides (2q-1)/3): {uncovered}\n")

    # Among uncovered: how often is (2q-1)/3 still composite?
    uncov_indices = set(range(total)) - covered
    uncov_composite = 0
    uncov_prime = 0
    for i in uncov_indices:
        n, q, p = sophie_pairs[i]
        if p <= 1:
            continue
        if isprime(p):
            uncov_prime += 1
        else:
            uncov_composite += 1
    print(f"Among uncovered: (2q-1)/3 composite by larger factor: {uncov_composite}")
    print(f"Among uncovered: (2q-1)/3 actually prime (hardest case): {uncov_prime}")
    if uncovered:
        print(f"  uncovered prime fraction: {uncov_prime/uncovered:.4f}")

    # Show a few uncovered primes that ARE counterexamples to easy proof
    print("\nFirst 20 uncovered Sophie pairs with (2q-1)/3 PRIME (true hard cases):")
    hard = [(n, q, p) for i, (n, q, p) in enumerate(sophie_pairs)
            if i not in covered and p > 1 and isprime(p)]
    for n, q, p in hard[:20]:
        print(f"  n={n:>8}  q={q:>7}  p=(2q-1)/3={p:>7}  [n-3={n-3}, n-3 = 3·{p}]")
    print(f"\nTotal hard cases (uncovered + p prime) in scan: {len(hard)}")

    # Alternative reduction: for these, try witness m = n-4.
    # n-4 = 2(q-1) = 2·2r = 4r where r = (q-1)/2.
    # τ(n-4) = τ(4r) = 3·τ(r) if r odd and gcd(2,r)=1, else more.
    # Actually τ(4r) depends. If r prime, τ(4r) = τ(4)·τ(r) = 3·2 = 6.
    # Then (n-4) + τ(n-4) = n-4+6 = n+2, NOT strictly greater. Not enough.
    # If r composite with τ(r) ≥ 3, τ(4r) ≥ 9 (or more). Then n-4+9 = n+5 > n+2.
    # So witness n-4 works iff r is composite (τ(r) ≥ 3) (since r odd, 2∤r).
    # Equivalently, r = (n-4)/4 = (q-1)/2 must be composite.
    print("\n\n=== Alternative witness m = n-4 ===")
    print("n-4 = 4r where r = (q-1)/2. Need r composite for τ(n-4) ≥ 9 so witness works.")
    print("(if r = (q-1)/2 is prime, n-4 = 4·prime has τ=6, n-4+6 = n+2 — not enough).")
    r_composite = 0
    r_prime = 0
    r_one = 0
    for (n, q, p) in sophie_pairs:
        r = (q - 1) // 2
        if r <= 1:
            r_one += 1
        elif isprime(r):
            r_prime += 1
        else:
            r_composite += 1
    print(f"  r = (q-1)/2 composite: {r_composite}  prime: {r_prime}  small: {r_one}")
    print(f"  fraction r composite: {r_composite/total:.4f}")

    # Doubly-hard cases: r prime AND (2q-1)/3 prime
    print("\n\n=== Doubly hard cases ===")
    print("Cases where BOTH r = (q-1)/2 is prime AND p = (2q-1)/3 is prime.")
    print("These are 'Cunningham chain index 3' configurations.")
    doubly_hard = []
    for (n, q, p) in sophie_pairs:
        r = (q - 1) // 2
        if r > 1 and isprime(r) and p > 1 and isprime(p):
            doubly_hard.append((n, q, p, r))
    print(f"Total doubly-hard cases: {len(doubly_hard)} / {total}  ({len(doubly_hard)/total:.4f})")
    print(f"\nFirst 20 doubly-hard:")
    for n, q, p, r in doubly_hard[:20]:
        print(f"  n={n:>8}  q={q:>7}  r=(q-1)/2={r:>6}  p=(2q-1)/3={p:>7}")

    # Best modular sub-class to prove cleanly?
    # The cleanest "modular obstruction" Lean theorem:
    #   "For Sophie Germain pairs (n-1, q) with q ≡ (l+1)/2 (mod l) for some
    #   small l in {5,7,11,...}, the Erdős 647 inequality cannot hold."
    # This subclass covers `len(covered)/total` ≈ ??? of cases.
    print(f"\n\n=== Summary: best provable subclass ===")
    print(f"Subclass: q ≡ a (mod l) for some l in {small_primes}")
    print(f"Coverage: {len(covered)} / {total} = {len(covered)/total*100:.2f}% of Sophie pairs.")
    print(f"\nResidual uncovered: {uncovered} pairs ({uncovered/total*100:.2f}%)")
    print(f"  of which {uncov_composite} have (2q-1)/3 composite by larger factor")
    print(f"  of which {uncov_prime} have (2q-1)/3 actually prime (true sieve gap).")


if __name__ == "__main__":
    main()
