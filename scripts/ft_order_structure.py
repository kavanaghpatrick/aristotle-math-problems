#!/usr/bin/env python3
"""
Feit-Thompson p=3 — Deep analysis of ord_A(3) structure.

KEY OBSERVATION: For all 28 eligible q, ord(3) = q * m where m | (q+1).
The ratio m/(q+1) takes values like 1/24, 1/12, 1/6, 1/12, etc.
This means (q+1)/m is the "index" of ord(3) in the full q*(q+1).

If ord(3) = q always (i.e., m = 1), that's 3^q = 1 — a counterexample.
But m > 1 always. What is the structure of m and (q+1)/m?

Under FT assumption: ord(3) = q, so m = 1 and (q+1)/m = q+1.
Unconditionally: m > 1 and (q+1)/m < q+1.

Can we prove m > 1 MUST hold? That IS the Feit-Thompson conjecture for p=3!
"""

from sympy import isprime, factorint, divisors, gcd
from collections import Counter, defaultdict
from fractions import Fraction

def find_eligible(limit=100000):
    eligible = []
    for q in range(71, limit, 72):
        if not isprime(q):
            continue
        A = q*q + q + 1
        if not isprime(A):
            continue
        eligible.append((q, A))
    return eligible

def compute_ord3(q, A):
    """Compute ord(3) mod A, knowing it divides q*(q+1)."""
    qp1 = q + 1
    divs = sorted(divisors(qp1))
    # Check d | (q+1) first (smaller values)
    for d in divs:
        if pow(3, d, A) == 1:
            return d
    # Then q*d for d | (q+1)
    for d in divs:
        if pow(3, q * d, A) == 1:
            return q * d
    return q * qp1  # should be A-1 = q*(q+1)

def main():
    eligible = find_eligible(100000)
    print(f"Found {len(eligible)} eligible primes q < 100000")
    print()

    # ========================================
    # A. Distribution of m = ord(3)/q and (q+1)/m
    # ========================================
    print("=" * 70)
    print("A. Structure of ord(3) = q * m, index = (q+1)/m")
    print("=" * 70)

    data = []
    for q, A in eligible:
        ord3 = compute_ord3(q, A)
        if ord3 % q == 0:
            m = ord3 // q
            index = (q + 1) // m if (q + 1) % m == 0 else None
            data.append((q, A, ord3, m, index))
        else:
            # ord(3) | (q+1), doesn't involve q
            data.append((q, A, ord3, 0, None))

    print(f"\n  {'q':>6s} {'q+1':>6s} {'ord(3)':>12s} {'m':>8s} {'(q+1)/m':>8s} "
          f"{'m factors':>25s}")
    print("  " + "-" * 75)
    for q, A, ord3, m, index in data[:40]:
        if m > 0:
            m_factors = factorint(m)
            m_str = " · ".join(f"{p}^{e}" if e > 1 else str(p)
                              for p, e in sorted(m_factors.items()))
            print(f"  {q:6d} {q+1:6d} {ord3:12d} {m:8d} {index:8d} {m_str:>25s}")
        else:
            print(f"  {q:6d} {q+1:6d} {ord3:12d} {'???':>8s} {'???':>8s}")
    print()

    # ========================================
    # B. Distribution of index = (q+1)/m
    # ========================================
    print("=" * 70)
    print("B. Distribution of index = (q+1)/m")
    print("=" * 70)
    index_dist = Counter()
    for q, A, ord3, m, index in data:
        if index is not None:
            index_dist[index] += 1

    print(f"  Total: {len(data)} eligible q")
    for idx, cnt in sorted(index_dist.items()):
        pct = 100 * cnt / len(data)
        print(f"  index = {idx:6d}: {cnt:3d} ({pct:5.1f}%)")
    print()

    # What fraction of indices are small (≤ 72)?
    small = sum(cnt for idx, cnt in index_dist.items() if idx <= 72)
    print(f"  Index ≤ 72: {small}/{len(data)} ({100*small/len(data):.1f}%)")
    print()

    # ========================================
    # C. Factorization pattern of index
    # ========================================
    print("=" * 70)
    print("C. Factor structure of index = (q+1)/m")
    print("   Under assumption: index = q+1 (all of q+1)")
    print("   Unconditionally: index is a PROPER divisor of q+1")
    print("=" * 70)

    index_factor_set = defaultdict(int)
    for q, A, ord3, m, index in data:
        if index is not None and index > 0:
            factors = factorint(index)
            for p in factors:
                index_factor_set[p] += 1

    print(f"  Prime divisors appearing in index across all eligible q:")
    for p, cnt in sorted(index_factor_set.items()):
        print(f"    p={p}: appears in {cnt}/{len(data)} indices")
    print()

    # ========================================
    # D. Is index always divisible by some fixed prime?
    # ========================================
    print("=" * 70)
    print("D. What always divides the index?")
    print("=" * 70)

    for p_test in [2, 3, 4, 6, 8, 12, 24]:
        all_div = all(index is not None and index % p_test == 0
                     for q, A, ord3, m, index in data)
        count = sum(1 for q, A, ord3, m, index in data
                   if index is not None and index % p_test == 0)
        print(f"  {p_test} | index: {count}/{len(data)} ({'ALL' if all_div else 'not all'})")
    print()

    # ========================================
    # E. CRITICAL: Does ord(3) always divide q * (q+1)/gcd(6, q+1)?
    #    For q ≡ 71 mod 72: gcd(6, q+1) = 6, so (q+1)/6 divides (q+1).
    #    Is ord(3) ≤ q * (q+1)/6? i.e., is m ≤ (q+1)/6? i.e., index ≥ 6?
    # ========================================
    print("=" * 70)
    print("E. Is index always ≥ 6? (i.e., is ord(3) ≤ q*(q+1)/6?)")
    print("   Recall: 3 is a 6th power residue (χ₆(3) = 1 always)")
    print("   So: 3^{(A-1)/6} = 1, meaning ord(3) | (A-1)/6 = q(q+1)/6")
    print("   Therefore: ord(3) ≤ q(q+1)/6, so m ≤ (q+1)/6, so index ≥ 6")
    print("=" * 70)

    all_ge_6 = all(index is not None and index >= 6
                  for q, A, ord3, m, index in data)
    print(f"  index ≥ 6 for all: {all_ge_6}")

    min_index = min(index for q, A, ord3, m, index in data if index is not None)
    print(f"  Minimum index: {min_index}")

    # Cases with small index
    print(f"\n  Cases with small index (< 24):")
    for q, A, ord3, m, index in data:
        if index is not None and index < 24:
            print(f"    q={q}, index={index}, m={m}, ord(3)={ord3}")
    print()

    # ========================================
    # F. More precise: what is the exact n such that ord(3) | q*(q+1)/n?
    #    We know n ≥ 6 (from χ₆(3) = 1).
    #    From data: is n always ≥ 12? ≥ 24?
    # ========================================
    print("=" * 70)
    print("F. Tightest bound: index = (q+1)/m. What's the minimum?")
    print("   χ₆(3) = 1 → index ≥ 6 (proven)")
    print("   If χ₈(3) = 1 always → index ≥ 8 (but χ₈ varies!)")
    print("   If χ₉(3) = 1 always → index ≥ 9 (but χ₉ varies!)")
    print("=" * 70)

    # What's the GCD of all indices?
    from functools import reduce
    from math import gcd as mathgcd
    indices = [index for q, A, ord3, m, index in data if index is not None and index > 0]
    g = reduce(mathgcd, indices)
    print(f"  GCD of all indices: {g}")
    print(f"  Indices: {sorted(set(indices))}")
    print()

    # ========================================
    # G. The key question: under the FT assumption, index = q+1.
    #    Unconditionally, index | (q+1) and index ≥ 6.
    #    For a contradiction, we need to show index ≠ q+1,
    #    i.e., m ≠ 1, i.e., ord(3) ≠ q.
    #
    #    But index = q+1 means ord(3) = q. And we've shown
    #    computationally that ord(3) = q*m with m ≥ 3.
    #
    #    The THEORETICAL question: can we prove index < q+1?
    #    This IS the FT conjecture! Any proof of index < q+1 = proof of FT.
    #
    #    Character approach gives index ≥ 6 (from χ₆). Can we improve?
    # ========================================
    print("=" * 70)
    print("G. Can we improve the lower bound on index beyond 6?")
    print("   We need: 3^{(A-1)/n} = 1 for some n > 6")
    print("   i.e., 3 is an n-th power residue for all n | something > 6")
    print("=" * 70)

    # For each eligible q, find the largest n such that 3^{(A-1)/n} = 1
    # This equals ord(3), and (A-1)/ord(3) is the index.
    # So the "largest n" is ord(3) itself.
    # But we want UNIVERSAL n: for ALL q, 3^{(A-1)/n} = 1.
    # i.e., for all q, n | (A-1)/ord(3) = index.
    # This means n | GCD of all indices = g (computed above).
    # So the universal bound is: index ≥ g.

    print(f"  Universal n: must divide GCD of all indices = {g}")
    print(f"  So the universal lower bound on index is {g}")
    print(f"  This means: ord(3) | q*(q+1)/{g} for ALL eligible q")
    print()

    if g > 6:
        print(f"  IMPROVEMENT! Index ≥ {g} > 6 (better than sextic character)")
        print(f"  But does this follow from a known character condition?")
        # Check: what character gives this?
        # 3^{(A-1)/g} = 1 for all eligible q?
        all_ok = True
        for q, A, ord3, m, index in data:
            Am1 = A - 1
            if Am1 % g != 0:
                all_ok = False
                print(f"  !! {g} does not divide A-1 for q={q}")
                break
            if pow(3, Am1 // g, A) != 1:
                all_ok = False
                print(f"  !! 3^{{(A-1)/{g}}} ≠ 1 for q={q}")
                break
        if all_ok:
            print(f"  CONFIRMED: 3^{{(A-1)/{g}}} = 1 for all eligible q")
    else:
        print(f"  No improvement beyond 6 from GCD analysis")

    print()

    # ========================================
    # H. But wait — maybe a CONDITIONAL improvement is possible.
    #    For q ≡ 7 mod 8: v₂(q+1) ≥ 3 (since q+1 ≡ 0 mod 8)
    #    χ₂(3) = 1 means 2 | index.
    #    χ₄(3) = 1 iff 3^{(A-1)/4} = 1. Check:
    # ========================================
    print("=" * 70)
    print("H. Character refinements: χ₄(3), χ₈(3), χ₁₂(3)")
    print("=" * 70)

    for n_test in [4, 8, 12, 16, 18, 24, 36, 48, 72]:
        count = 0
        total = 0
        for q, A in eligible:
            Am1 = A - 1
            if Am1 % n_test != 0:
                continue
            total += 1
            if pow(3, Am1 // n_test, A) == 1:
                count += 1
        pct = 100 * count / total if total > 0 else 0
        print(f"  χ_{n_test}(3) = 1: {count}/{total} ({pct:.0f}%)")

    print()
    print("  KEY: Any character where it's ALWAYS 1 gives a universal index bound")
    print("  From data: χ₆ = 1 always. χ₄ = 1 always? → check lcm(4,6) = 12")
    print()

    # Check χ₄ explicitly
    chi4_all = True
    for q, A in eligible:
        Am1 = A - 1
        if Am1 % 4 == 0 and pow(3, Am1 // 4, A) != 1:
            chi4_all = False
            break

    print(f"  χ₄(3) = 1 for ALL eligible q? {chi4_all}")

    if chi4_all:
        # Then 3 is a 4th power residue for all q
        # Combined with 3 being a 6th power residue:
        # 3^{(A-1)/4} = 1 and 3^{(A-1)/6} = 1
        # → 3^{gcd((A-1)/4, (A-1)/6)} = 1
        # gcd((A-1)/4, (A-1)/6) = (A-1)/lcm(4,6) = (A-1)/12
        # → 3^{(A-1)/12} = 1
        # → index ≥ 12

        # Verify
        chi12_all = True
        for q, A in eligible:
            Am1 = A - 1
            if Am1 % 12 == 0 and pow(3, Am1 // 12, A) != 1:
                chi12_all = False
                break
        print(f"  → χ₁₂(3) = 1 for ALL? {chi12_all}")
        if chi12_all:
            print(f"  → Universal index bound: index ≥ 12!")
            print(f"  → ord(3) | q*(q+1)/12 for ALL eligible q")
            print()

            # Can we prove χ₄(3) = 1 theoretically?
            # χ₄(3) = 3^{(A-1)/4} = 3^{q(q+1)/4}
            # For q ≡ 71 mod 72: q+1 ≡ 0 mod 8, so (q+1)/4 is even
            # q(q+1)/4 = q * (q+1)/4
            # 3^{q(q+1)/4} = (3^{q(q+1)/2})^{1/2} ... nope
            # 3^{(A-1)/4} = (3^{(A-1)/2})^{1/2}? Only if we can take square roots.
            # Actually: 3^{(A-1)/2} = (3/A) = 1. So 3^{(A-1)/4} is a square root of 1.
            # i.e., 3^{(A-1)/4} ∈ {1, -1}.
            # If it's always 1, that's a stronger statement.

            print("  THEORETICAL CHECK: 3^{(A-1)/4} ∈ {1, -1} since (3^{(A-1)/4})² = (3/A) = 1")
            chi4_vals = Counter()
            for q, A in eligible:
                Am1 = A - 1
                val = pow(3, Am1 // 4, A)
                if val == 1:
                    chi4_vals['+1'] += 1
                elif val == A - 1:
                    chi4_vals['-1'] += 1
                else:
                    chi4_vals[str(val)] += 1
            print(f"  χ₄(3) = +1: {chi4_vals.get('+1', 0)}, -1: {chi4_vals.get('-1', 0)}")
            print()

            # For χ₄(3) = 3^{(A-1)/4}: this is the biquadratic residue symbol
            # It equals +1 iff 3 is a 4th power residue mod A
            # By biquadratic reciprocity (in Z[i]), this can be computed...
            # For A ≡ 1 mod 4 (which it is since A ≡ 1 mod 8 for q ≡ 7 mod 8):
            # There exists π in Z[i] with ππ̄ = A
            # χ₄(3) = (3/π)_4 (quartic residue symbol in Z[i])

            print("  To PROVE χ₄(3) = 1:")
            print("  Need: 3 is a 4th power residue mod A = q²+q+1")
            print("  A ≡ 1 (mod 4) always (since A = q²+q+1, q odd)")
            print("  A ≡ 1 (mod 8) for q ≡ 7 mod 8 (since q+1 ≡ 0 mod 8, q(q+1)/2 even)")
            print()

            # CHECK: is A ≡ 1 mod 8 always?
            a_mod8_dist = Counter()
            for q, A in eligible:
                a_mod8_dist[A % 8] += 1
            print(f"  A mod 8 distribution: {dict(a_mod8_dist)}")
            # A = q²+q+1. q ≡ 7 mod 8. q² ≡ 1 mod 8. q²+q ≡ 1+7 = 0 mod 8.
            # A = q²+q+1 ≡ 1 mod 8. Confirmed!
            print(f"  A ≡ 1 (mod 8) always (since q ≡ 7 mod 8: q²≡1, q²+q≡0)")
            print()

            # CHECK: A ≡ 1 mod 16?
            a_mod16_dist = Counter()
            for q, A in eligible:
                a_mod16_dist[A % 16] += 1
            print(f"  A mod 16 distribution: {dict(a_mod16_dist)}")
            # q ≡ 7 mod 8 means q = 8k+7
            # q² = 64k²+112k+49 ≡ 49 ≡ 1 mod 16
            # q²+q = 1 + (8k+7) = 8k+8 mod 16
            # For k even: 8·0+8 = 8 mod 16 → A ≡ 9 mod 16
            # For k odd: 8·1+8 = 16 ≡ 0 mod 16 → A ≡ 1 mod 16
            # q ≡ 71 mod 72: q = 72j + 71 = 8(9j+8) + 7, so k = 9j+8
            # k mod 2: 9j+8 mod 2 = j+0 mod 2. So k even ↔ j even.
            # q mod 16: q = 72j+71. 72j mod 16 = 8j. 71 mod 16 = 7.
            # q mod 16 = 8j+7 mod 16. j even: q ≡ 7 mod 16. j odd: q ≡ 15 mod 16.
            print(f"  (Depends on q mod 16: q≡7→A≡9, q≡15→A≡1)")
            print()

    # ========================================
    # I. Check: is the index related to 12 | index always?
    # ========================================
    print("=" * 70)
    print("I. Does 12 always divide the index?")
    print("=" * 70)
    all_12 = all(index is not None and index % 12 == 0
                for q, A, ord3, m, index in data)
    count_12 = sum(1 for q, A, ord3, m, index in data
                  if index is not None and index % 12 == 0)
    print(f"  12 | index: {count_12}/{len(data)} ({'ALL' if all_12 else 'not all'})")

    if not all_12:
        non12 = [(q, index) for q, A, ord3, m, index in data
                if index is not None and index % 12 != 0]
        print(f"  Exceptions: {non12[:10]}")

    all_6 = all(index is not None and index % 6 == 0
               for q, A, ord3, m, index in data)
    print(f"   6 | index: {'ALL' if all_6 else 'not all'}")
    print()

    # ========================================
    # J. Structure of q+1 and m
    # ========================================
    print("=" * 70)
    print("J. What is v₂(m) and v₃(m) compared to v₂(q+1) and v₃(q+1)?")
    print("   index = (q+1)/m, so v_p(index) = v_p(q+1) - v_p(m)")
    print("=" * 70)

    for q, A, ord3, m, index in data[:25]:
        if m == 0 or index is None:
            continue
        qp1 = q + 1
        v2_qp1 = 0
        temp = qp1
        while temp % 2 == 0:
            v2_qp1 += 1
            temp //= 2
        v2_m = 0
        temp = m
        while temp % 2 == 0:
            v2_m += 1
            temp //= 2
        v3_qp1 = 0
        temp = qp1
        while temp % 3 == 0:
            v3_qp1 += 1
            temp //= 3
        v3_m = 0
        temp = m
        while temp % 3 == 0:
            v3_m += 1
            temp //= 3

        print(f"  q={q:6d}: v₂(q+1)={v2_qp1}, v₂(m)={v2_m}, v₂(idx)={v2_qp1-v2_m} | "
              f"v₃(q+1)={v3_qp1}, v₃(m)={v3_m}, v₃(idx)={v3_qp1-v3_m} | "
              f"index={index}")

    print()

    # ========================================
    # K. Key theoretical question:
    #    Can we prove v₂(index) ≥ 1 and v₃(index) ≥ 1?
    #    v₂(index) ≥ 1: 3 is a QR (proved), so 2 | index.
    #    v₃(index) ≥ 1: 3 is a cubic residue (proved for q ≡ 8 mod 9), so 3 | index.
    #    Together: 6 | index (proved).
    #    v₂(index) ≥ 2: 3 is a 4th power residue. CHECK.
    # ========================================
    print("=" * 70)
    print("K. Can we prove v₂(index) ≥ 2? (χ₄(3) = 1)")
    print("=" * 70)

    # 3^{(A-1)/4} mod A
    v2_index_min = 100
    for q, A, ord3, m, index in data:
        if index is None:
            continue
        v2 = 0
        temp = index
        while temp % 2 == 0:
            v2 += 1
            temp //= 2
        v2_index_min = min(v2_index_min, v2)

    print(f"  Minimum v₂(index) across all data: {v2_index_min}")

    v3_index_min = 100
    for q, A, ord3, m, index in data:
        if index is None:
            continue
        v3 = 0
        temp = index
        while temp % 3 == 0:
            v3 += 1
            temp //= 3
        v3_index_min = min(v3_index_min, v3)

    print(f"  Minimum v₃(index) across all data: {v3_index_min}")
    print(f"  → Minimum index ≥ 2^{v2_index_min} · 3^{v3_index_min} = {2**v2_index_min * 3**v3_index_min}")
    print()

    # ========================================
    # L. THEORETICAL: Can we prove 3^{(A-1)/4} = 1?
    #
    # 3^{(A-1)/4} = 3^{q(q+1)/4}
    # = (3^q)^{(q+1)/4} · ??? No, it's just 3^{q(q+1)/4}
    #
    # Alternative: 3^{(A-1)/4} = 3^{(A-1)/2 · 1/2} = (3^{(A-1)/2})^{?}
    # 3^{(A-1)/2} = 1 (Legendre symbol). So x := 3^{(A-1)/4} satisfies x² = 1.
    # Thus x = ±1. We need x = 1.
    #
    # 3^{(A-1)/4} mod A = 3^{q(q+1)/4} mod A
    #
    # For A ≡ 1 mod 8: by theory, -1 is a 4th power mod A.
    # But we need 3 to be a 4th power, not -1.
    #
    # Quartic residuacity of 3 mod A depends on the representation A = a²+b²
    # where a is odd (A ≡ 1 mod 4).
    # Actually for 3: 3 is a 4th power mod A iff:
    # A = x² + 9y² for some integers x, y (by quartic reciprocity for 3)
    # or equivalently: A splits completely in Q(ζ₁₂) = Q(√3, i)
    # ========================================
    print("=" * 70)
    print("L. Does A = x² + 9y² (quartic residuacity of 3)?")
    print("   A = q²+q+1 = (q + 1/2)² + 3/4 = (2q+1)²/4 + 3/4 = ((2q+1)²+3)/4")
    print("=" * 70)

    # A = (4q²+4q+4)/4 = ((2q+1)² + 3)/4
    # For A = x² + 9y²:
    # Also A = x² + 9y² iff 3 is a 4th power residue mod A (when A ≡ 1 mod 12)

    # Check A mod 12:
    for q, A in eligible[:5]:
        print(f"  q={q}: A mod 12 = {A%12}, A mod 3 = {A%3}")

    # A ≡ 1 mod 3 (proved). A ≡ 1 mod 4 (proved). So A ≡ 1 mod 12.
    print(f"  A ≡ 1 mod 12 always (confirmed)")
    print()

    # Try to represent A = x² + 9y²
    count_rep = 0
    for q, A in eligible:
        found = False
        for y in range(1, int(A**0.5) // 3 + 2):
            rem = A - 9 * y * y
            if rem <= 0:
                break
            x = int(rem ** 0.5)
            if x * x == rem:
                found = True
                if count_rep < 10:
                    print(f"  q={q:6d}: A = {x}² + 9·{y}² = {x*x + 9*y*y}")
                count_rep += 1
                break
        if not found and count_rep < 10:
            print(f"  q={q:6d}: A ≠ x² + 9y² for any x,y!")
    print(f"\n  A = x² + 9y²: {count_rep}/{len(eligible)}")
    print()

    if count_rep == len(eligible):
        print("  *** A = x² + 9y² for ALL eligible q! ***")
        print("  This PROVES χ₄(3) = 1, giving index ≥ 12!")
        print()
        print("  THEORETICAL PROOF:")
        print("  A = q²+q+1. Set y = 1: x² = A - 9 = q²+q-8.")
        print("  Discriminant: q²+q-8 is a perfect square?")
        for q, A in eligible[:10]:
            val = q*q + q - 8
            sq = int(val**0.5)
            print(f"    q={q}: q²+q-8 = {val}, √ = {sq}, sq² = {sq*sq}, match: {sq*sq == val}")
        print("  No — y ≠ 1 in general. The representation uses various y values.")
        print()

        # But CAN we prove A = x² + 9y² always?
        # A = q²+q+1. We need to show this is always of the form x² + 9y².
        # By genus theory: n = x²+9y² iff n ≡ 1 mod 3 and n = x²+9y² is a
        # consequence of the class number of Q(√-9) = Q(√-1)... hmm, not quite.
        # Actually h(-36) = 2, so not every prime ≡ 1 mod 12 is x²+9y².
        # Primes ≡ 1 mod 12 are x²+9y² iff cubic residue of something...

        # Actually for the class group of discriminant -36:
        # h(-36) = 2, forms are x²+9y² and 2x²+2xy+5y² (or 3x²+3y²... )
        # Hmm, let me just check: is EVERY prime ≡ 1 mod 12 of the form x²+9y²?
        # No! That would mean h=1. With h=2, half of primes ≡ 1 mod 12 are x²+9y²
        # and half are 2x²+2xy+5y² (or the other form).
        # But our data shows ALL eligible A are x²+9y². This must be because
        # A = q²+q+1 has special structure!

        print("  NOTE: Not all primes ≡ 1 (mod 12) are x²+9y² (class number 2).")
        print("  But A = q²+q+1 always is! This is structural:")
        print("  A = q²+q+1 = (q)² + q + 1. Hmm...")
        print("  Actually: 4A = (2q+1)² + 3 = (2q+1)² + 3·1²")
        print("  So 4A = u² + 3v² with u=2q+1, v=1.")
        print("  Now A = x² + 9y² iff 4A = (2x)² + 36y² iff 4A = X² + 36Y²")
        print("  But 4A = (2q+1)² + 3 which is X² + 3 with X = 2q+1.")
        print("  For this to be X² + 36Y²: need 3 = 36Y² → Y² = 1/12. No.")
        print()
        print("  4A = u² + 3v² has the UNIQUE representation u=2q+1, v=1.")
        print("  Now 4(x²+9y²) = (2x)² + 36y². And 4A = (2q+1)² + 3.")
        print("  So (2x)² + 36y² = (2q+1)² + 3.")
        print("  If y=0: 4x² = (2q+1)²+3 → not a square generally.")
        print("  The representation A = x²+9y² comes from a DIFFERENT decomposition.")


if __name__ == "__main__":
    main()
