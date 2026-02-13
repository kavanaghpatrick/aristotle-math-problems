#!/usr/bin/env python3
"""
Feit-Thompson p=3 sextic character exploration.

For primes q ≡ 71 (mod 72) with A = q²+q+1 prime, explore:
1. χ₆(3) = 3^{(A-1)/6} mod A
2. χ₆(1-q) = (1-q)^{(A-1)/6} mod A
3. χ₈(3) = 3^{(A-1)/8} mod A
4. χ₉(3) = 3^{(A-1)/9} mod A
5. χ₂₄(3) = 3^{(A-1)/24} mod A
6. 3^{q+1} mod A  (the q-th power residue character of 3)
7. 3^{(q+1)/6} mod A
8. Various other elements

Also verify the QR computation: (3/A) via Legendre symbol.
"""

from sympy import isprime, legendre_symbol, primitive_root
from collections import Counter, defaultdict
import sys

def explore_eligible_primes(limit=20000):
    """Find all eligible q and compute power residue characters."""

    eligible = []
    for q in range(71, limit, 72):
        if not isprime(q):
            continue
        A = q*q + q + 1
        if not isprime(A):
            continue
        eligible.append((q, A))

    print(f"Found {len(eligible)} eligible primes q ≡ 71 (mod 72) with A prime, q < {limit}")
    print(f"First 10: {[q for q,A in eligible[:10]]}")
    print()

    # ========================================
    # 1. χ₆(3) = 3^{(A-1)/6} mod A
    # ========================================
    print("=" * 70)
    print("1. χ₆(3) = 3^{(A-1)/6} mod A")
    print("=" * 70)
    chi6_3_vals = Counter()
    chi6_3_detail = []
    for q, A in eligible:
        exp = (A - 1) // 6
        val = pow(3, exp, A)
        chi6_3_vals[val == 1] += 1
        if val != 1:
            chi6_3_detail.append((q, A, val))

    print(f"  χ₆(3) = 1: {chi6_3_vals[True]} times")
    print(f"  χ₆(3) ≠ 1: {chi6_3_vals[False]} times")
    if chi6_3_detail:
        print(f"  Non-1 cases: {chi6_3_detail[:10]}")
    print()

    # ========================================
    # 2. Verify (3/A) = Legendre symbol
    # ========================================
    print("=" * 70)
    print("2. Legendre symbol (3/A)")
    print("=" * 70)
    leg_vals = Counter()
    for q, A in eligible:
        ls = legendre_symbol(3, A)
        leg_vals[ls] += 1
    print(f"  (3/A) = +1: {leg_vals[1]} times")
    print(f"  (3/A) = -1: {leg_vals[-1]} times")
    print(f"  Confirms: 3 is always a QR mod A for q ≡ 2 mod 3: {leg_vals[-1] == 0}")
    print()

    # ========================================
    # 3. χ₃(3) = 3^{(A-1)/3} mod A
    # ========================================
    print("=" * 70)
    print("3. χ₃(3) = 3^{(A-1)/3} mod A")
    print("=" * 70)
    chi3_3_vals = Counter()
    for q, A in eligible:
        exp = (A - 1) // 3
        val = pow(3, exp, A)
        chi3_3_vals[val == 1] += 1
    print(f"  χ₃(3) = 1: {chi3_3_vals[True]} times")
    print(f"  χ₃(3) ≠ 1: {chi3_3_vals[False]} times")
    print(f"  Confirms: 3 is always a cubic residue mod A for q ≡ 8 mod 9: {chi3_3_vals[False] == 0}")
    print()

    # ========================================
    # 4. χ₈(3) = 3^{(A-1)/8} mod A
    # ========================================
    print("=" * 70)
    print("4. χ₈(3) = 3^{(A-1)/8} mod A  [8th power residue]")
    print("=" * 70)
    chi8_3_is1 = Counter()
    chi8_3_detail = []
    for q, A in eligible:
        assert (A - 1) % 8 == 0, f"8 does not divide A-1 for q={q}"
        exp = (A - 1) // 8
        val = pow(3, exp, A)
        chi8_3_is1[val == 1] += 1
        if val != 1 and len(chi8_3_detail) < 20:
            chi8_3_detail.append((q, val))
    print(f"  χ₈(3) = 1: {chi8_3_is1[True]} times")
    print(f"  χ₈(3) ≠ 1: {chi8_3_is1[False]} times")
    if chi8_3_detail:
        print(f"  Non-1 cases (q, val): {chi8_3_detail[:10]}")

    # Under assumption 3^q=1: 3^{(A-1)/8} = 3^{q(q+1)/8} = (3^q)^{(q+1)/8} = 1
    # since 8|(q+1) for q≡71 mod 72
    print(f"  Under assumption 3^q=1: χ₈(3) = 1^{{(q+1)/8}} = 1 (no contradiction possible)")
    print()

    # ========================================
    # 5. χ₉(3) = 3^{(A-1)/9} mod A
    # ========================================
    print("=" * 70)
    print("5. χ₉(3) = 3^{(A-1)/9} mod A  [9th power residue]")
    print("=" * 70)
    chi9_3_is1 = Counter()
    chi9_3_detail = []
    for q, A in eligible:
        assert (A - 1) % 9 == 0, f"9 does not divide A-1 for q={q}"
        exp = (A - 1) // 9
        val = pow(3, exp, A)
        chi9_3_is1[val == 1] += 1
        if val != 1 and len(chi9_3_detail) < 20:
            chi9_3_detail.append((q, val))
    print(f"  χ₉(3) = 1: {chi9_3_is1[True]} times")
    print(f"  χ₉(3) ≠ 1: {chi9_3_is1[False]} times")
    if chi9_3_detail:
        print(f"  Non-1 cases (q, val): {chi9_3_detail[:10]}")

    # Under assumption: 3^{q(q+1)/9} = (3^q)^{(q+1)/9} = 1 since 9|(q+1)
    print(f"  Under assumption 3^q=1: χ₉(3) = 1^{{(q+1)/9}} = 1 (no contradiction possible)")
    print()

    # ========================================
    # 6. χ₂₄(3) = 3^{(A-1)/24} mod A
    # ========================================
    print("=" * 70)
    print("6. χ₂₄(3) = 3^{(A-1)/24} mod A  [24th power residue]")
    print("=" * 70)
    chi24_is1 = Counter()
    chi24_detail = []
    for q, A in eligible:
        # Check 24 | (A-1)
        if (A - 1) % 24 != 0:
            print(f"  WARNING: 24 does not divide A-1 for q={q}")
            continue
        exp = (A - 1) // 24
        val = pow(3, exp, A)
        chi24_is1[val == 1] += 1
        if val != 1 and len(chi24_detail) < 20:
            chi24_detail.append((q, val))
    print(f"  χ₂₄(3) = 1: {chi24_is1[True]} times")
    print(f"  χ₂₄(3) ≠ 1: {chi24_is1[False]} times")
    if chi24_detail:
        print(f"  Non-1 cases (q, val): {chi24_detail[:10]}")
    # Under assumption: 3^{q(q+1)/24} = (3^q)^{(q+1)/24} = 1 since 24|(q+1)
    # q≡71 mod 72 → q+1≡72≡0 mod 72, so 24|(q+1). Yes.
    print(f"  Under assumption 3^q=1: χ₂₄(3) = 1 (no contradiction possible)")
    print()

    # ========================================
    # 7. THE KEY: 3^{q+1} mod A  (q-th power residue)
    # ========================================
    print("=" * 70)
    print("7. *** 3^{q+1} mod A  [q-th power residue of 3] ***")
    print("   Under assumption 3^q=1: 3^{q+1} = 3·3^q = 3·1 = 3")
    print("   If 3^{q+1} ≠ 3 unconditionally → CONTRADICTION!")
    print("=" * 70)

    qp1_vals = Counter()
    qp1_is3 = Counter()
    qp1_detail = []
    for q, A in eligible:
        val = pow(3, q + 1, A)
        qp1_is3[val == 3] += 1
        if val != 3 and len(qp1_detail) < 30:
            qp1_detail.append((q, A, val))
        # Track what fraction of the time it equals 3

    print(f"  3^{{q+1}} = 3: {qp1_is3[True]} times")
    print(f"  3^{{q+1}} ≠ 3: {qp1_is3[False]} times")
    if qp1_is3[True] > 0:
        print(f"  !! 3^{{q+1}} = 3 sometimes (so no universal contradiction)")
        # Show cases where it equals 3
        eq3_cases = [(q, A) for q, A in eligible if pow(3, q+1, A) == 3]
        print(f"  Cases where 3^{{q+1}} = 3: q = {[q for q,A in eq3_cases[:20]]}")
    if qp1_detail:
        print(f"  First non-3 cases: {qp1_detail[:10]}")
    print()

    # ========================================
    # 8. 3^{(q+1)/k} mod A for various k dividing q+1
    # ========================================
    print("=" * 70)
    print("8. 3^{(q+1)/k} mod A for small k | (q+1)")
    print("   q ≡ 71 mod 72 → q+1 ≡ 0 mod 72")
    print("   Under assumption: 3^{(q+1)/k} = 3^{(q+1)/k} (NO simplification!)")
    print("   Because 3^q = 1 gives 3^{q+1} = 3, NOT 3^{(q+1)/k} = 3^{1/k}")
    print("=" * 70)

    for k in [2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72]:
        vals = Counter()
        for q, A in eligible:
            if (q + 1) % k != 0:
                continue
            exp = (q + 1) // k
            val = pow(3, exp, A)
            vals[val] += 1

        # Show distribution
        total = sum(vals.values())
        is1 = vals.get(1, 0)
        print(f"  k={k:3d}: 3^{{(q+1)/{k}}} = 1 in {is1}/{total} cases, "
              f"distinct values: {len(vals)}")
    print()

    # ========================================
    # 9. Characters of (1-q): χ₆(1-q), and ord(1-q)
    # ========================================
    print("=" * 70)
    print("9. χ₆(1-q) = (1-q)^{(A-1)/6} mod A")
    print("=" * 70)
    chi6_1mq = Counter()
    chi6_1mq_detail = []
    for q, A in eligible[:50]:  # first 50 for detail
        val_1mq = (1 - q) % A
        exp = (A - 1) // 6
        chi6 = pow(val_1mq, exp, A)
        chi6_1mq[chi6 == 1] += 1
        chi6_1mq_detail.append((q, chi6))

    print(f"  χ₆(1-q) = 1: {chi6_1mq[True]} times (out of {sum(chi6_1mq.values())})")
    print(f"  χ₆(1-q) ≠ 1: {chi6_1mq[False]} times")
    if chi6_1mq[False] > 0:
        non1 = [(q, v) for q, v in chi6_1mq_detail if v != 1]
        print(f"  Non-1 values: {non1[:15]}")
    print()

    # ========================================
    # 10. Higher power characters that DON'T factor through 3^q
    # ========================================
    print("=" * 70)
    print("10. CRITICAL: Characters involving ord_A(3) directly")
    print("    ord_A(3) = order of 3 in (Z/AZ)*")
    print("    Under assumption: q | ord_A(3). If ord_A(3) = q, then 3^q ≡ 1.")
    print("    Unconditionally: ord_A(3) | (A-1) = q(q+1)")
    print("=" * 70)

    ord_dist = Counter()
    ord_detail = []
    for q, A in eligible[:100]:  # first 100
        # Compute order of 3 mod A
        # ord | A-1 = q(q+1)
        # Check divisors of q(q+1)
        order = None
        qp1 = q + 1
        Am1 = A - 1

        # Quick: check if 3^q = 1
        if pow(3, q, A) == 1:
            # Order divides q. Since q is prime, order is 1 or q.
            if pow(3, 1, A) == 1:
                order = 1
            else:
                order = q
        elif pow(3, qp1, A) == 1:
            # Order divides q+1 but not q
            # Find smallest divisor of q+1 that works
            order = qp1
            for d in range(2, qp1):
                if qp1 % d == 0 and pow(3, d, A) == 1:
                    order = d
                    break
        else:
            # Order doesn't divide q or q+1
            # Must involve both factors
            # Order divides q(q+1) but not q and not q+1
            # So order = q * (divisor of q+1)
            for d in sorted(set(d for d in range(1, qp1+1) if qp1 % d == 0)):
                if pow(3, q * d, A) == 1:
                    order = q * d
                    break

        ord_dist[order] += 1
        ord_detail.append((q, A, order))

    print(f"  Order distribution (first 100 eligible q):")
    for o, cnt in sorted(ord_dist.items(), key=lambda x: -x[1]):
        desc = ""
        if o is not None:
            for q, A, order in ord_detail:
                if order == o:
                    if o == q:
                        desc = " [= q, assumption holds!]"
                    elif o == q + 1:
                        desc = " [= q+1]"
                    elif o is not None and o % q == 0:
                        desc = f" [= q * {o//q}]"
                    break
        print(f"    ord = {o}: {cnt} times{desc}")

    # Specifically: how often does 3^q ≡ 1 mod A?
    assumption_holds = sum(1 for q, A, o in ord_detail if o is not None and o <= q and q % o == 0)
    # More precisely: 3^q = 1 means ord | q, so ord = 1 or q
    actual = sum(1 for q, A in eligible[:100] if pow(3, q, A) == 1)
    print(f"\n  3^q ≡ 1 (mod A) for {actual} out of {min(100, len(eligible))} eligible q")
    print(f"  (These would be actual Feit-Thompson counterexamples if they existed!)")
    print()

    # ========================================
    # 11. What is 3^{q+1} mod A — distribution
    # ========================================
    print("=" * 70)
    print("11. Distribution of 3^{q+1} mod A")
    print("=" * 70)
    val_set = []
    for q, A in eligible:
        val = pow(3, q + 1, A)
        val_set.append((q, A, val))

    # Check various structural properties
    is_3 = sum(1 for _, _, v in val_set if v == 3)
    is_9 = sum(1 for _, A, v in val_set if v == 9)
    is_inv3 = sum(1 for q, A, v in val_set if (v * 3) % A == 1)
    print(f"  3^{{q+1}} = 3: {is_3} / {len(val_set)}")
    print(f"  3^{{q+1}} = 9: {is_9} / {len(val_set)}")
    print(f"  3^{{q+1}} = 3^{{-1}}: {is_inv3} / {len(val_set)}")

    # What is 3^{q+1} in terms of powers of 3?
    print(f"\n  First 20 values of 3^{{q+1}} mod A:")
    for q, A, val in val_set[:20]:
        # Find discrete log base 3 mod A if feasible
        # Just report the value
        val_as_3pow = None
        p3 = 1
        for i in range(min(200, A)):
            if p3 == val:
                val_as_3pow = i
                break
            p3 = (p3 * 3) % A
        desc = f"= 3^{val_as_3pow}" if val_as_3pow is not None else f"= {val}"
        print(f"    q={q:6d}, A={A:12d}, 3^{{q+1}} {desc}")
    print()

    # ========================================
    # 12. NON-assumption approach: higher-order conditions
    # ========================================
    print("=" * 70)
    print("12. Explore: v_q(A-1) — exact power of q dividing A-1")
    print("    A-1 = q(q+1), so v_q(A-1) = 1 (since gcd(q, q+1) = 1)")
    print("    If 3^q = 1, then ord(3) | q, so ord(3) = q (since q prime, 3≠1)")
    print("    Then q | φ(A) = A-1 = q(q+1), consistent.")
    print("    But: does the EXACT structure of A-1 = q(q+1) constrain things?")
    print("=" * 70)

    # For each q, factor q+1 and see the structure
    print(f"\n  Factorization of q+1 for first 15 eligible q:")
    from sympy import factorint
    for q, A in eligible[:15]:
        qp1_factors = factorint(q + 1)
        factor_str = " · ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(qp1_factors.items()))
        print(f"    q={q:6d}, q+1={q+1:6d} = {factor_str}, A-1 = q·(q+1)")
    print()

    # ========================================
    # 13. THE DEEPEST CHECK: for d | (q+1), is 3^d ≡ 1 mod A?
    # ========================================
    print("=" * 70)
    print("13. For d | (q+1), check 3^d ≡ 1 (mod A)")
    print("    Under assumption ord(3) = q: 3^d ≡ 1 iff q | d, i.e., never for d | (q+1)")
    print("    since gcd(q, q+1) = 1.")
    print("    Unconditionally: if 3^d ≡ 1 for some d | (q+1), then ord(3) | d | (q+1)")
    print("    and also ord(3) | q(q+1), so this is possible.")
    print("=" * 70)

    found_d = 0
    for q, A in eligible[:50]:
        qp1 = q + 1
        # Get divisors of q+1
        divs = []
        for d in range(1, qp1 + 1):
            if qp1 % d == 0:
                divs.append(d)

        for d in divs:
            if d == qp1:
                continue  # skip full q+1
            if pow(3, d, A) == 1:
                found_d += 1
                if found_d <= 10:
                    print(f"    q={q}, d={d} | (q+1)={qp1}: 3^{d} ≡ 1 (mod A)!")

    if found_d == 0:
        print(f"    No proper divisor d of (q+1) with 3^d ≡ 1 (first 50 eligible q)")
    print()

    # ========================================
    # 14. Explore higher characters: χ_n(3) for n | q(q+1), n > 6
    # ========================================
    print("=" * 70)
    print("14. For which n | (A-1) is 3^{(A-1)/n} ≠ 1 unconditionally?")
    print("    Under assumption 3^q=1: 3^{(A-1)/n} = 3^{q(q+1)/n}")
    print("    This = 1 iff n | q·(something) where (something) makes exponent")
    print("    a multiple of ord(3)=q.")
    print("    i.e., 3^{q·(q+1)/n} = (3^q)^{(q+1)/n} = 1 when n | (q+1)")
    print("    But when n doesn't divide (q+1), the exponent is q·(q+1)/n")
    print("    where n = q·m for some m | (q+1)/gcd(n,q+1)... complicated.")
    print("=" * 70)

    # Key insight: if n does NOT divide (q+1), then (A-1)/n = q(q+1)/n
    # requires q | n for this to be an integer...
    # Actually (A-1)/n must be an integer, so n | q(q+1).
    # If q | n, say n = q·m where m | (q+1), then (A-1)/n = (q+1)/m
    # Under assumption: 3^{(q+1)/m} — this is NOT necessarily 1!
    # It's 1 iff ord(3) | (q+1)/m, i.e., q | (q+1)/m, i.e., qm | (q+1).
    # Since m | (q+1), we need q | (q+1)/m. But (q+1)/m ≤ q+1 < 2q for m≥1.
    # So q | (q+1)/m only if (q+1)/m = q, i.e., m = (q+1)/q, impossible for integer m.
    # THEREFORE: for n = q·m with 1 ≤ m ≤ q, 3^{(A-1)/n} = 3^{(q+1)/m} under assumption,
    # and this is NOT 1 (since ord(3)=q does not divide (q+1)/m).

    print("\n  KEY INSIGHT: For n = q·m (m | q+1, m < q+1):")
    print("  Under assumption: 3^{(A-1)/n} = 3^{(q+1)/m}")
    print("  Since ord(3) = q and q ∤ (q+1)/m (as (q+1)/m < 2q and ≠ q),")
    print("  we get 3^{(q+1)/m} ≠ 1.")
    print()
    print("  Unconditionally: 3^{(A-1)/n} = 3^{(q+1)/m}")
    print("  If this IS 1 unconditionally → contradiction (since under assumption it's NOT 1)")
    print()
    print("  Wait — that's backwards! Under assumption it's NOT 1,")
    print("  so we need it to ALWAYS BE 1 unconditionally for contradiction.")
    print()

    # Check: is 3^{(q+1)/m} ≡ 1 (mod A) for m | (q+1)?
    print("  Checking 3^{(q+1)/m} mod A for m = 2, 3, 4, 6, 8:")
    for m in [2, 3, 4, 6, 8, 9, 12, 24, 36, 72]:
        is1_count = 0
        total = 0
        for q, A in eligible:
            if (q + 1) % m != 0:
                continue
            exp = (q + 1) // m
            val = pow(3, exp, A)
            total += 1
            if val == 1:
                is1_count += 1
        print(f"    m={m:3d}: 3^{{(q+1)/{m}}} ≡ 1 in {is1_count}/{total} cases")
    print()

    # ========================================
    # 15. THE REVERSED CHECK: Under assumption, 3^{(q+1)/m} ≠ 1.
    #     So if unconditionally 3^{(q+1)/m} = 1 always → contradiction.
    #     But the data above shows it's NOT always 1. So no contradiction this way.
    #
    #     HOWEVER: What if under assumption, 3^{(q+1)/m} takes a SPECIFIC value
    #     (like ω, a root of unity) and unconditionally it NEVER takes that value?
    # ========================================
    print("=" * 70)
    print("15. Under assumption 3^q=1: 3^{(q+1)/2} = 3^{(q+1)/2}")
    print("    = 3^{(q-1)/2} · 3 = (3/A)_Legendre · 3 (if we use Euler's criterion)")
    print("    Wait: 3^{(q-1)/2} is NOT (3/A) — that's 3^{(A-1)/2}.")
    print("    3^{(q+1)/2} is just... 3^{(q+1)/2}. No simplification without assumption.")
    print("=" * 70)
    print()

    # But WITH assumption 3^q = 1:
    # 3^{(q+1)/2} = 3^{q} · 3^{(1-q)/2} = 1 · 3^{(1-q)/2}
    # Hmm, (1-q)/2 is negative since q > 1, so this is 3^{-(q-1)/2} = (3^{(q-1)/2})^{-1}
    # Not obviously helpful.

    # ========================================
    # 16. THE ACTUAL PROMISING DIRECTION:
    #     Consider (1-q)^{6q} = -1 under assumption.
    #     This means (1-q)^{12q} = 1, (1-q)^{6q} = -1.
    #     So ord(1-q) divides 12q but not 6q.
    #     Since ord(1-q) | A-1 = q(q+1), we need:
    #     ord(1-q) | gcd(12q, q(q+1)) = q · gcd(12, q+1)
    #     For q ≡ 71 mod 72: q+1 ≡ 0 mod 72, so gcd(12, q+1) = 12.
    #     So ord(1-q) | 12q. Good, consistent.
    #     Also ord(1-q) ∤ 6q. So v_2(ord(1-q)) > v_2(6q) or v_3(ord(1-q)) > v_3(6q)?
    #     No — we need ord(1-q) ∤ 6q meaning 12q / ord(1-q) divides 2 but
    #     hmm this needs more careful analysis.
    # ========================================
    print("=" * 70)
    print("16. Order of (1-q) mod A — unconditional")
    print("=" * 70)

    for q, A in eligible[:20]:
        val_1mq = (1 - q) % A  # = A - q + 1 = q^2 + 1
        # Compute order
        Am1 = A - 1
        # Factor Am1 = q * (q+1)
        # Get all divisors
        from sympy import divisors
        divs_Am1 = divisors(Am1)
        order = Am1
        for d in sorted(divs_Am1):
            if pow(val_1mq, d, A) == 1:
                order = d
                break

        # Also check (1-q)^{6q} and (1-q)^{12q}
        v6q = pow(val_1mq, 6 * q, A)
        v12q = pow(val_1mq, 12 * q, A)

        print(f"    q={q:6d}: ord(1-q) = {order:10d}, "
              f"(1-q)^{{6q}} = {'−1' if v6q == A-1 else v6q}, "
              f"(1-q)^{{12q}} = {v12q}")
    print()

    # ========================================
    # 17. QUADRATIC RESIDUE of (1-q) mod A
    # ========================================
    print("=" * 70)
    print("17. Legendre symbol ((1-q)/A) = ((q²+1)/A)")
    print("    Since 1-q ≡ q²+1 (mod A) [as A = q²+q+1, so -q ≡ q²+1 mod A]")
    print("    Wait: 1-q mod A = A + 1 - q = q² + 2")
    print("=" * 70)

    for q, A in eligible[:15]:
        val_1mq = (1 - q) % A
        ls = legendre_symbol(val_1mq, A)
        print(f"    q={q:6d}: 1-q ≡ {val_1mq} (mod A={A}), ((1-q)/A) = {ls}")
    print()

    # ========================================
    # 18. Can we get a contradiction from COMBINING conditions?
    #     Under assumption:
    #     (a) 3^q ≡ 1 (mod A)
    #     (b) (1-q)^{6q} ≡ -1 (mod A)  [proven]
    #     (c) A ≡ 1 (mod q)  [always true]
    #     Condition (b) means ord(1-q) involves a factor of 2 beyond what 6q has
    # ========================================
    print("=" * 70)
    print("18. COMBINED: Under assumption, (1-q)^{6q} = -1")
    print("    This means 2 | (A-1)/(6q) · (something about the 2-part)")
    print("    A-1 = q(q+1). (A-1)/(6q) = (q+1)/6.")
    print("    For q ≡ 71 mod 72: (q+1)/6 is even (since q+1 ≡ 0 mod 72, (q+1)/6 ≡ 0 mod 12)")
    print("    So (A-1)/(12q) = (q+1)/12 is an integer.")
    print("=" * 70)
    print()

    # Summary of what assumption gives us for the 2-adic structure:
    # ord(3) = q. So 3 generates a cyclic subgroup of order q in (Z/AZ)*.
    # (Z/AZ)* is cyclic of order q(q+1).
    # Let g be a generator. 3 = g^{(q+1)k} for some k with gcd(k, q)=...
    # Actually 3 = g^m where ord(3) = q(q+1)/gcd(m, q(q+1)) = q, so gcd(m, q(q+1)) = q+1.
    # So m = (q+1)·s where gcd(s, q) = 1.

    # Under assumption: (1-q)^{6q} = -1 = g^{q(q+1)/2}
    # Let 1-q = g^t. Then 6qt ≡ q(q+1)/2 (mod q(q+1)).
    # → 6t ≡ (q+1)/2 (mod (q+1)).
    # → t ≡ (q+1)/12 (mod (q+1)/gcd(6, q+1))
    # For q+1 ≡ 0 mod 72: gcd(6, q+1) = 6, so t ≡ (q+1)/12 (mod (q+1)/6)

    print("Final key computation: (q+1)/12 mod (q+1)/6 for eligible q:")
    for q, A in eligible[:10]:
        r1 = (q+1) // 12
        r2 = (q+1) // 6
        print(f"    q={q}: (q+1)/12 = {r1}, (q+1)/6 = {r2}, ratio = 1/2")

    print("\n  So t ≡ (q+1)/12 (mod (q+1)/6), i.e., t = (q+1)/12 + j·(q+1)/6")
    print("  for some integer j. This means 12t/(q+1) ≡ 1 (mod 2).")
    print("  i.e., 12t/(q+1) is odd.")
    print()

    return eligible


if __name__ == "__main__":
    eligible = explore_eligible_primes(20000)
