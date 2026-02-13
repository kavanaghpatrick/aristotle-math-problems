#!/usr/bin/env python3
"""
Explore quartic residue character of (1-q) mod A = q^2+q+1
for primes q ≡ 23 (mod 24), in context of Feit-Thompson p=3 conjecture.

The remaining open case after slot590 (q≡1 mod 4) and slot610 (q≡3 mod 8)
is q ≡ 7 (mod 8), i.e., q ≡ 23 (mod 24).

Key: A = q^2+q+1 ≡ 1 (mod 8) when q ≡ 7 (mod 8), so quartic characters exist.
"""

from sympy import isprime, sqrt_mod, factorint
from collections import defaultdict
import sys

LIMIT = 50000

def classify_quartic(val, A):
    """Classify val in {1, -1, i, -i} mod A."""
    if val == 1:
        return "+1"
    elif val == A - 1:
        return "-1"
    else:
        if pow(val, 2, A) == A - 1:
            return "i_class"
        else:
            return f"OTHER({val})"

def classify_octic(val, A):
    """Classify val as 8th root of unity mod A."""
    if val == 1:
        return "+1"
    elif val == A - 1:
        return "-1"
    v2 = pow(val, 2, A)
    if v2 == 1:
        return "sqrt(1)"
    if v2 == A - 1:
        return "±i (4th root)"
    v4 = pow(v2, 2, A)
    if v4 == A - 1:
        return "±ζ₈ (primitive 8th root)"
    if v4 == 1:
        return "±i (4th root) [v2]"
    return f"OTHER(ord?)"

def main():
    print("=" * 80)
    print("QUARTIC RESIDUE CHARACTER EXPLORATION")
    print("Feit-Thompson p=3, case q ≡ 7 (mod 8)")
    print(f"Primes q < {LIMIT} with q ≡ 23 (mod 24) and A = q^2+q+1 prime")
    print("=" * 80)

    # Collect qualifying primes
    primes_by_class = defaultdict(list)
    all_qs = []

    for q in range(23, LIMIT, 24):
        if not isprime(q):
            continue
        A = q * q + q + 1
        if not isprime(A):
            continue
        cls = q % 72
        primes_by_class[cls].append(q)
        all_qs.append(q)

    print(f"\nFound {len(all_qs)} qualifying primes")
    for cls in sorted(primes_by_class.keys()):
        print(f"  q ≡ {cls} (mod 72): {len(primes_by_class[cls])} primes")
        if len(primes_by_class[cls]) <= 10:
            print(f"    Values: {primes_by_class[cls]}")
        else:
            print(f"    First 10: {primes_by_class[cls][:10]}")

    # =========================================================================
    # SECTION 1: Quartic character of (1-q)
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 1: QUARTIC CHARACTER χ₄(1-q) = (1-q)^{(A-1)/4} mod A")
    print("=" * 80)

    quartic_results = defaultdict(lambda: defaultdict(list))

    for q in all_qs:
        A = q * q + q + 1
        elem = (1 - q) % A
        quartic = pow(elem, (A - 1) // 4, A)
        val_class = classify_quartic(quartic, A)
        cls = q % 72
        quartic_results[cls][val_class].append(q)

    for cls in sorted(quartic_results.keys()):
        cond_val = "-1" if ((cls + 1) // 4) % 12 == 6 else "+1"
        print(f"\n  q ≡ {cls} (mod 72): conditional χ₄ = {cond_val}")
        print(f"    (q+1)/4 mod 12 = {((cls+1)//4) % 12}")
        for val_class, qs in sorted(quartic_results[cls].items()):
            print(f"    Unconditional χ₄ = {val_class}: {len(qs)} primes")
            if len(qs) <= 8:
                print(f"      Values: {qs}")
            else:
                print(f"      First 8: {qs[:8]}")

        # Check for contradiction
        if cond_val == "-1":
            if "+1" in quartic_results[cls] and len(quartic_results[cls]) == 1:
                print(f"    *** CONTRADICTION: unconditional always +1, conditional -1 ***")
            elif "+1" in quartic_results[cls]:
                n_plus = len(quartic_results[cls].get("+1", []))
                n_total = sum(len(v) for v in quartic_results[cls].values())
                print(f"    Note: {n_plus}/{n_total} have unconditional +1 (would contradict assumption)")
        elif cond_val == "+1":
            if "-1" in quartic_results[cls] and len(quartic_results[cls]) == 1:
                print(f"    *** CONTRADICTION: unconditional always -1, conditional +1 ***")
            elif "-1" in quartic_results[cls]:
                n_minus = len(quartic_results[cls].get("-1", []))
                n_total = sum(len(v) for v in quartic_results[cls].values())
                print(f"    Note: {n_minus}/{n_total} have unconditional -1 (would contradict assumption)")

    # =========================================================================
    # SECTION 2: Check which q actually satisfy 3^q ≡ 1 (mod A)
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 2: WHICH q SATISFY 3^q ≡ 1 (mod A)?")
    print("(FT: if p=3, then 3^q ≡ 1 mod A since ord(3|A) | q)")
    print("=" * 80)

    satisfies_assumption = []
    not_satisfies = []
    for q in all_qs:
        A = q * q + q + 1
        if pow(3, q, A) == 1:
            satisfies_assumption.append(q)
        else:
            not_satisfies.append(q)

    print(f"\n  Satisfy 3^q ≡ 1 (mod A): {len(satisfies_assumption)} primes")
    if satisfies_assumption:
        print(f"    Values: {satisfies_assumption[:20]}")
    print(f"  Do NOT satisfy: {len(not_satisfies)} primes")

    # For those satisfying, check conditional vs unconditional
    if satisfies_assumption:
        print("\n  For q satisfying 3^q ≡ 1 (mod A):")
        for q in satisfies_assumption:
            A = q * q + q + 1
            elem = (1 - q) % A
            quartic = pow(elem, (A - 1) // 4, A)
            val_class = classify_quartic(quartic, A)
            cls = q % 72
            cond_val = "-1" if ((cls + 1) // 4) % 12 == 6 else "+1"

            elem_6q = pow(elem, 6 * q, A)
            elem_12q = pow(elem, 12 * q, A)
            print(f"    q={q} (mod72={cls}): unconditional={val_class}, "
                  f"(1-q)^(6q)={elem_6q if elem_6q < A//2 else elem_6q-A}, "
                  f"(1-q)^(12q)={elem_12q if elem_12q < A//2 else elem_12q-A}")

    # =========================================================================
    # SECTION 3: Octic character of (1-q)
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 3: OCTIC CHARACTER χ₈(1-q) = (1-q)^{(A-1)/8} mod A")
    print("=" * 80)

    octic_results = defaultdict(lambda: defaultdict(list))

    for q in all_qs:
        A = q * q + q + 1
        elem = (1 - q) % A
        octic = pow(elem, (A - 1) // 8, A)
        val_class = classify_octic(octic, A)
        cls = q % 72
        octic_results[cls][val_class].append(q)

    for cls in sorted(octic_results.keys()):
        print(f"\n  q ≡ {cls} (mod 72):")
        for val_class, qs in sorted(octic_results[cls].items()):
            print(f"    Octic class = {val_class}: {len(qs)} primes")
            if len(qs) <= 5:
                print(f"      Values: {qs}")

    # =========================================================================
    # SECTION 4: Quartic character of (2q+1)
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 4: QUARTIC CHARACTER χ₄(2q+1) mod A")
    print("(2q+1)^2 = 4q^2+4q+1 = 4(q^2+q+1)-3 = 4A-3 ≡ -3 (mod A)")
    print("=" * 80)

    quartic_2q1 = defaultdict(lambda: defaultdict(list))

    for q in all_qs:
        A = q * q + q + 1
        elem = (2 * q + 1) % A
        quartic = pow(elem, (A - 1) // 4, A)
        val_class = classify_quartic(quartic, A)
        cls = q % 72
        quartic_2q1[cls][val_class].append(q)

    for cls in sorted(quartic_2q1.keys()):
        print(f"\n  q ≡ {cls} (mod 72):")
        for val_class, qs in sorted(quartic_2q1[cls].items()):
            print(f"    χ₄(2q+1) = {val_class}: {len(qs)} primes")
            if len(qs) <= 5:
                print(f"      Values: {qs}")

    # Under assumption: (2q+1)^{2q} = (-3)^q = (-1)^q · 3^q
    # q odd: = -3^q · ... Under 3^q≡1: = -1
    # (2q+1)^{(A-1)/4} = (2q+1)^{q(q+1)/4}
    # q+1 ≡ 0 mod 8 (since q≡7 mod 8), so (q+1)/8 is integer
    # = ((2q+1)^{2q})^{(q+1)/8} = (-1)^{(q+1)/8}
    print("\n  Under assumption 3^q ≡ 1: (2q+1)^{2q} ≡ -1 mod A")
    print("  (A-1)/4 = q(q+1)/4. Since q+1≡0 mod 8: = 2q · (q+1)/8")
    print("  (2q+1)^{(A-1)/4} = ((2q+1)^{2q})^{(q+1)/8} = (-1)^{(q+1)/8}")

    for cls in sorted(quartic_2q1.keys()):
        exp_val = ((cls + 1) // 8) % 2
        cond = "-1" if exp_val == 1 else "+1"
        print(f"\n  q ≡ {cls} (mod 72): (q+1)/8 mod 2 = {exp_val}, conditional χ₄(2q+1) = {cond}")
        for val_class, qs in sorted(quartic_2q1[cls].items()):
            n = len(qs)
            match_str = "MATCH" if val_class == cond else "DIFFERS"
            print(f"    Unconditional = {val_class}: {n} primes [{match_str}]")

    # =========================================================================
    # SECTION 5: w = (1-q)^q mod A, and w^2
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 5: w = (1-q)^q mod A")
    print("=" * 80)

    for q in all_qs[:20]:
        A = q * q + q + 1
        elem = (1 - q) % A
        w = pow(elem, q, A)
        w2 = pow(elem, 2 * q, A)
        w3 = pow(elem, 3 * q, A)
        assert (w * w) % A == w2

        v_qp1 = pow(elem, q + 1, A)
        cls = q % 72
        print(f"  q={q:5d} (mod72={cls}): w^2={(w2 if w2 <= A//2 else w2-A):>15d}, "
              f"(1-q)^(q+1)={(v_qp1 if v_qp1 <= A//2 else v_qp1-A):>15d}")

    # =========================================================================
    # SECTION 6: Quartic character of 3
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 6: χ₄(3) = 3^{(A-1)/4} mod A")
    print("Under 3^q ≡ 1: χ₄(3) = (3^q)^{(q+1)/4} = 1")
    print("=" * 80)

    quartic_3 = defaultdict(lambda: defaultdict(list))

    for q in all_qs:
        A = q * q + q + 1
        quartic = pow(3, (A - 1) // 4, A)
        val_class = classify_quartic(quartic, A)
        cls = q % 72
        quartic_3[cls][val_class].append(q)

    for cls in sorted(quartic_3.keys()):
        print(f"\n  q ≡ {cls} (mod 72): χ₄(3) mod A")
        for val_class, qs in sorted(quartic_3[cls].items()):
            print(f"    χ₄(3) = {val_class}: {len(qs)} primes")
            if len(qs) <= 5:
                print(f"      Values: {qs}")

    print("\n  Under assumption 3^q ≡ 1: χ₄(3) = 1 always")
    print("  Any q with χ₄(3) ≠ 1 definitely does NOT satisfy 3^q ≡ 1")

    for cls in sorted(quartic_3.keys()):
        non_one = {k: v for k, v in quartic_3[cls].items() if k != "+1"}
        if non_one:
            n_non1 = sum(len(v) for v in non_one.values())
            n_total = sum(len(v) for v in quartic_3[cls].values())
            print(f"  q ≡ {cls} (mod 72): {n_non1}/{n_total} have χ₄(3) ≠ 1 → 3^q ≢ 1")

    # =========================================================================
    # SECTION 7: ord(3) mod A for small q
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 7: ord(3) modulo A for small q")
    print("=" * 80)

    for q in all_qs[:30]:
        A = q * q + q + 1
        n = A - 1
        factors = factorint(n)
        order = n
        for p_factor in factors:
            while order % p_factor == 0 and pow(3, order // p_factor, A) == 1:
                order //= p_factor
        cls = q % 72
        three_q = pow(3, q, A)
        is_one = "YES" if three_q == 1 else "no"
        divides_q = "YES" if q % order == 0 else "no"
        print(f"  q={q:5d} (mod72={cls}): ord(3)={order:>12d}, "
              f"A-1={n:>12d}, ord|q? {divides_q:>3s}, "
              f"3^q≡1? {is_one}")

    # =========================================================================
    # SECTION 8: Joint analysis — q with 3^q≡1, classify χ₄(1-q)
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 8: JOINT — Among q with 3^q ≡ 1 (mod A), classify χ₄(1-q)")
    print("=" * 80)

    joint = defaultdict(lambda: defaultdict(list))
    for q in satisfies_assumption:
        A = q * q + q + 1
        elem = (1 - q) % A
        quartic = pow(elem, (A - 1) // 4, A)
        val_class = classify_quartic(quartic, A)
        cls = q % 72
        joint[cls][val_class].append(q)

    if not satisfies_assumption:
        print("  No q in range satisfies 3^q ≡ 1 (mod A)!")
    else:
        for cls in sorted(joint.keys()):
            cond_val = "-1" if ((cls + 1) // 4) % 12 == 6 else "+1"
            print(f"\n  q ≡ {cls} (mod 72): conditional χ₄(1-q) = {cond_val}")
            for val_class, qs in sorted(joint[cls].items()):
                match = "MATCHES" if val_class == cond_val else "CONTRADICTS!"
                print(f"    Actual χ₄(1-q) = {val_class}: {len(qs)} primes [{match}]")
                print(f"      Values: {qs[:10]}")

    # =========================================================================
    # SECTION 9: Algebraic structure
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 9: ALGEBRAIC STRUCTURE")
    print("(1-q)^2 = 1 - 2q + q^2 ≡ 1 - 2q + (-q-1) = -3q (mod A)")
    print("Under 3^q ≡ 1: (1-q)^{2q} = (-3q)^q = (-3)^q·q^q = -q^q")
    print("q^q = q^{q mod 3} = q^2 ≡ -q-1 (mod A)")
    print("So w^2 = (1-q)^{2q} ≡ -(-q-1) = q+1 (mod A)")
    print("=" * 80)

    print("\n  Verification of (1-q)^2 ≡ -3q and w^2 ≡ -q^q:")
    for q in all_qs[:15]:
        A = q * q + q + 1
        elem = (1 - q) % A
        elem_sq = pow(elem, 2, A)
        neg3q = (-3 * q) % A
        assert elem_sq == neg3q, f"Failed for q={q}: {elem_sq} vs {neg3q}"

        w_sq = pow(elem, 2 * q, A)
        three_q = pow(3, q, A)
        expected = ((-1) * three_q * pow(q, q, A)) % A  # q odd
        assert w_sq == expected, f"Failed for q={q}"

        qp1 = (q + 1) % A
        cond_match = "YES" if w_sq == qp1 else "no"
        print(f"  q={q:5d}: (1-q)^2≡-3q ✓, w^2=(-3)^q·q^q ✓, "
              f"w^2≡q+1? {cond_match} (3^q≡{three_q})")

    # =========================================================================
    # SECTION 10: Quartic character of q
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 10: χ₄(q) = q^{(A-1)/4} mod A")
    print("q^3 ≡ 1 (mod A) since A | q^3 - 1")
    print("=" * 80)

    quartic_q = defaultdict(lambda: defaultdict(list))
    for q in all_qs:
        A = q * q + q + 1
        quartic = pow(q, (A - 1) // 4, A)
        val_class = classify_quartic(quartic, A)
        cls = q % 72
        quartic_q[cls][val_class].append(q)

    for cls in sorted(quartic_q.keys()):
        print(f"\n  q ≡ {cls} (mod 72):")
        for val_class, qs in sorted(quartic_q[cls].items()):
            print(f"    χ₄(q) = {val_class}: {len(qs)} primes")
            if len(qs) <= 5:
                print(f"      Values: {qs}")

    # q^3 ≡ 1, q(q+1)/4 mod 3:
    # q ≡ 2 mod 3, q+1 ≡ 0 mod 3, so q(q+1) ≡ 0 mod 3
    # q ≡ 7 mod 8, q+1 ≡ 0 mod 8, q(q+1) ≡ 0 mod 8, so q(q+1)/4 ≡ 0 mod 2
    # and q(q+1) ≡ 0 mod 12, so q(q+1)/4 ≡ 0 mod 3
    print("\n  Since q≡2 mod 3: q(q+1)/4 ≡ 0 mod 3 → χ₄(q) = q^0 = 1 always")

    # =========================================================================
    # SECTION 11: The ±i exclusion argument
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 11: RULING OUT χ₄(1-q) = ±i UNDER ASSUMPTION")
    print("=" * 80)

    print("""
  A ≡ 1 mod 8, so χ₄(-1) = (-1)^{(A-1)/4} = 1  [since (A-1)/4 is even]

  q^q = q^2 (since q≡2 mod 3), χ₄(q^2) = χ₄(q)^2 = 1
  So χ₄(-q^q) = χ₄(-1)·χ₄(q^q) = 1·1 = 1

  Under assumption: w^2 = -q^q, so χ₄(w^2) = 1
  χ₄(w^2) = χ₄(w)^2 = 1 → χ₄(w) ∈ {+1, -1}

  w = (1-q)^q → χ₄(w) = χ₄(1-q)^q
  q ≡ 3 mod 4:
    χ₄(1-q)=+1 → χ₄(w)=+1
    χ₄(1-q)=-1 → χ₄(w)=-1
    χ₄(1-q)=+i → χ₄(w)=i^q=i^3=-i  [NOT in {±1}!]
    χ₄(1-q)=-i → χ₄(w)=(-i)^q=(-i)^3=i  [NOT in {±1}!]

  CONCLUSION: Under 3^q ≡ 1, χ₄(1-q) ∈ {+1, -1} only.
  Therefore χ₄(1-q)^2 = 1, i.e., χ₄(q+1) = 1 under assumption.
""")

    # Verify for q with 3^q≡1
    for q in satisfies_assumption:
        A = q * q + q + 1
        elem = (1 - q) % A
        quartic = pow(elem, (A - 1) // 4, A)
        vc = classify_quartic(quartic, A)
        if "i" in vc.lower():
            print(f"  *** q={q}: χ₄(1-q) = {vc} — SHOULD NOT HAPPEN ***")
    if satisfies_assumption:
        print("  Verified: no ±i cases among q with 3^q ≡ 1")
    else:
        print("  (No q with 3^q ≡ 1 in range to verify)")

    # =========================================================================
    # SECTION 12: Quartic character of (q+1) — the key unconditional test
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 12: χ₄(q+1) = (q+1)^{(A-1)/4} mod A")
    print("Under assumption: χ₄(q+1) = 1")
    print("If unconditionally χ₄(q+1) ≠ 1 for some class → contradiction!")
    print("=" * 80)

    quartic_qp1 = defaultdict(lambda: defaultdict(list))
    for q in all_qs:
        A = q * q + q + 1
        quartic = pow(q + 1, (A - 1) // 4, A)
        val_class = classify_quartic(quartic, A)
        cls = q % 72
        quartic_qp1[cls][val_class].append(q)

    for cls in sorted(quartic_qp1.keys()):
        print(f"\n  q ≡ {cls} (mod 72):")
        for val_class, qs in sorted(quartic_qp1[cls].items()):
            print(f"    χ₄(q+1) = {val_class}: {len(qs)} primes")
            if len(qs) <= 8:
                print(f"      Values: {qs}")
            else:
                print(f"      First 8: {qs[:8]}")

    print("\n  CONTRADICTION CHECK:")
    for cls in sorted(quartic_qp1.keys()):
        total = sum(len(v) for v in quartic_qp1[cls].values())
        n_one = len(quartic_qp1[cls].get("+1", []))
        n_not_one = total - n_one
        if n_not_one > 0:
            pct = 100 * n_not_one / total
            print(f"  q ≡ {cls} (mod 72): {n_not_one}/{total} ({pct:.1f}%) have χ₄(q+1) ≠ 1")
            print(f"    → Those q CANNOT satisfy 3^q ≡ 1 (mod A)")
            print(f"    But {n_one}/{total} ({100*n_one/total:.1f}%) have χ₄(q+1) = 1 (compatible)")
        else:
            print(f"  q ≡ {cls} (mod 72): ALL {total} have χ₄(q+1) = 1 (no contradiction from χ₄)")

    # =========================================================================
    # SECTION 13: Legendre symbol (q+1 | A)
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 13: LEGENDRE SYMBOL (q+1 | A)")
    print("Under assumption: (q+1|A) = 1")
    print("=" * 80)

    legendre_qp1 = defaultdict(lambda: defaultdict(list))
    for q in all_qs:
        A = q * q + q + 1
        legendre = pow(q + 1, (A - 1) // 2, A)
        if legendre == 1:
            val_class = "+1"
        elif legendre == A - 1:
            val_class = "-1"
        else:
            val_class = f"OTHER({legendre})"
        cls = q % 72
        legendre_qp1[cls][val_class].append(q)

    for cls in sorted(legendre_qp1.keys()):
        print(f"\n  q ≡ {cls} (mod 72):")
        for val_class, qs in sorted(legendre_qp1[cls].items()):
            print(f"    (q+1|A) = {val_class}: {len(qs)} primes")

    for cls in sorted(legendre_qp1.keys()):
        n_minus = len(legendre_qp1[cls].get("-1", []))
        total = sum(len(v) for v in legendre_qp1[cls].values())
        if n_minus > 0:
            print(f"  q ≡ {cls} (mod 72): {n_minus}/{total} have (q+1|A) = -1 → CANNOT have 3^q≡1")

    # =========================================================================
    # SECTION 14: DEEPER — other elements and higher characters
    # =========================================================================
    print("\n" + "=" * 80)
    print("SECTION 14: ADDITIONAL ELEMENTS")
    print("=" * 80)

    # χ₄(q+1) doesn't give universal contradiction. Try other derived quantities.
    # Under assumption: w^2 = q+1, w = (1-q)^q
    # Also: (1-q)^{q+1} = (1-q)·w
    # And χ₄(1-q) = w^{(q+1)/4}

    # What about χ₄(-3)?
    print("\n  χ₄(-3) = (-3)^{(A-1)/4} mod A:")
    quartic_neg3 = defaultdict(lambda: defaultdict(list))
    for q in all_qs:
        A = q * q + q + 1
        quartic = pow(-3 % A, (A - 1) // 4, A)
        val_class = classify_quartic(quartic, A)
        cls = q % 72
        quartic_neg3[cls][val_class].append(q)

    for cls in sorted(quartic_neg3.keys()):
        print(f"  q ≡ {cls} (mod 72):")
        for val_class, qs in sorted(quartic_neg3[cls].items()):
            print(f"    χ₄(-3) = {val_class}: {len(qs)} primes")

    # Under assumption: (-3)^q = (1-q)^{2q}/q^q. Hmm...
    # (-3)^{(A-1)/4} = (-3)^{q(q+1)/4} = ((-3)^q)^{(q+1)/4}
    # Under assumption 3^q≡1: (-3)^q = (-1)^q·3^q = -1
    # So χ₄(-3) = (-1)^{(q+1)/4}
    print("\n  Under assumption: (-3)^q = -1, so χ₄(-3) = (-1)^{(q+1)/4}")
    for cls in [23, 47, 71]:
        exp = ((cls + 1) // 4) % 2
        cond = "-1" if exp == 1 else "+1"
        print(f"  q ≡ {cls} (mod 72): (q+1)/4 mod 2 = {exp}, conditional χ₄(-3) = {cond}")
        unc_vals = quartic_neg3[cls]
        for val_class, qs in sorted(unc_vals.items()):
            match_str = "MATCH" if val_class == cond else "DIFFERS"
            print(f"    Unconditional = {val_class}: {len(qs)} [{match_str}]")

    # =========================================================================
    # SECTION 15: COMPREHENSIVE SUMMARY
    # =========================================================================
    print("\n" + "=" * 80)
    print("COMPREHENSIVE SUMMARY")
    print("=" * 80)

    print("""
KEY ALGEBRAIC RESULTS (under assumption 3^q ≡ 1 mod A, q ≡ 23 mod 24):

  1. (1-q)^2 ≡ -3q (mod A)                 [algebraic identity]
  2. w := (1-q)^q satisfies w^2 ≡ q+1       [since (-3)^q·q^q = -q^2 = q+1]
  3. χ₄(1-q) ∈ {+1, -1} only                [±i ruled out via w^2 argument]
  4. χ₄(q+1) = χ₄(1-q)^2 = 1               [necessary condition on q+1]
  5. χ₄(q) = 1 always                       [q is cube root of 1 mod A]
  6. χ₄(-1) = 1                             [A ≡ 1 mod 8]
  7. χ₄(3) = 1                              [follows from 3^q ≡ 1]
  8. χ₄(-3) = (-1)^{(q+1)/4}               [follows from (-3)^q = -1]
  9. χ₄(2q+1) = (-1)^{(q+1)/8}             [follows from (2q+1)^{2q} = -1]

UNCONDITIONAL OBSERVATIONS:
""")

    # Count how many q have ALL conditions compatible
    print("  Testing: for how many q are ALL necessary conditions satisfied?")
    all_compatible = 0
    some_incompatible = 0
    for q in all_qs:
        A = q * q + q + 1
        cls = q % 72

        # Check χ₄(q+1) = 1
        c1 = pow(q + 1, (A - 1) // 4, A) == 1

        # Check χ₄(3) = 1
        c2 = pow(3, (A - 1) // 4, A) == 1

        # Check χ₄(-3) = (-1)^{(q+1)/4}
        chi4_neg3 = pow((-3) % A, (A - 1) // 4, A)
        exp = ((q + 1) // 4) % 2
        expected_neg3 = 1 if exp == 0 else A - 1
        c3 = chi4_neg3 == expected_neg3

        # Check χ₄(2q+1) = (-1)^{(q+1)/8}
        chi4_2q1 = pow((2*q+1) % A, (A - 1) // 4, A)
        exp8 = ((q + 1) // 8) % 2
        expected_2q1 = 1 if exp8 == 0 else A - 1
        c4 = chi4_2q1 == expected_2q1

        if c1 and c2 and c3 and c4:
            all_compatible += 1
        else:
            some_incompatible += 1
            reasons = []
            if not c1: reasons.append("χ₄(q+1)≠1")
            if not c2: reasons.append("χ₄(3)≠1")
            if not c3: reasons.append("χ₄(-3) wrong")
            if not c4: reasons.append("χ₄(2q+1) wrong")

    total = len(all_qs)
    print(f"  All conditions compatible: {all_compatible}/{total} ({100*all_compatible/total:.1f}%)")
    print(f"  Some condition violated: {some_incompatible}/{total} ({100*some_incompatible/total:.1f}%)")

    # For incompatible ones: breakdown of which condition fails
    print("\n  Breakdown of failures:")
    failure_counts = defaultdict(int)
    for q in all_qs:
        A = q * q + q + 1
        fails = []
        if pow(q + 1, (A - 1) // 4, A) != 1:
            fails.append("χ₄(q+1)")
        if pow(3, (A - 1) // 4, A) != 1:
            fails.append("χ₄(3)")
        chi4_neg3 = pow((-3) % A, (A - 1) // 4, A)
        exp = ((q + 1) // 4) % 2
        expected_neg3 = 1 if exp == 0 else A - 1
        if chi4_neg3 != expected_neg3:
            fails.append("χ₄(-3)")
        chi4_2q1 = pow((2*q+1) % A, (A - 1) // 4, A)
        exp8 = ((q + 1) // 8) % 2
        expected_2q1 = 1 if exp8 == 0 else A - 1
        if chi4_2q1 != expected_2q1:
            fails.append("χ₄(2q+1)")
        if fails:
            key = ", ".join(fails)
            failure_counts[key] += 1

    for key, count in sorted(failure_counts.items(), key=lambda x: -x[1]):
        print(f"    {key}: {count}")

    # Final: among the "all compatible" ones, do any actually have 3^q ≡ 1?
    print(f"\n  Among {all_compatible} compatible q: how many have 3^q ≡ 1?")
    compatible_and_satisfied = 0
    for q in all_qs:
        A = q * q + q + 1
        c1 = pow(q + 1, (A - 1) // 4, A) == 1
        c2 = pow(3, (A - 1) // 4, A) == 1
        chi4_neg3 = pow((-3) % A, (A - 1) // 4, A)
        exp = ((q + 1) // 4) % 2
        expected_neg3 = 1 if exp == 0 else A - 1
        c3 = chi4_neg3 == expected_neg3
        chi4_2q1 = pow((2*q+1) % A, (A - 1) // 4, A)
        exp8 = ((q + 1) // 8) % 2
        expected_2q1 = 1 if exp8 == 0 else A - 1
        c4 = chi4_2q1 == expected_2q1
        if c1 and c2 and c3 and c4:
            if pow(3, q, A) == 1:
                compatible_and_satisfied += 1
                print(f"    q={q}: ALL compatible AND 3^q ≡ 1!")
    if compatible_and_satisfied == 0:
        print("    NONE — quartic conditions alone rule out 3^q ≡ 1 in practice!")
        print("    (But we need a PROOF, not just empirical observation)")

    print("\nDone.")

if __name__ == "__main__":
    main()
