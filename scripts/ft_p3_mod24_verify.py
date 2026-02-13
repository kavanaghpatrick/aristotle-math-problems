#!/usr/bin/env python3
"""
Verify the Feit-Thompson p=3 contradiction argument for q ≡ 11 (mod 24).

For primes q > 3 with q ≡ 2 (mod 3), let A = q² + q + 1.
FT conjecture: 3^q ≢ 1 (mod A).

The argument derives a contradiction for q ≡ 11 (mod 24) by showing:
  - Conditionally (assuming 3^q ≡ 1): (1-q)^{(A-1)/2} ≡ -1 (mod A)
  - Unconditionally (quadratic reciprocity): Legendre(1-q, A) = +1
  - Euler criterion: these must agree → contradiction.

This script verifies every step computationally.
"""

from sympy import isprime, nextprime, legendre_symbol, jacobi_symbol
import sys

def verify_all(limit=10000):
    print("=" * 72)
    print(f"Feit-Thompson p=3, q ≡ 11 (mod 24) verification (q < {limit})")
    print("=" * 72)

    # Collect primes q > 3 with q ≡ 2 (mod 3) and A = q²+q+1 prime
    candidates = []
    q = 5
    while q < limit:
        if q % 3 == 2:
            A = q * q + q + 1
            if isprime(A):
                candidates.append((q, A))
        q = nextprime(q)

    print(f"\nFound {len(candidates)} primes q < {limit} with q ≡ 2 (mod 3) and A prime.\n")

    # Categorize
    cat_1mod4 = []    # q ≡ 1 (mod 4) — covered by slot590
    cat_11mod24 = []  # q ≡ 11 (mod 24) — new contradiction
    cat_23mod24 = []  # q ≡ 23 (mod 24) — still open

    for q, A in candidates:
        if q % 4 == 1:
            cat_1mod4.append((q, A))
        elif q % 24 == 11:
            cat_11mod24.append((q, A))
        elif q % 24 == 23:
            cat_23mod24.append((q, A))
        else:
            print(f"  BUG: q={q}, q%24={q%24} doesn't fit categories!")
            sys.exit(1)

    print(f"Category counts:")
    print(f"  q ≡ 1 (mod 4) [slot590]:    {len(cat_1mod4)}")
    print(f"  q ≡ 11 (mod 24) [new]:       {len(cat_11mod24)}")
    print(f"  q ≡ 23 (mod 24) [open]:      {len(cat_23mod24)}")
    total = len(candidates)
    print(f"  Total:                        {total}")
    print(f"\nPercentages:")
    print(f"  q ≡ 1 (mod 4):    {100*len(cat_1mod4)/total:.1f}%")
    print(f"  q ≡ 11 (mod 24):  {100*len(cat_11mod24)/total:.1f}%")
    print(f"  q ≡ 23 (mod 24):  {100*len(cat_23mod24)/total:.1f}%")
    print(f"  Covered (1mod4 + 11mod24): {100*(len(cat_1mod4)+len(cat_11mod24))/total:.1f}%")

    # ================================================================
    # TEST 1: Verify 3^q mod A ≠ 1 for ALL candidates (conjecture check)
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 1: Verify 3^q ≢ 1 (mod A) for all candidates")
    print("-" * 72)
    fail_count = 0
    for q, A in candidates:
        val = pow(3, q, A)
        if val == 1:
            print(f"  COUNTEREXAMPLE TO FT: q={q}, A={A}, 3^q ≡ 1 (mod A)")
            fail_count += 1
    if fail_count == 0:
        print(f"  PASS: 3^q ≢ 1 (mod A) for all {len(candidates)} candidates.")
    else:
        print(f"  FAIL: {fail_count} counterexamples found!")

    # ================================================================
    # TEST 2: Algebraic identity (1-q)² ≡ -3q (mod A) for all candidates
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 2: Verify (1-q)² ≡ -3q (mod A)")
    print("-" * 72)
    fail_count = 0
    for q, A in candidates:
        lhs = pow(1 - q, 2, A)
        rhs = (-3 * q) % A
        if lhs != rhs:
            print(f"  FAIL: q={q}, (1-q)²={lhs}, -3q={rhs} (mod A={A})")
            fail_count += 1
    if fail_count == 0:
        print(f"  PASS: Identity holds for all {len(candidates)} candidates.")
    else:
        print(f"  FAIL: {fail_count} failures!")

    # ================================================================
    # TEST 3: q³ ≡ 1 (mod A) for all candidates
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 3: Verify q³ ≡ 1 (mod A)")
    print("-" * 72)
    fail_count = 0
    for q, A in candidates:
        if pow(q, 3, A) != 1:
            print(f"  FAIL: q={q}, A={A}")
            fail_count += 1
    if fail_count == 0:
        print(f"  PASS: q³ ≡ 1 (mod A) for all {len(candidates)} candidates.")

    # ================================================================
    # TEST 4: For q ≡ 11 (mod 24), verify unconditional Legendre(1-q, A) = +1
    # THIS IS THE KEY TEST
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 4 [KEY]: Unconditional Legendre(1-q, A) for q ≡ 11 (mod 24)")
    print("-" * 72)
    fail_count = 0
    for q, A in cat_11mod24:
        euler_val = pow(1 - q, (A - 1) // 2, A)
        if euler_val == A - 1:
            leg = -1
        elif euler_val == 1:
            leg = 1
        else:
            leg = None

        leg_sympy = legendre_symbol((1 - q) % A, A)

        if leg != 1 or leg_sympy != 1:
            print(f"  *** COUNTEREXAMPLE: q={q}, A={A}, "
                  f"Euler={-1 if euler_val == A-1 else euler_val}, "
                  f"sympy={leg_sympy}")
            fail_count += 1

    if fail_count == 0:
        print(f"  PASS: Legendre(1-q, A) = +1 for all {len(cat_11mod24)} primes "
              f"with q ≡ 11 (mod 24).")
    else:
        print(f"  *** FAIL: {fail_count} counterexamples! Proof has a gap! ***")

    # ================================================================
    # TEST 5: Verify the QR chain step by step for q ≡ 11 (mod 24)
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 5: Step-by-step QR verification for q ≡ 11 (mod 24)")
    print("-" * 72)
    fail_count = 0
    for q, A in cat_11mod24:
        m = (q - 1) // 2

        assert q % 24 == 11
        assert A % 4 == 1, f"A={A} not ≡ 1 mod 4"

        # Step 1: (-1/A) = 1 since A ≡ 1 (mod 4)
        neg1_leg = legendre_symbol(A - 1, A)
        if neg1_leg != 1:
            print(f"  FAIL step1: q={q}, (-1/A)={neg1_leg}")
            fail_count += 1
            continue

        # Step 2: (1-q/A) = (q-1/A) since (-1/A) = 1
        leg_1mq = legendre_symbol((1 - q) % A, A)
        leg_qm1 = legendre_symbol((q - 1) % A, A)
        if leg_1mq != leg_qm1:
            print(f"  FAIL step2: q={q}, (1-q/A)={leg_1mq}, (q-1/A)={leg_qm1}")
            fail_count += 1
            continue

        # Step 3: v₂(q-1) = 1
        assert (q - 1) % 2 == 0
        assert (q - 1) % 4 != 0, f"v₂(q-1) > 1 for q={q}"

        # Step 4: (q-1/A) = (2/A)·(m/A)
        leg_2 = legendre_symbol(2, A)
        leg_m = legendre_symbol(m % A, A)
        if leg_qm1 != leg_2 * leg_m:
            print(f"  FAIL step4: q={q}, (q-1/A)={leg_qm1}, (2/A)={leg_2}, (m/A)={leg_m}")
            fail_count += 1
            continue

        # Step 5: A ≡ 5 (mod 8) → (2/A) = -1
        assert A % 8 == 5, f"A={A} ≡ {A%8} (mod 8), expected 5"
        assert leg_2 == -1, f"(2/A)={leg_2}, expected -1"

        # Step 6: A mod m = 3
        A_mod_m = A % m
        if A_mod_m != 3:
            print(f"  FAIL step6a: q={q}, A mod m = {A_mod_m}, expected 3")
            fail_count += 1
            continue

        # Jacobi symbols
        jac_m_A = jacobi_symbol(m % A, A)
        jac_A_m = jacobi_symbol(A % m, m)
        jac_3_m = jacobi_symbol(3, m)

        if jac_A_m != jac_3_m:
            print(f"  FAIL step6b: q={q}, Jacobi(A%m,m)={jac_A_m}, Jacobi(3,m)={jac_3_m}")
            fail_count += 1
            continue

        # QR: (m/A)·(A/m) = (-1)^{((m-1)/2)·((A-1)/2)}
        sign_exp = ((m - 1) // 2) * ((A - 1) // 2)
        qr_sign = (-1) ** (sign_exp % 2)

        if jac_m_A * jac_A_m != qr_sign:
            print(f"  FAIL step6c QR: q={q}")
            fail_count += 1
            continue

        predicted_m_A = qr_sign * jac_3_m
        if jac_m_A != predicted_m_A:
            print(f"  FAIL step6d: q={q}, (m/A)={jac_m_A}, predicted={predicted_m_A}")
            fail_count += 1
            continue

        # Step 7: m ≡ 5 (mod 12) → Jacobi(3,m) = -1
        assert m % 12 == 5, f"m={m}, m%12={m%12}"
        if jac_3_m != -1:
            print(f"  FAIL step7: q={q}, Jacobi(3,m)={jac_3_m}")
            fail_count += 1
            continue

        # Step 8: qr_sign = +1 (since (m-1)/2 is even)
        assert (m - 1) // 2 % 2 == 0
        if qr_sign != 1:
            print(f"  FAIL step8: q={q}, qr_sign={qr_sign}")
            fail_count += 1
            continue

        # Final: (1-q/A) = (-1)·(1·(-1)) = +1
        final = leg_2 * predicted_m_A
        if final != 1:
            print(f"  FAIL final: q={q}, result={final}")
            fail_count += 1

    if fail_count == 0:
        print(f"  PASS: All {len(cat_11mod24)} QR chains verified step by step.")
    else:
        print(f"  FAIL: {fail_count} failures in QR chain!")

    # ================================================================
    # TEST 6: For q ≡ 23 (mod 24), verify Legendre(1-q, A)
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 6: Legendre(1-q, A) for q ≡ 23 (mod 24)")
    print("-" * 72)
    plus1_count = 0
    minus1_count = 0
    minus1_examples = []
    for q, A in cat_23mod24:
        leg = legendre_symbol((1 - q) % A, A)
        if leg == 1:
            plus1_count += 1
        else:
            minus1_count += 1
            minus1_examples.append((q, A))

    print(f"  Legendre = +1: {plus1_count}")
    print(f"  Legendre = -1: {minus1_count}")
    if minus1_count == 0:
        print(f"  All +1 → consistent with conditional +1 (no contradiction for q ≡ 23).")
    else:
        print(f"\n  Some unconditional = -1 found!")
        print(f"  Conditional for q ≡ 23 (mod 24): (q+1)/2 ≡ 0 (mod 12)")
        print(f"    → (1-q)^{{q(q+1)/2}} = ((1-q)^{{12q}})^k = 1")
        print(f"  So conditional = +1, unconditional = -1 → CONTRADICTION for these too!")
        for q, A in minus1_examples[:10]:
            print(f"    q = {q}, A = {A}")

    # ================================================================
    # TEST 7: Specific case q = 59
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 7: Specific verification for q = 59")
    print("-" * 72)
    q = 59
    A = q * q + q + 1
    print(f"  q = {q}, A = {A}, A prime = {isprime(A)}")
    print(f"  q mod 24 = {q % 24}")
    print(f"  3^q mod A = {pow(3, q, A)} (expect != 1)")
    print(f"  (1-q)^2 mod A = {pow(1-q, 2, A)}")
    print(f"  -3q mod A = {(-3*q) % A}")
    leg = legendre_symbol((1 - q) % A, A)
    euler = pow(1 - q, (A - 1) // 2, A)
    euler_display = -1 if euler == A - 1 else (1 if euler == 1 else euler)
    print(f"  Legendre(1-q, A) = {leg}")
    print(f"  (1-q)^{{(A-1)/2}} mod A = {euler_display}")

    # ================================================================
    # TEST 8: Verify conditional chain algebraic steps
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 8: Verify conditional chain steps (algebraic)")
    print("-" * 72)
    fail_count = 0
    for q, A in cat_11mod24:
        # (1-q)^{2q} = ((1-q)^2)^q = (-3q)^q mod A
        lhs = pow(1 - q, 2 * q, A)
        rhs = pow(-3 * q, q, A)
        if lhs != rhs:
            print(f"  FAIL: q={q}, (1-q)^{{2q}} != (-3q)^q")
            fail_count += 1
            continue

        # (-3q)^q = (-1)^q * 3^q * q^q  and q^q = q^2 (since q^3=1, q%3=2)
        neg1_q = pow(-1, q, A)
        three_q = pow(3, q, A)
        q_q = pow(q, q, A)
        expected_qq = pow(q, 2, A)
        if q_q != expected_qq:
            print(f"  FAIL: q={q}, q^q != q^2")
            fail_count += 1
            continue

        product = (neg1_q * three_q * q_q) % A
        if rhs != product:
            print(f"  FAIL: q={q}, (-3q)^q != product")
            fail_count += 1
            continue

        # Under hypothesis 3^q=1: value = -q^2 = q+1 mod A
        hypothetical = ((-1) * 1 * pow(q, 2, A)) % A
        expected = (q + 1) % A
        if hypothetical != expected:
            print(f"  FAIL: q={q}, hypothetical != q+1")
            fail_count += 1
            continue

        # (q+1)^2 = q mod A
        if pow(q + 1, 2, A) != q % A:
            print(f"  FAIL: q={q}, (q+1)^2 != q")
            fail_count += 1
            continue

        # q*(q+1) = -1 mod A
        if (q * (q + 1)) % A != A - 1:
            print(f"  FAIL: q={q}, q*(q+1) != -1")
            fail_count += 1

    if fail_count == 0:
        print(f"  PASS: All {len(cat_11mod24)} algebraic chain steps verified.")
    else:
        print(f"  FAIL: {fail_count} failures!")

    # ================================================================
    # TEST 9: Exponent arithmetic
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 9: Exponent arithmetic for (A-1)/2 = q(q+1)/2")
    print("-" * 72)
    fail_9 = 0
    for q, A in cat_11mod24:
        half = (q + 1) // 2
        if (A - 1) // 2 != q * half:
            print(f"  FAIL: q={q}")
            fail_9 += 1
        if half % 12 != 6:
            print(f"  FAIL: q={q}, (q+1)/2 mod 12 = {half % 12}")
            fail_9 += 1
    if fail_9 == 0:
        print(f"  PASS: (q+1)/2 ≡ 6 (mod 12) for all {len(cat_11mod24)} with q ≡ 11 (mod 24).")

    fail_9b = 0
    for q, A in cat_23mod24:
        half = (q + 1) // 2
        if (A - 1) // 2 != q * half:
            print(f"  FAIL: q={q}")
            fail_9b += 1
        if half % 12 != 0:
            print(f"  FAIL: q={q}, (q+1)/2 mod 12 = {half % 12}")
            fail_9b += 1
    if fail_9b == 0:
        print(f"  PASS: (q+1)/2 ≡ 0 (mod 12) for all {len(cat_23mod24)} with q ≡ 23 (mod 24).")

    # ================================================================
    # TEST 10: A mod 8 verification
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 10: A mod 8 for each category")
    print("-" * 72)
    # q ≡ 11 (mod 24): q^2 ≡ 121 ≡ 1 (mod 8), q ≡ 3 (mod 8), A = q^2+q+1 ≡ 1+3+1 = 5 (mod 8)
    fail_10 = 0
    for q, A in cat_11mod24:
        if A % 8 != 5:
            print(f"  FAIL: q={q} (11mod24): A%8={A%8}")
            fail_10 += 1
    if fail_10 == 0:
        print(f"  q ≡ 11 (mod 24): A ≡ 5 (mod 8) for all {len(cat_11mod24)} — PASS")

    # q ≡ 23 (mod 24): q^2 ≡ 529 ≡ 1 (mod 8), q ≡ 7 (mod 8), A ≡ 1+7+1 = 1 (mod 8)
    fail_10b = 0
    for q, A in cat_23mod24:
        if A % 8 != 1:
            print(f"  FAIL: q={q} (23mod24): A%8={A%8}")
            fail_10b += 1
    if fail_10b == 0:
        print(f"  q ≡ 23 (mod 24): A ≡ 1 (mod 8) for all {len(cat_23mod24)} — PASS")
        print(f"    (Note: (2/A) = +1 when A ≡ 1 mod 8, so QR chain differs)")

    a_mod8_counts = {}
    for q, A in cat_1mod4:
        r = A % 8
        a_mod8_counts[r] = a_mod8_counts.get(r, 0) + 1
    print(f"  q ≡ 1 (mod 4): A mod 8 distribution: {a_mod8_counts}")

    # ================================================================
    # TEST 11: QR chain trace for q ≡ 23 (mod 24) — diagnostic
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 11: QR chain for q ≡ 23 (mod 24) — why no contradiction")
    print("-" * 72)
    print(f"  For q ≡ 23 (mod 24):")
    print(f"    A ≡ 1 (mod 8) → (2/A) = +1")
    print(f"    m = (q-1)/2 ≡ 11 (mod 12)")
    print(f"    (q+1)/2 ≡ 0 (mod 12) → conditional value = +1")
    print()
    for q, A in cat_23mod24[:8]:
        m = (q - 1) // 2
        leg_1mq = legendre_symbol((1 - q) % A, A)
        leg_2 = legendre_symbol(2, A)
        leg_m = legendre_symbol(m % A, A)
        jac_3_m = jacobi_symbol(3, m)

        # For m ≡ 11 (mod 12): m ≡ 2 (mod 3), m ≡ 3 (mod 4)
        # (3/m)·(m/3) = (-1)^{((3-1)/2)·((m-1)/2)} = (-1)^{(m-1)/2}
        # m ≡ 3 mod 4 → (m-1)/2 odd → sign = -1
        # (m/3) = (2/3) = -1 (since m ≡ 2 mod 3)
        # (3/m)·(-1) = -1 → (3/m) = +1

        # QR sign: (m-1)/2 · (A-1)/2
        # m ≡ 3 mod 4 → (m-1)/2 odd
        # A ≡ 1 mod 4 → (A-1)/2 even
        # Product even → qr_sign = +1
        # So (m/A) = qr_sign · (3/m) = (+1)·(+1) = +1
        # (1-q/A) = (2/A)·(m/A) = (+1)·(+1) = +1

        print(f"  q={q:5d}: m%12={m%12:2d}, (2/A)={int(leg_2):+d}, (m/A)={int(leg_m):+d}, "
              f"J(3,m)={int(jac_3_m):+d}, (1-q/A)={int(leg_1mq):+d}")

    print(f"\n  QR chain for q ≡ 23: (2/A)=+1, (m/A)=+1 → (1-q/A) = +1")
    print(f"  Conditional = +1 also → consistent (no contradiction).")

    # ================================================================
    # TEST 12: Verify the Jacobi(3,m) theoretical values
    # ================================================================
    print("\n" + "-" * 72)
    print("TEST 12: Jacobi(3, m) for each residue class of m mod 12")
    print("-" * 72)
    # Theoretical:
    # m ≡ 5 (mod 12) [q≡11 mod 24]: Jacobi(3,m) = -1
    # m ≡ 11 (mod 12) [q≡23 mod 24]: Jacobi(3,m) = +1
    fail_12 = 0
    for q, A in cat_11mod24:
        m = (q - 1) // 2
        j = jacobi_symbol(3, m)
        if j != -1:
            print(f"  FAIL: q={q}, m={m}, m%12={m%12}, Jacobi(3,m)={j} (expected -1)")
            fail_12 += 1
    for q, A in cat_23mod24:
        m = (q - 1) // 2
        j = jacobi_symbol(3, m)
        if j != 1:
            print(f"  FAIL: q={q}, m={m}, m%12={m%12}, Jacobi(3,m)={j} (expected +1)")
            fail_12 += 1
    if fail_12 == 0:
        print(f"  PASS: Jacobi(3,m) = -1 for all m ≡ 5 (mod 12) [q≡11 mod 24]")
        print(f"  PASS: Jacobi(3,m) = +1 for all m ≡ 11 (mod 12) [q≡23 mod 24]")
    else:
        print(f"  FAIL: {fail_12} failures!")

    # ================================================================
    # SUMMARY
    # ================================================================
    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    covered = len(cat_1mod4) + len(cat_11mod24)
    print(f"\nOf {total} primes q < {limit} with q ≡ 2 (mod 3), A prime:")
    print(f"  {len(cat_1mod4):4d} ({100*len(cat_1mod4)/total:5.1f}%) — q ≡ 1 (mod 4)   [slot590: PROVEN]")
    print(f"  {len(cat_11mod24):4d} ({100*len(cat_11mod24)/total:5.1f}%) — q ≡ 11 (mod 24) [NEW contradiction]")
    print(f"  {len(cat_23mod24):4d} ({100*len(cat_23mod24)/total:5.1f}%) — q ≡ 23 (mod 24) [OPEN]")
    print(f"  {'─'*4}   {'─'*7}")
    print(f"  {covered:4d} ({100*covered/total:5.1f}%) — TOTAL COVERED")
    print(f"  {len(cat_23mod24):4d} ({100*len(cat_23mod24)/total:5.1f}%) — REMAINING OPEN")

    print(f"\nFirst few q ≡ 23 (mod 24) with A prime (the open frontier):")
    for q, A in cat_23mod24[:15]:
        leg = legendre_symbol((1 - q) % A, A)
        print(f"  q = {q:5d}, A = {A:10d}, Legendre(1-q,A) = {int(leg):+d}")

    print(f"\nFirst few q ≡ 11 (mod 24) with A prime (newly proven):")
    for q, A in cat_11mod24[:10]:
        print(f"  q = {q:5d}, A = {A:10d}")

    print("\n" + "=" * 72)
    print("CONCLUSION")
    print("=" * 72)
    print(f"""
  All {len(cat_11mod24)} primes q ≡ 11 (mod 24) with A prime verified:
    - Unconditional: Legendre(1-q, A) = +1  [by QR chain]
    - Conditional:   (1-q)^{{(A-1)/2}} ≡ -1  [by order theory under 3^q=1]
    - Euler criterion forces equality → CONTRADICTION
    - Therefore 3^q ≢ 1 (mod A) for all q ≡ 11 (mod 24) with A prime.

  The QR chain:
    (1-q / A) = (q-1 / A)           [(-1/A) = 1 since A ≡ 1 mod 4]
              = (2/A) · (m/A)        [q-1 = 2m, v₂=1]
              = (-1) · (m/A)         [A ≡ 5 mod 8 → (2/A) = -1]
    By QR: (m/A) = (A mod m / m)     [QR sign = +1 since (m-1)/2 even]
              = (3/m)                 [A ≡ 3 mod m]
              = -1                    [m ≡ 5 mod 12: (3/m)·(m/3) = (-1)^{{(m-1)/2}} = 1,
                                       (m/3) = (2/3) = -1, so (3/m) = -1]
    So (1-q/A) = (-1)·(-1) = +1     ✓

  Combined with slot590 (q ≡ 1 mod 4):
    Coverage = {100*covered/total:.1f}% of relevant primes q < {limit}.
    Remaining: q ≡ 23 (mod 24) ({100*len(cat_23mod24)/total:.1f}%).

  Why q ≡ 23 (mod 24) doesn't work:
    - A ≡ 1 (mod 8) → (2/A) = +1 (not -1)
    - m ≡ 11 (mod 12) → Jacobi(3,m) = +1 (not -1)
    - (1-q/A) = (+1)·(+1) = +1
    - Conditional also +1 (since (q+1)/2 ≡ 0 mod 12)
    - Both sides agree → no contradiction
""")

if __name__ == "__main__":
    verify_all(10000)
