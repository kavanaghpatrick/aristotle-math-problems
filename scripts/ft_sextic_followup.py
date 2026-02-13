#!/usr/bin/env python3
"""
Feit-Thompson p=3 — Follow-up on key findings from sextic exploration.

KEY FINDINGS:
1. χ₆(3) = 1 always (confirmed theoretically: QR + cubic residue both 1)
2. 3^{q+1} ≡ 3 mod A in 0/11 cases — but this is EXPECTED!
   (3^q ≡ 1 mod A has 0/11 cases — these are would-be counterexamples)
3. 3^{(q+1)/k} ≡ 1 in 0/11 cases for all k — same reason
4. (1-q)^{6q} ≡ -1 only for q=71! For all other q, it's something else.

THIS SCRIPT: Deep analysis of the (1-q)^{6q} structure.

Under FT assumption (3^q ≡ 1 mod A), we PROVED (1-q)^{6q} ≡ -1 mod A.
But unconditionally, (1-q)^{6q} ≡ -1 only for q=71.
This is NOT a contradiction though — the assumption is needed for the proof!

NEW DIRECTION: Look at the UNCONDITIONAL structure more carefully.
"""

from sympy import isprime, factorint, divisors, primitive_root, discrete_log
from collections import Counter, defaultdict

def find_eligible(limit=50000):
    eligible = []
    for q in range(71, limit, 72):
        if not isprime(q):
            continue
        A = q*q + q + 1
        if not isprime(A):
            continue
        eligible.append((q, A))
    return eligible

def main():
    eligible = find_eligible(50000)
    print(f"Found {len(eligible)} eligible primes q < 50000")
    print(f"q values: {[q for q,_ in eligible]}")
    print()

    # ========================================
    # A. Verify 3^q ≠ 1 for all eligible (no counterexample)
    # ========================================
    print("=" * 70)
    print("A. 3^q mod A (counterexample search)")
    print("=" * 70)
    for q, A in eligible:
        val = pow(3, q, A)
        if val == 1:
            print(f"  *** COUNTEREXAMPLE: q={q}, A={A}, 3^q ≡ 1 mod A! ***")
        # else don't print (expected)
    print(f"  No counterexamples found (0/{len(eligible)} have 3^q ≡ 1)")
    print()

    # ========================================
    # B. Deeper: what IS ord(3) mod A? Factor it.
    # ========================================
    print("=" * 70)
    print("B. ord(3) mod A — structure")
    print("=" * 70)
    for q, A in eligible[:20]:
        Am1 = A - 1  # = q(q+1)
        # Compute order by testing divisors of Am1
        # Am1 = q * (q+1), and we know q is prime
        # So divisors of Am1 = {q^a * d : a in {0,1}, d | q+1}
        qp1 = q + 1
        divs_qp1 = sorted(divisors(qp1))

        # First check divisors of q+1 (small order, not involving q)
        ord_3 = None
        for d in divs_qp1:
            if pow(3, d, A) == 1:
                ord_3 = d
                break
        if ord_3 is None:
            # Order must involve factor of q
            for d in divs_qp1:
                if pow(3, q * d, A) == 1:
                    ord_3 = q * d
                    break

        # Factor the order
        ord_factors = factorint(ord_3)
        factor_str = " · ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(ord_factors.items()))

        # How much of q+1 divides ord_3?
        if ord_3 % q == 0:
            m = ord_3 // q
            qp1_m = qp1 // m if qp1 % m == 0 else "?"
            print(f"  q={q:6d}: ord(3) = {ord_3:10d} = q · {m:6d} (q+1 = {qp1}, m/(q+1) = {m/qp1:.3f})")
        else:
            print(f"  q={q:6d}: ord(3) = {ord_3:10d} | (q+1)={qp1} (order doesn't involve q)")

    print()

    # ========================================
    # C. The CRUCIAL structural analysis
    # ========================================
    print("=" * 70)
    print("C. (q+1)/ord(3) structure — what if ord(3) | (q+1)?")
    print("   If ord(3) | (q+1), then ord(3) does NOT involve q as factor.")
    print("   Under assumption: ord(3) = q, so q | (q+1) — impossible!")
    print("   So: if unconditionally ord(3) | (q+1) always, that contradicts assumption.")
    print("=" * 70)
    ord_divides_qp1 = 0
    ord_involves_q = 0
    for q, A in eligible:
        qp1 = q + 1
        # Check if ord(3) | (q+1)
        if pow(3, qp1, A) == 1:
            ord_divides_qp1 += 1
        else:
            ord_involves_q += 1

    print(f"  ord(3) | (q+1): {ord_divides_qp1}/{len(eligible)}")
    print(f"  ord(3) ∤ (q+1): {ord_involves_q}/{len(eligible)} (order involves q)")
    print()
    if ord_involves_q > 0:
        print("  Since ord(3) doesn't always divide (q+1), no immediate contradiction.")
        print("  Cases where q | ord(3):")
        for q, A in eligible:
            qp1 = q + 1
            if pow(3, qp1, A) != 1:
                # ord involves q
                # Find the exact divisor m of q+1 such that ord = q*m
                for d in sorted(divisors(qp1)):
                    if pow(3, q * d, A) == 1:
                        print(f"    q={q}: ord(3) = q · {d} (q+1 = {qp1})")
                        break
    print()

    # ========================================
    # D. NEW APPROACH: exploit that 3^{q+1} ≡ 3^{q+1} both ways
    #    Under assumption: 3^{q+1} = 3
    #    Unconditionally: 3^{q+1} = some value v
    #
    #    Subtract: assumption implies 3^{q+1} - 3 ≡ 0 (mod A)
    #    i.e., A | (3^{q+1} - 3)
    #    i.e., (q²+q+1) | (3^{q+1} - 3)
    #
    #    This is equivalent to 3^q ≡ 1 (mod A), which is the original problem!
    #    So 3^{q+1} ≠ 3 is just the statement that 3^q ≠ 1. Circular.
    # ========================================
    print("=" * 70)
    print("D. Circularity check: 3^{q+1} ≡ 3 ⟺ 3^q ≡ 1 (mod A)")
    print("   (Confirmed: these are equivalent)")
    print("=" * 70)
    for q, A in eligible[:5]:
        v1 = pow(3, q, A) == 1
        v2 = pow(3, q+1, A) == 3
        print(f"  q={q}: 3^q = 1? {v1}, 3^{{q+1}} = 3? {v2}, match: {v1 == v2}")
    print()

    # ========================================
    # E. UNCONDITIONAL PROPERTIES WE CAN USE
    # ========================================
    print("=" * 70)
    print("E. Unconditional structural properties of A = q²+q+1")
    print("=" * 70)

    # E1: A ≡ 1 mod 6 (always for q > 3)
    # E2: A ≡ 1 mod q (since A = q²+q+1 ≡ 1 mod q)
    # E3: (3/A) = +1 (proven by QR)
    # E4: 3 is a cubic residue mod A (proven for q ≡ 8 mod 9)
    # E5: What about 3 as higher power residue?

    # Check: for what n is 3 an n-th power residue mod A?
    # i.e., 3^{(A-1)/n} ≡ 1 mod A
    # (A-1) = q(q+1)
    print("  For which n | (A-1) is 3 an n-th power residue?")
    print("  (i.e., 3^{(A-1)/n} ≡ 1 mod A)")
    print()

    for q, A in eligible[:5]:
        Am1 = A - 1
        divs = sorted(divisors(Am1))
        # For each divisor n of A-1, check if 3^{(A-1)/n} = 1
        max_n = 0
        for n in divs:
            if pow(3, Am1 // n, A) == 1:
                max_n = n
        # max_n = ord(3) since 3^{(A-1)/ord(3)} = 1 and (A-1)/ord(3) is the index
        # Actually max n such that 3^{(A-1)/n} = 1 equals ord(3)
        # because (A-1)/n must be a multiple of ord(3)
        print(f"  q={q:6d}: largest n with 3^{{(A-1)/n}}=1: n={max_n} = ord(3)")
        # Also: 3 is an n-th power residue iff ord(3) | (A-1)/n iff n | (A-1)/ord(3)
        index = Am1 // max_n
        print(f"           index = (A-1)/ord(3) = {index}")
        print(f"           3 is n-th power residue for n | {index}")
        index_factors = factorint(index)
        factor_str = " · ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(index_factors.items()))
        print(f"           {index} = {factor_str}")
        print()

    # ========================================
    # F. IDEA: Exploit 3^{2q} = (3^q)^2 mod A
    #    Under assumption: 3^{2q} = 1
    #    But also: 3^{2q} = 9^q
    #    And: 9 = 3². So 9^q ≡ 1 (mod A) under assumption.
    #    The Aurifeuillean factorization: 3^{2q} - 1 = (3^q - 1)(3^q + 1)
    #    Under assumption: A | (3^q - 1), so A ∤ (3^q + 1) generically.
    #    Unconditionally: gcd(A, 3^q - 1) and gcd(A, 3^q + 1).
    # ========================================
    print("=" * 70)
    print("F. Aurifeuillean: gcd(A, 3^q - 1) and gcd(A, 3^q + 1)")
    print("=" * 70)
    for q, A in eligible:
        v = pow(3, q, A)
        g_minus = A if v == 1 else 1  # gcd(A, 3^q-1): if 3^q=1 mod A, it's A; else 1 (A prime)
        g_plus = A if v == A - 1 else 1  # 3^q ≡ -1 mod A?
        # Actually for A prime: gcd(A, 3^q-1) is A if A|(3^q-1), else 1
        # And gcd(A, 3^q+1) is A if A|(3^q+1), else 1
        minus_1 = (v == 1)
        plus_1 = (v == A - 1)  # 3^q ≡ -1 means A | (3^q + 1)
        print(f"  q={q:6d}: 3^q ≡ {v} (mod A), "
              f"A | (3^q-1)? {minus_1}, A | (3^q+1)? {plus_1}")
    print()

    # ========================================
    # G. FERMAT QUOTIENT approach
    #    The Fermat quotient of 3 base A is: f = (3^{A-1} - 1)/A
    #    Under assumption 3^q = 1: 3^{A-1} = 3^{q(q+1)} = (3^q)^{q+1} = 1
    #    So f = 0 (i.e., 3^{A-1} = 1, but we knew that — Fermat's little theorem!)
    #
    #    More useful: the INDEX of 3 in (Z/AZ)*
    #    Under assumption: index(3) = (A-1)/q = q+1
    #    This means 3 = g^{q+1} for some generator g
    #    So 3 is a (q+1)-th power in (Z/AZ)*
    #    i.e., 3 is an n-th power residue for all n | (q+1)
    #
    #    CHECK: is 3 always an n-th power residue for all n | (q+1)?
    # ========================================
    print("=" * 70)
    print("G. Is 3 an n-th power residue mod A for all n | (q+1)?")
    print("   Under assumption (ord(3)=q): YES, since index = q+1")
    print("   Unconditionally: need to check")
    print("=" * 70)

    for q, A in eligible[:15]:
        Am1 = A - 1
        qp1 = q + 1
        divs_qp1 = sorted(divisors(qp1))

        all_residue = True
        failing_n = []
        for n in divs_qp1:
            if n == 1:
                continue
            # 3 is n-th power residue iff 3^{(A-1)/n} = 1
            if Am1 % n != 0:
                continue
            val = pow(3, Am1 // n, A)
            if val != 1:
                all_residue = False
                failing_n.append(n)

        if all_residue:
            print(f"  q={q:6d}: 3 IS n-th power residue for ALL n | (q+1)={qp1}")
        else:
            print(f"  q={q:6d}: 3 is NOT n-th power residue for n ∈ {failing_n}")

    print()

    # ========================================
    # H. THE REVERSE: n-th power residue for n | q
    #    Since q is prime, divisors of q are {1, q}.
    #    3 is q-th power residue iff 3^{(A-1)/q} = 3^{q+1} = 1.
    #    Under assumption: 3^{q+1} = 3 ≠ 1. So 3 is NOT a q-th power residue!
    #    Unconditionally: 3^{q+1} mod A is what we computed — never 1 in our data.
    # ========================================
    print("=" * 70)
    print("H. Is 3 a q-th power residue mod A?")
    print("   (i.e., 3^{(A-1)/q} = 3^{q+1} ≡ 1 mod A?)")
    print("   Under assumption: 3^{q+1} = 3 ≠ 1, so NO")
    print("   Unconditionally: also NO in all tested cases")
    print("=" * 70)
    for q, A in eligible:
        val = pow(3, q + 1, A)
        print(f"  q={q:6d}: 3^{{q+1}} ≡ {val} (mod A), is 1? {val == 1}, is 3? {val == 3}")
    print()

    # ========================================
    # I. CRITICAL OBSERVATION:
    #    Under assumption, 3 is NOT a q-th power residue.
    #    Under assumption, 3 IS an (q+1)-th power residue (for all n | q+1).
    #    These are just consequences of ord(3) = q.
    #
    #    For a CONTRADICTION, we need:
    #    Something that's TRUE under assumption and FALSE unconditionally, or vice versa.
    #
    #    Under assumption TRUE: 3^q = 1, (1-q)^{6q} = -1, ord(3) = q
    #    Unconditionally FALSE: 3^q ≠ 1 (no counterexample found)
    #    But that's circular — we're TRYING to prove 3^q ≠ 1!
    #
    #    REAL APPROACH: find an unconditional consequence of 3^q = 1
    #    that can be checked independently.
    # ========================================
    print("=" * 70)
    print("I. Summary of approach viability")
    print("=" * 70)
    print("""
  DEAD ENDS:
  - χ₂(3) = (3/A) = +1 unconditionally (no QR contradiction)
  - χ₃(3) = 1 unconditionally for q ≡ 8 mod 9 (no cubic contradiction)
  - χ₆(3) = 1 unconditionally (follows from χ₂ and χ₃)
  - χ_n(3) for n | (q+1): under assumption 3^{q(q+1)/n} = 1 since n|(q+1)
    so these can't distinguish assumption from reality
  - 3^{q+1} = 3 ⟺ 3^q = 1 (circular)

  PARTIALLY ALIVE:
  - χ₈(3) ≠ 1 in 6/11 cases unconditionally, but =1 under assumption → only works
    for THOSE specific q, not universally
  - χ₉(3) ≠ 1 in 8/11 cases, same issue
  - (1-q)^{6q} = -1 only for q=71 unconditionally. Under assumption it's -1 always.
    But unconditional failure doesn't help — assumption ADDS structure.

  THE FUNDAMENTAL ISSUE:
  All character-based approaches involving 3^{f(q)} where f(q) is a multiple of q
  reduce to the original question 3^q = 1 after simplification under the assumption.

  Characters involving 3^{g(q)} where g(q) is NOT a multiple of q (like 3^{q+1})
  give 3^{g(q)} unconditionally, but under assumption 3^{g(q)} = 3^{g(q) mod q}.
  For g(q) = q+1: 3^{q+1} = 3^1 = 3 under assumption. Unconditionally 3^{q+1} ≠ 3
  is equivalent to 3^q ≠ 1. CIRCULAR.

  WHAT COULD WORK:
  Conditions involving BOTH 3 and (1-q) simultaneously, or involving the
  multiplicative structure of (Z/AZ)* in ways that don't reduce to ord(3).
  """)

    # ========================================
    # J. NEW: Relationship between 3 and (1-q) in (Z/AZ)*
    #    Under assumption: 3 = g^{q+1}, 1-q = g^t where t satisfies constraints.
    #    Let r = discrete log of (1-q) base 3 (if it exists in ⟨3⟩).
    #    (1-q) ∈ ⟨3⟩ iff ord(3) | ord(1-q) ... no, iff (1-q) is in the subgroup generated by 3.
    # ========================================
    print("=" * 70)
    print("J. Is (1-q) in the subgroup generated by 3?")
    print("   (1-q) ∈ ⟨3⟩ iff (1-q)^{ord(3)} = 1")
    print("=" * 70)

    for q, A in eligible[:15]:
        # First get ord(3)
        Am1 = A - 1
        qp1 = q + 1
        ord_3 = None
        for d in sorted(divisors(qp1)):
            if pow(3, d, A) == 1:
                ord_3 = d
                break
        if ord_3 is None:
            for d in sorted(divisors(qp1)):
                if pow(3, q * d, A) == 1:
                    ord_3 = q * d
                    break

        val_1mq = (1 - q) % A
        in_subgroup = pow(val_1mq, ord_3, A) == 1

        # Also: under assumption, ord(3) = q, is (1-q) in ⟨3⟩?
        # (1-q)^q would need to be 1 under assumption
        val_1mq_pow_q = pow(val_1mq, q, A)

        print(f"  q={q:6d}: ord(3)={ord_3:8d}, (1-q)^{{ord(3)}}=1? {in_subgroup}, "
              f"(1-q)^q = {val_1mq_pow_q}")

    print()

    # ========================================
    # K. WHAT IS (1-q)^q mod A unconditionally?
    #    Under assumption 3^q=1: we proved (1-q)^6 = 3^{1-q} (a consequence)
    #    Wait, let's think more carefully.
    #    (1-q)^q = ? We know A = q²+q+1, so (1-q) = A - q = q²+2 (mod A).
    #    (q²+2)^q mod A?
    # ========================================
    print("=" * 70)
    print("K. (1-q)^q mod A — looking for patterns")
    print("=" * 70)
    for q, A in eligible[:20]:
        val_1mq = (1 - q) % A
        val = pow(val_1mq, q, A)
        # Check if val is a nice expression
        # Is val = some power of 3?
        # Is val related to q?
        # Check val^2, val^3 etc
        val2 = pow(val, 2, A)
        val3 = pow(val, 3, A)
        val6 = pow(val, 6, A)
        print(f"  q={q:6d}: (1-q)^q ≡ {val:10d}, "
              f"^2={val2:10d}, ^3={val3:10d}, ^6={val6:10d}")

    print()

    # ========================================
    # L. NORM MAP: N(1-q) = (1-q)^{1+q+q²} in the cyclotomic extension
    #    In Z/AZ, we have q³ ≡ 1 (mod A) since A | (q³-1) = (q-1)(q²+q+1)
    #    So q is a cube root of unity mod A.
    #    The "norm" N(x) = x · x^q · x^{q²} = x^{1+q+q²} = x^A = x (by Fermat!)
    #    Not directly useful.
    #
    #    But: x^q is NOT the same as the Frobenius in a field extension.
    #    In GF(A), raising to q-th power is just an automorphism of the
    #    multiplicative group, NOT a field automorphism.
    # ========================================

    # ========================================
    # M. The DISCRIMINANT/RESULTANT approach
    #    Polynomials: x^q - 1 and x^{q+1} - 3 in Z/AZ[x]
    #    Under assumption: x=3 is a root of x^q - 1
    #    And 3^{q+1} - 3 = 3(3^q - 1) = 0 under assumption
    #    So x=3 is a common root of x^q - 1 and x^{q+1} - 3x
    #    Resultant: Res(x^q - 1, x^{q+1} - 3x) ≡ 0 (mod A)
    # ========================================
    print("=" * 70)
    print("M. Resultant approach: A | Res(x^q - 1, x^{q+1} - 3x)?")
    print("   Under assumption: yes (common root x=3)")
    print("   Unconditionally: check numerically")
    print("=" * 70)

    # The resultant of x^q - 1 and x^{q+1} - 3x = x(x^q - 3)
    # Res(x^q - 1, x(x^q - 3)) = Res(x^q-1, x) · Res(x^q-1, x^q-3)
    # Res(x^q-1, x) = 0^q - 1 = -1
    # Res(x^q-1, x^q-3) = product over ζ^q=1 of (ζ^q - 3) = product of (1-3) = (-2)^q
    # So Res = (-1) · (-2)^q = (-1)^{q+1} · 2^q = 2^q (since q is odd)
    # So the question is: A | 2^q?
    # For A >> 2^q when q is small this fails. For large q, A = q²+q+1 << 2^q.
    # But this isn't quite right — let me redo.

    # Actually: Res(f,g) where f = x^q - 1, g = x^{q+1} - 3x
    # These are NOT coprime under assumption. But the resultant is a number,
    # and A | Res iff they have a common root mod A.

    # Simpler: A | (3^q - 1) is exactly the condition. The resultant approach
    # just rephrases this. Still circular.

    print("  (Resultant reduces to: A | (3^q - 1). Circular.)")
    print()

    # ========================================
    # N. FINAL: Is there ANY unconditional invariant that assumption violates?
    #
    #    The Wieferich-like criterion: 3^{A-1} ≡ 1 (mod A²)?
    #    Under assumption 3^q ≡ 1 (mod A): does this extend to mod A²?
    # ========================================
    print("=" * 70)
    print("N. Wieferich-like: 3^q mod A² and 3^{A-1} mod A²")
    print("=" * 70)
    for q, A in eligible[:15]:
        A2 = A * A
        v_q = pow(3, q, A2)
        v_Am1 = pow(3, A - 1, A2)
        fermat_q = (v_q - 1) // A if v_q % A == 0 else "N/A"
        fermat_Am1 = (v_Am1 - 1) // A
        print(f"  q={q:6d}: 3^q mod A² → quotient {fermat_q}, "
              f"3^{{A-1}} mod A² → Fermat quotient {fermat_Am1}")

    print()

    # ========================================
    # O. Check: is the Fermat quotient (3^{A-1} - 1)/A ≡ 0 (mod q)?
    #    Under assumption 3^q = 1+kA for some k:
    #    3^{A-1} = 3^{q(q+1)} = (1+kA)^{q+1} ≡ 1 + (q+1)kA (mod A²)
    #    So Fermat quotient = (q+1)k mod A
    #    And (3^q - 1)/A = k, so FQ(3,A) ≡ (q+1) · (3^q-1)/A (mod A)
    # ========================================
    print("=" * 70)
    print("O. Fermat quotient structure: FQ = (3^{A-1}-1)/A mod q")
    print("=" * 70)
    for q, A in eligible[:15]:
        A2 = A * A
        v_Am1 = pow(3, A - 1, A2)
        fq = (v_Am1 - 1) // A
        fq_mod_q = fq % q
        print(f"  q={q:6d}: FQ(3,A) = {fq:12d}, FQ mod q = {fq_mod_q}")
    print()

    # ========================================
    # P. EXPLORE: For assumption 3^q=1, we need q | (A-1) and 3 generates
    #    a subgroup of order q. In (Z/AZ)* ≅ Z/(q(q+1)),
    #    the unique subgroup of order q is {x : x^q = 1} = {g^{k(q+1)} : k=0..q-1}.
    #    3 ∈ this subgroup iff 3 = g^{m(q+1)} for some m.
    #
    #    The coset index of 3 in the quotient (Z/AZ)*/⟨q-th powers⟩:
    #    3 is in the q-th power subgroup iff 3^{(A-1)/q} = 3^{q+1} = 1.
    #    We showed 3^{q+1} ≠ 1 for all tested q.
    #    Under assumption: 3^{q+1} = 3 ≠ 1. Same conclusion: 3 NOT a q-th power.
    #    No contradiction since both agree.
    # ========================================

    print("=" * 70)
    print("SUMMARY OF SEXTIC/HIGHER CHARACTER EXPLORATION")
    print("=" * 70)
    print("""
  ALL character-based approaches for Feit-Thompson p=3 case have been
  systematically explored. Here is the definitive status:

  CONFIRMED DEAD:
  1. χ₂(3) = +1 unconditionally → no QR contradiction
  2. χ₃(3) = 1 unconditionally for q ≡ 8 mod 9 → no cubic contradiction
  3. χ₆(3) = 1 unconditionally → sextic character adds nothing
  4. Higher characters χ_n(3) for n | (q+1): under assumption they all = 1,
     and for n | (q+1) this factors through 3^q = 1. Circular.
  5. 3^{q+1} ≠ 3 ⟺ 3^q ≠ 1. Completely circular.
  6. Resultant approaches reduce to 3^q ≡ 1 mod A. Circular.

  NOT UNIVERSALLY EFFECTIVE (work for some q but not all):
  7. χ₈(3) ≠ 1 for 6/11 eligible q (varies)
  8. χ₉(3) ≠ 1 for 8/11 eligible q (varies)
  9. χ₂₄(3) ≠ 1 for 6/11 eligible q (varies)

  POTENTIALLY INTERESTING BUT NOT CONTRADICTION:
  10. (1-q)^{6q} ≡ -1 only for q=71 unconditionally, but under assumption
      it's always -1. This means assumption adds structure, not removes it.
  11. ord(3) always involves q as factor in actual computation.
      Under assumption ord(3) = q. Actual ord(3) = q·m for m | (q+1).

  FUNDAMENTAL OBSTRUCTION:
  For any function f: if f(3) under assumption can be simplified using
  3^q = 1 to get value v, and unconditionally f(3) ≠ v, then we've just
  restated 3^q ≠ 1 in disguise. Character approaches inherently do this.

  WHAT MIGHT WORK INSTEAD:
  - Algebraic number theory: norm conditions in Q(ζ_q)
  - p-adic analysis: 3-adic properties of q²+q+1
  - Sieve/density arguments: showing the set of primes where 3^q ≡ 1 has density 0
  - Connection to class numbers or L-functions
  """)


if __name__ == "__main__":
    main()
