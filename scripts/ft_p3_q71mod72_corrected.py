#!/usr/bin/env python3
"""
Feit-Thompson p=3 q≡71 mod 72: CORRECTED exploration

The previous script had an algebraic error in deriving (q+1)^{q+1} = -1.
Let's carefully re-derive and find what ACTUALLY works.

KEY CORRECT FACTS (all verified):
- (1-q)^q = (q+2) · 3^{(q-1)/2} mod A          ← VERIFIED
- (q+2)^q = -(q+2)·q · 3^{(q-1)/2} mod A        ← VERIFIED
- (1-q)^6 = (q+2)^6 = -27 mod A                  ← VERIFIED
- (1-q)^2 = -3q, (q+2)^2 = 3(q+1), (q+2)^4 = 9q ← VERIFIED
- q^q = q² = -q-1 mod A (since q ≡ 2 mod 3)     ← VERIFIED
- 3^q = (1-q)^{2q}/(q+1) = (1-q)^{2q}·(q+1)^{-1}← VERIFIED

NEW STRATEGY: Since low-order power residue characters all fail (3 is always
a k-th power res for k=2,3,4,6,12), we need a fundamentally different approach.

Explore:
1. What is (q+1)^{q+1} mod A actually?
2. The key formula (1-q)^q = (q+2)·3^{(q-1)/2} — can we extract info from this?
3. Under assumption 3^q=1: (1-q)^{2q} = q+1. What does this constrain?
4. Quadratic residuosity of (q+1) mod A?
5. The element 3^{(q-1)/2} mod A — what is its ORDER?
"""

from sympy import isprime, factorint, primitive_root, jacobi_symbol
from collections import Counter, defaultdict

def find_eligible_primes(limit=100000):
    eligible = []
    for q in range(71, limit, 72):
        if not isprime(q):
            continue
        A = q*q + q + 1
        if isprime(A):
            eligible.append((q, A))
    return eligible

def main():
    primes = find_eligible_primes(100000)
    print(f"Found {len(primes)} eligible primes q < 100000\n")

    print("=" * 80)
    print("SECTION 1: What is (q+1)^{q+1} mod A actually?")
    print("=" * 80)

    for q, A in primes[:15]:
        val = pow(q + 1, q + 1, A)
        # q+1 = -(q²) mod A. So (q+1)^{q+1} = (-q²)^{q+1} = (-1)^{q+1} · q^{2(q+1)}.
        # q+1 is even → (-1)^{q+1} = -1.
        # 2(q+1) mod 3: q ≡ 2 mod 3, q+1 ≡ 0 mod 3, 2(q+1) ≡ 0 mod 3.
        # q^{2(q+1)} = (q^3)^{2(q+1)/3} = 1. So (q+1)^{q+1} = -1.
        # But the script says it's NOT -1! Let me check...
        neg1 = A - 1
        is_neg1 = (val == neg1)

        # Let me verify step by step
        q_sq = pow(q, 2, A)  # q² mod A
        neg_q_sq = (-q_sq) % A  # -q² mod A = q+1 mod A
        check_qp1 = (q + 1) % A
        step1 = (neg_q_sq == check_qp1)

        # (-q²)^{q+1}
        val2 = pow(neg_q_sq, q + 1, A)
        step2 = (val == val2)

        # (-1)^{q+1} · q^{2(q+1)}
        neg1_exp = pow(A - 1, q + 1, A)  # (-1)^{q+1}
        q_exp = pow(q, 2 * (q + 1), A)  # q^{2(q+1)}
        val3 = (neg1_exp * q_exp) % A
        step3 = (val2 == val3)

        print(f"  q={q}: (q+1)^(q+1)={val}, -1={neg1}, is -1? {is_neg1}")
        print(f"    q+1 = -q² mod A? {step1}")
        print(f"    (-q²)^(q+1) matches? {step2}")
        print(f"    (-1)^(q+1)·q^(2(q+1)) matches? {step3}")
        print(f"    (-1)^(q+1) = {neg1_exp}, q^(2(q+1)) = {q_exp}")

    print("\n  ISSUE: Let me check if q+1 = -q² mod A correctly.")
    for q, A in primes[:5]:
        print(f"  q={q}: A={A}, q²+q+1={q*q+q+1}, q²={q*q}, -q²-1={-(q*q)-1}")
        print(f"    q+1 = {q+1}, -q² mod A = {(-q*q) % A}")
        print(f"    Equal? {(q+1) % A == (-q*q) % A}")

    print("\n  Hmm, q+1 = -(q²) mod A? A = q²+q+1, so q² = A-q-1 ≡ -q-1 mod A.")
    print("  -q² ≡ q+1 mod A. YES, this is correct.")
    print("  But (-1)^{q+1}: q is odd, q+1 is even, so (-1)^{q+1} = 1, NOT -1!")
    print("  I had the sign wrong earlier!\n")

    for q, A in primes[:5]:
        neg1_exp = pow(A - 1, q + 1, A)
        print(f"  q={q}: (-1)^(q+1) = {neg1_exp} (should be 1 since q+1 even)")
        # So (q+1)^{q+1} = 1 · q^{2(q+1)} = q^{2(q+1)}.
        # 2(q+1) mod 3: q ≡ 2 mod 3 → q+1 ≡ 0 → 2(q+1) ≡ 0.
        # q^{2(q+1)} = 1.
        q_exp = pow(q, 2 * (q + 1), A)
        print(f"    q^(2(q+1)) = {q_exp}")

    print("\n  So (q+1)^{q+1} = 1 mod A. Always. This is trivial:")
    print("  (q+1) = -q² → (q+1)^{q+1} = (-1)^{q+1}·q^{2(q+1)} = 1·(q³)^{2(q+1)/3} = 1.")
    print("  And (q+1)^{(q+1)/2} = (-q²)^{(q+1)/2} = (-1)^{(q+1)/2} · q^{q+1}.")
    print("  (q+1)/2 is even iff 4|(q+1). q≡71 mod 72 → q+1≡0 mod 8 → (q+1)/2≡0 mod 4. Even!")
    print("  So (-1)^{(q+1)/2} = 1. And q^{q+1}: (q+1) mod 3 = 0, so q^{q+1} = 1.")
    print("  Therefore (q+1)^{(q+1)/2} = 1 always. Confirmed.\n")

    print("  The derivation in the previous script was correct in algebra but")
    print("  wrong in the sign of (-1)^{q+1}. The necessary condition was tautological.\n")

    print("=" * 80)
    print("SECTION 2: Go back to the KEY formula and work carefully")
    print("=" * 80)

    print("\n  VERIFIED FORMULAS:")
    print("  (I)  (1-q)^q = (q+2) · 3^{(q-1)/2} mod A")
    print("  (II) 3^q = (1-q)^{2q} · (q+1)^{-1} mod A")
    print("  (III) (1-q)^{2q} = [(1-q)^6]^{(q-2)/3} · (1-q)^4 = (-27)^{(q-2)/3} · (-9(q+1))")
    print("  (IV) Combining: 3^q = (-27)^{(q-2)/3} · (-9(q+1)) · (q+1)^{-1}")
    print("       = (-27)^{(q-2)/3} · (-9)\n")

    # Verify formula (IV)
    print("  Verifying formula (IV): 3^q = (-27)^{(q-2)/3} · (-9) mod A:")
    for q, A in primes[:15]:
        n = (q - 2) // 3
        val = (pow((-27) % A, n, A) * ((-9) % A)) % A
        three_q = pow(3, q, A)
        print(f"  q={q}: (-27)^n · (-9) = {val}, 3^q = {three_q}, match: {val == three_q}")

    print("\n  YES! Formula verified: 3^q ≡ (-9) · (-27)^{(q-2)/3} mod A")
    print("  Equivalently: 3^q = -9 · (-27)^n where n = (q-2)/3.\n")

    print("  Now: 3^q = 1 iff (-27)^n = (-9)^{-1} = -9^{-1} mod A")
    print("  iff (-27)^n = -3^{-2} mod A")
    print("  iff (-1)^n · 27^n = -3^{-2}")
    print("  iff (-1)^n · 3^{3n} = -3^{-2}")
    print("  iff (-1)^n · 3^{3n+2} = -1")
    print("  Now 3n+2 = 3·(q-2)/3 + 2 = q-2+2 = q.")
    print("  So: (-1)^n · 3^q = -1.")
    print("  If 3^q = 1: (-1)^n = -1, i.e., n is odd.")
    print("  n = (q-2)/3. For q ≡ 71 mod 72: (71-2)/3 = 23, which IS odd. Consistent.\n")

    print("  THIS IS THE CIRCULAR PART. We cannot avoid it this way.\n")

    print("=" * 80)
    print("SECTION 3: Non-algebraic approach — order constraints")
    print("=" * 80)

    print("\n  From the first exploration: d = ord(3)/q always divides (q+1).")
    print("  d is ALWAYS ≥ 3. Can we prove d ≥ 3?\n")

    print("  d ≥ 2 means ord(3) ≥ 2q, i.e., 3^q ≠ 1 AND 3^{2q} ≠ 1.")
    print("  3^{2q} = (3^q)^2 ≠ 1 means 3^q ≠ ±1.")
    print("  We want to show at minimum: 3^q ≠ 1.\n")

    print("  Let's look at this from the CONGRUENCE perspective.")
    print("  3^q mod A: what congruence class mod small numbers?")

    for q, A in primes[:15]:
        three_q = pow(3, q, A)
        # 3^q mod small numbers
        print(f"  q={q}: 3^q mod A = {three_q}, mod 3 = {three_q % 3}, "
              f"mod 8 = {three_q % 8}, mod 9 = {three_q % 9}, mod 72 = {three_q % 72}")

    print("\n" + "=" * 80)
    print("SECTION 4: 3^q mod 3 — is there a universal pattern?")
    print("=" * 80)

    print("\n  3^q ≡ 0 mod 3 (trivially, since 3 | 3^q).")
    print("  So 3^q mod A ≡ 0 mod 3 always. If 3^q = 1 mod A, then 1 ≡ 0 mod 3, impossible!")
    print("  WAIT — is this right? No! 3^q mod A is an element of {0,...,A-1}.")
    print("  3^q is an integer, and 3 | 3^q. So 3^q mod A has 3^q ≡ 0 mod 3 as integer.")
    print("  BUT 3^q mod A is (3^q) mod A. The integer 3^q is divisible by 3.")
    print("  So (3^q mod A) ≡ 3^q ≡ 0 mod 3 AS AN INTEGER...")
    print("  NO! (3^q mod A) is the remainder, which could be anything.")
    print("  3^q = k·A + r where r = 3^q mod A. Then r = 3^q - k·A.")
    print("  3 | 3^q. A = q²+q+1. 3 | A iff 3 | (q²+q+1).")
    print("  q ≡ 2 mod 3 → q² ≡ 1, q²+q+1 ≡ 1+2+1 = 4 ≡ 1 mod 3.")
    print("  So 3 ∤ A. Thus r = 3^q - k·A ≡ 0 - k·1 ≡ -k mod 3.")
    print("  Not necessarily 0 mod 3. False alarm.\n")

    print("=" * 80)
    print("SECTION 5: NEW — the (q-1)/2 exponent of 3")
    print("=" * 80)

    print("\n  From formula: (1-q)^q = (q+2) · 3^{(q-1)/2}.")
    print("  Under 3^q = 1: 3^{(q-1)/2} = 3^{-1/2} in the cyclic group <3>.")
    print("  More precisely: 3^{(q-1)/2} = 3^{(q-1)/2 mod q} = 3^{(q-1)/2}.")
    print("  Since ord(3) = q: 3^{(q-1)/2} has order q/gcd((q-1)/2, q) = q")
    print("  (since gcd((q-1)/2, q) = 1 for odd prime q > 2).\n")

    print("  So under 3^q = 1: (1-q)^q = (q+2) · g where g has order q.")
    print("  (1-q)^q is in the (q+1)-torsion (as computed earlier).")
    print("  (q+2) = some fixed element.")
    print("  For the equation to hold: (q+2) · g must be in (q+1)-torsion.")
    print("  g is in q-torsion. So (q+2) must map to (q+1)-torsion · (q-torsion)^{-1}.")
    print("  Since q-torsion ∩ (q+1)-torsion = {1} and their product is the whole group,")
    print("  any element decomposes uniquely. Let (q+2) = α·β with α ∈ C_q, β ∈ C_{q+1}.")
    print("  Then (q+2)·g = α·g · β. For this to be in C_{q+1}: α·g = 1, i.e., g = α^{-1}.")
    print("  So: 3^{(q-1)/2} = α^{-1} where α = projection of (q+2) onto C_q.\n")

    print("  α = (q+2)^{q+1} mod A (projection onto q-torsion).")
    print("  Checking α = [(q+2)^{q+1}]^{-1} = inverse of 3^{(q-1)/2} under assumption 3^q=1:\n")

    for q, A in primes[:10]:
        alpha = pow((q+2) % A, q + 1, A)  # q-torsion projection of (q+2)
        three_half = pow(3, (q - 1) // 2, A)
        alpha_inv = pow(alpha, A - 2, A)
        # Under 3^q = 1: three_half should equal alpha_inv
        # But 3^q ≠ 1, so this won't hold. Let's just see what alpha is.
        print(f"  q={q}: α=(q+2)^(q+1)={alpha}, 3^((q-1)/2)={three_half}, "
              f"α^(-1)={alpha_inv}")

    print("\n  Let's verify: does α always equal 3^{-(q-1)/2} when 3^q ≠ 1? No reason it should.")
    print("  The formula holds only under 3^q = 1.\n")

    print("=" * 80)
    print("SECTION 6: Re-examining d = ord(3)/q — what determines it?")
    print("=" * 80)

    print("\n  d divides (q+1). The key observation from earlier: d is always ≥ 3.")
    print("  More precisely: d = order of 3^q in the (q+1)-torsion subgroup.\n")

    print("  3^q is the '(q+1)-th power residue character' of 3.")
    print("  d = ord(3^q) in C_{q+1}. We need d > 1.\n")

    print("  From the formula 3^q = -9 · (-27)^{(q-2)/3} mod A:")
    print("  -9 = -3² and -27 = -3³.")
    print("  Let x = -27 mod A. Then 3^q = -9 · x^n where n = (q-2)/3.\n")
    print("  x = -27. What is ord(x) mod A?")

    for q, A in primes[:10]:
        x = (-27) % A
        am1 = A - 1
        am1_f = factorint(am1)
        ox = am1
        for p in am1_f:
            while ox % p == 0 and pow(x, ox // p, A) == 1:
                ox //= p
        print(f"  q={q}: ord(-27) = {ox}, A-1 = {am1}, A-1/ord = {am1 // ox}")

    print("\n  -27 = (-1)·3³. ord(-27) depends on the interplay of ord(-1) and ord(3).")
    print("  ord(-1) divides 2. If ord(-1) = 2 (i.e., -1 ≠ 1 mod A, which is A > 2): yes.\n")

    print("=" * 80)
    print("SECTION 7: Key realization — try a TOTALLY different approach")
    print("=" * 80)

    print("\n  All algebraic manipulations in F_A are tautological because we're")
    print("  working in the same field. We need EXTERNAL information.\n")

    print("  Approach 1: Counting/density argument")
    print("  Approach 2: Use structure of Z[ω] BEFORE reducing mod A")
    print("  Approach 3: Relate to something provable like Weil's theorem\n")

    print("  Let's try approach 2 more carefully.")
    print("  In Z[ω], (1-ω)^q is a specific algebraic integer.")
    print("  Its real and imaginary parts are determined by q.")
    print("  After reduction mod π_A = q-ω, we get (1-q)^q mod A.\n")

    print("  (1-ω)^q = c₀ + c₁ω where c₀, c₁ ∈ Z are explicit sums of binomials.")
    print("  (1-ω)^q mod (q-ω) = c₀ + c₁q (replacing ω by q in Z/(A)).\n")

    # Compute c₀, c₁ for small q
    # (1-ω)^q = Σ C(q,k)(-ω)^k = Σ C(q,k)(-1)^k ω^k
    # Group by ω^{k mod 3}: k=3j → 1, k=3j+1 → ω, k=3j+2 → ω² = -1-ω
    # S₀ = Σ_{k≡0(3)} C(q,k)(-1)^k
    # S₁ = Σ_{k≡1(3)} C(q,k)(-1)^k
    # S₂ = Σ_{k≡2(3)} C(q,k)(-1)^k
    # (1-ω)^q = S₀ + S₁·ω + S₂·(-1-ω) = (S₀ - S₂) + (S₁ - S₂)·ω
    # So c₀ = S₀ - S₂, c₁ = S₁ - S₂.

    print("  For q = 71, 1583 etc. these are HUGE numbers, but we can compute them mod A.\n")

    for q, A in primes[:5]:
        # Compute S₀, S₁, S₂ mod A
        S = [0, 0, 0]
        binom = 1
        for k in range(q + 1):
            sign = pow(-1, k)  # (-1)^k
            S[k % 3] = (S[k % 3] + sign * binom) % A
            binom = binom * (q - k) // (k + 1)  # next binomial coeff
            # This division might not be exact mod A. Let me use modular arithmetic.

        # Redo with modular arithmetic
        S = [0, 0, 0]
        binom = 1
        for k in range(q + 1):
            sign = 1 if k % 2 == 0 else -1
            S[k % 3] = (S[k % 3] + sign * binom) % A
            if k < q:
                binom = binom * (q - k) * pow(k + 1, A - 2, A) % A

        c0 = (S[0] - S[2]) % A
        c1 = (S[1] - S[2]) % A

        # Verify: c0 + c1*q should equal (1-q)^q mod A
        val = (c0 + c1 * q) % A
        direct = pow((1 - q) % A, q, A)
        print(f"  q={q}: c₀+c₁·q = {val}, (1-q)^q = {direct}, match: {val == direct}")
        print(f"    c₀ = {c0}, c₁ = {c1}")

    print("\n  The c₀, c₁ representation gives us the EISENSTEIN INTEGER (1-ω)^q mod A.")
    print("  But we need properties of (1-ω)^q BEFORE reducing, which requires the actual")
    print("  integer values, not just their residues.\n")

    print("=" * 80)
    print("SECTION 8: Norm constraint approach")
    print("=" * 80)

    print("\n  In Z[ω]: N((1-ω)^q) = 3^q (as integers).")
    print("  (1-ω)^q = c₀ + c₁ω. N(c₀ + c₁ω) = c₀² - c₀c₁ + c₁² = 3^q.")
    print("  This is a Diophantine equation: c₀² - c₀c₁ + c₁² = 3^q.\n")
    print("  The solutions are known: they correspond to representations of 3^q as norms.")
    print("  3^q = (1-ω)^q · (1-ω²)^q in Z[ω].")
    print("  The factorization in Z[ω] is unique (up to units ±1, ±ω, ±ω²).\n")

    print("  Now: 3^q ≡ 1 mod A in Z iff A | (3^q - 1) iff (q-ω)(q-ω²) | (3^q - 1) in Z[ω].")
    print("  3^q - 1 = (1-ω)^q(1-ω²)^q - 1.")
    print("  For (q-ω) | ((1-ω)^q(1-ω²)^q - 1):")
    print("  (1-ω)^q(1-ω²)^q ≡ 1 mod (q-ω).")
    print("  But (1-ω) ≡ (1-q) mod (q-ω) and (1-ω²) ≡ (1-q²) ≡ (q+2) mod (q-ω).")
    print("  So (1-q)^q(q+2)^q ≡ 1 mod (q-ω), which is just 3^q ≡ 1 mod A. Circular.\n")

    print("=" * 80)
    print("SECTION 9: Valuation approach — v_π(3^q - 1)")
    print("=" * 80)

    print("\n  Let π₃ = 1-ω. In Z[ω], 3 = -ω²π₃² and π₃ has norm 3.")
    print("  3^q - 1 = (-ω²)^q · π₃^{2q} - 1.")
    print("  q ≡ 2 mod 3 → (-ω²)^q = (-1)^q · ω^{2q} = -ω^{2q}.")
    print("  2q mod 3: q ≡ 2 → 2q ≡ 1 → ω^{2q} = ω.")
    print("  So (-ω²)^q = -ω.")
    print("  3^q - 1 = -ω · π₃^{2q} - 1.\n")

    print("  v_{π₃}(3^q - 1): since -ω is a unit and π₃^{2q} has π₃-valuation 2q,")
    print("  the term -ω·π₃^{2q} has v_{π₃} = 2q. And -1 has v_{π₃} = 0.")
    print("  So v_{π₃}(3^q - 1) = min(2q, 0) = 0.")
    print("  This means π₃ ∤ (3^q - 1), so 3 ∤ (3^q - 1).")
    print("  Consistent: 3^q ≡ 0 ≢ 1 mod 3.\n")

    print("  v_{π_A}(3^q - 1) ≥ 1 iff A | (3^q - 1) in Z iff 3^q ≡ 1 mod A.")
    print("  This is exactly what we want to disprove.\n")

    print("=" * 80)
    print("SECTION 10: HYBRID approach — combine two characters")
    print("=" * 80)

    print("\n  We know:")
    print("  - (3/A)₂ = 1 always (3 is QR)")
    print("  - (3/A)₃ = 1 always (3 is cubic residue)")
    print("  - (3/A)₄ = 1 always")
    print("  - (3/A)₆ = 1 always")
    print("  - (3/A)₁₂ = 1 always")
    print("  - (3/A)₂₄ varies (14/28 = 50%)")
    print("  - (3/A)₈ varies")
    print("  - (3/A)₉ varies\n")

    print("  The issue: no SINGLE character universally obstructs 3^q = 1.")
    print("  But maybe a PRODUCT or RATIO of characters does?\n")

    print("  For instance: the Jacobi symbol approach.")
    print("  Consider (-3/A). Since -3 = (1-q)² / q ... hmm.")
    print("  Actually: (-3/A) = (-1/A)·(3/A) = 1·1 = 1 (since A ≡ 1 mod 4 and 3).\n")

    print("  What about (q+1/A)? This is the Legendre symbol.")
    for q, A in primes[:10]:
        js = jacobi_symbol(q + 1, A)
        print(f"  q={q}: (q+1/A) = {js}")

    print("\n  Varies. What about the quartic character of (q+1)?")
    for q, A in primes[:10]:
        val = pow(q + 1, (A - 1) // 4, A)
        print(f"  q={q}: (q+1)^((A-1)/4) = {val} {'=1' if val == 1 else ''}")

    print("\n  (q+1) is always a 4th power residue mod A? Let me check systematically.")
    qp1_4th = all(pow(q + 1, (A - 1) // 4, A) == 1 for q, A in primes)
    print(f"  (q+1) is always a 4th power res? {qp1_4th}")

    # Actually we proved (q+1)^{(q+1)/2} = 1, so (q+1)^{q(q+1)/2} = [(q+1)^{(q+1)/2}]^q = 1.
    # (A-1)/2 = q(q+1)/2. So (q+1)^{(A-1)/2} = 1. QR.
    # (A-1)/4 = q(q+1)/4. (q+1)^{q(q+1)/4} = [(q+1)^{(q+1)/4}]^q.
    # And (q+1)^{(q+1)/4} = (-q²)^{(q+1)/4} = q^{(q+1)/2} (since (-1)^{(q+1)/4} = 1).
    # q^{(q+1)/2}: (q+1)/2 mod 3 = 0/2 = 0 (since 3|(q+1)). So q^{(q+1)/2} = 1.
    # Hence (q+1)^{(A-1)/4} = 1. Always.

    print("\n  This is because (q+1) = -q² and powers of q are periodic mod 3.")

    print("\n" + "=" * 80)
    print("SECTION 11: Focus on SPECIFIC obstruction — what prime p divides d always?")
    print("=" * 80)

    print("\n  Recall from the deep exploration: d = ord(3)/q varies wildly.")
    print("  No single small prime always divides d.")
    print("  But d > 1 ALWAYS. The minimum was d = 3.\n")

    print("  d = 3 means 3^{3q} = 1 but 3^q ≠ 1. So 3^q is a primitive cube root of 1.")
    print("  This happens for q = 71 (d=3) and q = 3671 (d=9, not 3).\n")

    print("  d = 3: 3^q is a primitive cube root of unity mod A.")
    print("  The cube roots of unity mod A are {1, q, q²} (since q³ = 1 mod A).")
    print("  So d = 3 means 3^q ∈ {q, q²}.\n")

    for q, A in primes[:5]:
        three_q = pow(3, q, A)
        q_mod = q % A
        q2_mod = pow(q, 2, A)
        print(f"  q={q}: 3^q = {three_q}, q = {q_mod}, q² = {q2_mod}")
        if three_q == q_mod:
            print(f"    3^q = q! So log_g(3^q) ≡ log_g(q) mod (A-1)")
        elif three_q == q2_mod:
            print(f"    3^q = q²!")

    print("\n  For q=71: 3^q = 5041 = q². So 3^q = q² when d = 3.")
    print("  Since q³ = 1 and 3^{3q} = 1, and 3^q = q²: 3^{2q} = (3^q)² = q⁴ = q.")
    print("  So 3^{3q} = 3^q · 3^{2q} = q² · q = q³ = 1. ✓\n")

    print("  The interesting question: can we show 3^q ∉ {1} universally?")
    print("  We need: 3^q mod A ≠ 1. This is just our original problem.\n")

    print("=" * 80)
    print("SECTION 12: ACTUAL new approach — analytic/Weil bound")
    print("=" * 80)

    print("\n  Character sum approach: Consider the sum")
    print("  S = Σ_{t=0}^{q-1} χ(3^t - 1) where χ is a character of order (q+1).")
    print("  By the Polya-Vinogradov inequality: |S| ≤ √A · log A.")
    print("  This counts t with 3^t ≡ 1 mod A in a way weighted by χ.")
    print("  But this doesn't directly help prove 3^q ≠ 1.\n")

    print("  Weil bound for character sums: if f(x) is a polynomial of degree d,")
    print("  |Σ_{x ∈ F_A} χ(f(x))| ≤ (d-1)√A.")
    print("  Not directly applicable to exponential 3^q.\n")

    print("=" * 80)
    print("SECTION 13: Different angle — (q+2)^{q+1} in the q-torsion")
    print("=" * 80)

    print("\n  (q+2)^{q+1} is the projection of (q+2) onto the q-torsion subgroup C_q.")
    print("  (q+2) = (1-q²) = -(q-1)(q+1). So:")
    print("  (q+2)^{q+1} = [-(q-1)(q+1)]^{q+1} = (-1)^{q+1}(q-1)^{q+1}(q+1)^{q+1}")
    print("  = (q-1)^{q+1} · 1  [since (-1)^{q+1} = 1, (q+1)^{q+1} = 1 as shown]")
    print("  = (q-1)^{q+1}.\n")

    print("  Now (q-1) mod A: q-1 is just q-1.")
    print("  (q-1)^{q+1}: (q-1) = (q-1). Let's compute the order of (q-1) in C_q.")

    for q, A in primes[:10]:
        val = pow(q - 1, q + 1, A)
        print(f"  q={q}: (q-1)^(q+1) = {val}")

        # Is this a primitive element of C_q?
        val_q = pow(val, q, A)
        print(f"    [(q-1)^(q+1)]^q = {val_q} (should be 1)")

    print("\n  So under assumption 3^q = 1:")
    print("  (q-1)^{q+1} = α (some element of C_q)")
    print("  and 3^{(q-1)/2} = α^{-1}.")
    print("  So 3^{(q-1)/2} = [(q-1)^{q+1}]^{-1} = (q-1)^{-(q+1)}.\n")

    print("  Under 3^q = 1: 3^{(q-1)/2} · (q-1)^{q+1} = 1 mod A.\n")

    # Test this necessary condition
    print("  Testing necessary condition: 3^{(q-1)/2} · (q-1)^{q+1} = 1 mod A:")
    for q, A in primes[:15]:
        val = (pow(3, (q-1)//2, A) * pow(q-1, q+1, A)) % A
        print(f"  q={q}: 3^((q-1)/2) · (q-1)^(q+1) = {val} "
              f"{'= 1' if val == 1 else '≠ 1 → 3^q ≠ 1!'}")

    # Extended check
    extended = find_eligible_primes(200000)
    never_1_count = 0
    eq_1_count = 0
    for q, A in extended:
        val = (pow(3, (q-1)//2, A) * pow(q-1, q+1, A)) % A
        if val == 1:
            eq_1_count += 1
        else:
            never_1_count += 1

    print(f"\n  Extended ({len(extended)} primes): = 1: {eq_1_count}, ≠ 1: {never_1_count}")
    if eq_1_count == 0:
        print("  *** UNIVERSAL: 3^{(q-1)/2} · (q-1)^{q+1} ≠ 1 for ALL tested primes! ***")
        print("  Since this is NECESSARY for 3^q = 1, we have 3^q ≠ 1 ALWAYS.")
        print("\n  CAN WE PROVE THIS?")
        print("  3^{(q-1)/2} · (q-1)^{q+1} ≠ 1 mod A where A = q²+q+1.")
        print("  Equivalently: 3^{(q-1)/2} ≠ (q-1)^{-(q+1)} mod A.")
    else:
        print("  Not universal. Try something else.")

    print("\n" + "=" * 80)
    print("SECTION 14: Even simpler necessary conditions from the formula")
    print("=" * 80)

    print("\n  From (1-q)^q = (q+2) · 3^{(q-1)/2}:")
    print("  Raise both sides to (q+1):")
    print("  (1-q)^{q(q+1)} = (q+2)^{q+1} · 3^{(q-1)(q+1)/2}")
    print("  LHS = (1-q)^{A-1} = 1.")
    print("  RHS = (q+2)^{q+1} · 3^{(q²-1)/2}.")
    print("  So (q+2)^{q+1} · 3^{(q²-1)/2} = 1 mod A.\n")

    print("  Verify:")
    for q, A in primes[:10]:
        lhs = (pow((q+2) % A, q+1, A) * pow(3, (q*q-1)//2, A)) % A
        print(f"  q={q}: (q+2)^(q+1) · 3^((q²-1)/2) = {lhs}")

    print("\n  This is always 1 (it's a tautology from Fermat's little theorem).")
    print("  Not useful.\n")

    print("  From (1-q)^q = (q+2) · 3^{(q-1)/2}, raise to 2:")
    print("  (1-q)^{2q} = (q+2)² · 3^{q-1} = 3(q+1) · 3^{q-1} = 3^q · (q+1).")
    print("  So (1-q)^{2q} = 3^q · (q+1).")
    print("  Equivalently: 3^q = (1-q)^{2q} / (q+1). Already known.\n")

    print("  Under 3^q = 1: (1-q)^{2q} = (q+1).")
    print("  Under 3^q = 1: (1-q)^{2q} has order dividing (q+1) in (Z/AZ)*.")
    print("  (1-q)^{2q} = (q+1) means the element is specifically (q+1), not just any")
    print("  element of the (q+1)-torsion.\n")

    print("  Can we show (1-q)^{2q} ≠ (q+1)?")
    for q, A in primes[:10]:
        one_mq = (1 - q) % A
        val = pow(one_mq, 2*q, A)
        qp1 = (q + 1) % A
        print(f"  q={q}: (1-q)^(2q) = {val}, q+1 = {qp1}, equal? {val == qp1}")

    print("\n  Of course they're not equal (since 3^q ≠ 1).")
    print("  But proving this algebraically is equivalent to proving 3^q ≠ 1. Circular.\n")

    print("=" * 80)
    print("SECTION 15: Distribution of 3^q mod A in the (q+1)-torsion")
    print("=" * 80)

    print("\n  3^q mod A has order d dividing (q+1). Let's see its distribution")
    print("  relative to (q+1)-th roots of unity.\n")

    for q, A in primes[:10]:
        three_q = pow(3, q, A)
        # The (q+1)-torsion is the unique subgroup of order (q+1).
        # 3^q is in this subgroup. What's its discrete log relative to a generator?
        # Generator of (q+1)-torsion: g^q where g is a primitive root of A.
        g = primitive_root(A)
        gen = pow(g, q, A)  # has order (q+1)

        # Find log of three_q base gen in the (q+1)-torsion
        idx = None
        val = 1
        for j in range(q + 1):
            if val == three_q:
                idx = j
                break
            val = (val * gen) % A

        print(f"  q={q}: 3^q = gen^{idx} in C_{{q+1}} (q+1={q+1})")
        if idx is not None:
            # Factors of idx and q+1
            gcd_val = 1
            t = idx
            for p in factorint(q+1):
                while t % p == 0:
                    t //= p
            # Actually just compute gcd
            from math import gcd
            g_val = gcd(idx, q+1)
            print(f"    gcd(idx, q+1) = {g_val}, ord(3^q) = {(q+1)//g_val}")

    print("\n" + "=" * 80)
    print("SECTION 16: Trying 3^q ≡ -3q(q+1)^{-1} · (-27)^{(q-2)/3} approach")
    print("=" * 80)

    print("\n  We have 3^q = -9 · (-27)^{(q-2)/3} mod A.")
    print("  -9 = -9. -27 = -27. These are FIXED integers, not depending on q.")
    print("  A varies with q. So 3^q mod A = (-9 · (-27)^{(q-2)/3}) mod (q²+q+1).\n")

    print("  Key: (-27)^{(q-2)/3} mod (q²+q+1).")
    print("  This is a modular exponentiation of a FIXED base with the modulus q-dependent.")
    print("  For 3^q = 1: (-27)^{(q-2)/3} ≡ -9^{-1} mod (q²+q+1).")
    print("  9^{-1} mod A: 9 · x ≡ 1 mod A, x = (A+1)/9 if 9|(A+1).")
    print("  A+1 = q²+q+2. q ≡ 8 mod 9 → q² ≡ 1 → q²+q+2 ≡ 1+8+2 = 11 ≡ 2 mod 9.")
    print("  So 9 ∤ (A+1). Compute 9^{-1} differently.")

    for q, A in primes[:5]:
        inv9 = pow(9, A-2, A)
        neg_inv9 = (-inv9) % A
        rhs = neg_inv9
        n = (q-2)//3
        lhs = pow((-27) % A, n, A)
        print(f"  q={q}: (-27)^n = {lhs}, -9^(-1) = {rhs}, equal? {lhs == rhs} (would mean 3^q=1)")

    print("\n  For small q = 71: (-27)^23 mod 5113 vs -9^{-1} mod 5113")
    A71 = 5113
    val1 = pow((-27) % A71, 23, A71)
    val2 = (-pow(9, A71-2, A71)) % A71
    print(f"  (-27)^23 mod 5113 = {val1}")
    print(f"  -9^(-1) mod 5113 = {val2}")
    print(f"  Equal? {val1 == val2}")

    print("\n" + "=" * 80)
    print("SECTION 17: Universal obstruction — small prime factors")
    print("=" * 80)

    print("\n  For each q, which prime factor of (q+1) provides the obstruction?")
    print("  i.e., for which p | (q+1) is 3^{q·(q+1)/p} ≠ 1?\n")

    obstruction_data = []
    for q, A in primes[:30]:
        qp1 = q + 1
        qp1_f = factorint(qp1)
        obs = []
        for p_exp in sorted(qp1_f.keys()):
            exp_val = q * (qp1 // p_exp)
            val = pow(3, exp_val, A)
            if val != 1:
                obs.append(p_exp)
        # smallest obstruction
        smallest = min(obs) if obs else None
        obstruction_data.append((q, qp1, obs, smallest))

    for q, qp1, obs, sm in obstruction_data:
        print(f"  q={q}: q+1={qp1}, obstruction primes: {obs}, smallest: {sm}")

    # Distribution of smallest obstruction
    sm_counter = Counter(sm for _, _, _, sm in obstruction_data if sm is not None)
    print(f"\n  Smallest obstruction distribution: {dict(sorted(sm_counter.items()))}")

    print("\n  The smallest obstruction is ALWAYS ≤ some bound? Let's check:")
    all_smallest = [sm for _, _, _, sm in obstruction_data if sm is not None]
    print(f"  Max smallest obstruction: {max(all_smallest)}")
    print(f"  Min: {min(all_smallest)}")

    # Extended
    print("\n  Extended to all primes q < 100000:")
    all_smallest_ext = []
    for q, A in primes:
        qp1 = q + 1
        qp1_f = factorint(qp1)
        obs = []
        for p_exp in sorted(qp1_f.keys()):
            exp_val = q * (qp1 // p_exp)
            val = pow(3, exp_val, A)
            if val != 1:
                obs.append(p_exp)
        if obs:
            all_smallest_ext.append(min(obs))
        else:
            print(f"  *** NO OBSTRUCTION for q={q}! 3^q = 1??? ***")

    if all_smallest_ext:
        sm_ext_counter = Counter(all_smallest_ext)
        print(f"\n  Distribution: {dict(sorted(sm_ext_counter.items()))}")
        print(f"  Max smallest: {max(all_smallest_ext)}")
        # The key: is the max bounded?

if __name__ == '__main__':
    main()
