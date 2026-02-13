#!/usr/bin/env python3
"""
Feit-Thompson p=3 q≡71 mod 72: FINAL focused exploration

KEY FINDINGS from rounds 1&2:
1. 3 is ALWAYS a 12th power residue (so low-order characters don't help)
2. d = ord(3)/q is ALWAYS > 1 (d ≥ 3), confirming 3^q ≠ 1
3. d = ord(3)/q is NEVER divisible by ALL primes of (q+1) — it varies wildly
4. No single prime p always provides an obstruction
5. The 2-adic gap v₂(q+1) - v₂(d) is always ≥ 2
6. The 3-adic gap v₃(q+1) - v₃(d) is always ≥ 1

NEW FOCUS:
- The 2-adic gap being ≥ 2 means 3^{(A-1)/4} = 1 always (4th power residue)
  But 3 is NOT always an 8th power residue.
  Similarly, 3 is always a 9th power residue? Let's check.
- Can we use algebraic identities to prove d > 1 without pinpointing WHICH prime?
- What about the STRUCTURE of g = 3^q as an element of the (q+1)-torsion subgroup?
"""

from sympy import isprime, factorint, primitive_root
from sympy.ntheory import discrete_log
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
    print("SECTION 1: Key algebraic identity — what IS 3^q in closed form?")
    print("=" * 80)

    print("\n  3 = (1-q)(1-q²) mod A. So 3^q = (1-q)^q · (1-q²)^q.")
    print("  We know: (1-q)^6 = -27 mod A.")
    print("  Write q = 6m + r where r = q mod 6.")
    print("  q ≡ 5 mod 6 (since q ≡ -1 mod 6).")
    print("  So q = 6m + 5, and (1-q)^q = (1-q)^{6m+5} = (-27)^m · (1-q)^5.\n")

    for q, A in primes[:15]:
        one_mq = (1 - q) % A
        m = q // 6
        r = q % 6
        assert r == 5

        val_direct = pow(one_mq, q, A)
        val_formula = (pow(-27 % A, m, A) * pow(one_mq, 5, A)) % A
        match = val_direct == val_formula

        # (1-q)^5 = (1-q)^4 · (1-q) = -9(q+1) · (1-q) = -9(q+1)(1-q)
        # = -9(q + 1 - q² - q) = -9(1 - q²) = -9(q+2) [since q² = -q-1, 1-q² = q+2]
        val5 = pow(one_mq, 5, A)
        val5_formula = (-9 * (q + 2)) % A
        match5 = val5 == val5_formula

        print(f"  q={q}: (1-q)^q via (-27)^m·(1-q)^5: match={match}, "
              f"(1-q)^5 = -9(q+2)? {match5}")

    print("\n  So (1-q)^q = (-27)^{(q-5)/6} · (-9)(q+2)")
    print("  = (-1)^{(q-5)/6} · 27^{(q-5)/6} · (-9)(q+2)")
    print("  = (-1)^{(q-5)/6+1} · 9 · 27^{(q-5)/6} · (q+2)")
    print("  = (-1)^{(q+1)/6} · 9 · 3^{(q-5)/2} · (q+2)")
    print("  since 27^{(q-5)/6} = 3^{3(q-5)/6} = 3^{(q-5)/2}")

    print("\n  Similarly (1-q²)^q = (q+2)^q. Let's find a formula for this too.")
    print("  1-q² = q+2 mod A. And (q+2) = -(q²-1) = -(q-1)(q+1).")
    print("  (q+2)^6 = [(q+2)^2]^3. (q+2)^2 = q²+4q+4 = (-q-1)+4q+4 = 3q+3 = 3(q+1).")
    print("  (q+2)^4 = [3(q+1)]^2 = 9(q+1)² = 9(q²+2q+1) = 9(-q-1+2q+1) = 9q.")
    print("  (q+2)^6 = (q+2)^4 · (q+2)^2 = 9q · 3(q+1) = 27q(q+1) = 27(A-1).")
    print("  But A-1 ≡ -1 mod A! So (q+2)^6 = 27·(-1) = -27 mod A.\n")

    for q, A in primes[:10]:
        qp2 = (q + 2) % A
        val6 = pow(qp2, 6, A)
        neg27 = (-27) % A
        print(f"  q={q}: (q+2)^6 mod A = {val6}, -27 mod A = {neg27}, match: {val6 == neg27}")

    print("\n  Both (1-q)^6 and (q+2)^6 equal -27 mod A!")
    print("  So [(1-q)(q+2)]^6 = (-27)² = 729 = 3^6 mod A. Consistent (3^6 = 729).")

    print("\n  Now: (q+2)^q = (-27)^{(q-5)/6} · (q+2)^5")
    print("  (q+2)^5 = (q+2)^4 · (q+2) = 9q · (q+2) = 9q(q+2) = 9(q²+2q) = 9(-q-1+2q) = 9(q-1).")

    for q, A in primes[:10]:
        qp2 = (q + 2) % A
        val5 = pow(qp2, 5, A)
        formula = (9 * (q - 1)) % A
        print(f"  q={q}: (q+2)^5 = {val5}, 9(q-1) = {formula}, match: {val5 == formula}")

    print("\n" + "=" * 80)
    print("SECTION 2: Closed form for 3^q")
    print("=" * 80)

    print("\n  3^q = (1-q)^q · (q+2)^q")
    print("  = [(-27)^m · (-9)(q+2)] · [(-27)^m · 9(q-1)]")
    print("  = (-27)^{2m} · (-9)(q+2) · 9(q-1)")
    print("  = 729^m · (-81) · (q+2)(q-1)")
    print("  = 3^{6m} · (-81) · (q²+q-2)")
    print("  = 3^{q-5} · (-81) · (A - 3)")
    print("  since q²+q-2 = (q²+q+1) - 3 = A - 3")
    print("  = 3^{q-5} · (-81) · (-3) mod A   [since A ≡ 0, A-3 ≡ -3]")
    print("  = 3^{q-5} · 243")
    print("  = 3^{q-5} · 3^5")
    print("  = 3^q")
    print("  ...tautology! The algebraic identity is consistent but gives no info.")

    print("\n  Let me redo this more carefully WITHOUT using 3^{6m} = 3^{q-5}:\n")
    print("  3^q = (-27)^{2m} · (-81) · (-3)")
    print("  where m = (q-5)/6.")
    print("  (-27)^{2m} = 27^{2m} · (-1)^{2m} = 27^{2m} = 3^{6m} = 3^{q-5}.")
    print("  So 3^q = 3^{q-5} · 243 = 3^{q-5} · 3^5 = 3^q. Indeed tautological.\n")

    print("  The ISSUE: we factored 3 = (1-q)(q+2) and computed each factor's q-th power,")
    print("  but the result collapsed. We need a different decomposition.\n")

    print("=" * 80)
    print("SECTION 3: Alternative — 3^q via 3 = (1-q)²/(-q) or 3 = -(1-q)²/q")
    print("=" * 80)

    print("\n  (1-q)² = -3q → 3 = -(1-q)²/q → 3^q = (-(1-q)²)^q / q^q")
    print("  = (-1)^q · (1-q)^{2q} / q^q")
    print("  = -(1-q)^{2q} · q^{-q} mod A  [since q odd, (-1)^q = -1]")
    print("  = -(1-q)^{2q} / q^q\n")

    print("  Now q^q mod A: since q³ ≡ 1 mod A, q^q = q^{q mod 3}.")
    print("  q ≡ 2 mod 3 → q^q = q² = -q-1 mod A.\n")

    for q, A in primes[:10]:
        qq = pow(q, q, A)
        q2 = pow(q, 2, A)  # = (-q-1) mod A
        neg_q_minus_1 = (-q - 1) % A
        print(f"  q={q}: q^q = {qq}, q² = {q2}, -q-1 = {neg_q_minus_1}, "
              f"match: {qq == neg_q_minus_1}")

    print("\n  So 3^q = -(1-q)^{2q} / (-q-1) = (1-q)^{2q} / (q+1) mod A")

    for q, A in primes[:10]:
        one_mq = (1 - q) % A
        val_2q = pow(one_mq, 2*q, A)
        qp1_inv = pow(q + 1, A - 2, A)
        formula_val = (val_2q * qp1_inv) % A
        three_q = pow(3, q, A)
        print(f"  q={q}: (1-q)^{{2q}}/(q+1) = {formula_val}, 3^q = {three_q}, match: {formula_val == three_q}")

    print("\n  KEY FORMULA: 3^q ≡ (1-q)^{2q} / (q+1) mod A")
    print("  So 3^q = 1 iff (1-q)^{2q} ≡ (q+1) mod A")
    print("  Recall from the problem context: under the ASSUMPTION 3^q = 1,")
    print("  (1-q)^{2q} = q+1 was given as a known identity. This confirms it.\n")

    print("  Now: (1-q)^{2q} = [(1-q)^6]^{(2q-r)/6} · (1-q)^r where r = 2q mod 6.")
    print("  2q mod 6: q ≡ 5 mod 6 → 2q ≡ 10 ≡ 4 mod 6. So r = 4.")
    print("  (1-q)^{2q} = (-27)^{(2q-4)/6} · (1-q)^4 = (-27)^{(q-2)/3} · (-9)(q+1)")
    print("  [since (1-q)^4 = -9(q+1)]")

    for q, A in primes[:10]:
        one_mq = (1 - q) % A
        val_2q = pow(one_mq, 2*q, A)
        m2 = (q - 2) // 3
        assert (q - 2) % 3 == 0  # q ≡ 2 mod 3
        formula = (pow((-27) % A, m2, A) * ((-9 * (q + 1)) % A)) % A
        print(f"  q={q}: (1-q)^{{2q}} = {val_2q}, (-27)^{{(q-2)/3}}·(-9)(q+1) = {formula}, "
              f"match: {val_2q == formula}")

    print("\n  So 3^q = 1 iff (-27)^{(q-2)/3} · (-9)(q+1) ≡ (q+1) mod A")
    print("  iff (-27)^{(q-2)/3} · (-9) ≡ 1 mod A  [dividing by q+1, which is nonzero]")
    print("  iff (-27)^{(q-2)/3} ≡ -1/9 mod A")
    print("  iff (-27)^{(q-2)/3} ≡ -9^{-1} mod A")
    print("  iff (-1)^{(q-2)/3} · 27^{(q-2)/3} ≡ -9^{-1} mod A")
    print("  iff (-1)^{(q-2)/3} · 3^{q-2} ≡ -3^{-2} mod A")
    print("  iff (-1)^{(q-2)/3} · 3^q ≡ -1 mod A")
    print("  ...circular again with 3^q.\n")

    print("  Let me try a different manipulation. We have:")
    print("  3^q = 1 iff (-27)^{(q-2)/3} = -1/9 = -(3^{-2}) mod A")
    print("  Set n = (q-2)/3. Then:")
    print("  (-27)^n = -3^{-2} mod A")
    print("  (-1)^n · 3^{3n} = -3^{-2}")
    print("  (-1)^n · 3^{3n+2} = -1")
    print("  3n+2 = 3·(q-2)/3 + 2 = q-2+2 = q")
    print("  So (-1)^n · 3^q = -1")
    print("  If 3^q = 1: (-1)^n = -1, i.e., n is odd.")
    print("  n = (q-2)/3. q ≡ 71 mod 72. n = (71-2)/3 = 23 mod 24. n ≡ 23 mod 24.")
    print("  23 is odd. So the condition is consistent. Tautological again.\n")

    print("=" * 80)
    print("SECTION 4: Discrete log approach — CRT decomposition")
    print("=" * 80)

    print("\n  (Z/AZ)* has order A-1 = q(q+1). Since gcd(q, q+1) = 1,")
    print("  (Z/AZ)* ≅ C_q × C_{q+1} (as abstract groups).")
    print("  3^q = 1 iff the projection of 3 onto C_{q+1} is trivial.")
    print("  i.e., iff log_g(3) ≡ 0 mod (q+1).\n")

    print("  Computing log_g(3) mod (q+1) for small primes:")

    dl_mod_qp1_vals = []
    for q, A in primes[:12]:
        g = primitive_root(A)
        try:
            dl = discrete_log(A, 3, g)
            r = dl % (q + 1)
            dl_mod_qp1_vals.append((q, r, q+1, dl))
            print(f"  q={q}: log_g(3) = {dl}, mod (q+1)={q+1}: {r}")
        except Exception as e:
            print(f"  q={q}: failed ({e})")

    print("\n  log_g(3) mod q (should be nonzero since 3^{q+1} ≠ 1 usually):")
    for q, r, qp1, dl in dl_mod_qp1_vals:
        rq = dl % q
        print(f"  q={q}: log_g(3) mod q = {rq}")

    print("\n" + "=" * 80)
    print("SECTION 5: Gauss period approach")
    print("=" * 80)

    print("\n  The cubic Gauss period η = q + q² is an element of Z.")
    print("  Since q + q² = q + (-q-1) = -1 mod A.")
    print("  So η = -1 mod A. Not helpful directly.\n")

    print("  The 'sextic period' with generator of order (q+1)/6:")
    print("  Since 6 | (q+1), let h be an element of order (q+1)/6 in the")
    print("  (q+1)-torsion of (Z/AZ)*.")
    print("  Actually, Gauss periods relate to subfields of cyclotomic fields,")
    print("  not directly to our setting.\n")

    print("=" * 80)
    print("SECTION 6: Stickelberger / Gauss sum approach")
    print("=" * 80)

    print("\n  Key idea: In Z[ω], the prime π = 1-ω above 3 satisfies π·π̄ = 3.")
    print("  The Gauss sum g(χ) for a character χ of order 3 mod A satisfies:")
    print("  g(χ)³ = A · J(χ,χ) where J is the Jacobi sum.")
    print("  |g(χ)|² = A.\n")

    print("  For our purposes: the cubic residue symbol (3/π_A)₃ where π_A = q-ω")
    print("  can be computed via: (3/π_A)₃ = 3^{(A-1)/3} mod π_A.")
    print("  In Z/AZ: 3^{(A-1)/3} = 3^{q(q+1)/3}.\n")

    print("  q+1 ≡ 0 mod 72 → q+1 ≡ 0 mod 3 → (q+1)/3 is integer.")
    print("  3^{q(q+1)/3} = (3^q)^{(q+1)/3}.")
    print("  If 3^q = 1: (3^q)^{(q+1)/3} = 1. So (3/π_A)₃ = 1.\n")
    print("  We already confirmed 3 is always a cubic residue. Consistent.\n")

    print("  Stickelberger's theorem: In Z[ω], for prime π_A of norm A,")
    print("  the Gauss sum τ(χ) satisfies τ(χ)^{1+σ+σ²} = (-1)·A")
    print("  where σ is the Galois automorphism ω → ω².\n")

    print("  This gives a constraint on the factorization of Gauss sums in Z[ω],")
    print("  but it's not clear how to use it for our specific problem.\n")

    print("=" * 80)
    print("SECTION 7: Completely new approach — norm equations")
    print("=" * 80)

    print("\n  If 3^q = 1 mod A, then in Z[ω]: (1-ω)^q · (1-ω²)^q ≡ 1 mod π_A")
    print("  where π_A = q - ω.")
    print("  This means: (π₃)^q · (π̄₃)^q ≡ 1 mod π_A")
    print("  i.e., N(π₃)^q ≡ 1 mod π_A, i.e., 3^q ≡ 1 mod π_A. (Tautological.)\n")

    print("  But what about working in Z[ω] directly (not reducing mod π_A)?")
    print("  (1-ω)^q in Z[ω]: this is a specific element.")
    print("  (1-ω) = π₃. π₃^q in Z[ω] is some element a + bω.")
    print("  Its reduction mod π_A gives (1-q)^q mod A.\n")

    print("  Can we compute π₃^q = (1-ω)^q in Z[ω]?")
    print("  Using binomial theorem: (1-ω)^q = Σ C(q,k)(-ω)^k = Σ C(q,k)(-1)^k ω^k")
    print("  Group by ω^k mod (ω² + ω + 1 = 0):")
    print("  = [Σ_{k≡0(3)} C(q,k)(-1)^k] + [Σ_{k≡1(3)} C(q,k)(-1)^k]ω")
    print("    + [Σ_{k≡2(3)} C(q,k)(-1)^k]ω²")
    print("  Replace ω² = -ω - 1:")
    print("  = [S₀ - S₂] + [S₁ - S₂]ω")
    print("  where S_j = Σ_{k≡j(3)} C(q,k)(-1)^k.\n")

    print("  By roots of unity filter:")
    print("  S₀ = [0^q + (1-ω)^q + (1-ω²)^q]/3")
    print("  where the first 0^q = 0 (since (1-1)^q = 0).")
    print("  But (1-ω)^q and (1-ω²)^q are exactly what we want to compute! Circular.\n")

    print("  However, we can compute S₀, S₁, S₂ mod 3 easily:")
    print("  C(q,k) mod 3: by Lucas' theorem, depends on base-3 digits of q and k.")
    print("  q ≡ 2 mod 3. In base 3: q = ...d₂d₁·2 (last digit is 2).")
    print("  q ≡ 8 mod 9: second-to-last digit is 2 as well (8 = 2·3 + 2).")
    print("  So q in base 3 ends in ...22.\n")

    for q, _ in primes[:10]:
        # Base 3 representation
        digits = []
        t = q
        while t > 0:
            digits.append(t % 3)
            t //= 3
        print(f"  q={q} in base 3: {''.join(str(d) for d in reversed(digits))}")

    print("\n" + "=" * 80)
    print("SECTION 8: Trying the p-adic / lifting approach")
    print("=" * 80)

    print("\n  3-adic approach: v₃(3^q - 1) where 3^q is computed mod A.")
    print("  In Z: 3^q - 1 = (3-1)(3^{q-1} + ... + 1) = 2·(3^{q-1} + ... + 1).")
    print("  v₃(3^q - 1) = 0 since 3^q ≡ 0 mod 3 and 3^q - 1 ≡ -1 mod 3.")
    print("  So gcd(3^q - 1, 3) = 1. This doesn't constrain A.\n")

    print("  What about the order of 3 in the 3-adic integers?")
    print("  3 is not a unit in Z₃, so this doesn't make sense directly.\n")

    print("=" * 80)
    print("SECTION 9: Fermat quotient approach")
    print("=" * 80)

    print("\n  Fermat quotient: Q_A(3) = (3^{A-1} - 1) / A mod A.")
    print("  (A Wieferich-type quantity.)")
    print("  If 3^q = 1, then 3^{A-1} = 3^{q(q+1)} = (3^q)^{q+1} = 1, so Q_A(3) = 0.")
    print("  Can we show Q_A(3) ≠ 0? This is equivalent to showing 3^{A-1} ≢ 1 mod A².")
    print("  But 3^{A-1} = 1 mod A by Fermat, so 3^{A-1} = 1 + tA for some integer t.")
    print("  Q_A(3) = t mod A. This is hard to compute.\n")

    print("  Actually, showing Q_A(3) ≠ 0 would prove ord(3) = A-1 mod A,")
    print("  which is WAY stronger than what we need. Skip.\n")

    print("=" * 80)
    print("SECTION 10: Approaching via index theory — Ind(3) mod q and mod (q+1)")
    print("=" * 80)

    print("\n  Let g be a primitive root mod A. Write 3 = g^s.")
    print("  3^q = 1 iff q·s ≡ 0 mod (A-1) = q(q+1)")
    print("  iff s ≡ 0 mod (q+1).")
    print("  So we need: s ≢ 0 mod (q+1), i.e., Ind(3) ≢ 0 mod (q+1).\n")

    print("  Can we compute Ind(3) mod (q+1)?")
    print("  Note: 3^{(A-1)/2} = 3^{q(q+1)/2} mod A.")
    print("  This tells us the parity of Ind(3)/(q) component, but not directly mod (q+1).\n")

    print("  What CAN we compute? For each prime power p^a | (q+1):")
    print("  Ind(3) mod p^a ↔ 3^{(A-1)/p^a} mod A.\n")

    print("  Key: Ind(3) ≡ 0 mod (q+1) iff Ind(3) ≡ 0 mod p^a for ALL p^a || (q+1).")
    print("  So 3^q ≠ 1 iff for SOME p^a || (q+1), Ind(3) ≢ 0 mod p^a.")
    print("  i.e., 3^{q(q+1)/p^a} ≠ 1.\n")

    print("  We need to find, for each q, some p^a || (q+1) with 3^{q(q+1)/p^a} ≠ 1.")
    print("  The question: is there a UNIVERSAL such p^a that works for all q?")
    print("  From round 1: NO. The obstruction prime varies.\n")

    print("  BUT: maybe we can prove the obstruction EXISTS without identifying it?")
    print("  If we could show |{p^a || (q+1) : 3^{q(q+1)/p^a} = 1}| < ω(q+1)")
    print("  (i.e., not ALL prime powers provide consistency), that would suffice.")

    print("\n" + "=" * 80)
    print("SECTION 11: NEW IDEA — 3 as norm, multiplicative structure")
    print("=" * 80)

    print("\n  In Z[ω], 3 = π₃·π̄₃ where π₃ = 1-ω, π̄₃ = 1-ω².")
    print("  Reducing mod π_A = q-ω: π₃ → 1-q, π̄₃ → 1-q² = q+2.")
    print("  So in F_A: 3 = (1-q)(q+2), which we already know.\n")

    print("  Now consider: does (1-q) generate the whole group (Z/AZ)*?")
    print("  i.e., is (1-q) a primitive root mod A?\n")

    for q, A in primes[:15]:
        one_mq = (1 - q) % A
        am1 = A - 1
        am1_f = factorint(am1)
        is_prim = True
        for p in am1_f:
            if pow(one_mq, am1 // p, A) == 1:
                is_prim = False
                break
        ord_1mq = am1
        for p in am1_f:
            while ord_1mq % p == 0 and pow(one_mq, ord_1mq // p, A) == 1:
                ord_1mq //= p
        d_1mq = am1 // ord_1mq

        print(f"  q={q}: ord(1-q) = {ord_1mq}, A-1 = {am1}, "
              f"index = {d_1mq}, primitive? {is_prim}")

    print("\n" + "=" * 80)
    print("SECTION 12: BREAKTHROUGH IDEA — using (1-q)^q and (q+2)^q separately")
    print("=" * 80)

    print("\n  From Section 1: (1-q)^q = (-27)^m · (-9)(q+2) where m = (q-5)/6")
    print("  and (q+2)^q = (-27)^m · 9(q-1).")
    print("  3^q = (1-q)^q · (q+2)^q = (-27)^{2m} · (-81)(q+2)(q-1)")
    print("  = 27^{2m} · (-81)(q²-q-2+q) ... let me redo.\n")
    print("  (q+2)(q-1) = q² + q - 2 = A - 3 ≡ -3 mod A.")
    print("  So 3^q = (-27)^{2m} · (-81)·(-3) = (-27)^{2m} · 243.\n")
    print("  (-27)^{2m} = 729^m = 3^{6m} = 3^{q-5}.")
    print("  So 3^q = 3^{q-5} · 243 = 3^{q-5} · 3^5 = 3^q. Tautological again.\n")

    print("  The tautology happens because 3 = (1-q)(q+2) is a NORM.")
    print("  Any decomposition into conjugate pairs will be tautological.\n")
    print("  We need an approach that breaks the conjugation symmetry.\n")

    print("=" * 80)
    print("SECTION 13: ASYMMETRIC approach — work mod π_A in Z[ω]")
    print("=" * 80)

    print("\n  Instead of working in Z/AZ, work in Z[ω]/π_A ≅ F_A.")
    print("  The key: (1-ω)^q mod π_A = (1-q)^q mod A (already computed).")
    print("  But (1-ω̄)^q = (1-ω²)^q in Z[ω], which mod π_A gives (q+2)^q.\n")

    print("  In Z[ω]: N((1-ω)^q) = N(1-ω)^q = 3^q.")
    print("  (1-ω)^q = α where α ∈ Z[ω] with N(α) = 3^q.\n")

    print("  α mod π_A = (1-q)^q. α mod π̄_A = (1-q²)^q = (q+2)^q (different!).")
    print("  So knowing α mod π_A AND α mod π̄_A determines α mod A in Z[ω].\n")

    print("  But: α mod π_A · (ᾱ mod π_A) = N(α) mod A = 3^q mod A.")
    print("  And ᾱ mod π_A = conjugate(α) mod π_A = (1-ω²)^q mod π_A = (q+2)^q mod A.")
    print("  So (1-q)^q · (q+2)^q = 3^q mod A. Already known.\n")

    print("  The asymmetry: α mod π_A ≠ ᾱ mod π_A (in general).")
    print("  If 3^q = 1, then α · ᾱ ≡ 1 mod π_A, so ᾱ ≡ α^{-1} mod π_A.")
    print("  But α = (1-ω)^q and ᾱ = (1-ω²)^q.")
    print("  So (1-ω)^q · (1-ω²)^q ≡ 1 mod π_A → 3^q ≡ 1 mod A.\n")

    print("  We need to understand (1-ω)^q mod π_A = (1-q)^q mod A ALONE.")
    print("  (1-q)^q mod A = (-27)^{(q-5)/6} · (-9)(q+2)")
    print("  = (-1)^{(q-5)/6} · 27^{(q-5)/6} · (-9) · (q+2)")
    print("  = (-1)^{(q+1)/6} · 3^{(q-5)/2} · 9 · (q+2)")
    print("  [since (-1)^{(q-5)/6+1} = (-1)^{(q+1)/6}]\n")

    print("  Now: (q-5)/6 = (q+1)/6 - 1. (-1)^{(q-5)/6} = (-1)^{(q+1)/6 - 1}.")
    print("  = (-1)^{(q+1)/6} · (-1)^{-1} = -(-1)^{(q+1)/6}.\n")
    print("  So (1-q)^q = -(-1)^{(q+1)/6} · 3^{(q-5)/2} · (-9)(q+2)")
    print("  = (-1)^{(q+1)/6} · 3^{(q-5)/2} · 9 · (q+2)")
    print("  = (-1)^{(q+1)/6} · 3^{(q-1)/2} · (q+2)\n")

    print("  Checking this formula:")
    for q, A in primes[:10]:
        one_mq = (1 - q) % A
        val_q = pow(one_mq, q, A)

        sign = pow(-1, (q+1)//6) % A  # (-1)^{(q+1)/6}
        three_half = pow(3, (q-1)//2, A)
        formula = (sign * three_half * ((q + 2) % A)) % A

        print(f"  q={q}: (1-q)^q = {val_q}, (-1)^{{(q+1)/6}} · 3^{{(q-1)/2}} · (q+2) = {formula}, "
              f"match: {val_q == formula}")

    print("\n  CLEAN FORMULA: (1-q)^q ≡ (-1)^{(q+1)/6} · 3^{(q-1)/2} · (q+2) mod A")
    print("  And 3^{(q-1)/2} = (3/A) = Legendre symbol = +1 (since A ≡ 1 mod 24).")
    print("  So (1-q)^q = ±(q+2) where the sign is (-1)^{(q+1)/6}.\n")

    print("  Verify: since A ≡ 1 mod 24, (3/A) = 3^{(A-1)/2} = 1.")
    print("  But here we have 3^{(q-1)/2}, NOT 3^{(A-1)/2}.")
    print("  These are different! (A-1)/2 = q(q+1)/2 ≠ (q-1)/2.\n")

    print("  Actually let's just verify 3^{(q-1)/2} mod A:")
    for q, A in primes[:10]:
        val = pow(3, (q-1)//2, A)
        print(f"  q={q}: 3^{{(q-1)/2}} = {val} {'= 1' if val == 1 else ''}")

    print("\n  Hmm, these are NOT all 1. 3^{(q-1)/2} is related to (3/q), not (3/A).")
    print("  By QR: (3/q) depends on q mod 12. q ≡ 71 mod 72 → q ≡ 11 mod 12.")
    print("  (3/q) = (q/3) · (-1)^{...} by QR. q ≡ 2 mod 3, so (q/3) = (2/3) = -1.")
    print("  But actually 3^{(q-1)/2} mod q gives (3/q), not mod A.")
    print("  3^{(q-1)/2} mod A is something different.\n")

    print("  3^{(q-1)/2} mod A: this is NOT a standard symbol.")
    print("  Let's see what it equals:")
    half_q_vals = []
    for q, A in primes[:20]:
        val = pow(3, (q-1)//2, A)
        # Find what this is relative to (q+2) etc.
        qp2 = (q + 2) % A
        one_mq_q = pow((1-q) % A, q, A)
        ratio = (one_mq_q * pow(qp2, A-2, A)) % A
        sign = 1 if ratio == pow(-1, (q+1)//6) % A else -1

        half_q_vals.append((q, val))
        print(f"  q={q}: 3^{{(q-1)/2}} mod A = {val}")

    print("\n" + "=" * 80)
    print("SECTION 14: CRUCIAL — What is 3^{(q-1)/2} mod A?")
    print("=" * 80)

    print("\n  Let's think about this differently.")
    print("  In F_A, the group has order q(q+1). The subgroup of order q")
    print("  consists of (q+1)-th power residues.")
    print("  3^{(q-1)/2}: here (q-1)/2 is just an exponent, not related to |F_A*|.\n")

    print("  Key: 3^{(q-1)/2} = 3^{(q-1)/2}. And 3^q = 3^{(q-1)/2} · 3^{(q+1)/2}.")
    print("  Hmm, this doesn't factor nicely either.\n")

    print("  Let's try yet another angle.")
    print("  We have the formula 3^q = (1-q)^q · (q+2)^q.")
    print("  If there's a WAY to show (1-q)^q ≠ (q+2)^{-q} mod A")
    print("  (which would mean their product ≠ 1, i.e., 3^q ≠ 1)...")
    print("  Actually (1-q)^q · (q+2)^q = 3^q. So 3^q = 1 iff (1-q)^q = (q+2)^{-q}.\n")

    print("  (q+2)^{-q} = [(q+2)^{-1}]^q. And (q+2)^{-1} = (1-q)/3 mod A")
    print("  [since (1-q)(q+2) = 3 → (q+2)^{-1} = (1-q)·3^{-1}].")
    print("  So (q+2)^{-q} = [(1-q)/3]^q = (1-q)^q / 3^q.")
    print("  3^q = 1 iff (1-q)^q = (1-q)^q / 3^q iff 3^q = 1. Circular again.\n")

    print("=" * 80)
    print("SECTION 15: TOTALLY NEW — Weil pairing / elliptic curve approach")
    print("=" * 80)

    print("\n  A = q²+q+1 = Φ₃(q). This is the number of F_q-rational points")
    print("  on the elliptic curve y² = x³ + 1 when the Frobenius trace is -q")
    print("  ... actually #E(F_q) = q + 1 - t where t is the trace.")
    print("  For y² = x³ + 1 (j-invariant 0): #E(F_q) depends on CM structure.")
    print("  #E(F_q) = q+1 - (ω^r + ω̄^r) where ω = e^{2πi/3}, some r.")
    print("  If r=1: trace = ω + ω̄ = -1, so #E = q+1+1 = q+2.")
    print("  If r=2: trace = ω² + ω̄² = -1 (same).")
    print("  Hmm, these all give q+2, not q²+q+1 = A.\n")

    print("  Actually for y² = x³ - 1 or y² = x³ + b: the point count is")
    print("  q + 1 - a where a² + 3b² = 4q for some integers a, b")
    print("  (Deuring's theorem for CM by Z[ω]).")
    print("  This gives a ≈ 2√q, so #E ≈ q - 2√q, which is ~q, not ~q².\n")

    print("  So A = q²+q+1 is NOT directly a point count on an ordinary EC over F_q.")
    print("  But it IS Φ₃(q) = the number of points on P²(F_q) minus affine part")
    print("  ... or related to the order of the Frobenius in GL(2).\n")

    print("  Actually: A = q²+q+1 = |PG(2, F_q)| / (q-1) ... not quite.")
    print("  |PG(2, F_q)| = q²+q+1 = A. YES! A is the number of points in the")
    print("  projective plane PG(2, F_q).\n")

    print("  Interesting but not obviously helpful for our specific problem.\n")

    print("=" * 80)
    print("SECTION 16: Counting approach — how many q have 3^q = 1 mod A?")
    print("=" * 80)

    print("\n  For a random prime A with q | (A-1), the probability that 3^q = 1 is 1/q")
    print("  (if 3 is 'random' in the group). For q ≈ 10⁴, this is ~0.01%.")
    print("  With ~28 primes tested, expected 0 counterexamples. Consistent.\n")

    print("  But we need a PROOF, not just heuristics.\n")

    print("=" * 80)
    print("SECTION 17: THE RIGHT APPROACH — use 3 = (1-ω)² · (-ω²)")
    print("=" * 80)

    print("\n  In Z[ω]: 3 = (1-ω)(1-ω²) = |1-ω|²")
    print("  Also: 3 = -(1-ω)²ω² (easy to verify: (1-ω)² = 1-2ω+ω² = -3ω,")
    print("  so -(1-ω)²ω² = 3ωω² = 3ω³ = 3. Yes.)")
    print("  In F_A: 3 = -(1-q)²q² = -(-3q)q² = 3q³ = 3·1 = 3. ✓\n")

    print("  (1-ω)² = -3ω, so (1-ω) = √(-3ω).")
    print("  (1-ω)^q = (-3ω)^{q/2} if q were even, but q is odd.")
    print("  (1-ω)^q = (1-ω) · (1-ω)^{q-1} = (1-ω) · [(-3ω)]^{(q-1)/2}")
    print("  = (1-ω) · (-3)^{(q-1)/2} · ω^{(q-1)/2}")
    print("  In F_A: (1-q) · (-3)^{(q-1)/2} · q^{(q-1)/2}.\n")

    print("  Now q^{(q-1)/2}: q ≡ 2 mod 3, (q-1)/2 mod 3?")
    print("  q ≡ 2 mod 3 → q-1 ≡ 1 mod 3 → (q-1)/2 mod 3 depends on q mod 6.")
    print("  q ≡ 5 mod 6 → (q-1)/2 = (q-1)/2. q = 6k+5 → (q-1)/2 = 3k+2.")
    print("  (q-1)/2 ≡ 2 mod 3. So q^{(q-1)/2} = q^{...} where exponent ≡ 2 mod 3.")
    print("  q^{3n+2} = q^2 (since q³ = 1 mod A).")
    print("  q² = -q-1 mod A.\n")

    print("  So (1-q)^q = (1-q) · (-3)^{(q-1)/2} · (-q-1)")
    print("  = -(1-q)(q+1) · (-3)^{(q-1)/2}")
    print("  Now (1-q)(q+1) = q+1-q²-q = q+1-(-q-1)-q = q+1+q+1-q = q+2.")
    print("  So (1-q)^q = -(q+2) · (-3)^{(q-1)/2}.")
    print("  = -(q+2) · (-1)^{(q-1)/2} · 3^{(q-1)/2}")
    print("  q ≡ 7 mod 8 → q-1 ≡ 6 mod 8 → (q-1)/2 ≡ 3 mod 4 → (-1)^{(q-1)/2} = -1.")
    print("  So (1-q)^q = -(q+2) · (-1) · 3^{(q-1)/2} = (q+2) · 3^{(q-1)/2}.\n")

    print("  VERIFYING this formula:")
    for q, A in primes[:10]:
        one_mq = (1 - q) % A
        lhs = pow(one_mq, q, A)
        rhs = (((q + 2) % A) * pow(3, (q-1)//2, A)) % A
        print(f"  q={q}: (1-q)^q = {lhs}, (q+2)·3^{{(q-1)/2}} = {rhs}, match: {lhs == rhs}")

    print("\n  Similarly: (q+2)^q = (1-q²)^q. By the conjugation ω ↔ ω²:")
    print("  (1-ω²)^q = (1-ω²)·(-3ω²)^{(q-1)/2}")
    print("  In F_A: (q+2) · (-3)^{(q-1)/2} · (q²)^{(q-1)/2}")
    print("  q^{2·(q-1)/2} = q^{q-1}. (q-1) mod 3: q ≡ 2 mod 3, so q-1 ≡ 1 mod 3.")
    print("  q^{q-1} = q^1 = q mod A.")
    print("  So (q+2)^q = (q+2) · (-3)^{(q-1)/2} · q")
    print("  = (q+2) · (-1)^{(q-1)/2} · 3^{(q-1)/2} · q")
    print("  = (q+2) · (-1) · 3^{(q-1)/2} · q [since (-1)^{(q-1)/2} = -1]")
    print("  = -(q+2)q · 3^{(q-1)/2}.\n")

    print("  VERIFYING:")
    for q, A in primes[:10]:
        qp2 = (q + 2) % A
        lhs = pow(qp2, q, A)
        rhs = ((-((q + 2) * q) % A) * pow(3, (q-1)//2, A)) % A
        print(f"  q={q}: (q+2)^q = {lhs}, -(q+2)q·3^{{(q-1)/2}} = {rhs}, match: {lhs == rhs}")

    print("\n  PRODUCT: 3^q = (1-q)^q · (q+2)^q")
    print("  = [(q+2) · 3^{(q-1)/2}] · [-(q+2)q · 3^{(q-1)/2}]")
    print("  = -(q+2)²q · 3^{q-1}")
    print("  Now (q+2)² = 3(q+1) [from earlier: (q+2)² = q²+4q+4 = -q-1+4q+4 = 3q+3 = 3(q+1)].")
    print("  So 3^q = -3(q+1)·q · 3^{q-1} = -3^q · q(q+1) = -3^q · (A-1).")
    print("  A-1 ≡ -1 mod A. So 3^q = -3^q · (-1) = 3^q. Tautological again.\n")

    print("  BUT: the intermediate formulas are NOT tautological!")
    print("  (1-q)^q = (q+2) · 3^{(q-1)/2} mod A  <--- THIS IS NEW")
    print("  (q+2)^q = -(q+2)q · 3^{(q-1)/2} mod A  <--- AND THIS\n")

    print("  Under the assumption 3^q = 1:")
    print("  (1-q)^q = (q+2) · 3^{(q-1)/2}")
    print("  (q+2)^q = -(q+2)q · 3^{(q-1)/2}")
    print("  Product = -(q+2)²q · 3^{q-1} = -3(q+1)q · 3^{q-1}")
    print("  = -q(q+1) · 3^q = (A-1)·(-1)·3^q... wait, need 3^q = 1.")
    print("  Product = -q(q+1) · 1 = -(A-1) = 1 mod A. ✓ Consistent.\n")

    print("  The key formula: (1-q)^q = (q+2) · 3^{(q-1)/2}")
    print("  If 3^q = 1: (1-q)^q = (q+2) · 3^{-1/2}")
    print("  Hmm, 3^{(q-1)/2} = 3^{(q-1)/2}. Under 3^q = 1: 3^{q-1} = 3^{-1}.")
    print("  So 3^{(q-1)/2} = (3^{-1})^{1/2} ... only if squaring is bijective.\n")

    print("=" * 80)
    print("SECTION 18: Using the formula to constrain 3^{(q-1)/2} mod A")
    print("=" * 80)

    print("\n  We have (1-q)^q = (q+2) · 3^{(q-1)/2}.")
    print("  If 3^q = 1 (i.e., ord(3) = q), then 3 generates a cyclic subgroup of order q.")
    print("  3^{(q-1)/2} is an element of this subgroup.")
    print("  Since q is prime, every nonidentity element has order q.")
    print("  (q-1)/2 < q (for q > 1), so 3^{(q-1)/2} has order q (it's ≠ 1).\n")

    print("  So under 3^q = 1: (1-q)^q = (q+2) · (some element of order q).\n")

    print("  The (q+1)-torsion subgroup: 3^q is in this group. If 3^q = 1, it's trivial.")
    print("  (1-q)^q: what subgroup is this in?")
    print("  [(1-q)^q]^{q+1} = (1-q)^{q(q+1)} = (1-q)^{A-1} = 1. So it's in (q+1)-torsion.")
    print("  [(1-q)^q]^q = (1-q)^{q²}. Since q² = A-1-q → (1-q)^{q²} = (1-q)^{A-1-q}")
    print("  = (1-q)^{A-1}/(1-q)^q = 1/(1-q)^q.")
    print("  So [(1-q)^q]^q = [(1-q)^q]^{-1}.")
    print("  This means [(1-q)^q]^{q+1} = 1, i.e., (1-q)^q is in the (q+1)-torsion. ✓\n")

    print("  Key constraint: (1-q)^q = (q+2) · 3^{(q-1)/2}.")
    print("  LHS is in the (q+1)-torsion (order divides q+1).")
    print("  RHS: (q+2) is some element, 3^{(q-1)/2} is in the q-torsion (if 3^q=1).")
    print("  So RHS = (q+2) · (something in q-torsion).")
    print("  For RHS to be in (q+1)-torsion, we need (q+2) to be in")
    print("  (q+1)-torsion · q-torsion^{-1} ... but the group is abelian so")
    print("  (q+1)-torsion + q-torsion = entire group (since gcd(q,q+1)=1).")
    print("  So (q+2) can be anything. No constraint.\n")

    print("  WAIT. The formula says: (element of (q+1)-torsion) = (q+2) · (element of q-torsion).")
    print("  Decompose (q+2) = α · β where α ∈ C_q, β ∈ C_{q+1}.")
    print("  Then: (q+1)-torsion element = β · α · (q-torsion element).")
    print("  The C_q component of the RHS is α · 3^{(q-1)/2}.")
    print("  The C_{q+1} component of LHS = (1-q)^q.")
    print("  For equality: α · 3^{(q-1)/2} must be trivial in C_q, i.e., α = [3^{(q-1)/2}]^{-1}.")
    print("  So the C_q component of (q+2) must be [3^{(q-1)/2}]^{-1}.")
    print("  The C_q component of (q+2) is (q+2)^{q+1} mod A.")
    print("  And [3^{(q-1)/2}]^{-1} = 3^{(q+1)/2} in C_q (since (3^q)^{...} ... ")
    print("  actually in C_q: 3^{(q-1)/2} has some order dividing q.)\n")

    print("  Let's compute: C_q projection of (q+2) = (q+2)^{q+1} mod A:")
    for q, A in primes[:10]:
        proj = pow((q+2) % A, q+1, A)
        # This should satisfy proj^q = 1 (it's in C_q)
        check = pow(proj, q, A)
        # What is 3^{(q+1)/2} mod A?
        three_half = pow(3, (q+1)//2, A)
        # Under assumption 3^q = 1: 3^{(q+1)/2} = 3^{1/2}·3^{q/2} = 3^{1/2}·1 ... hmm
        print(f"  q={q}: (q+2)^(q+1) = {proj}, proj^q=1? {check==1}, "
              f"3^((q+1)/2) = {three_half}")

    print("\n" + "=" * 80)
    print("SECTION 19: Key test — ord of (q+2)^{q+1} in the q-torsion")
    print("=" * 80)

    print("\n  (q+2)^{q+1} is the projection of (q+2) onto C_q.")
    print("  Under 3^q = 1: this must equal 3^{-(q-1)/2} = 3^{(q+1)/2}.")
    print("  So 3^q = 1 IMPLIES (q+2)^{q+1} = 3^{(q+1)/2} mod A.")
    print("  Equivalently: (q+2)^{q+1} · 3^{(q-1)/2} = 1 mod A (in C_q).\n")

    print("  Testing this NECESSARY condition:")
    for q, A in primes[:15]:
        lhs = (pow((q+2) % A, q+1, A) * pow(3, (q-1)//2, A)) % A
        print(f"  q={q}: (q+2)^(q+1) · 3^((q-1)/2) mod A = {lhs} "
              f"{'= 1 (consistent)' if lhs == 1 else '≠ 1 → CONTRADICTION with 3^q=1!'}")

    print("\n  If this is NEVER 1, we have proved 3^q ≠ 1!")

    # Extended check
    never_1 = True
    for q, A in primes:
        lhs = (pow((q+2) % A, q+1, A) * pow(3, (q-1)//2, A)) % A
        if lhs == 1:
            never_1 = False
            print(f"  *** FOUND: q={q} has (q+2)^(q+1) · 3^((q-1)/2) = 1 mod A ***")

    if never_1:
        print(f"\n  *** Over all {len(primes)} primes: NEVER equals 1! ***")
        print("  *** But wait — this condition is necessary for 3^q = 1, not sufficient. ***")
        print("  *** If it's never 1, it means the NECESSARY condition for 3^q=1 fails! ***")
        print("  *** THIS IS THE PROOF (if it holds universally)! ***\n")

        # Double-check with extended range
        extended = find_eligible_primes(200000)
        still_never = True
        for q, A in extended:
            lhs = (pow((q+2) % A, q+1, A) * pow(3, (q-1)//2, A)) % A
            if lhs == 1:
                still_never = False
                print(f"  *** COUNTEREXAMPLE at q={q}! ***")
                break

        if still_never:
            print(f"  Extended to {len(extended)} primes q < 200000: STILL NEVER 1!")
        else:
            print("  Failed in extended range.")
    else:
        print("  Sometimes equals 1, so this condition is not a universal obstruction.")

    print("\n" + "=" * 80)
    print("SECTION 20: Simplify the obstruction")
    print("=" * 80)

    print("\n  Condition: (q+2)^{q+1} · 3^{(q-1)/2} ≠ 1 mod A.")
    print("  Let's rewrite: (q+2)^{q+1} = [(q+2)²]^{(q+1)/2} = [3(q+1)]^{(q+1)/2}")
    print("  = 3^{(q+1)/2} · (q+1)^{(q+1)/2}.\n")
    print("  So the condition becomes:")
    print("  3^{(q+1)/2} · (q+1)^{(q+1)/2} · 3^{(q-1)/2} ≠ 1")
    print("  3^{q/2+1/2+q/2-1/2} · (q+1)^{(q+1)/2} ≠ 1")
    print("  3^q · (q+1)^{(q+1)/2} ≠ 1")
    print("  But if 3^q = 1, this becomes (q+1)^{(q+1)/2} ≠ 1.\n")

    print("  Wait, let me recheck. (q+2)^{q+1} · 3^{(q-1)/2} = 1")
    print("  3^{(q+1)/2} · (q+1)^{(q+1)/2} · 3^{(q-1)/2} = 1")
    print("  3^{(q+1+q-1)/2} · (q+1)^{(q+1)/2} = 1")
    print("  3^q · (q+1)^{(q+1)/2} = 1.\n")

    print("  So: the condition (q+2)^{q+1} · 3^{(q-1)/2} = 1 is equivalent to")
    print("  3^q · (q+1)^{(q+1)/2} = 1, i.e., 3^q = [(q+1)^{(q+1)/2}]^{-1}.\n")

    print("  If 3^q = 1: need (q+1)^{(q+1)/2} = 1 mod A.")
    print("  So 3^q ≠ 1 if (q+1)^{(q+1)/2} ≠ 1 mod A.\n")

    print("  BUT WAIT — can we just directly test (q+1)^{(q+1)/2} mod A?")
    print("  This is PURELY a function of q, no 3 involved!")

    for q, A in primes[:20]:
        val = pow(q + 1, (q + 1) // 2, A)
        print(f"  q={q}: (q+1)^((q+1)/2) mod A = {val} "
              f"{'= 1' if val == 1 else '≠ 1 → 3^q ≠ 1!'}")

    # Extended
    print(f"\n  Extended check over all {len(primes)} primes:")
    count_ne1 = 0
    count_eq1 = 0
    for q, A in primes:
        val = pow(q + 1, (q + 1) // 2, A)
        if val == 1:
            count_eq1 += 1
            print(f"  *** q={q}: (q+1)^((q+1)/2) = 1 mod A! ***")
        else:
            count_ne1 += 1

    print(f"\n  (q+1)^((q+1)/2) ≠ 1: {count_ne1}/{len(primes)}")
    print(f"  (q+1)^((q+1)/2) = 1: {count_eq1}/{len(primes)}")

    if count_eq1 == 0:
        print("\n  *** UNIVERSAL: (q+1)^{(q+1)/2} ≠ 1 mod A for ALL tested q! ***")
        print("  Since 3^q = 1 would require (q+1)^{(q+1)/2} = 1,")
        print("  this proves 3^q ≠ 1 (if we can prove the universal statement).\n")
        print("  Key: (q+1)^{(q+1)/2} mod A. This is a HALVING of (q+1)^{q+1}.")
        print("  (q+1)^{q+1} = (q+1)^{q+1} mod A. Note q+1 = -(q²) mod A (since q²+q+1=A).")
        print("  So (q+1)^{q+1} = (-q²)^{q+1} = (-1)^{q+1} · q^{2(q+1)} mod A.")
        print("  q+1 is even → (-1)^{q+1} = -1.")
        print("  q^{2(q+1)}: 2(q+1) mod 3. q ≡ 2 mod 3, q+1 ≡ 0 mod 3, 2(q+1) ≡ 0 mod 3.")
        print("  So q^{2(q+1)} = (q³)^{2(q+1)/3} = 1^{...} = 1.")
        print("  Therefore (q+1)^{q+1} = -1 mod A.\n")

        print("  VERIFYING (q+1)^{q+1} = -1 mod A:")
        for q, A in primes[:10]:
            val = pow(q + 1, q + 1, A)
            print(f"  q={q}: (q+1)^(q+1) = {val}, A-1 = {A-1}, match -1? {val == A - 1}")

        print("\n  YES! (q+1)^{q+1} = -1 mod A ALWAYS!")
        print("  So (q+1)^{(q+1)/2} is a SQUARE ROOT of -1 mod A.")
        print("  For (q+1)^{(q+1)/2} = 1, we'd need 1² = -1 mod A, i.e., -1 = 1 mod A, i.e., A = 2.")
        print("  But A = q²+q+1 ≥ 71²+72 >> 2.")
        print("  THEREFORE (q+1)^{(q+1)/2} ≠ 1 mod A for ALL A > 2.")
        print("\n  *** THIS IS THE PROOF! ***\n")

        print("  PROOF SUMMARY:")
        print("  1. (q+2)² = 3(q+1) mod A")
        print("  2. (q+2)^{q+1} = [3(q+1)]^{(q+1)/2} = 3^{(q+1)/2} · (q+1)^{(q+1)/2}")
        print("  3. (1-q)^q = (q+2) · 3^{(q-1)/2} mod A  [from (1-ω)² = -3ω structure]")
        print("  4. 3^q = (1-q)^q · (q+2)^q = (1-q)^{2q} / (-q-1) ... combined formulas give:")
        print("     3^q = 1 implies (q+1)^{(q+1)/2} = 1 mod A")
        print("  5. But (q+1)^{q+1} = -1 mod A (proved algebraically)")
        print("  6. So (q+1)^{(q+1)/2} is a square root of -1, hence ≠ ±1 if A > 2.")
        print("     Wait: it could equal -1. Let me check that.\n")

        print("  Actually: (q+1)^{(q+1)/2} could be +1 or -1 or some other sq root of -1.")
        print("  It's a square root of -1 mod A. Since A ≡ 1 mod 4 (A ≡ 1 mod 8 actually),")
        print("  -1 IS a QR mod A, so square roots of -1 exist.")
        print("  They are NOT ±1 (since (-1)² = 1, not -1, and 1² = 1, not -1).")
        print("  So (q+1)^{(q+1)/2} is a non-trivial square root of -1.")
        print("  In particular, it is NEVER equal to 1.")
        print("  QED!\n")

    print("\n" + "=" * 80)
    print("FINAL VERIFICATION")
    print("=" * 80)

    extended = find_eligible_primes(200000)
    print(f"\n  Testing over {len(extended)} primes q < 200000:\n")

    all_pass = True
    for q, A in extended:
        # Test (q+1)^{q+1} = -1 mod A
        val_full = pow(q + 1, q + 1, A)
        if val_full != A - 1:
            print(f"  FAIL: q={q}, (q+1)^(q+1) ≠ -1")
            all_pass = False

        # Test (q+1)^{(q+1)/2} ≠ 1 and ≠ -1 (it's a nontrivial sqrt of -1)
        val_half = pow(q + 1, (q + 1) // 2, A)
        if val_half == 1:
            print(f"  FAIL: q={q}, (q+1)^((q+1)/2) = 1")
            all_pass = False
        if val_half == A - 1:
            print(f"  NOTE: q={q}, (q+1)^((q+1)/2) = -1 (still ≠ 1, proof holds)")

        # Verify 3^q ≠ 1
        three_q = pow(3, q, A)
        if three_q == 1:
            print(f"  COUNTEREXAMPLE: q={q}, 3^q = 1!!!")
            all_pass = False

    if all_pass:
        print(f"  ALL {len(extended)} PRIMES PASS!")
        print("  (q+1)^{q+1} = -1 mod A always.")
        print("  (q+1)^{(q+1)/2} ≠ 1 mod A always.")
        print("  3^q ≠ 1 mod A always.\n")

if __name__ == '__main__':
    main()
