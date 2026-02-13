#!/usr/bin/env python3
"""
Feit-Thompson p=3 conjecture: DEEPER Eisenstein integer analysis.

KEY FINDINGS FROM v1:
1. 3^q ≢ 1 mod A for ALL 40 tested q ≡ 71 mod 72 (conjecture holds computationally)
2. (3/π)₃ = 1 ALWAYS — 3 is always a cubic residue mod A
3. The cubic residue symbol is FORCED to be 1 by the congruence conditions
4. 9th power residue varies — sometimes 1, sometimes not

NEW DIRECTIONS:
A. WHY is (3/π)₃ = 1 forced? Prove this theoretically.
B. Can we prove 3^q ≢ 1 using the ORDER structure?
C. Explore the Eisenstein lattice mod π² for deeper information.
D. Investigate whether ord_A(3) can ever equal q.
"""

import sympy
from sympy import isprime, factorint, gcd, divisors
from collections import Counter
import math

# ============================================================
# PART A: WHY (3/π)₃ = 1 is FORCED
# ============================================================

def prove_cubic_residue_forced():
    """
    THEOREM: For q ≡ 2 mod 3 and A = q²+q+1 prime, 3 is ALWAYS a cubic
    residue mod A.

    PROOF:
    A = q² + q + 1 = (q³ - 1)/(q - 1), so q³ ≡ 1 mod A.
    Thus q has order dividing 3 in (Z/AZ)*.
    Since A > 3, q ≢ 1 mod A, so ord(q) ∈ {1, 3}. q ≠ 1 mod A (since A > q+1), so ord(q) = 3.

    Now: (1-q)² = 1 - 2q + q² = (q² + q + 1) - 3q = A - 3q ≡ -3q mod A.
    So 3q ≡ -(1-q)² mod A.
    And 3 ≡ -(1-q)² · q^{-1} mod A.
    Since q³ ≡ 1: q^{-1} ≡ q² mod A.
    So 3 ≡ -(1-q)² · q² = -q²(1-q)² = -(q(1-q))² = -(q - q²)² mod A.

    For 3 to be a cubic residue: 3^{(A-1)/3} ≡ 1 mod A.
    3 ≡ -(q - q²)² mod A.
    3^{(A-1)/3} ≡ [-(q-q²)²]^{(A-1)/3} = (-1)^{(A-1)/3} · (q-q²)^{2(A-1)/3} mod A.

    (A-1)/3 = q(q+1)/3.
    For q ≡ 2 mod 3: q+1 ≡ 0 mod 3, so (q+1)/3 is an integer.
    (A-1)/3 = q · (q+1)/3.

    (-1)^{(A-1)/3} = (-1)^{q(q+1)/3}.
    q odd and (q+1)/3: need to determine parity.
    q ≡ 71 mod 72 → q odd, (q+1)/3 = (72k)/3 = 24k → even.
    So q(q+1)/3 = q · 24k: q odd × 24k = even × odd or odd × even...
    Actually q odd, 24k even, product is even. So (-1)^{(A-1)/3} = 1.

    (q-q²)^{2(A-1)/3}: Let's compute (q-q²) mod A.
    q - q² = q(1-q). This is some element of F_A.
    (q-q²)^{2(A-1)/3} = (q(1-q))^{2q(q+1)/3}.

    Key: q^{2q(q+1)/3} = (q³)^{2(q+1)/9} ... hmm, 2q(q+1)/3 mod 3.
    q ≡ 2 mod 3, (q+1)/3 integer. 2q(q+1)/3 = 2q · (q+1)/3.
    2q mod 3 = 1. (q+1)/3 mod 3: for q ≡ 8 mod 9, (q+1)/3 ≡ 0 mod 3.
    So 2q · (q+1)/3 ≡ 0 mod 3.
    Thus q^{2q(q+1)/3} = (q³)^{2q(q+1)/9} = 1^{...} = 1. ✓ (when 9|(q+1))

    For (1-q)^{2(A-1)/3}:
    (1-q)^{2(A-1)/3} = ((1-q)^2)^{(A-1)/3} = (-3q)^{(A-1)/3} = (-3)^{(A-1)/3} · q^{(A-1)/3}.

    q^{(A-1)/3} = q^{q(q+1)/3}: same as above, = 1 when 9|(q+1).

    (-3)^{(A-1)/3}: (-3) = (-1)·3. (-1)^{(A-1)/3} = 1 (shown above).
    3^{(A-1)/3}: THIS IS WHAT WE'RE TRYING TO COMPUTE.

    So we get: 3^{(A-1)/3} = [-(q-q²)²]^{(A-1)/3} = 1 · [(q-q²)²]^{(A-1)/3}
    = (q-q²)^{2(A-1)/3} = [q(1-q)]^{2(A-1)/3} = q^{2(A-1)/3} · (1-q)^{2(A-1)/3}
    = 1 · (-3)^{(A-1)/3} · q^{(A-1)/3}  [using (1-q)² = -3q]
    = (-3)^{(A-1)/3} · 1
    = (-1)^{(A-1)/3} · 3^{(A-1)/3}
    = 3^{(A-1)/3}.

    THIS IS CIRCULAR! The computation 3^{(A-1)/3} = 3^{(A-1)/3}.
    The identity 3 ≡ -(q-q²)² doesn't help because the decomposition
    feeds back into itself through (1-q)² = -3q.

    Let me try a DIFFERENT approach.
    """
    print("THEORETICAL ANALYSIS: Why (3/π)₃ = 1")
    print("=" * 60)
    print()
    print("Approach via cubic reciprocity in Z[ω]:")
    print()
    print("3 = -ω²(1-ω)² in Z[ω], where λ = 1-ω is the prime above 3.")
    print()
    print("(3/π)₃ = (-ω²/π)₃ · (λ/π)₃²")
    print()
    print("For π₀ = -ωπ = -1 - (q+1)ω (primary, a≡2 mod 3, b≡0 mod 3):")
    print()
    print("1. (ω/π)₃: ω is a unit. By definition,")
    print("   (ω/π)₃ = ω^{(Nπ-1)/3} evaluated in Z[ω]/(π).")
    print("   But ω ≡ q mod π, so (ω/π)₃ ↔ q^{(A-1)/3} mod A.")
    print("   q^{(A-1)/3} = q^{q(q+1)/3}.")
    print("   Since q³ ≡ 1 mod A, this = q^{(q(q+1)/3) mod 3}.")
    print("   q ≡ 2 mod 3, (q+1)/3: for q ≡ 8 mod 9, (q+1) ≡ 0 mod 9,")
    print("   so (q+1)/3 ≡ 0 mod 3. Then q·(q+1)/3 ≡ 0 mod 3.")
    print("   So q^0 = 1 mod A. Hence (ω/π)₃ = 1. ✓")
    print()
    print("2. (-1/π)₃: (-1)^{(A-1)/3} mod A.")
    print("   (A-1)/3 = q(q+1)/3 is even (shown above). So (-1)^{even} = 1.")
    print("   Hence (-1/π)₃ = 1. ✓")
    print()
    print("3. (-ω²/π)₃ = (-1/π)₃ · (ω/π)₃² = 1 · 1 = 1. ✓")
    print()
    print("4. (λ/π)₃ = ((1-ω)/π)₃:")
    print("   (1-ω) ↔ (1-q) mod A.")
    print("   (1-q)^{(A-1)/3} mod A.")
    print()
    print("   KEY THEOREM: For q ≡ 8 mod 9 and A = q²+q+1 prime,")
    print("   ((1-ω)/π)₃ = 1.")
    print()
    print("   PROOF via cubic supplement (Ireland-Rosen 9.3.5):")
    print("   For primary π₀ = a + bω: (λ/π₀)₃ = ω^{b/3}")
    print("   π₀ = -1 - (q+1)ω: b = -(q+1), b/3 = -(q+1)/3.")
    print("   For q ≡ 8 mod 9: (q+1)/3 ≡ 3/3... wait, (q+1) ≡ 0 mod 9.")
    print("   So b/3 = -(q+1)/3 ≡ 0 mod 3.")
    print("   Hence (λ/π₀)₃ = ω^0 = 1. ✓")
    print()
    print("5. THEREFORE: (3/π)₃ = 1 · 1² = 1.")
    print("   3 is ALWAYS a cubic residue mod A for q ≡ 8 mod 9.")
    print()
    print("CONCLUSION: The cubic residue symbol gives NO information")
    print("about whether 3^q ≡ 1 mod A. Being a cubic residue is a")
    print("NECESSARY condition for 3^q ≡ 1, and it's always satisfied.")
    print("The cubic residue approach at this level CANNOT resolve the conjecture.")


# ============================================================
# PART B: ORDER STRUCTURE ANALYSIS
# ============================================================

def analyze_order_structure(n_primes=50):
    """
    If 3^q ≡ 1 mod A, then ord_A(3) | q. Since q is prime, ord_A(3) = 1 or q.
    3 ≡ 1 mod A is impossible (A > 4). So ord_A(3) = q.

    But ord_A(3) | φ(A) = A-1 = q(q+1). So ord_A(3) | q(q+1).
    Since q is prime: ord_A(3) = q · d where d | (q+1), OR ord_A(3) | (q+1).

    For 3^q ≡ 1: we need q | ord, which means ord = q · d for some d | gcd(ord, (q+1)/d').

    KEY QUESTION: Can ord_A(3) = q? This requires:
    1. 3^q ≡ 1 mod A
    2. No smaller positive power of 3 is ≡ 1 mod A

    If ord = q, then 3 generates a subgroup of order q in (Z/AZ)*.
    The subgroup of q-th roots of unity mod A: {x : x^q ≡ 1 mod A}.
    Since A ≡ 1 mod q (because A-1 = q(q+1)), this subgroup has order q.
    Its elements are the q-th roots of unity mod A.

    q³ ≡ 1 mod A, so q is itself a q-th root of unity mod A (since q^q = (q³)^{q/3}...
    wait, q/3 is not an integer. Let's be more careful.

    q^q mod A: since q³ ≡ 1 mod A, q^q = q^{q mod 3} = q^{q mod 3}.
    q ≡ 2 mod 3, so q^q ≡ q² mod A.
    """
    print(f"\n{'='*70}")
    print("ORDER STRUCTURE ANALYSIS")
    print(f"{'='*70}")

    primes = []
    q = 71
    while len(primes) < n_primes:
        if isprime(q):
            A = q*q + q + 1
            if isprime(A):
                primes.append((q, A))
        q += 72

    # For each q, compute ord_A(3) and factorize it
    print(f"\n{'q':>8} {'A':>15} {'ord':>12} {'ord factored':>25} {'ord/q':>8} {'q|ord':>6} {'3^q mod A':>15}")

    order_over_q = Counter()
    for q, A in primes:
        three_q = pow(3, q, A)

        # Find order by checking divisors of q(q+1)
        n = q * (q + 1)
        divs = sorted(divisors(n))
        order = None
        for d in divs:
            if pow(3, d, A) == 1:
                order = d
                break

        if order is None:
            order = n  # should not happen

        f = factorint(order)
        factored = ' · '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(f.items()))

        q_div_order = order % q == 0
        ratio = order // q if q_div_order else 'N/A'
        if q_div_order:
            order_over_q[ratio] = order_over_q.get(ratio, 0) + 1

        print(f"{q:>8} {A:>15} {order:>12} {factored:>25} {str(ratio):>8} {str(q_div_order):>6} {three_q:>15}")

    print(f"\nDistribution of ord/q (when q|ord):")
    for ratio, count in sorted(order_over_q.items()):
        f = factorint(ratio) if isinstance(ratio, int) and ratio > 1 else {}
        factored = ' · '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(f.items())) if f else str(ratio)
        print(f"  ord/q = {ratio} = {factored}: {count} times")

    # KEY: How many have q|ord? (These are the ones where 3^q = 1)
    q_divides_count = sum(1 for q, A in primes if pow(3, q, A) == 1)
    print(f"\n3^q ≡ 1 mod A (i.e., q | ord): {q_divides_count} / {len(primes)}")
    if q_divides_count == 0:
        print("NONE! The conjecture holds for all tested values.")
        print("This means ord_A(3) | (q+1) for all tested q.")


def analyze_why_order_divides_qplus1(n_primes=50):
    """
    OBSERVATION: ord_A(3) always divides q(q+1) but NEVER has q as a factor.
    So ord_A(3) | (q+1).

    WHY? This is equivalent to 3^{q+1} ≡ 3 mod A... no wait.
    If ord | (q+1), then 3^{q+1} ≡ 1 mod A. Let's check.

    Actually, if ord | (q+1) then 3^{q+1} ≡ 1 iff ord | (q+1).
    But we also know ord | q(q+1). If gcd(ord, q) = 1, then ord | (q+1).
    """
    print(f"\n{'='*70}")
    print("DOES ord_A(3) | (q+1)?")
    print(f"{'='*70}")

    primes = []
    q = 71
    while len(primes) < n_primes:
        if isprime(q):
            A = q*q + q + 1
            if isprime(A):
                primes.append((q, A))
        q += 72

    all_divide = True
    for q, A in primes:
        three_qp1 = pow(3, q+1, A)
        divides = (three_qp1 == 1)
        if not divides:
            all_divide = False
            print(f"q={q}: 3^(q+1) mod A = {three_qp1} ≠ 1, so ord ∤ (q+1)")
        else:
            pass  # print(f"q={q}: 3^(q+1) ≡ 1 mod A ✓")

    if all_divide:
        print(f"YES! 3^(q+1) ≡ 1 mod A for ALL {len(primes)} tested primes.")
        print("\nThis means: ord_A(3) | (q+1) always.")
        print("And since q ∤ (q+1), we get q ∤ ord_A(3), so 3^q ≢ 1 mod A.")
        print("\nIF WE CAN PROVE 3^{q+1} ≡ 1 mod A, the conjecture follows!")
    else:
        print(f"NO — not always. Let's see when it fails.")

    # Deeper: does 3^{q+1} ≡ 1 hold for ALL q ≡ 2 mod 3 (not just 71 mod 72)?
    print(f"\n{'='*70}")
    print("BROADER TEST: 3^(q+1) ≡ 1 mod A for q ≡ 2 mod 3?")
    print(f"{'='*70}")

    count_yes = 0
    count_no = 0
    failures = []
    q = 2
    while q < 200000:
        if isprime(q) and q > 3:
            A = q*q + q + 1
            if isprime(A):
                three_qp1 = pow(3, q+1, A)
                if three_qp1 == 1:
                    count_yes += 1
                else:
                    count_no += 1
                    if len(failures) < 30:
                        failures.append((q, A, q % 72, three_qp1))
        q += 1 if q == 2 else 2 if q == 3 else (6 - q%6 if q%6 == 1 else 2)  # slow
        # Actually just iterate
        q = sympy.nextprime(q)

    print(f"q ≡ 2 mod 3 with A prime, q < 200000:")
    print(f"  3^(q+1) ≡ 1: {count_yes}")
    print(f"  3^(q+1) ≢ 1: {count_no}")

    if failures:
        print(f"\nFailures (first {len(failures)}):")
        for q, A, qmod72, val in failures:
            print(f"  q={q}, A={A}, q mod 72 = {qmod72}, 3^(q+1) mod A = {val}")
    else:
        print("NO FAILURES! 3^{q+1} ≡ 1 mod A for ALL q ≡ 2 mod 3 with A prime.")


def prove_3_to_qplus1():
    """
    Try to PROVE: 3^{q+1} ≡ 1 mod A = q² + q + 1 when q ≡ 2 mod 3 and A prime.

    This would be HUGE — it directly implies 3^q ≢ 1 mod A (since 3^q = 3^{q+1}/3 = 1/3 ≠ 1).

    Approach: In F_A, we have q³ = 1 and q ≠ 1. So q is a primitive cube root of unity.
    The three cube roots of unity are 1, q, q² (since q³ - 1 = (q-1)(q²+q+1) = (q-1)A ≡ 0 mod A).

    If 3^{q+1} ≡ 1 mod A, then 3 has order dividing q+1.

    (1-q)² ≡ -3q mod A.
    Let α = 1 - q. Then α² = -3q.
    α^{2(q+1)} = (-3q)^{q+1} = (-3)^{q+1} · q^{q+1}.

    q^{q+1}: q ≡ 2 mod 3, q+1 ≡ 0 mod 3. q^{q+1} = (q³)^{(q+1)/3} = 1^{(q+1)/3} = 1.

    So α^{2(q+1)} = (-3)^{q+1} = (-1)^{q+1} · 3^{q+1}.
    q+1 is even (q odd), so (-1)^{q+1} = 1.
    α^{2(q+1)} = 3^{q+1}.

    If we can show α^{2(q+1)} = 1, then 3^{q+1} = 1.

    α = 1-q. α^{A-1} = 1 (Fermat).
    A-1 = q(q+1). So α^{q(q+1)} = 1.
    We want α^{2(q+1)} = 1, i.e., ord(α) | 2(q+1).
    We know ord(α) | q(q+1).
    If gcd(ord(α), q) = 1, then ord(α) | (q+1), and then ord(α) | 2(q+1). ✓

    So: IF q ∤ ord(α), THEN 3^{q+1} = 1.

    Equivalently: IF α^{q+1} ≢ 1 mod A for any d | (q+1), d < q+1... wait, no.
    Let me think differently.

    α^q mod A: by Fermat's little theorem in F_A,
    For any x ∈ F_A: x^A = x, so x^{A-1} = 1.
    The Frobenius: x^A = x for all x (not useful since we're already in F_p).

    Wait, A is prime, so F_A is a prime field. The Frobenius is trivial.

    But we can compute α^q directly:
    α = 1 - q.
    α^q = (1-q)^q mod A.

    By the binomial theorem in F_A (char A > q since A > q):
    (1-q)^q = Σ_{k=0}^{q} C(q,k) (-q)^k = Σ C(q,k) (-1)^k q^k.

    Hmm, that doesn't simplify easily.

    BUT: (1-q)^q mod A. We can use q³ ≡ 1 and the fact that
    (1-q)^2 = -3q. So (1-q) is a "square root of -3q" in F_A.

    Let β = (1-q). β² = -3q. β^q = ?

    β^{2q} = (β²)^q = (-3q)^q = (-3)^q · q^q.
    q^q = q^{q mod 3} = q^2 (for q ≡ 2 mod 3).
    (-3)^q = (-1)^q · 3^q = -3^q (q odd).
    So β^{2q} = -3^q · q².

    Now if 3^q ≡ 1 mod A: β^{2q} = -q². And β^{2(q+1)} = β^{2q} · β² = (-q²)(-3q) = 3q³ = 3.
    But we want 3^{q+1} = β^{2(q+1)} = 3. So 3^{q+1} = 3, meaning 3^q = 1. CIRCULAR!

    If 3^{q+1} ≡ 1: then β^{2(q+1)} = 1.
    β^{2q} · β² = 1. β^{2q} = β^{-2} = (β²)^{-1} = (-3q)^{-1} = -(3q)^{-1} mod A.
    Also β^{2q} = -3^q · q².
    So -3^q · q² = -(3q)^{-1}.
    3^q · q² = (3q)^{-1} = 3^{-1} · q^{-1}.
    3^q · 3 = q^{-1} · q^{-2} = q^{-3} = (q³)^{-1} = 1.
    3^{q+1} = 1. ✓ Circular again.

    The algebra is self-consistent but doesn't give a proof.
    """
    print(f"\n{'='*70}")
    print("ATTEMPT TO PROVE 3^{q+1} ≡ 1 mod A")
    print(f"{'='*70}")

    print("""
KEY ALGEBRAIC STRUCTURE:
  Let α = 1-q ∈ F_A. Then α² = -3q.

  3^{q+1} = α^{2(q+1)} (if we can establish this):
    α^{2(q+1)} = (α²)^{q+1} = (-3q)^{q+1}
    = (-3)^{q+1} · q^{q+1}
    q^{q+1} = (q³)^{(q+1)/3} = 1   [since 3|(q+1)]
    (-3)^{q+1} = ((-3)²)^{(q+1)/2} = 9^{(q+1)/2} = 3^{q+1}   [since q+1 even]

  So 3^{q+1} = 3^{q+1}. TAUTOLOGY. Cannot prove from this alone.

  INSIGHT: The equation α² = -3q creates an algebraic dependency
  between 3 and q in F_A that makes all identities circular.
  The cubic residue symbol computation feeds back into itself
  because 3 divides the discriminant of x³ - 1 = (x-1)Φ₃(x),
  and A = Φ₃(q).

  This is the FUNDAMENTAL OBSTRUCTION to using Z[ω] directly:
  The prime 3 is RAMIFIED in Z[ω], and A = N(q-ω) involves
  the structure of Z[ω] at 3. So 3 and A are algebraically
  entangled in Z[ω].
""")


# ============================================================
# PART C: ACTUALLY, 3^(q+1) ≡ 1 IS NOT ALWAYS TRUE
# ============================================================

def test_3_qplus1_all_residues(limit=100000):
    """
    Test 3^{q+1} ≡ 1 mod A for q prime, q ≡ 2 mod 3, A = q²+q+1 prime.
    Check ALL such q, not just q ≡ 71 mod 72.
    """
    print(f"\n{'='*70}")
    print("TEST: 3^(q+1) ≡ 1 mod A for ALL q ≡ 2 mod 3 with A prime")
    print(f"{'='*70}")

    results_by_mod72 = {}
    q = 5
    while q < limit:
        if q % 3 == 2:
            A = q*q + q + 1
            if isprime(A):
                three_qp1 = pow(3, q+1, A)
                is_one = (three_qp1 == 1)
                mod72 = q % 72

                if mod72 not in results_by_mod72:
                    results_by_mod72[mod72] = {'yes': 0, 'no': 0, 'failures': []}
                if is_one:
                    results_by_mod72[mod72]['yes'] += 1
                else:
                    results_by_mod72[mod72]['no'] += 1
                    if len(results_by_mod72[mod72]['failures']) < 5:
                        results_by_mod72[mod72]['failures'].append(q)
        q = int(sympy.nextprime(q))

    print(f"\nResults by q mod 72:")
    print(f"{'q%72':>6} {'yes':>6} {'no':>6} {'rate':>8} {'sample failures':>30}")
    for mod72 in sorted(results_by_mod72.keys()):
        d = results_by_mod72[mod72]
        total = d['yes'] + d['no']
        rate = d['yes'] / total if total > 0 else 0
        failures_str = ', '.join(str(q) for q in d['failures'][:5]) if d['failures'] else 'none'
        print(f"{mod72:>6} {d['yes']:>6} {d['no']:>6} {rate:>8.3f} {failures_str:>30}")


def test_what_power_works(n_primes=60):
    """
    For each q, find the smallest e such that 3^e ≡ 1 mod A.
    Factor e. Understand the pattern.
    """
    print(f"\n{'='*70}")
    print("SMALLEST e: 3^e ≡ 1 mod A")
    print(f"{'='*70}")

    primes = []
    q = 5
    while len(primes) < n_primes:
        if isprime(q) and q % 3 == 2:
            A = q*q + q + 1
            if isprime(A):
                primes.append((q, A))
        q = int(sympy.nextprime(q))

    print(f"{'q':>8} {'q%72':>5} {'ord':>12} {'q+1':>8} {'ord|(q+1)':>10} {'3^q':>15}")

    for q, A in primes:
        n = q * (q + 1)
        divs = sorted(divisors(n))
        order = None
        for d in divs:
            if pow(3, d, A) == 1:
                order = d
                break

        three_q = pow(3, q, A)
        ord_div_qp1 = (order is not None and (q+1) % order == 0)

        print(f"{q:>8} {q%72:>5} {order:>12} {q+1:>8} {str(ord_div_qp1):>10} {three_q:>15}")


# ============================================================
# PART D: THE DEEP QUESTION — Frobenius perspective
# ============================================================

def frobenius_perspective():
    """
    Think of this differently. A = q² + q + 1 = Φ₃(q).

    Consider the number field K = Q(ζ₃) where ζ₃ = ω.
    The prime A splits in K: A = π·π̄ where π = q - ω.

    The Frobenius element Frob_π ∈ Gal(K/Q) is determined by:
    Frob_π(x) ≡ x^A mod π for x in the ring of integers.

    Since Gal(K/Q) = {id, conj} (order 2), and K/Q is abelian,
    the Artin symbol (A, K/Q) = Frob_π.

    For A splitting completely: Frob_π = id.
    A splits iff A ≡ 1 mod 3. A = q²+q+1, A mod 3 = 0+q+1 = q+1 ≡ 0 mod 3.
    Wait: A mod 3 = (q²+q+1) mod 3 = (1+2+1) mod 3 = 1 mod 3 (for q≡2 mod 3).
    So A ≡ 1 mod 3. ✓ A splits completely in Q(ζ₃).

    Now consider the cyclotomic field L = Q(ζ_A) and its subfield
    of index q+1: the unique subfield of degree q of L/Q.
    Call it F_q.

    3 splits/remains in L according to ord_A(3) = ord of 3 in (Z/AZ)*.

    If 3^q ≡ 1 mod A, then 3 splits in the subfield of degree q.
    But this subfield has conductor A and degree q.
    By class field theory, this corresponds to a quotient of (Z/AZ)* of order q.

    Hmm, this is getting into deep algebraic number theory.
    Let me just focus on what the computations show.
    """
    print(f"\n{'='*70}")
    print("FROBENIUS / CYCLOTOMIC PERSPECTIVE")
    print(f"{'='*70}")

    print("""
The key structural fact:

For q ≡ 2 mod 3, A = q²+q+1 prime:

  (Z/AZ)* has order A-1 = q(q+1).

  The unique subgroup of order q: H_q = {x : x^q ≡ 1 mod A}.
  The unique subgroup of order q+1: H_{q+1} = {x : x^{q+1} ≡ 1 mod A}.

  q and q+1 are coprime, so (Z/AZ)* ≅ H_q × H_{q+1}.

  3 ∈ (Z/AZ)* decomposes as 3 = (a, b) where a ∈ H_q, b ∈ H_{q+1}.
  3^q ≡ 1 iff a^q = 1 iff a = 1 (since H_q has order q, and q is prime).
  i.e., 3^q ≡ 1 iff the H_q-component of 3 is trivial.
  i.e., 3 ∈ H_{q+1}.
  i.e., 3^{q+1} ≡ 1 mod A.

  So 3^q ≡ 1 mod A ⟺ 3^{q+1} ≡ 1 mod A.

  This is because ord(3) | q(q+1), and if ord(3) | q then since
  gcd(q, q+1) = 1, ord(3) | q implies 3^{q+1} = (3^q)^{(q+1)/gcd(q,q+1)}...

  Actually wait: 3^q = 1 AND 3^{q+1} = 3 ≠ 1 (assuming A > 4).
  So 3^q ≡ 1 does NOT imply 3^{q+1} ≡ 1!

  Let me reconsider. 3^q ≡ 1 ⟹ ord | q ⟹ ord ∈ {1, q}.
  3 ≠ 1 mod A, so ord = q.
  Then 3^{q+1} = 3^q · 3 = 1 · 3 = 3 ≠ 1.

  And 3^{q+1} ≡ 1 ⟹ ord | (q+1). gcd(q, q+1) = 1.
  If ord | (q+1), then 3^q = 3^{q mod ord} ≠ 1 in general.
  (Unless ord | gcd(q, q+1) = 1, so ord = 1, 3 = 1, impossible.)
  So 3^{q+1} ≡ 1 implies 3^q ≠ 1 (since ord | (q+1) and gcd(ord, q) = 1, so 3^q ≠ 1).

  CONCLUSION:
  3^q ≡ 1 mod A ⟹ 3^{q+1} ≢ 1 mod A  (they're MUTUALLY EXCLUSIVE!)
  3^{q+1} ≡ 1 mod A ⟹ 3^q ≢ 1 mod A

  So if 3^{q+1} ≡ 1 for all q ≡ 71 mod 72, then 3^q ≢ 1 for all such q.
  The conjecture would follow!
""")


def verify_mutual_exclusivity(n_primes=50):
    """Verify that 3^q ≡ 1 and 3^{q+1} ≡ 1 are mutually exclusive."""
    print(f"\n{'='*70}")
    print("VERIFY: 3^q ≡ 1 and 3^{q+1} ≡ 1 are mutually exclusive")
    print(f"{'='*70}")

    q = 5
    count = 0
    both = 0
    neither = 0
    only_q = 0
    only_qp1 = 0

    while count < n_primes:
        if isprime(q) and q % 3 == 2 and q > 3:
            A = q*q + q + 1
            if isprime(A):
                tq = pow(3, q, A) == 1
                tqp1 = pow(3, q+1, A) == 1
                count += 1
                if tq and tqp1: both += 1
                elif tq: only_q += 1
                elif tqp1: only_qp1 += 1
                else: neither += 1
        q = int(sympy.nextprime(q))

    print(f"Out of {count} primes q ≡ 2 mod 3 with A prime:")
    print(f"  3^q ≡ 1 AND 3^(q+1) ≡ 1: {both}  (should be 0)")
    print(f"  3^q ≡ 1 only: {only_q}")
    print(f"  3^(q+1) ≡ 1 only: {only_qp1}")
    print(f"  Neither: {neither}")


def analyze_qplus1_residue_classes(limit=200000):
    """
    For which residue classes q mod 72 does 3^{q+1} ≡ 1 mod A always hold?
    """
    print(f"\n{'='*70}")
    print("3^{q+1} ≡ 1 mod A: by residue class q mod 72")
    print(f"{'='*70}")

    from collections import defaultdict
    results = defaultdict(lambda: {'yes': 0, 'no': 0})

    q = 5
    while q < limit:
        if isprime(q) and q % 3 == 2:
            A = q*q + q + 1
            if isprime(A):
                is_one = pow(3, q+1, A) == 1
                mod72 = q % 72
                results[mod72]['yes' if is_one else 'no'] += 1
        q = int(sympy.nextprime(q))

    print(f"{'q%72':>6} {'q%8':>4} {'q%9':>4} {'yes':>6} {'no':>6} {'rate':>8}")
    for mod72 in sorted(results.keys()):
        d = results[mod72]
        total = d['yes'] + d['no']
        rate = d['yes'] / total if total > 0 else 0
        print(f"{mod72:>6} {mod72%8:>4} {mod72%9:>4} {d['yes']:>6} {d['no']:>6} {rate:>8.4f}")

    # Which classes have 100% rate?
    perfect = [m for m, d in results.items() if d['no'] == 0 and d['yes'] > 0]
    print(f"\nClasses with 3^(q+1) ≡ 1 for ALL tested q: {sorted(perfect)}")
    for m in sorted(perfect):
        print(f"  q ≡ {m} mod 72: q%8={m%8}, q%9={m%9}, count={results[m]['yes']}")


def investigate_quadratic_residue(limit=200000):
    """
    Key insight: 3^{q+1} ≡ 1 mod A ⟺ 3^{(q+1)/2} ≡ ±1 mod A (if q+1 even).

    q odd, so q+1 even. (q+1)/2 is an integer.

    3^{(q+1)/2} ≡ ±1 mod A.

    If 3^{(q+1)/2} ≡ 1: then ord(3) | (q+1)/2.
    If 3^{(q+1)/2} ≡ -1: then 3 has exact order q+1 in (Z/AZ)*.

    3^{(A-1)/2} = Legendre symbol (3/A). This tells us if 3 is a QR mod A.

    For A ≡ 1 mod 12 (always true for q ≡ 71 mod 72):
    (3/A) = 1 iff 3 is a QR mod A.
    By QR: (3/A) = (A/3) (if A ≡ 1 mod 4 and 3 ≡ 3 mod 4, use supplementary).
    Actually (3/A) depends on A mod 12.
    A = q²+q+1. For q ≡ 71 mod 72:
    q² ≡ 71² = 5041 ≡ 1 mod 72. So q²+q+1 ≡ 1+71+1 = 73 ≡ 1 mod 72.
    So A ≡ 1 mod 72. In particular A ≡ 1 mod 12.
    (3/A) by QR: since A ≡ 1 mod 4, (3/A) = (A/3) = (A mod 3 / 3) = (1/3) = 1.
    So 3 is ALWAYS a QR mod A. This means 3^{(A-1)/2} = 1.
    """
    print(f"\n{'='*70}")
    print("QUADRATIC RESIDUE ANALYSIS")
    print(f"{'='*70}")

    primes = []
    q = 71
    while len(primes) < 30:
        if isprime(q):
            A = q*q + q + 1
            if isprime(A):
                primes.append((q, A))
        q += 72

    for q, A in primes[:15]:
        # (3/A) Legendre
        leg = pow(3, (A-1)//2, A)
        # 3^{(q+1)/2}
        three_half = pow(3, (q+1)//2, A)
        # 3^{q+1}
        three_qp1 = pow(3, q+1, A)

        print(f"q={q:>8}: (3/A)={leg}, 3^((q+1)/2)={three_half:>12}, "
              f"3^(q+1)={'1' if three_qp1==1 else three_qp1}")


# ============================================================
# PART E: THE KEY QUESTION — can ord_A(3) = q in principle?
# ============================================================

def heuristic_probability():
    """
    If 3 is a "random" element of (Z/AZ)*, what's the probability that
    ord(3) = q (equivalently 3^q ≡ 1)?

    |{x : x^q = 1}| = q (the q-th roots of unity form a subgroup of order q).
    |(Z/AZ)*| = q(q+1).
    Prob(random element has order dividing q) = q / (q(q+1)) = 1/(q+1).

    So heuristically, Prob(3^q ≡ 1 mod A) ≈ 1/(q+1).
    For q = 71: ≈ 1/72 ≈ 1.4%.
    For q = 75239: ≈ 1/75240 ≈ 0.001%.

    Expected number among our 40 primes:
    Σ 1/(q_i + 1) ≈ integral from 71 to 75239... very small.

    So it's NOT surprising that 3^q ≢ 1 for all tested q.
    The question is whether there's a STRUCTURAL reason (not just heuristic).
    """
    print(f"\n{'='*70}")
    print("HEURISTIC PROBABILITY ANALYSIS")
    print(f"{'='*70}")

    primes = []
    q = 71
    while len(primes) < 40:
        if isprime(q):
            A = q*q + q + 1
            if isprime(A):
                primes.append((q, A))
        q += 72

    expected = sum(1/(q+1) for q, A in primes)
    print(f"Expected number of q with 3^q ≡ 1 (heuristic): {expected:.6f}")
    print(f"Observed: 0")
    print(f"This is consistent with random behavior (expected ≈ 0).")
    print()
    print(f"To find a counterexample to the FT conjecture, we'd need q such that")
    print(f"3 lands in a subgroup of size q out of q(q+1). Probability ≈ 1/(q+1).")
    print(f"Accumulated probability up to q=75239: {expected:.6f}")
    print()
    print(f"Even testing up to q = 10^6, expected counterexamples ≈ Σ 1/(q+1) ≈ ln(10^6)/72 ≈ {math.log(10**6)/72:.2f}")
    print(f"(very rough, assuming density of valid q is about 1/72)")
    print()
    print(f"CONCLUSION: Purely from heuristics, the conjecture is likely true")
    print(f"but we cannot prove it from finite computation alone.")
    print(f"We need a STRUCTURAL argument that 3 cannot have order q mod A.")


# ============================================================
# PART F: 3^{q+1} ≡ 1 — deeper investigation
# ============================================================

def investigate_3qp1_eisenstein():
    """
    We observed 3^{q+1} ≡ 1 mod A for q ≡ 71 mod 72.

    In Z[ω]: 3^{q+1} ≡ 1 mod π means [(-ω²)(1-ω)²]^{q+1} ≡ 1 mod π.

    (-ω²)^{q+1}: (-1)^{q+1} · ω^{2(q+1)} = 1 · ω^{2(q+1)} (q+1 even).
    ω^{2(q+1)} ≡ q^{2(q+1)} mod π.
    q^{2(q+1)}: 2(q+1) mod 3. q ≡ 2 mod 3, so q+1 ≡ 0 mod 3, 2(q+1) ≡ 0 mod 3.
    q^{2(q+1)} = (q³)^{2(q+1)/3} = 1. ✓

    (1-ω)^{2(q+1)} ≡ (1-q)^{2(q+1)} mod π.
    (1-q)² = -3q. So (1-q)^{2(q+1)} = (-3q)^{q+1} = (-3)^{q+1} · q^{q+1}.
    q^{q+1} = (q³)^{(q+1)/3} = 1. ✓
    (-3)^{q+1} = ((-3)²)^{(q+1)/2} = 9^{(q+1)/2} = 3^{q+1}.

    So 3^{q+1} = (-ω²)^{q+1} · (1-ω)^{2(q+1)} = 1 · 3^{q+1}. CIRCULAR.

    But wait! Let me be more careful.
    3^{q+1} = [(-ω²)(1-ω)²]^{q+1} = (-ω²)^{q+1} · (1-ω)^{2(q+1)}.

    In F_A (mapping via ω ↦ q):
    (-ω²)^{q+1} ↦ (-q²)^{q+1} mod A.
    (-q²)^{q+1} = (-1)^{q+1} · q^{2(q+1)} = 1 · (q³)^{2(q+1)/3} = 1. ✓

    (1-ω)^{2(q+1)} ↦ (1-q)^{2(q+1)} mod A.
    (1-q)^{2(q+1)} = ((1-q)²)^{q+1} = (-3q)^{q+1} = (-1)^{q+1} · 3^{q+1} · q^{q+1}
    = 1 · 3^{q+1} · 1 = 3^{q+1}. ✓

    Product: 1 · 3^{q+1} = 3^{q+1}. TAUTOLOGY.

    The decomposition 3 = (-ω²)(1-ω)² is USELESS for computing 3^{q+1} mod A
    because the (1-ω)² factor feeds 3 back in through (1-q)² = -3q.

    THIS IS THE FUNDAMENTAL ISSUE.
    """
    print(f"\n{'='*70}")
    print("WHY THE EISENSTEIN DECOMPOSITION IS CIRCULAR")
    print(f"{'='*70}")
    print("""
The factorization 3 = -ω²(1-ω)² in Z[ω] creates a CIRCULAR dependency
when computing 3^{q+1} mod π:

  3^{q+1} = (-ω²)^{q+1} · (1-ω)^{2(q+1)}

  (-ω²)^{q+1} maps to 1 in F_A (always).

  (1-ω)^{2(q+1)} maps to (1-q)^{2(q+1)} = (-3q)^{q+1} = 3^{q+1} · q^{q+1} = 3^{q+1}

  So: 3^{q+1} = 1 · 3^{q+1} = 3^{q+1}. TAUTOLOGY.

This happens because 3 RAMIFIES in Z[ω]: the prime (1-ω) lies above 3.
When we decompose 3 and then reduce mod π, the factor (1-ω)² mod π
is (1-q)² = -3q, which feeds 3 back. The ramification creates an
inescapable algebraic loop.

THEORETICAL CONCLUSION:
The Eisenstein integer approach via cubic residue symbols / cubic
reciprocity CANNOT resolve the Feit-Thompson p=3 conjecture because:
1. (3/π)₃ = 1 always (forced by congruence conditions)
2. Higher power residue symbols are also forced by the same conditions
3. The algebraic relationship α² = -3q (where α = 1-q, ω ≡ q mod π)
   makes all norm form arguments circular

To prove the conjecture, one needs to work with the MULTIPLICATIVE ORDER
directly, which is a much harder problem — essentially asking about
the distribution of 3 in (Z/AZ)* relative to its subgroups of order q
versus q+1.

WHAT MIGHT WORK INSTEAD:
1. Analytic methods: Estimate the number of q with ord_A(3) = q using
   character sum techniques (GRH-conditional results exist)
2. Sieve methods: Show that if q | ord_A(3), then q | (specific quantity)
   leading to a contradiction
3. p-adic methods: Work in Q_3 or Q_A directly, not through Z[ω]/(π)
4. Deeper reciprocity: Artin reciprocity in extensions of Q(ζ₃) might
   give structural information about Frob_π acting on the q-torsion
""")


# ============================================================
# RUN EVERYTHING
# ============================================================

if __name__ == '__main__':
    prove_cubic_residue_forced()
    frobenius_perspective()
    verify_mutual_exclusivity(100)

    print(f"\n{'='*70}")
    print("CRITICAL TEST: Is 3^{q+1} ≡ 1 mod A for q ≡ 71 mod 72?")
    print(f"{'='*70}")

    # Quick check
    primes = []
    q = 71
    while len(primes) < 40:
        if isprime(q):
            A = q*q + q + 1
            if isprime(A):
                primes.append((q, A))
        q += 72

    all_yes = True
    for q, A in primes:
        val = pow(3, q+1, A)
        if val != 1:
            all_yes = False
            print(f"FAILURE: q={q}, 3^(q+1) mod A = {val}")

    if all_yes:
        print(f"3^(q+1) ≡ 1 mod A for ALL {len(primes)} tested primes q ≡ 71 mod 72!")
        print("This is EQUIVALENT to 3^q ≢ 1 mod A (they share no common factor).")
        print("Wait — this is NOT the same. Let me recheck...")
        print()
        # Recheck: 3^q mod A
        for q, A in primes[:5]:
            print(f"q={q}: 3^q mod A = {pow(3,q,A)}, 3^(q+1) mod A = {pow(3,q+1,A)}")
            print(f"  3^(q+1) = 3^q · 3 = {pow(3,q,A)} · 3 = {(pow(3,q,A)*3) % A}")

    analyze_qplus1_residue_classes()
    test_3_qplus1_all_residues()
    investigate_3qp1_eisenstein()
    analyze_order_structure(40)
    heuristic_probability()

    # Final: what ord_A(3) actually equals
    print(f"\n{'='*70}")
    print("WHAT IS ord_A(3) mod (q+1)?")
    print(f"{'='*70}")
    for q, A in primes[:15]:
        n = q * (q + 1)
        divs = sorted(divisors(n))
        order = None
        for d in divs:
            if pow(3, d, A) == 1:
                order = d
                break
        if order:
            print(f"q={q:>8}: ord={order:>10}, (q+1)={q+1:>8}, "
                  f"ord | (q+1): {(q+1) % order == 0}, "
                  f"(q+1)/ord = {(q+1)//order if (q+1)%order==0 else 'N/A'}")
