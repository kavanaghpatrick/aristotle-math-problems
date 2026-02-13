#!/usr/bin/env python3
"""
Feit-Thompson p=3 case: Exploration for q ≡ 71 (mod 72)

We need to prove 3^q ≢ 1 (mod A) where A = q²+q+1, q prime, q ≡ 2 mod 3.
The remaining open case is q ≡ 71 (mod 72), i.e. q ≡ 7 mod 8 AND q ≡ 8 mod 9.

Strategy: Compute power residue characters and look for universal patterns.
"""

from sympy import isprime, factorint, primitive_root
from collections import Counter, defaultdict
import sys

def find_eligible_primes(limit=10000):
    """Find primes q < limit with q ≡ 71 mod 72 and A = q²+q+1 prime."""
    eligible = []
    for q in range(71, limit, 72):
        if not isprime(q):
            continue
        A = q*q + q + 1
        if isprime(A):
            eligible.append((q, A))
    return eligible

def compute_characters(q, A):
    """Compute various power residue characters mod A."""
    results = {}

    # Basic elements
    one_minus_q = (1 - q) % A  # = A + 1 - q
    q_mod = q % A
    three_mod = 3 % A
    q_plus_2 = (q + 2) % A

    # Verify basic algebraic facts
    assert pow(q_mod, 3, A) == 1, f"q³ ≠ 1 mod A for q={q}"

    # Check (1-q)² ≡ -3q mod A
    lhs = pow(one_minus_q, 2, A)
    rhs = (-3 * q) % A
    assert lhs == rhs, f"(1-q)² ≠ -3q mod A for q={q}"

    # Check (1-q)(q+2) = 3 mod A
    prod = (one_minus_q * q_plus_2) % A
    assert prod == 3, f"(1-q)(q+2) ≠ 3 mod A for q={q}"

    # 3^q mod A — should NOT be 1 (confirming conjecture)
    three_to_q = pow(3, q, A)
    results['3^q mod A'] = three_to_q
    results['3^q = 1?'] = (three_to_q == 1)

    # Order of 3 mod A
    # A-1 = q² + q, so possible orders divide q²+q = q(q+1)
    results['A-1'] = A - 1
    results['A-1 factored'] = factorint(A - 1)

    # Power residue characters for various elements and orders k
    # χ_k(x) = x^{(A-1)/k} mod A
    for k in [2, 3, 4, 6, 8, 9, 12, 18, 24, 36]:
        if (A - 1) % k != 0:
            continue
        exp = (A - 1) // k

        for name, val in [('1-q', one_minus_q), ('q', q_mod), ('3', three_mod),
                          ('q+2', q_plus_2), ('-3', (-3) % A), ('-1', A-1),
                          ('q+1', (q+1) % A), ('-q', (-q) % A)]:
            key = f'χ_{k}({name})'
            results[key] = pow(val, exp, A)

    # Special: check 3^{(A-1)/k} for small k
    for k in [2, 3, 4, 6, 8, 12, 24]:
        if (A - 1) % k != 0:
            continue
        exp = (A - 1) // k
        results[f'3^((A-1)/{k})'] = pow(3, exp, A)

    # Check (1-q)^{(A-1)/12} — this could give 12th root of unity
    if (A - 1) % 12 == 0:
        val12 = pow(one_minus_q, (A-1)//12, A)
        results['(1-q)^((A-1)/12)'] = val12
        # What power of a primitive 12th root is this?
        # Check: is val12^12 = 1?
        assert pow(val12, 12, A) == 1

    # Compute the actual order of 3 mod A
    order_3 = None
    am1 = A - 1
    factors_am1 = factorint(am1)
    order_3 = am1
    for p_factor in factors_am1:
        while order_3 % p_factor == 0 and pow(3, order_3 // p_factor, A) == 1:
            order_3 //= p_factor
    results['ord(3)'] = order_3

    # Compute order of (1-q) mod A
    order_1mq = am1
    for p_factor in factors_am1:
        while order_1mq % p_factor == 0 and pow(one_minus_q, order_1mq // p_factor, A) == 1:
            order_1mq //= p_factor
    results['ord(1-q)'] = order_1mq

    # Compute order of (q+2) mod A
    order_qp2 = am1
    for p_factor in factors_am1:
        while order_qp2 % p_factor == 0 and pow(q_plus_2, order_qp2 // p_factor, A) == 1:
            order_qp2 //= p_factor
    results['ord(q+2)'] = order_qp2

    return results

def find_roots_of_unity(A, k):
    """Find all k-th roots of unity mod A."""
    if (A - 1) % k != 0:
        return set()
    exp = (A - 1) // k
    g = primitive_root(A)
    roots = set()
    for j in range(k):
        roots.add(pow(g, j * exp, A))
    return roots

def identify_root(val, A, k):
    """Identify which k-th root of unity val is (as index j where ζ^j = val)."""
    g = primitive_root(A)
    exp = (A - 1) // k
    for j in range(k):
        if pow(g, j * exp, A) == val:
            return j
    return None

def main():
    print("=" * 80)
    print("Feit-Thompson p=3: Exploring q ≡ 71 (mod 72) case")
    print("=" * 80)

    primes = find_eligible_primes(10000)
    print(f"\nFound {len(primes)} eligible primes q < 10000 with q ≡ 71 mod 72 and A prime:")
    for q, A in primes:
        print(f"  q = {q}, A = {A}")

    if not primes:
        print("No eligible primes found! Extending search...")
        primes = find_eligible_primes(50000)
        print(f"Found {len(primes)} eligible primes q < 50000")
        for q, A in primes[:20]:
            print(f"  q = {q}, A = {A}")

    print("\n" + "=" * 80)
    print("SECTION 1: Verify conjecture holds (3^q ≠ 1 mod A)")
    print("=" * 80)

    all_results = []
    for q, A in primes:
        res = compute_characters(q, A)
        all_results.append((q, A, res))
        status = "COUNTEREXAMPLE!" if res['3^q = 1?'] else "OK (≠ 1)"
        print(f"  q={q}: 3^q mod A = {res['3^q mod A']}  [{status}]")

    print("\n" + "=" * 80)
    print("SECTION 2: Orders of key elements")
    print("=" * 80)

    for q, A, res in all_results:
        print(f"\n  q={q}, A={A}, A-1={res['A-1']}")
        print(f"    A-1 factored: {res['A-1 factored']}")
        print(f"    ord(3) = {res['ord(3)']}")
        print(f"    ord(1-q) = {res['ord(1-q)']}")
        print(f"    ord(q+2) = {res['ord(q+2)']}")
        # Check: does ord(3) divide q? (would mean 3^q = 1)
        print(f"    ord(3) | q? {res['ord(3)'] != 0 and q % res['ord(3)'] == 0}")
        # What's q mod ord(3)?
        print(f"    q mod ord(3) = {q % res['ord(3)']}")

    print("\n" + "=" * 80)
    print("SECTION 3: Power residue characters — looking for universals")
    print("=" * 80)

    # Collect character values across all primes
    char_values = defaultdict(list)
    for q, A, res in all_results:
        for key, val in res.items():
            if key.startswith('χ_') or key.startswith('3^((A-1)'):
                char_values[key].append((q, val))

    # For each character, check if the value is "universal" in some sense
    print("\n  Checking for universal character values...")
    for key in sorted(char_values.keys()):
        vals = char_values[key]
        unique_vals = set(v for _, v in vals)
        if len(unique_vals) == 1:
            v = list(unique_vals)[0]
            print(f"  *** UNIVERSAL: {key} = {v} for all q ***")
        else:
            # Check if value is always ≠ 1
            all_ne_1 = all(v != 1 for _, v in vals)
            if all_ne_1 and '3' in key:
                print(f"  ** {key}: always ≠ 1 (but varies): {sorted(unique_vals)}")
            elif len(unique_vals) <= 4:
                print(f"  {key}: takes values {sorted(unique_vals)}")

    print("\n" + "=" * 80)
    print("SECTION 4: Detailed 12th root analysis")
    print("=" * 80)

    for q, A, res in all_results:
        if (A - 1) % 12 != 0:
            print(f"  q={q}: 12 ∤ (A-1), skipping")
            continue

        one_minus_q = (1 - q) % A
        three_mod = 3 % A
        q_mod = q % A
        q_plus_2 = (q + 2) % A

        # Find primitive 12th root
        g = primitive_root(A)
        exp12 = (A - 1) // 12
        zeta12 = pow(g, exp12, A)

        # Express (1-q)^{(A-1)/12} as power of ζ₁₂
        val = pow(one_minus_q, exp12, A)
        idx = None
        for j in range(12):
            if pow(zeta12, j, A) == val:
                idx = j
                break

        # Same for 3
        val3 = pow(three_mod, exp12, A)
        idx3 = None
        for j in range(12):
            if pow(zeta12, j, A) == val3:
                idx3 = j
                break

        # Same for q
        valq = pow(q_mod, exp12, A)
        idxq = None
        for j in range(12):
            if pow(zeta12, j, A) == valq:
                idxq = j
                break

        # Same for q+2
        valqp2 = pow(q_plus_2, exp12, A)
        idxqp2 = None
        for j in range(12):
            if pow(zeta12, j, A) == valqp2:
                idxqp2 = j
                break

        print(f"  q={q}: (1-q)^((A-1)/12) = ζ₁₂^{idx}, "
              f"3^((A-1)/12) = ζ₁₂^{idx3}, "
              f"q^((A-1)/12) = ζ₁₂^{idxq}, "
              f"(q+2)^((A-1)/12) = ζ₁₂^{idxqp2}")

        # Check: idx for (1-q) + idx for (q+2) should = idx for 3 (mod 12)
        # since (1-q)(q+2) = 3
        if idx is not None and idxqp2 is not None and idx3 is not None:
            print(f"    Check: {idx} + {idxqp2} = {(idx + idxqp2) % 12} vs idx3={idx3} (mod 12)")

    print("\n" + "=" * 80)
    print("SECTION 5: Quadratic character of 3 and deeper analysis")
    print("=" * 80)

    for q, A, res in all_results:
        three_mod = 3 % A

        # Legendre symbol (3/A)
        leg_3 = pow(three_mod, (A-1)//2, A)

        # By QR: (3/A) depends on A mod 12
        A_mod_12 = A % 12

        # Also: A = q²+q+1. For q ≡ 71 mod 72:
        # q ≡ 7 mod 8, q ≡ 8 mod 9
        # q² ≡ 1 mod 8, q²+q+1 ≡ 1+7+1 = 9 ≡ 1 mod 8
        # So A ≡ 1 mod 8 → (2/A) = 1
        # q² ≡ 64 ≡ 1 mod 9, q²+q+1 ≡ 1+8+1 = 10 ≡ 1 mod 9
        # So A ≡ 1 mod 9 → A ≡ 1 mod 3
        # A mod 12: A ≡ 1 mod 8, A ≡ 1 mod 3 → A ≡ 1 mod 24

        print(f"  q={q}: A mod 24 = {A % 24}, (3/A) = {'+1' if leg_3 == 1 else '-1'}")

    print("\n" + "=" * 80)
    print("SECTION 6: Cubic character of 3 (since 3 | A-1)")
    print("=" * 80)

    for q, A, res in all_results:
        # A ≡ 1 mod 3, so cubic characters exist
        three_mod = 3 % A
        exp3 = (A - 1) // 3
        chi3_of_3 = pow(three_mod, exp3, A)

        # Since A ≡ 1 mod 9, we also have 9th power residue
        if (A - 1) % 9 == 0:
            exp9 = (A - 1) // 9
            chi9_of_3 = pow(three_mod, exp9, A)
        else:
            chi9_of_3 = "N/A"

        print(f"  q={q}: χ₃(3) = {chi3_of_3}, 3^((A-1)/3) mod A")
        if chi9_of_3 != "N/A":
            # Identify as 9th root
            g = primitive_root(A)
            exp9 = (A - 1) // 9
            zeta9 = pow(g, exp9, A)
            idx9 = None
            for j in range(9):
                if pow(zeta9, j, A) == chi9_of_3:
                    idx9 = j
                    break
            print(f"         χ₉(3) = ζ₉^{idx9}")

    print("\n" + "=" * 80)
    print("SECTION 7: Interaction of quadratic and cubic characters")
    print("=" * 80)

    print("\n  Key question: Can we combine (3/A) = +1 with cubic character info?")
    print("  Since A ≡ 1 mod 24, both quadratic and cubic characters of 3 exist.")
    print("  The 6th power residue character χ₆(3) = 3^{(A-1)/6} combines both.\n")

    chi6_vals = []
    for q, A, res in all_results:
        three_mod = 3 % A
        if (A - 1) % 6 == 0:
            exp6 = (A - 1) // 6
            chi6 = pow(three_mod, exp6, A)

            g = primitive_root(A)
            zeta6 = pow(g, (A-1)//6, A)
            idx6 = None
            for j in range(6):
                if pow(zeta6, j, A) == chi6:
                    idx6 = j
                    break
            chi6_vals.append(idx6)
            print(f"  q={q}: χ₆(3) = ζ₆^{idx6}")

    unique_chi6 = set(chi6_vals)
    print(f"\n  χ₆(3) values across all q: {sorted(unique_chi6)}")
    if 0 not in unique_chi6:
        print("  *** χ₆(3) is NEVER 1 (= ζ₆^0) → 3 is never a 6th power residue! ***")

    print("\n" + "=" * 80)
    print("SECTION 8: What if 3^q ≡ 1? Derive consequences and check")
    print("=" * 80)

    print("\n  If 3^q ≡ 1 mod A, then ord(3) | q. Since q is prime, ord(3) = 1 or q.")
    print("  ord(3) = 1 means 3 ≡ 1 mod A, impossible for A > 2.")
    print("  So ord(3) = q. Then 3^q ≡ 1 means q | (A-1) = q(q+1).")
    print("  Indeed q | q(q+1). So the order condition is consistent.")
    print("  But: 3^{(A-1)/q} = 3^{q+1} ≡ 3·(3^q) ≡ 3 (mod A) if 3^q=1.")
    print("  Wait: 3^{q+1} = 3^q · 3 = 1·3 = 3. So 3^{(A-1)/q} ≡ 3 mod A.")
    print("  This means 3 is a q-th power residue iff 3 ≡ 3 mod A, tautological.\n")

    print("  But also: if ord(3) = q, then 3 generates a subgroup of order q in (Z/AZ)*.")
    print("  The group (Z/AZ)* has order A-1 = q(q+1).")
    print("  q+1 is even (q ≡ 71 mod 72 → q is odd → q+1 even).\n")

    # Under assumption ord(3) = q, check what (A-1)/q = q+1 tells us
    for q, A, res in all_results:
        three_mod = 3 % A
        # 3^{q+1} mod A
        val = pow(three_mod, q+1, A)
        print(f"  q={q}: 3^(q+1) mod A = {val} (should = 3 if 3^q=1, actual 3^q={res['3^q mod A']})")

    print("\n" + "=" * 80)
    print("SECTION 9: Deeper — (A-1)/k characters of 3 for all k | (A-1)")
    print("=" * 80)

    # For each q, compute 3^{(A-1)/p} for each prime p dividing A-1
    for q, A, res in all_results[:5]:  # first 5 for readability
        am1 = A - 1
        prime_divs = list(factorint(am1).keys())
        print(f"\n  q={q}, A-1={am1}, prime divisors: {prime_divs}")
        for p in prime_divs:
            exp_val = am1 // p
            val = pow(3, exp_val, A)
            is_one = (val == 1)
            print(f"    3^((A-1)/{p}) = {val} {'= 1 (3 is p-th power res)' if is_one else '≠ 1'}")

    print("\n" + "=" * 80)
    print("SECTION 10: Norm-based approach — N(1-q) in Z[ω]")
    print("=" * 80)

    print("\n  Since A = q²+q+1 = Φ₃(q), the ring Z[ω]/(A) where ω = e^{2πi/3}")
    print("  has the property that q ≡ ω (a cube root of unity) in some sense.")
    print("  More precisely: q is a primitive cube root of unity mod A.")
    print("  So 1-q plays the role of 1-ω in this ring.")
    print("  N(1-ω) = (1-ω)(1-ω²) = 1 - ω - ω² + ω³ = 1 - (-1) + 1 = 3")
    print("  Indeed (1-q)(1-q²) ≡ 3 mod A. Let's verify:\n")

    for q, A, res in all_results:
        one_minus_q = (1 - q) % A
        q_sq = pow(q, 2, A)
        one_minus_q2 = (1 - q_sq) % A
        prod = (one_minus_q * one_minus_q2) % A
        # (1-q)(1-q²) = (1-q)(1-q)(1+q) = (1-q)²(1+q)
        # But also = 1 - q - q² + q³ = 1 - q - q² + 1 = 2 - q - q²
        # And q² + q + 1 = A ≡ 0, so q² = -q - 1, so 2 - q - (-q-1) = 2 - q + q + 1 = 3
        print(f"  q={q}: (1-q)(1-q²) mod A = {prod} (should be 3)")

    print("\n" + "=" * 80)
    print("SECTION 11: Key test — is ord(3) always NOT divisible by large primes of q+1?")
    print("=" * 80)

    for q, A, res in all_results:
        am1 = A - 1  # = q(q+1)
        ord3 = res['ord(3)']
        qp1 = q + 1
        qp1_factors = factorint(qp1)

        print(f"\n  q={q}: ord(3)={ord3}, q+1={qp1}={dict(qp1_factors)}")
        print(f"    A-1 = q(q+1) = {q}·{qp1}")
        print(f"    ord(3) / gcd(ord(3), q) = {ord3 // (ord3 if q % ord3 == 0 else 1) if ord3 != 0 else 'N/A'}")

        # Factor ord(3)
        ord3_factors = factorint(ord3)
        print(f"    ord(3) factored: {dict(ord3_factors)}")

        # Does q divide ord(3)?
        print(f"    q | ord(3)? {ord3 % q == 0}")
        # Does (q+1) divide ord(3)?
        print(f"    (q+1) | ord(3)? {ord3 % qp1 == 0}")

        # What's ord(3) / q if q | ord(3)?
        if ord3 % q == 0:
            ratio = ord3 // q
            print(f"    ord(3)/q = {ratio}, factors: {dict(factorint(ratio))}")

    print("\n" + "=" * 80)
    print("SECTION 12: Sextic residue symbol via Eisenstein integers")
    print("=" * 80)

    print("\n  In Z[ω], π = 1-ω is the unique prime above 3.")
    print("  The sextic residue symbol (α/π)₆ for α ∈ Z[ω] coprime to π")
    print("  satisfies α^{(Nπ-1)/6} ≡ (α/π)₆ mod π.")
    print("  Here Nπ = 3, so this is just α mod π = α mod (1-ω).")
    print("  But we want the symbol at A, not at 3.\n")

    print("  Let's think differently: A = Φ₃(q) splits in Z[ω] as")
    print("  A = (q-ω)(q-ω²) = ππ̄ where π_A = q-ω, π̄_A = q-ω².")
    print("  The sextic residue symbol (3/π_A)₆ = 3^{(Nπ_A - 1)/6} mod π_A")
    print("  where Nπ_A = A. So (3/π_A)₆ = 3^{(A-1)/6} mod A.\n")

    print("  Computing (3/π_A)₆ = 3^{(A-1)/6} mod A for each q:")

    sextic_indices = []
    for q, A, res in all_results:
        if (A - 1) % 6 != 0:
            continue
        val = pow(3, (A-1)//6, A)
        g = primitive_root(A)
        zeta6 = pow(g, (A-1)//6, A)
        idx = None
        for j in range(6):
            if pow(zeta6, j, A) == val:
                idx = j
                break
        sextic_indices.append(idx)
        print(f"  q={q}: (3/π_A)₆ = ζ₆^{idx}  [val={val}]")

    unique_sextic = set(sextic_indices)
    print(f"\n  Sextic residue symbol values: {sorted(unique_sextic)}")
    if 0 not in unique_sextic:
        print("  *** 3 is NEVER a sextic residue mod A! This could be the proof! ***")
        print("  If we can prove (3/π_A)₆ ≠ 1 universally, then ord(3) ∤ (A-1)/6")
        print("  which means ord(3) must have the full factor of 6 from A-1.")

    print("\n" + "=" * 80)
    print("SECTION 13: What does ord(3) = q imply for sextic character?")
    print("=" * 80)

    print("\n  If ord(3) = q, then 3^{(A-1)/6} = 3^{q(q+1)/6}.")
    print("  Since 3^q = 1 under assumption: 3^{q(q+1)/6} = (3^q)^{(q+1)/6} = 1^{(q+1)/6} = 1.")
    print("  Wait — this requires 6 | (q+1). Let's check:\n")

    for q, A, res in all_results:
        qp1 = q + 1
        print(f"  q={q}: q+1={qp1}, 6|(q+1)? {qp1 % 6 == 0}, "
              f"q mod 6 = {q % 6}")

    print("\n  q ≡ 71 mod 72 → q ≡ 71 mod 72. 71 mod 6 = 5. So q ≡ 5 mod 6 → q+1 ≡ 0 mod 6.")
    print("  YES! 6 always divides q+1 for q ≡ 71 mod 72.")
    print("  So if ord(3) = q, then 3^{(A-1)/6} = 1, i.e., 3 IS a sextic residue.")
    print("  CONTRAPOSITIVE: If 3 is NOT a sextic residue, then ord(3) ≠ q, so 3^q ≠ 1!")
    print("  *** THIS IS THE KEY INSIGHT IF (3/π_A)₆ ≠ 1 universally! ***")

    print("\n" + "=" * 80)
    print("SECTION 14: Can we PROVE (3/π_A)₆ ≠ 1 using sextic reciprocity?")
    print("=" * 80)

    print("\n  Sextic reciprocity in Z[ω]: For primary primes π, λ in Z[ω],")
    print("  (π/λ)₆ = (λ/π)₆")
    print("  (with conditions on primary normalization)")
    print("")
    print("  Here: 3 = -ω²(1-ω)² in Z[ω], and π_A = q - ω.")
    print("  The prime (1-ω) has norm 3.")
    print("  So (3/π_A)₆ involves the symbol ((1-ω)²/π_A)₆ · (-ω²/π_A)₆")
    print("  = ((1-ω)/π_A)₆² · (-ω²/π_A)₆")
    print("")
    print("  By sextic reciprocity: ((1-ω)/π_A)₆ = (π_A/(1-ω))₆ (up to correction)")
    print("  And (π_A/(1-ω))₆ = (q-ω mod (1-ω))₆.")
    print("  Since ω ≡ 1 mod (1-ω): q - ω ≡ q - 1 mod (1-ω).")
    print("  In Z[ω]/(1-ω) ≅ F₃: q-1 mod 3.")
    print("  q ≡ 71 mod 72 → q ≡ 2 mod 3 → q-1 ≡ 1 mod 3.")
    print("  So (π_A/(1-ω))₆ = (1 mod 3) in F₃*, which needs careful interpretation.\n")

    # Let's compute more carefully with the Eisenstein structure
    print("  Let's verify computationally what (1-q)^{(A-1)/6} looks like:")
    for q, A, res in all_results:
        if (A - 1) % 6 != 0:
            continue
        one_minus_q = (1 - q) % A
        val = pow(one_minus_q, (A-1)//6, A)
        g = primitive_root(A)
        zeta6 = pow(g, (A-1)//6, A)
        idx = None
        for j in range(6):
            if pow(zeta6, j, A) == val:
                idx = j
                break
        print(f"  q={q}: (1-q)^((A-1)/6) = ζ₆^{idx}")

    print("\n" + "=" * 80)
    print("SECTION 15: Extended exploration — higher power residues")
    print("=" * 80)

    # Check various k-th power residue of 3
    for k in [4, 8, 12, 18, 24, 36]:
        vals_k = []
        applicable = True
        for q, A, res in all_results:
            if (A - 1) % k != 0:
                applicable = False
                break
            val = pow(3, (A-1)//k, A)
            g = primitive_root(A)
            zetak = pow(g, (A-1)//k, A)
            idx = None
            for j in range(k):
                if pow(zetak, j, A) == val:
                    idx = j
                    break
            vals_k.append(idx)

        if not applicable:
            print(f"  k={k}: not always applicable (k ∤ A-1 for some q)")
            continue

        unique = set(vals_k)
        is_never_1 = 0 not in unique
        print(f"  3^((A-1)/{k}): indices = {sorted(unique)}, "
              f"{'NEVER 1' if is_never_1 else 'sometimes 1'}")

    print("\n" + "=" * 80)
    print("SECTION 16: The (q+1)/6 exponent — direct test")
    print("=" * 80)

    print("\n  We showed: if 3^q = 1, then 3^{(A-1)/6} = 3^{q·(q+1)/6} = (3^q)^{(q+1)/6} = 1.")
    print("  So (3/A)₆ = 1 is NECESSARY for 3^q = 1.")
    print("  If we can show (3/A)₆ ≠ 1, we're done.\n")
    print("  Let's also check: what about (A-1)/4?")
    print("  If 3^q = 1: 3^{(A-1)/4} = 3^{q(q+1)/4}. Need 4 | q(q+1).")
    print("  q is odd, q+1 is even. q ≡ 7 mod 8 → q+1 ≡ 0 mod 8 → 4 | (q+1).")
    print("  So 3^{(A-1)/4} = (3^q)^{(q+1)/4} = 1. So (3/A)₄ = 1 too.\n")

    for q, A, res in all_results:
        # Check 3 is quartic residue?
        if (A - 1) % 4 != 0:
            continue
        val4 = pow(3, (A-1)//4, A)
        is_4th = (val4 == 1)

        # Check 3 is sextic residue?
        if (A - 1) % 6 != 0:
            continue
        val6 = pow(3, (A-1)//6, A)
        is_6th = (val6 == 1)

        # Check 3 is 12th power residue?
        if (A - 1) % 12 != 0:
            continue
        val12 = pow(3, (A-1)//12, A)
        is_12th = (val12 == 1)

        # Under assumption: 3^q = 1 implies 3^{q(q+1)/12} = 1 iff 12 | q(q+1)
        # q ≡ 7 mod 8 → q+1 ≡ 0 mod 8. q ≡ 8 mod 9 → q ≡ 2 mod 3 → q+1 ≡ 0 mod 3.
        # So q+1 ≡ 0 mod 24. And 12 | q(q+1) since 12 | (q+1)·something?
        # Actually need 12 | (q+1). q+1 ≡ 0 mod 8 and q+1 ≡ 0 mod 3, so q+1 ≡ 0 mod 24.
        # So 12 | (q+1), hence 3^{(A-1)/12} = (3^q)^{(q+1)/12} = 1.

        print(f"  q={q}: 3 is 4th-pow-res? {is_4th}, 6th? {is_6th}, 12th? {is_12th}")
        if not is_6th:
            print(f"    *** 3 is NOT a sextic residue mod A! Contradiction with 3^q=1! ***")

    print("\n" + "=" * 80)
    print("SECTION 17: Deeper — what MUST divide ord(3) for 3^q ≠ 1?")
    print("=" * 80)

    print("\n  For each q, computing the full factorization of ord(3):\n")
    ord3_patterns = defaultdict(list)
    for q, A, res in all_results:
        ord3 = res['ord(3)']
        ord3_f = factorint(ord3)
        am1_f = factorint(A - 1)

        # For each prime power p^a || (A-1), what's the p-part of ord(3)?
        parts = {}
        for p, a in am1_f.items():
            p_part = 1
            while ord3 % (p_part * p) == 0:
                p_part *= p
            parts[p] = (p_part, p**a)

        print(f"  q={q}: ord(3) = {ord3} = {dict(ord3_f)}")
        print(f"    A-1 = {dict(am1_f)}")
        for p in sorted(parts):
            ppart, pfull = parts[p]
            print(f"    {p}-part of ord(3): {ppart} out of {pfull}")

        # Record for pattern detection
        for p in sorted(parts):
            ppart, pfull = parts[p]
            ord3_patterns[p].append((q, ppart, pfull))

    print("\n  Pattern summary — minimum p-part of ord(3) across all q:")
    for p in sorted(ord3_patterns):
        min_part = min(pp for _, pp, _ in ord3_patterns[p])
        max_full = max(pf for _, _, pf in ord3_patterns[p])
        print(f"    p={p}: min p-part = {min_part}, max p^a in A-1 = {max_full}")
        if min_part > 1:
            print(f"    *** p={p} ALWAYS divides ord(3)! ***")

    print("\n" + "=" * 80)
    print("SECTION 18: Testing 3^{(A-1)/p} ≠ 1 for each prime p | (A-1)")
    print("=" * 80)

    # For each prime factor p of A-1, check if 3^{(A-1)/p} ≠ 1 universally
    all_prime_factors = set()
    for q, A, res in all_results:
        all_prime_factors.update(factorint(A-1).keys())

    print(f"\n  All prime factors of A-1 across data: {sorted(all_prime_factors)}\n")

    for p_test in sorted(all_prime_factors):
        results_for_p = []
        for q, A, res in all_results:
            if (A - 1) % p_test != 0:
                results_for_p.append((q, 'N/A'))
                continue
            val = pow(3, (A-1)//p_test, A)
            results_for_p.append((q, val == 1))

        always_ne_1 = all(v == False for _, v in results_for_p if v != 'N/A')
        applicable = any(v != 'N/A' for _, v in results_for_p)

        if applicable:
            is_one_count = sum(1 for _, v in results_for_p if v == True)
            ne_one_count = sum(1 for _, v in results_for_p if v == False)
            na_count = sum(1 for _, v in results_for_p if v == 'N/A')

            if always_ne_1 and ne_one_count > 0:
                print(f"  p={p_test}: 3^((A-1)/p) ≠ 1 for ALL {ne_one_count} applicable q "
                      f"{'*** UNIVERSAL! ***' if ne_one_count >= 3 else '(few data points)'}")
            else:
                print(f"  p={p_test}: =1 for {is_one_count}, ≠1 for {ne_one_count}, N/A for {na_count}")

    print("\n" + "=" * 80)
    print("SECTION 19: Combined character — (3·something)^{exponent}")
    print("=" * 80)

    # Try various combinations
    for q, A, res in all_results:
        one_minus_q = (1 - q) % A
        three = 3
        q_mod = q % A

        # 3 = (1-q)(q+2), so maybe look at (q+2)^{(A-1)/k}
        q_plus_2 = (q + 2) % A

        for k in [3, 4, 6, 12]:
            if (A - 1) % k != 0:
                continue
            exp_k = (A - 1) // k

            # (q+2)^{(A-1)/k}
            vqp2 = pow(q_plus_2, exp_k, A)

            g = primitive_root(A)
            zetak = pow(g, (A-1)//k, A)
            idx = None
            for j in range(k):
                if pow(zetak, j, A) == vqp2:
                    idx = j
                    break

        # Just print for first few
        if q == all_results[0][0]:
            print(f"  Example q={q}:")
            for k in [3, 4, 6, 12]:
                if (A - 1) % k != 0:
                    continue
                for name, val in [('3', 3), ('1-q', (1-q)%A), ('q+2', (q+2)%A),
                                  ('q', q%A), ('-3q', (-3*q)%A)]:
                    v = pow(val, (A-1)//k, A)
                    g = primitive_root(A)
                    zetak = pow(g, (A-1)//k, A)
                    idx = None
                    for j in range(k):
                        if pow(zetak, j, A) == v:
                            idx = j
                            break
                    print(f"    {name}^((A-1)/{k}) = ζ_{k}^{idx}")

    print("\n" + "=" * 80)
    print("SECTION 20: CRITICAL — Testing claim: 3 never sextic residue for q≡71 mod 72")
    print("=" * 80)

    # Extended search with more primes
    print("\n  Extending search to q < 50000...")
    extended_primes = find_eligible_primes(50000)
    print(f"  Found {len(extended_primes)} eligible primes\n")

    sextic_never_1 = True
    sextic_results = Counter()

    for q, A in extended_primes:
        if (A - 1) % 6 != 0:
            print(f"  q={q}: 6 ∤ (A-1), UNEXPECTED!")
            continue
        val = pow(3, (A-1)//6, A)
        is_sextic_res = (val == 1)
        sextic_results[is_sextic_res] += 1
        if is_sextic_res:
            sextic_never_1 = False
            print(f"  *** q={q}: 3 IS a sextic residue mod A={A}! ***")

    print(f"\n  Results: sextic residue: {sextic_results[True]}, "
          f"not sextic residue: {sextic_results[False]}")

    if sextic_never_1 and len(extended_primes) > 0:
        print(f"\n  *** CONFIRMED over {len(extended_primes)} primes: "
              f"3 is NEVER a sextic residue mod A for q ≡ 71 mod 72! ***")
        print("  This means: if 3^q = 1 then (3/A)₆ = 1, but (3/A)₆ ≠ 1 always.")
        print("  CONTRADICTION → 3^q ≠ 1 mod A for all such q.")
        print("  Now we need to PROVE this using sextic reciprocity in Z[ω].")
    else:
        print("  The sextic residue approach does NOT give a universal statement.")
        if sextic_results[True] > 0:
            print("  Need a different approach for those cases.")

    print("\n" + "=" * 80)
    print("SECTION 21: If sextic fails, try 12th power residue")
    print("=" * 80)

    twelfth_results = Counter()
    for q, A in extended_primes:
        if (A - 1) % 12 != 0:
            continue
        val = pow(3, (A-1)//12, A)
        is_12th = (val == 1)
        twelfth_results[is_12th] += 1

    print(f"  12th power residue: yes={twelfth_results[True]}, no={twelfth_results[False]}")

    # Also try 24th
    twenty4th_results = Counter()
    for q, A in extended_primes:
        if (A - 1) % 24 != 0:
            twenty4th_results['N/A'] += 1
            continue
        val = pow(3, (A-1)//24, A)
        is_24th = (val == 1)
        twenty4th_results[is_24th] += 1

    print(f"  24th power residue: yes={twenty4th_results.get(True,0)}, "
          f"no={twenty4th_results.get(False,0)}, N/A={twenty4th_results.get('N/A',0)}")

    print("\n" + "=" * 80)
    print("SUMMARY OF FINDINGS")
    print("=" * 80)

    print("""
Key findings from computational exploration:

1. CONJECTURE VERIFIED: 3^q ≠ 1 mod A for all tested q ≡ 71 mod 72 with A prime.

2. ALGEBRAIC FRAMEWORK:
   - A = q²+q+1, A-1 = q(q+1)
   - q ≡ 71 mod 72 → q+1 ≡ 0 mod 24
   - If 3^q = 1 then ord(3) = q, which means:
     * 3^{q(q+1)/k} = (3^q)^{(q+1)/k} = 1 for any k | (q+1)
     * In particular: 3 must be a k-th power residue for k | (q+1)
     * Since 24 | (q+1): 3 must be a 2nd, 3rd, 4th, 6th, 8th, 12th, 24th power residue

3. PROOF STRATEGY: Find the smallest k such that 3 is NEVER a k-th power
   residue mod A for q ≡ 71 mod 72. Then 3^q = 1 is impossible.
""")

if __name__ == '__main__':
    main()
