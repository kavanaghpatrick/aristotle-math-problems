#!/usr/bin/env python3
"""
Feit-Thompson p=3 q≡71 mod 72: DEEP exploration

Key insight from round 1:
- 3 is ALWAYS a 12th power residue mod A (so sextic, quartic etc all fail)
- 3 is NOT always a 24th power residue (50/50 split)
- q ALWAYS divides ord(3) (by Fermat's little theorem in the Fp structure)
- But ord(3) ≠ q because ord(3)/q is always > 1

Focus: What makes ord(3)/q > 1? Can we find a universal obstruction?
"""

from sympy import isprime, factorint, primitive_root, gcd
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
    print("SECTION A: ord(3)/q analysis — what factor of (q+1) appears in ord(3)?")
    print("=" * 80)

    # Key: A-1 = q(q+1). ord(3) = q * d where d | (q+1).
    # We need d > 1 always. What's the minimum d?
    ratios = []
    for q, A in primes:
        # Compute ord(3)
        am1 = A - 1
        am1_f = factorint(am1)
        ord3 = am1
        for p in am1_f:
            while ord3 % p == 0 and pow(3, ord3 // p, A) == 1:
                ord3 //= p

        # d = ord(3) / q (since q | ord(3))
        assert ord3 % q == 0, f"q does not divide ord(3) for q={q}!"
        d = ord3 // q
        d_factors = factorint(d) if d > 1 else {1: 1}

        qp1 = q + 1
        qp1_factors = factorint(qp1)

        ratios.append((q, A, ord3, d, d_factors, qp1, qp1_factors))

    print(f"\n{'q':>8} | {'ord(3)':>12} | {'d=ord(3)/q':>10} | d factors | q+1 factors")
    print("-" * 90)
    for q, A, ord3, d, df, qp1, qf in ratios[:30]:
        print(f"{q:>8} | {ord3:>12} | {d:>10} | {dict(df)} | {dict(qf)}")

    # What's the GCD pattern?
    print(f"\n\nStatistics on d = ord(3)/q:")
    d_vals = [d for _, _, _, d, _, _, _ in ratios]
    print(f"  min(d) = {min(d_vals)}")
    print(f"  max(d) = {max(d_vals)}")
    print(f"  d > 1 always? {all(d > 1 for d in d_vals)}")
    print(f"  d is always odd? {all(d % 2 == 1 for d in d_vals)}")
    print(f"  d is always even? {all(d % 2 == 0 for d in d_vals)}")
    print(f"  3 | d always? {all(d % 3 == 0 for d in d_vals)}")

    # Check: is d always divisible by 3?
    div_by = {}
    for k in [2, 3, 4, 5, 6, 7, 8, 9, 12, 18, 24]:
        div_by[k] = sum(1 for d in d_vals if d % k == 0)
    print(f"\n  Divisibility of d by small numbers (out of {len(d_vals)}):")
    for k, count in sorted(div_by.items()):
        print(f"    {k} | d: {count}/{len(d_vals)} = {100*count/len(d_vals):.1f}%"
              f" {'*** UNIVERSAL ***' if count == len(d_vals) else ''}")

    print("\n" + "=" * 80)
    print("SECTION B: Focus on 2-part and 3-part of d")
    print("=" * 80)

    two_parts = []
    three_parts = []
    for q, A, ord3, d, df, qp1, qf in ratios:
        # 2-part of d
        t = d
        two_part = 0
        while t % 2 == 0:
            two_part += 1
            t //= 2

        # 2-valuation of q+1
        t2 = qp1
        two_val_qp1 = 0
        while t2 % 2 == 0:
            two_val_qp1 += 1
            t2 //= 2

        # 3-part of d
        t = d
        three_part = 0
        while t % 3 == 0:
            three_part += 1
            t //= 3

        # 3-valuation of q+1
        t3 = qp1
        three_val_qp1 = 0
        while t3 % 3 == 0:
            three_val_qp1 += 1
            t3 //= 3

        two_parts.append((q, two_part, two_val_qp1))
        three_parts.append((q, three_part, three_val_qp1))

    print("\n  2-adic valuation: v₂(d) vs v₂(q+1):")
    for q, v2d, v2qp1 in two_parts[:20]:
        print(f"    q={q}: v₂(d) = {v2d}, v₂(q+1) = {v2qp1}, gap = {v2qp1 - v2d}")

    v2_gaps = [v2qp1 - v2d for _, v2d, v2qp1 in two_parts]
    print(f"\n  min gap: {min(v2_gaps)}, max gap: {max(v2_gaps)}")
    print(f"  Gap distribution: {Counter(v2_gaps)}")

    print("\n  3-adic valuation: v₃(d) vs v₃(q+1):")
    for q, v3d, v3qp1 in three_parts[:20]:
        print(f"    q={q}: v₃(d) = {v3d}, v₃(q+1) = {v3qp1}, gap = {v3qp1 - v3d}")

    v3_gaps = [v3qp1 - v3d for _, v3d, v3qp1 in three_parts]
    print(f"\n  min gap: {min(v3_gaps)}, max gap: {max(v3_gaps)}")
    print(f"  Gap distribution: {Counter(v3_gaps)}")

    print("\n" + "=" * 80)
    print("SECTION C: Does q | ord(3) follow from something provable?")
    print("=" * 80)

    print("\n  We know A-1 = q(q+1). By Fermat: 3^{A-1} = 1.")
    print("  3^{(A-1)/q} = 3^{q+1} mod A. If this ≠ 1, then q | ord(3).")
    print("  Testing 3^{q+1} mod A:\n")

    for q, A in primes[:15]:
        val = pow(3, q+1, A)
        print(f"    q={q}: 3^(q+1) mod A = {val} {'= 1' if val == 1 else '≠ 1'}")

    # Universally check
    q_divides_always = all(pow(3, q+1, A) != 1 for q, A in primes)
    print(f"\n  3^(q+1) ≠ 1 for all q? {q_divides_always}")
    if q_divides_always:
        print("  *** q ALWAYS divides ord(3)! Provable if we can show 3^{q+1} ≠ 1. ***")

    # Can we prove 3^{q+1} ≠ 1?
    # 3^{q+1} ≡ 3·3^q. So 3^{q+1} = 1 iff 3^q = 3^{-1} = (A+1)/3 mod A.
    # But we're trying to prove 3^q ≠ 1, so this is circular in a way.
    # However: 3^{q+1} = 1 means ord(3) | (q+1). This is a STRONGER statement.
    # Maybe we can prove ord(3) ∤ (q+1)?

    print("\n  Alternative: Does ord(3) | (q+1)? (i.e., 3^{q+1} = 1?)")
    any_divides = any(pow(3, q+1, A) == 1 for q, A in primes)
    print(f"  3^(q+1) = 1 for any q? {any_divides}")
    print("  (If never, then ord(3) never divides q+1, so ord(3) must involve q factor)")

    print("\n" + "=" * 80)
    print("SECTION D: Key idea — 3^{q+1} mod A has special structure")
    print("=" * 80)

    print("\n  3^{q+1} = 3 · 3^q. We want to show 3^{q+1} ≠ 1, i.e., 3^q ≠ 3^{-1} mod A.")
    print("  In F_A, 3^{-1} = (A+1)/3 = (q²+q+2)/3.")
    print("  q ≡ 2 mod 3 → q² ≡ 1 mod 3, q²+q+2 ≡ 1+2+2 = 5 ≡ 2 mod 3.")
    print("  Hmm, (q²+q+2)/3 is not an integer! Let's compute more carefully.\n")

    for q, A in primes[:5]:
        inv3 = pow(3, A-2, A)  # 3^{-1} mod A
        print(f"  q={q}: A={A}, 3^(-1) mod A = {inv3}")
        # Check: (q²+q+2) mod 3
        val = q*q + q + 2
        print(f"    q²+q+2 = {val}, mod 3 = {val % 3}")
        # Actually 3^{-1} mod A: 3 * inv3 ≡ 1 mod A
        assert (3 * inv3) % A == 1

    print("\n  So 3^q = 1 ↔ ord(3) | q.")
    print("  3^{q+1} = 1 ↔ ord(3) | (q+1).")
    print("  3^{q+1} ≠ 1 means: ord(3) does NOT divide q+1.")
    print("  Since ord(3) | q(q+1), and ord(3) ∤ (q+1), we'd need q | ord(3).\n")

    print("  But wait: proving 3^{q+1} ≠ 1 is EQUIVALENT to proving q | ord(3),")
    print("  which combined with ord(3) | q(q+1) and q prime means ord(3) ∈ {q, 2q, ...}.")
    print("  But we need ord(3) ≠ q specifically, not just q | ord(3).")

    print("\n" + "=" * 80)
    print("SECTION E: The real question — why is ord(3) > q?")
    print("=" * 80)

    print("\n  ord(3) = q means 3^q ≡ 1 (mod A).")
    print("  ord(3) > q with q | ord(3) means ord(3) = q·e for some e > 1, e | (q+1).")
    print("  So 3^q ≠ 1 but 3^{q·e} ≡ 1. Let g = 3^q mod A. Then g^e ≡ 1, g ≠ 1.")
    print("  g = 3^q has order e in (Z/AZ)*, where e | (q+1).\n")

    print("  Computing g = 3^q mod A and its order e:\n")

    e_values = []
    for q, A in primes:
        g = pow(3, q, A)
        # Find order of g, which divides q+1
        qp1 = q + 1
        qp1_f = factorint(qp1)
        e = qp1
        for p in qp1_f:
            while e % p == 0 and pow(g, e // p, A) == 1:
                e //= p
        e_values.append((q, g, e, qp1, factorint(e) if e > 1 else {}))

    for q, g, e, qp1, ef in e_values[:20]:
        print(f"  q={q}: g=3^q mod A = ..., e=ord(g) = {e}, q+1={qp1}, "
              f"e factors={dict(ef)}, (q+1)/e={qp1//e}")

    print(f"\n  Distribution of e values:")
    e_only = [e for _, _, e, _, _ in e_values]
    print(f"    min(e) = {min(e_only)}, max(e) = {max(e_only)}")
    print(f"    e > 1 always? {all(e > 1 for e in e_only)}")
    if all(e > 1 for e in e_only):
        print("    *** YES! g = 3^q is NEVER 1 mod A ***")

    # What's the distribution of e mod small numbers?
    for m in [2, 3, 4, 6, 8, 12, 24]:
        vals = Counter(e % m for e in e_only)
        print(f"    e mod {m}: {dict(vals)}")

    print("\n" + "=" * 80)
    print("SECTION F: What is 3^q mod A in terms of q? Is there a pattern?")
    print("=" * 80)

    print("\n  If we write 3 = (1-q)(q+2), then 3^q = (1-q)^q · (q+2)^q.")
    print("  By Fermat-Euler in ZMod A: q^q ≡ q^{q mod (A-1)} mod A.")
    print("  But q < A-1, so q^q is just computed directly.\n")
    print("  Let's see what (1-q)^q and (q+2)^q are:\n")

    for q, A in primes[:10]:
        one_mq = (1 - q) % A
        qp2 = (q + 2) % A
        val_1mq_q = pow(one_mq, q, A)
        val_qp2_q = pow(qp2, q, A)
        prod = (val_1mq_q * val_qp2_q) % A
        three_q = pow(3, q, A)
        assert prod == three_q, f"Product mismatch for q={q}"

        # Is (1-q)^q related to known values?
        # (1-q)^2 = -3q mod A
        # (1-q)^q = ((1-q)^2)^{(q-1)/2} · (1-q) = (-3q)^{(q-1)/2} · (1-q)
        val2 = pow(-3*q % A, (q-1)//2, A)
        val_check = (val2 * one_mq) % A
        assert val_check == val_1mq_q, f"Identity check failed for q={q}"

        print(f"  q={q}: (1-q)^q = {val_1mq_q}, (q+2)^q = {val_qp2_q}, product = {prod} = 3^q")

    print("\n" + "=" * 80)
    print("SECTION G: Frobenius approach — q acts as Frobenius on F_{A}")
    print("=" * 80)

    print("\n  Since A = q²+q+1 and q³ ≡ 1 mod A, the map x → x^q is like a Frobenius.")
    print("  In F_A, raising to the q-th power is meaningful because |F_A*| = A-1 = q(q+1).")
    print("  For any x: x^{q³} = x^1 = x (since q³ ≡ 1 mod A-1? Let's check...)\n")

    for q, A in primes[:5]:
        am1 = A - 1
        q_cubed_mod = pow(q, 3, am1)  # q³ mod (A-1)
        print(f"  q={q}: A-1={am1}, q³ mod (A-1) = {q_cubed_mod}")
        # q³ = q·q² = q·(A-1-q) = q(A-1) - q² = q(A-1) - (A-1-q)
        # = (q+1)(A-1) - A + 1 + q = ... this is getting complex
        # Actually q³ mod (A-1): q³ - 1 = (q-1)(q²+q+1) = (q-1)A
        # So q³ ≡ 1 mod A. But mod (A-1)?
        # q³ - 1 = (q-1)A. (q-1)A mod (A-1) = (q-1)(A-1) + (q-1) mod (A-1)
        # = (q-1) mod (A-1)
        # So q³ ≡ 1 + (q-1) = q mod (A-1). So x^{q³} = x^q, not x.

    print("\n  So x^{q³} = x^q (not x). The 'Frobenius' has order dividing A-1, not 3.")
    print("  But q as element of (Z/(A-1)Z)* has some order. Let's compute:\n")

    for q, A in primes[:10]:
        am1 = A - 1
        # Order of q in (Z/(A-1)Z)*
        # First check: gcd(q, A-1). A-1 = q(q+1), so gcd(q, A-1) = q.
        # q is not coprime to A-1! So q is not in (Z/(A-1)Z)*.
        g = gcd(q, am1)
        print(f"  q={q}: gcd(q, A-1) = {g} (= q). So q is NOT a unit mod (A-1).")

    print("\n  The Frobenius action x → x^q is not an automorphism of (Z/AZ)*.")
    print("  But it IS a well-defined endomorphism of the multiplicative group.")

    print("\n" + "=" * 80)
    print("SECTION H: The q-th power map on specific elements")
    print("=" * 80)

    print("\n  The map φ: x → x^q on (Z/AZ)*")
    print("  Key: φ(3) = 3^q, and we want φ(3) ≠ 1.")
    print("  Since 3 = (1-q)(1-q²) [the norm], φ(3) = (1-q)^q · (1-q²)^q.\n")

    print("  But q² ≡ -q-1 mod A, so 1-q² ≡ q+2 mod A.")
    print("  And (q+2)^q: let's see what happens with q+2 under q-th power.\n")

    print("  Actually, let's try: (q+2) = (1-q²)/(1) = -(q²-1)/(...).")
    print("  More useful: q+2 ≡ -(q²-1) mod A? q²-1 ≡ (-q-1)-1 = -q-2, so -(q²-1) = q+2. Yes!")
    print("  So q+2 = -(q-1)(q+1) mod A.\n")

    # Let's explore (q+2)^q
    for q, A in primes[:10]:
        qp2 = (q + 2) % A
        val = pow(qp2, q, A)
        # Also: (q+2) = A+2-q² = A - q² + 2 ≡ -q²+2 ≡ q+1+2 = q+3? No.
        # q² ≡ A-(q+1) = q²+q+1-q-1 = q². Tautology.
        # q² ≡ -q-1 mod A. So q+2 = -(q²-1) = -((-q-1)-1) = -(-q-2) = q+2. Circular.
        print(f"  q={q}: (q+2)^q mod A = {val}")

    print("\n" + "=" * 80)
    print("SECTION I: Discrete log analysis — where does 3 sit in (Z/AZ)*?")
    print("=" * 80)

    print("\n  For small A, compute discrete log of 3 and analyze:")

    for q, A in primes[:5]:
        g = primitive_root(A)
        am1 = A - 1
        # Compute discrete log of 3 base g
        # Baby-step giant-step for small A
        from sympy.ntheory.residues import discrete_log
        try:
            dl3 = discrete_log(A, 3, g)
        except:
            dl3 = None

        if dl3 is not None:
            print(f"\n  q={q}, A={A}: log_g(3) = {dl3}")
            print(f"    A-1 = {am1} = q·(q+1) = {q}·{q+1}")
            print(f"    log_g(3) mod q = {dl3 % q}")
            print(f"    log_g(3) mod (q+1) = {dl3 % (q+1)}")
            print(f"    log_g(3) / gcd(log,A-1) = {dl3 // gcd(dl3, am1)}")
            print(f"    gcd(log_g(3), A-1) = {gcd(dl3, am1)}")
            print(f"    ord(3) = {am1 // gcd(dl3, am1)}")

            # 3^q = 1 iff q·dl3 ≡ 0 mod (A-1) iff dl3 ≡ 0 mod (q+1)
            print(f"    3^q = 1 iff log_g(3) ≡ 0 mod (q+1). Actually: {dl3 % (q+1)} ≠ 0 → 3^q ≠ 1 ✓")

    print("\n" + "=" * 80)
    print("SECTION J: Is log_g(3) mod (q+1) ever 0?")
    print("=" * 80)

    print("\n  Key: 3^q = 1 mod A iff (q+1) | log_g(3). Testing:\n")

    from sympy.ntheory.residues import discrete_log

    dl_mod_qp1 = []
    for q, A in primes[:15]:  # Limit for speed
        g = primitive_root(A)
        try:
            dl3 = discrete_log(A, 3, g)
            residue = dl3 % (q + 1)
            dl_mod_qp1.append((q, residue, q+1))
            print(f"  q={q}: log_g(3) mod (q+1) = {residue} (out of {q+1})")
        except Exception as e:
            print(f"  q={q}: discrete log failed: {e}")

    print("\n" + "=" * 80)
    print("SECTION K: Lifting the exponent / Hensel-type analysis")
    print("=" * 80)

    print("\n  3 = (1-q)(1-q²) mod A. Compute 3^q:")
    print("  3^q = [(1-q)(1-q²)]^q = (1-q)^q · (1-q²)^q")
    print("")
    print("  Key identities in ZMod A:")
    print("  (1-q)^2 = 1 - 2q + q² = 1 - 2q + (-q-1) = -3q")
    print("  (1-q)^3 = (1-q)·(-3q) = -3q + 3q² = -3q + 3(-q-1) = -6q - 3")
    print("  Actually let's compute (1-q)^3 = -3q(1-q) = -3q + 3q² = -3q + 3(-q-1) = -6q-3 = -3(2q+1)")
    print("  And (1-q)^4 = (-3q)^2 = 9q² = 9(-q-1) = -9q-9 = -9(q+1)")
    print("  (1-q)^6 = (-3q)^3 = -27q³ = -27·1 = -27 mod A")
    print("")
    print("  ** (1-q)^6 ≡ -27 mod A always! **")
    print("  ** So (1-q)^{6} = -3³ mod A. **\n")

    for q, A in primes[:10]:
        val6 = pow((1-q) % A, 6, A)
        neg27 = (-27) % A
        print(f"  q={q}: (1-q)^6 mod A = {val6}, -27 mod A = {neg27}, match: {val6 == neg27}")

    print("\n  Since (1-q)^6 = -27 = -3³:")
    print("  3^q = [(1-q)(1-q²)]^q = (1-q)^q · (1-q²)^q")
    print("  = (1-q)^q · [(1-q)(1+q)]^q = (1-q)^{2q} · (1+q)^q")
    print("")
    print("  And (1-q)^{2q} = [(1-q)^6]^{q/3} · (1-q)^{2q - 6·⌊q/3⌋}")
    print("  But q ≡ 71 mod 72 → q ≡ 2 mod 3, so q/3 is not integer. Hmm.")
    print("  Let's just compute (1-q)^{2q} directly.\n")

    for q, A in primes[:10]:
        one_mq = (1-q) % A
        val_2q = pow(one_mq, 2*q, A)
        # Check: this should be (q+1) if we had 3^q = 1 and use the identity
        # from the prompt: (1-q)^{2q} = q+1 if 3^q = 1
        qp1 = (q+1) % A
        print(f"  q={q}: (1-q)^{{2q}} = {val_2q}, q+1 = {qp1}, equal? {val_2q == qp1}")

    print("\n  (1-q)^{2q} ≠ q+1 in general (that was only under assumption 3^q=1).")

    print("\n" + "=" * 80)
    print("SECTION L: Binomial expansion of 3^q = [(1-q)(q+2)]^q in ZMod A")
    print("=" * 80)

    print("\n  (1-q)^q = Σ C(q,k)(-q)^k = Σ C(q,k)(-1)^k q^k")
    print("  In ZMod A, q³ = 1, so q^k depends only on k mod 3.")
    print("  q^{3m} = 1, q^{3m+1} = q, q^{3m+2} = q²")
    print("")
    print("  (1-q)^q = S₀ + S₁·q + S₂·q² mod A where")
    print("  S₀ = Σ_{k≡0 mod 3} C(q,k)(-1)^k")
    print("  S₁ = Σ_{k≡1 mod 3} C(q,k)(-1)^k")
    print("  S₂ = Σ_{k≡2 mod 3} C(q,k)(-1)^k")
    print("")
    print("  Using roots of unity filter: S₀ = [(1-1)^q + (1-ω)^q + (1-ω²)^q]/3")
    print("  where ω = e^{2πi/3}")
    print("  S₀ = [0 + (1-ω)^q + (1-ω̄)^q] / 3")
    print("  S₁ = [0 + ω²(1-ω)^q + ω(1-ω̄)^q] / 3")
    print("  S₂ = [0 + ω(1-ω)^q + ω²(1-ω̄)^q] / 3")
    print("")
    print("  Now |1-ω|² = 3, and 1-ω = √3 · e^{iπ/6}.")
    print("  So (1-ω)^q = 3^{q/2} · e^{iqπ/6}.")
    print("  This involves 3^{q/2} which is exactly the quantity related to QR!")

    print("\n" + "=" * 80)
    print("SECTION M: Connection to Jacobi sums")
    print("=" * 80)

    print("\n  In the Eisenstein ring Z[ω], 3 = -ω²(1-ω)² (up to units).")
    print("  The prime A splits as A = π·π̄ where π = q - ω.")
    print("  The key Jacobi sum is J(χ,χ) = -Σ χ(a)χ(1-a) for a ≠ 0,1.")
    print("  For cubic character χ mod A: J(χ,χ) = π (up to units) by Gauss.")
    print("")
    print("  3^q mod A: since 3 = (1-ω)(1-ω̄) = |1-ω|² in Z,")
    print("  and in ZMod A, ω ↦ q (or q²), we get 3 = (1-q)(1-q²).")
    print("  Now (1-q) 'is' 1-ω mod A, and has norm 3.")
    print("")
    print("  Key question: what is (1-q)^q mod A?")
    print("  By analogy with Frobenius: Frob_A(1-ω) should relate to the")
    print("  sextic residue symbol. But A isn't inert in Z[ω], it splits.")
    print("  Frob at π = q-ω would map 1-ω to (1-ω)^{Nπ} = (1-ω)^A mod π.")
    print("  But we need (1-ω)^q, not (1-ω)^A.\n")

    print("  Let's see: (1-ω)^A = (1-ω)^{q²+q+1} = (1-ω)^{q²} · (1-ω)^q · (1-ω)")
    print("  In Z[ω]/π: the Frobenius map sends ω to ω^A = ω^{q²+q+1}.")
    print("  But ω^3 = 1, so ω^A = ω^{A mod 3}.")
    print("  A = q²+q+1. q ≡ 2 mod 3 → q² ≡ 1 → A ≡ 1+2+1 = 4 ≡ 1 mod 3.")
    print("  So ω^A = ω. Thus Frob_π is the identity on the residue field!")
    print("  (This makes sense since A splits completely.)\n")

    print("  So the Frobenius approach gives (1-ω)^A ≡ 1-ω mod π.")
    print("  This means (1-ω)^{A-1} ≡ 1 mod π, which is just Fermat's little thm.")

    print("\n" + "=" * 80)
    print("SECTION N: Arithmetic in Z[ω]/(π) — direct approach")
    print("=" * 80)

    print("\n  Z[ω]/(π) = Z[ω]/(q-ω) ≅ F_A.")
    print("  Under this map: ω → q, so (1-ω) → (1-q).")
    print("  3 = -ω²(1-ω)² → -q²(1-q)² = -(−q−1)(1-q)² mod A")
    print("  = (q+1)(1-q)² = (q+1)(1-2q+q²) = (q+1)(1-2q-q-1) = (q+1)(-3q) = -3q(q+1)")
    print("  = -3q·(-q²) = 3q³ = 3·1 = 3. ✓\n")

    print("  Now: 3^q = [(1-q)(1-q²)]^q = (1-q)^q · (q+2)^q")
    print("  In terms of Eisenstein: this is [(1-ω)(1-ω²)]^q = N(1-ω)^q = 3^q. Circular.\n")

    print("  But let's think about it differently.")
    print("  (1-ω)^q in Z[ω]: write 1-ω = π₃ (prime above 3).")
    print("  π₃^q = ? In Z[ω], π₃ has norm 3, so π₃·π̄₃ = 3.")
    print("  π₃^q in Z[ω]: this is a unit times some power of π₃ and π̄₃.")
    print("  Actually π₃^q is just an element of Z[ω]. Its norm is N(π₃)^q = 3^q.")

    print("\n" + "=" * 80)
    print("SECTION O: NEW APPROACH — congruence conditions on q directly")
    print("=" * 80)

    print("\n  What if we use the fact that q ≡ 71 mod 72 more carefully?")
    print("  71 ≡ -1 mod 8 and 71 ≡ 8 mod 9.")
    print("  So q ≡ -1 mod 8 and q ≡ -1 mod 9. i.e., q ≡ -1 mod 72.")
    print("  Wait: 71 mod 9 = 8 = -1 mod 9. And 71 mod 8 = 7 = -1 mod 8.")
    print("  So q ≡ -1 mod 72! That means q+1 ≡ 0 mod 72.\n")

    for q, A in primes[:5]:
        print(f"  q={q}: q mod 72 = {q % 72}, q+1 mod 72 = {(q+1) % 72}")

    print("\n  So q ≡ -1 mod 72 for all these. The condition is really q ≡ -1 mod lcm(8,9) = 72.")

    print("\n" + "=" * 80)
    print("SECTION P: Testing 3^{2q} and 3^{3q} patterns")
    print("=" * 80)

    for q, A in primes[:10]:
        g3q = pow(3, q, A)      # 3^q
        g32q = pow(3, 2*q, A)   # 3^{2q}
        g33q = pow(3, 3*q, A)   # 3^{3q}

        # 3^{3q} = 3^{3q mod (A-1)}. 3q mod q(q+1) = 3q (if 3 < q+1).
        # For q > 2: 3q < q(q+1), so 3^{3q} = (3^q)^3.
        assert g33q == pow(g3q, 3, A)

        # Is 3^{3q} = 3^3 = 27? (Would be true if q ≡ 0 mod something)
        print(f"  q={q}: 3^q = {g3q}, 3^{{2q}} = {g32q}, 3^{{3q}} = {g33q}, "
              f"3^3 = 27, 3^{{3q}} = 27? {g33q == 27}")

    print("\n" + "=" * 80)
    print("SECTION Q: Power of 3 modular arithmetic — 3^q mod (q+1)")
    print("=" * 80)

    print("\n  Since A ≡ 1 mod (q+1) (because A-1 = q(q+1)), every (q+1)-th root of unity exists in F_A.")
    print("  3 has some position relative to the subgroup of (q+1)-th power residues.")
    print("  3^q mod A lives in the subgroup of order (q+1) (since (3^q)^{q+1} = 3^{q(q+1)} = 3^0 = 1).")
    print("  So g = 3^q has order dividing q+1. We need g ≠ 1.\n")

    print("  Idea: Can we compute 3^q mod A via the Chinese Remainder Theorem on Z[ω]?")
    print("  A = π·π̄ in Z[ω]. So F_A ≅ F_A (it's a field since A is prime).")
    print("  No CRT factorization for F_A itself.\n")

    print("  Let's try: 3 mod (q+1). Since q ≡ -1 mod 72, q+1 ≡ 0 mod 72.")
    print("  3^q mod various small moduli:")
    for q, A in primes[:10]:
        for m in [8, 9, 24, 72]:
            val = pow(3, q, m)
            print(f"  q={q}: 3^q mod {m} = {val}", end="")
        print()

    print("\n" + "=" * 80)
    print("SECTION R: 3^q in (Z/AZ)* — index in the (q+1)-part")
    print("=" * 80)

    print("\n  (Z/AZ)* ≅ Z/q × Z/(q+1) approximately (since q and q+1 are coprime).")
    print("  The projection of 3 onto the Z/q component: 3^{q+1} mod A.")
    print("  The projection of 3 onto the Z/(q+1) component: 3^q mod A.\n")

    for q, A in primes[:10]:
        proj_q = pow(3, q+1, A)  # order divides q
        proj_qp1 = pow(3, q, A)  # order divides q+1

        # proj_q is in the unique subgroup of order q
        # proj_qp1 is in the unique subgroup of order (q+1)
        # 3 = proj_q * proj_qp1 in (Z/AZ)* (approximately)

        # Actually more precisely: using CRT on orders
        # 3 has order d. d | q(q+1). d = lcm(d_1, d_2) where d_1 | q, d_2 | (q+1).
        # d_1 = ord(3^{q+1}) as element of order dividing q
        # d_2 = ord(3^q) as element of order dividing q+1

        # Compute d_1
        d1 = q
        fq = factorint(q)
        for p in fq:
            while d1 % p == 0 and pow(proj_q, d1 // p, A) == 1:
                d1 //= p

        # Compute d_2
        d2_full = q + 1
        fqp1 = factorint(d2_full)
        d2 = d2_full
        for p in fqp1:
            while d2 % p == 0 and pow(proj_qp1, d2 // p, A) == 1:
                d2 //= p

        print(f"  q={q}: d₁=ord(3^(q+1))={d1} (divides q={q}), "
              f"d₂=ord(3^q)={d2} (divides q+1={q+1})")
        print(f"    3^q ≠ 1 iff d₂ > 1: {'YES ✓' if d2 > 1 else 'NO!'}")

    print("\n" + "=" * 80)
    print("SECTION S: What makes d₂ = ord(3^q) > 1? Mod (q+1) analysis")
    print("=" * 80)

    print("\n  d₂ = ord(3^q) in the (q+1)-part of (Z/AZ)*.")
    print("  This is the order of 3^q as element of the cyclic group of order (q+1).")
    print("  3^q ≠ 1 iff d₂ > 1 iff 3 is NOT a q-th power residue mod A.")
    print("")
    print("  Wait — 3^q = 1 iff log_g(3) ≡ 0 mod (q+1), where g is primitive root.")
    print("  Equivalently: 3 ≡ h^{q+1} mod A for some h.")
    print("  i.e., 3 is a (q+1)-th power residue mod A.\n")

    print("  So: 3^q ≡ 1 mod A iff 3 is a (q+1)-th power residue mod A.")
    print("  We want to show: 3 is NEVER a (q+1)-th power residue mod A.\n")

    print("  Since A ≡ 1 mod (q+1), the (q+1)-th power residue symbol is well-defined.")
    print("  (3/A)_{q+1} = 3^{(A-1)/(q+1)} = 3^q mod A.")
    print("  We want this to be ≠ 1.\n")

    print("  THIS IS EXACTLY OUR ORIGINAL PROBLEM RESTATED!")
    print("  The (q+1)-th power residue of 3 is exactly 3^q.")

    print("\n" + "=" * 80)
    print("SECTION T: Factor (q+1) and check sub-characters")
    print("=" * 80)

    print("\n  q+1 = 72·m for some integer m. The prime factors of q+1 vary.")
    print("  If we can show 3 is not a p-th power residue for some prime p | (q+1),")
    print("  then 3 is not a (q+1)-th power residue, hence 3^q ≠ 1.\n")

    print("  The prime factors of q+1 always include 2, 3 (from the 72 factor).")
    print("  We already know: 3 IS a QR mod A (i.e., 2nd power res), and IS a cubic res.")
    print("  What about the HIGHER powers of 2 and 3 in q+1?\n")

    print("  q+1 ≡ 0 mod 8 and q+1 ≡ 0 mod 9. So 72 | (q+1).")
    print("  We need: for some prime p^a || (q+1), 3 is not a p^a-th power residue.")
    print("  i.e., 3^{(A-1)/p^a} ≠ 1.\n")

    print("  Testing p=2: we need 3^{(A-1)/2^v} ≠ 1 where 2^v || (q+1).")
    print("  But 2^v || (q+1) and A-1 = q(q+1), 2-val of A-1 = 2-val of q+1 (since q is odd).")
    print("  So (A-1)/2^v = q · (q+1)/2^v, which is odd.\n")

    for q, A in primes[:15]:
        qp1 = q + 1
        v2 = 0
        t = qp1
        while t % 2 == 0:
            v2 += 1
            t //= 2

        # 3^{(A-1)/2^v2} = 3^{q · (q+1)/2^v2}
        exp_val = (A - 1) // (2**v2)
        val = pow(3, exp_val, A)

        # Also check 3^{(A-1)/2^k} for k = 1, ..., v2
        vals_2k = []
        for k in range(1, v2 + 1):
            exp_k = (A - 1) // (2**k)
            v_k = pow(3, exp_k, A)
            vals_2k.append((k, v_k == 1))

        # Find the largest k such that 3^{(A-1)/2^k} = 1
        max_k = 0
        for k, is_one in vals_2k:
            if is_one:
                max_k = k

        print(f"  q={q}: v₂(q+1) = {v2}, "
              f"2-adic val of ord(3) in 2-part: max k with 3^((A-1)/2^k)=1 is {max_k}")

    print("\n  Similarly for p=3:")
    for q, A in primes[:15]:
        qp1 = q + 1
        v3 = 0
        t = qp1
        while t % 3 == 0:
            v3 += 1
            t //= 3

        vals_3k = []
        for k in range(1, v3 + 1):
            exp_k = (A - 1) // (3**k)
            v_k = pow(3, exp_k, A)
            vals_3k.append((k, v_k == 1))

        max_k = 0
        for k, is_one in vals_3k:
            if is_one:
                max_k = k

        print(f"  q={q}: v₃(q+1) = {v3}, "
              f"3-adic val of ord(3) in 3-part: max k with 3^((A-1)/3^k)=1 is {max_k}")

    print("\n" + "=" * 80)
    print("SECTION U: CRITICAL — check if 3 is an 8th power residue")
    print("=" * 80)

    print("\n  Since 8 | (q+1), 8 | (A-1). If 3 is not an 8th power residue,")
    print("  then 3^{(A-1)/8} ≠ 1. Since (A-1)/8 = q(q+1)/8 and 8|(q+1),")
    print("  this means (3^q)^{(q+1)/8} ≠ 1, so 3^q ≠ 1. Done!\n")

    print("  Testing 3^{(A-1)/8} for all eligible primes:\n")

    eighth_power_residue = []
    for q, A in primes:
        val = pow(3, (A-1)//8, A)
        is_8th = (val == 1)
        eighth_power_residue.append((q, is_8th, val))
        print(f"  q={q}: 3^((A-1)/8) = {val}, 8th power residue? {is_8th}")

    never_8th = all(not is_8th for _, is_8th, _ in eighth_power_residue)
    sometimes_8th = any(is_8th for _, is_8th, _ in eighth_power_residue)
    print(f"\n  3 is 8th power residue sometimes? {sometimes_8th}")
    if not never_8th:
        print("  :-( 3 IS an 8th power residue for some q. Can't use this universally.")

    print("\n  Same for 9th power residue:")
    ninth_power_residue = []
    for q, A in primes:
        if (A-1) % 9 != 0:
            continue
        val = pow(3, (A-1)//9, A)
        is_9th = (val == 1)
        ninth_power_residue.append((q, is_9th, val))

    never_9th = all(not is_9th for _, is_9th, _ in ninth_power_residue)
    sometimes_9th = any(is_9th for _, is_9th, _ in ninth_power_residue)
    print(f"  3 is 9th power residue sometimes? {sometimes_9th}")

    print("\n" + "=" * 80)
    print("SECTION V: FINAL — which prime factor of (q+1) provides the obstruction?")
    print("=" * 80)

    print("\n  For each q, find a prime p | (q+1) such that 3 is NOT a p-th power res:\n")

    for q, A in primes:
        qp1 = q + 1
        qp1_f = factorint(qp1)
        obstructions = []
        for p in sorted(qp1_f.keys()):
            exp_val = (A - 1) // p
            val = pow(3, exp_val, A)
            if val != 1:
                obstructions.append(p)

        print(f"  q={q}: q+1={qp1}, primes of q+1: {sorted(qp1_f.keys())}, "
              f"obstructions (3 not p-res): {obstructions}")

    # Extended
    print("\n  Extended to all 28 primes q < 50000:")
    extended_primes = find_eligible_primes(50000)
    all_obstructions = defaultdict(int)
    unique_obstruction_primes = set()
    for q, A in extended_primes:
        qp1 = q + 1
        qp1_f = factorint(qp1)
        for p in sorted(qp1_f.keys()):
            exp_val = (A - 1) // p
            val = pow(3, exp_val, A)
            if val != 1:
                all_obstructions[p] += 1
                unique_obstruction_primes.add(p)
                break  # just record the smallest obstruction

    print(f"  Smallest obstruction prime distribution: {dict(sorted(all_obstructions.items()))}")

    print("\n  For each prime factor p of any q+1, how often is it an obstruction?")
    prime_obstruction_rate = defaultdict(lambda: [0, 0])  # [obstruction_count, total_count]
    for q, A in extended_primes:
        qp1 = q + 1
        qp1_f = factorint(qp1)
        for p in qp1_f:
            exp_val = (A - 1) // p
            val = pow(3, exp_val, A)
            prime_obstruction_rate[p][1] += 1
            if val != 1:
                prime_obstruction_rate[p][0] += 1

    for p in sorted(prime_obstruction_rate.keys()):
        obs, total = prime_obstruction_rate[p]
        pct = 100 * obs / total if total > 0 else 0
        marker = " *** UNIVERSAL ***" if obs == total and total >= 3 else ""
        print(f"  p={p}: obstruction {obs}/{total} = {pct:.0f}%{marker}")

if __name__ == '__main__':
    main()
