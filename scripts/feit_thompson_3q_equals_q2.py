#!/usr/bin/env python3
"""
REMARKABLE OBSERVATION: For q=71, 3^q mod A = 5041 = 71² = q².

Is 3^q ≡ q² mod A always? Or only sometimes?
If 3^q ≡ q² always, then since q² ≠ 1 (q > 1), the conjecture follows!

Let's check.
"""

from sympy import isprime, nextprime, factorint

def check_3q_vs_q2(limit=200000):
    print("CHECK: Is 3^q ≡ q² mod A?")
    print("=" * 70)

    q = 5
    match_count = 0
    total_count = 0

    print(f"{'q':>8} {'q%72':>5} {'3^q mod A':>15} {'q² mod A':>15} {'match':>6} {'ratio':>15}")

    while q < limit:
        if isprime(q) and q % 3 == 2:
            A = q*q + q + 1
            if isprime(A):
                total_count += 1
                tq = pow(3, q, A)
                q2 = pow(q, 2, A)
                match = (tq == q2)
                if match:
                    match_count += 1

                # Also compute the ratio 3^q / q² mod A
                ratio = (tq * pow(q2, -1, A)) % A

                if total_count <= 50 or match:
                    print(f"{q:>8} {q%72:>5} {tq:>15} {q2:>15} {'YES' if match else 'no':>6} {ratio:>15}")

        q = int(nextprime(q))

    print(f"\nMatches: {match_count} / {total_count}")
    if match_count == total_count:
        print("3^q ≡ q² mod A ALWAYS! This would prove the FT conjecture!")
    else:
        print(f"NOT always. But pattern is interesting.")

    # Check other patterns: is 3^q ≡ q mod A? Or 3^q ≡ -1 mod A? etc.
    print(f"\n{'='*70}")
    print("WHAT IS 3^q / q² mod A? (Looking for patterns)")
    print(f"{'='*70}")

    q = 5
    count = 0
    ratio_to_q_count = {}

    while q < limit and count < 100:
        if isprime(q) and q % 3 == 2:
            A = q*q + q + 1
            if isprime(A):
                count += 1
                tq = pow(3, q, A)
                q2 = pow(q, 2, A)
                ratio = (tq * pow(q2, -1, A)) % A

                # Is ratio related to q?
                # Check: ratio ≡ q^k mod A for k = 0, 1, 2
                q_mod = q % A
                q2_mod = q2
                q3_mod = 1  # q³ ≡ 1 mod A

                if ratio == 1:
                    kind = "1 (=q^0)"
                elif ratio == q_mod:
                    kind = "q (=q^1)"
                elif ratio == q2_mod:
                    kind = "q² (=q^2)"
                else:
                    # Is it a power of 3?
                    found = False
                    for k in range(1, 20):
                        if pow(3, k, A) == ratio:
                            kind = f"3^{k}"
                            found = True
                            break
                    if not found:
                        kind = f"{ratio}"

                if count <= 60:
                    print(f"q={q:>8}, 3^q/q² = {ratio:>12} = {kind}")

        q = int(nextprime(q))

    # NEW: check if 3^q ≡ q² * (something involving q mod 72)
    print(f"\n{'='*70}")
    print("3^q mod A expressed as power of q times power of 3")
    print(f"{'='*70}")

    q_val = 5
    count = 0
    while q_val < 50000 and count < 40:
        if isprime(q_val) and q_val % 3 == 2:
            A = q_val*q_val + q_val + 1
            if isprime(A):
                count += 1
                tq = pow(3, q_val, A)

                # Express 3^q in terms of order structure
                # 3^q ∈ H_{q+1} (order divides q+1)
                # What is the order of 3^q?
                ord_3q = None
                for d in range(1, q_val + 2):
                    if (q_val + 1) % d == 0:
                        if pow(tq, d, A) == 1:
                            ord_3q = d
                            break

                # Also: what is 3^q as a power of a generator of H_{q+1}?
                # H_{q+1} = {x : x^{q+1} = 1}. Generator: q^q is in H_{q+1}.
                # Actually q^q: (q^q)^{q+1} = q^{q(q+1)} = q^{A-1} = 1. ✓
                # Order of q^q: q^q has order (q+1)/gcd(q, ???).
                # q has order 3 in (Z/AZ)*. q^q = q^{q mod 3} = q^2.
                # q^2 has order 3. 3 | (q+1)? Yes (q ≡ 2 mod 3).
                # So q^2 has order 3 in H_{q+1}. Not a generator of H_{q+1}.

                # Let's find a generator of H_{q+1}
                # A primitive root g mod A generates (Z/AZ)*.
                # g^q generates H_{q+1} (which has order q+1).
                # But finding a primitive root is expensive.

                # Instead: what power of q is 3^q?
                # 3^q ∈ H_{q+1}. q² ∈ H_{q+1} with order 3.
                # 3^q / q² = some element of H_{q+1}.

                ratio = (tq * pow(q_val*q_val % A, -1, A)) % A
                # Order of ratio in H_{q+1}
                ord_ratio = None
                for d in range(1, q_val + 2):
                    if (q_val + 1) % d == 0:
                        if pow(ratio, d, A) == 1:
                            ord_ratio = d
                            break

                print(f"q={q_val:>8}: ord(3^q)={ord_3q:>8}, 3^q/q²={ratio:>12}, ord(3^q/q²)={ord_ratio}")

        q_val = int(nextprime(q_val))


def check_71_special():
    """The case q=71 gave 3^q = q². Understand why."""
    q = 71
    A = q*q + q + 1
    print(f"\n{'='*70}")
    print(f"SPECIAL CASE: q = {q}, A = {A}")
    print(f"{'='*70}")

    print(f"3^q mod A = {pow(3, q, A)}")
    print(f"q² mod A = {q*q % A}")
    print(f"q² = {q*q}, A = {A}, q² = A - q - 1 = A - 72")
    print(f"So q² ≡ -(q+1) ≡ -72 mod A")
    print()

    # 3^71 mod 5113 = 5041 = 71²
    # Why? ord(3) mod 5113:
    # A-1 = 5112 = 71 · 72 = 71 · 8 · 9
    # ord(3) = 213 = 3 · 71
    # 3^71 has order 213/gcd(213, 71) = 213/71 = 3.
    # So 3^71 is a primitive cube root of unity mod 5113.
    # The primitive cube roots of unity mod A are q and q².
    # 3^71 = q² = 71² = 5041. ✓

    print(f"ord_A(3) = 213 = 3 × 71")
    print(f"3^71 has order 213/71 = 3 in (Z/AZ)*")
    print(f"The cube roots of unity mod A = {A} are: 1, q={q}, q²={q*q}")
    print(f"3^71 = {pow(3, 71, A)} = q². ✓")
    print()
    print(f"This is because ord(3) = 3·q, so 3^q is a primitive 3rd root of unity.")
    print(f"There are two: q and q². 3^q happened to be q².")
    print()
    print(f"For other q: ord(3)/q varies, so 3^q is not generally a cube root of unity.")

    # Verify for q=71: which cube root is 3^q?
    # 3 is a generator (sort of) → 3 = g^k for some k.
    # 3^q = g^{kq}. This is a cube root iff q | ord and 3 | (ord/q).
    # For q=71: ord = 3·71. ord/q = 3. So 3^q has order 3. ✓
    # 3^q = q or q²? Since q² ≡ -q-1 ≡ -(q+1) mod A:
    # 3^q = q² iff 3^q ≡ -(q+1) mod A.


if __name__ == '__main__':
    check_71_special()
    check_3q_vs_q2(100000)
