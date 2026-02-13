#!/usr/bin/env python3
"""
Explore polynomial relations between q and 3 in F_A where A = q^2 + q + 1.

For primes q ≡ 8 (mod 9) with q < 1000:
1. Check if A is prime and whether 3^q ≡ 1 (mod A)
2. Compute discrete logs of q and 3 in (Z/AZ)*
3. Search for low-degree polynomial relations f(q) ≡ g(3) (mod A)
4. Report patterns
"""

import sympy
from sympy import isprime, primitive_root, mod_inverse, factorint
from itertools import product
import time

def discrete_log_brute(g, x, p, max_steps=None):
    """Compute discrete log of x base g mod p by baby-step giant-step."""
    if max_steps is None:
        max_steps = p - 1
    n = int(max_steps**0.5) + 1
    table = {}
    power = 1
    for j in range(n):
        table[power] = j
        power = (power * g) % p
    factor = pow(g, (p - 1 - n) % (p - 1), p)
    gamma = x
    for i in range(n):
        if gamma in table:
            log_val = (i * n + table[gamma]) % (p - 1)
            if pow(g, log_val, p) == x % p:
                return log_val
        gamma = (gamma * factor) % p
    return None

def find_generator(p):
    """Find a primitive root mod p."""
    return primitive_root(p)

def main():
    print("=" * 80)
    print("POLYNOMIAL RELATIONS BETWEEN q AND 3 IN Z/AZ, A = q^2 + q + 1")
    print("For primes q = 8 (mod 9), q < 1000")
    print("=" * 80)

    candidates = []
    for q in range(8, 1000, 9):
        if isprime(q):
            candidates.append(q)

    print(f"\nFound {len(candidates)} primes q = 8 (mod 9) with q < 1000:")
    print(candidates)

    # =========================================================================
    # PART 1: Basic verification
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 1: BASIC PROPERTIES")
    print("=" * 80)
    print(f"{'q':>6} {'A=q^2+q+1':>12} {'A prime?':>10} {'3^q mod A':>12} {'3^q=1?':>8} {'ord_A(3)':>10}")
    print("-" * 70)

    valid_qs = []
    for q in candidates:
        A = q * q + q + 1
        A_prime = isprime(A)
        three_pow_q = pow(3, q, A)
        is_one = (three_pow_q == 1)

        ord_3 = None
        if A_prime:
            valid_qs.append(q)
            order = A - 1
            for p_factor in sorted(factorint(order).keys()):
                while order % p_factor == 0 and pow(3, order // p_factor, A) == 1:
                    order //= p_factor
            ord_3 = order

        print(f"{q:>6} {A:>12} {'YES' if A_prime else 'no':>10} {three_pow_q:>12} {'YES' if is_one else 'no':>8} {str(ord_3) if ord_3 else 'N/A':>10}")

    # =========================================================================
    # PART 2: Discrete logs and group structure
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 2: DISCRETE LOGS AND GROUP STRUCTURE")
    print("=" * 80)
    print(f"\n{'q':>6} {'A':>10} {'g':>4} {'log_g(3)':>10} {'log_g(q)':>10} {'ord(3)':>10} {'A-1':>12} {'log3 mod(q+1)':>14}")
    print("-" * 82)

    dlog_data = []
    for q in valid_qs:
        A = q * q + q + 1
        g = find_generator(A)
        log3 = discrete_log_brute(g, 3, A)
        logq = discrete_log_brute(g, q % A, A)

        order_3 = (A - 1) // sympy.gcd(log3, A - 1) if log3 else None

        dlog_data.append((q, A, g, log3, logq, order_3))

        log3_mod_qp1 = log3 % (q + 1) if log3 is not None else "N/A"
        print(f"{q:>6} {A:>10} {g:>4} {str(log3):>10} {str(logq):>10} {str(order_3):>10} {A-1:>12} {str(log3_mod_qp1):>14}")

    # =========================================================================
    # PART 2b: Relationship between log_g(3) and q
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 2b: PATTERNS IN DISCRETE LOGS")
    print("=" * 80)
    for q, A, g, log3, logq, ord3 in dlog_data[:10]:
        if log3 is None or logq is None:
            continue
        print(f"\nq={q}, A={A}, g={g}")
        print(f"  log_g(3) = {log3}, log_g(q) = {logq}")
        print(f"  log_g(3) mod q = {log3 % q}, log_g(3) mod (q+1) = {log3 % (q+1)}")
        print(f"  log_g(q) mod q = {logq % q}, log_g(q) mod (q+1) = {logq % (q+1)}")
        print(f"  q^3 mod A = {pow(q, 3, A)}  (should be 1 since q^2+q+1=0)")
        third = (A - 1) // 3
        print(f"  (A-1)/3 = {third}, log_g(q) / ((A-1)/3) = {logq / third:.4f}")
        print(f"  log_g(q) mod ((A-1)/3) = {logq % third}")

    # =========================================================================
    # PART 3: Low-degree polynomial relations
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 3: POLYNOMIAL RELATION SEARCH")
    print("=" * 80)
    print("Searching for relations: sum of a_i * q^i = sum of b_j * 3^j (mod A)")

    for q, A, g, log3, logq, ord3 in dlog_data[:8]:
        print(f"\n{'~' * 60}")
        print(f"q = {q}, A = {A}")
        print(f"{'~' * 60}")

        q_pows = [pow(q, i, A) for i in range(6)]
        three_pows = [pow(3, i, A) for i in range(6)]

        print(f"  q^0=1, q^1={q}, q^2={q_pows[2]} (= A-q-1 = {A-q-1})")
        print(f"  3^0=1, 3^1=3, 3^2=9, 3^3=27, 3^4=81, 3^5=243")

        # Search: a*q + b*3 + c = 0 (mod A) for small a, b, c
        found_linear = []
        for a in range(-50, 51):
            for b in range(-50, 51):
                val = (a * q + b * 3) % A
                c = (-val) % A
                if c <= 50 or c >= A - 50:
                    c_small = c if c <= 50 else c - A
                    if not (a == 0 and b == 0 and c_small == 0):
                        found_linear.append((a, b, c_small))

        if found_linear:
            found_linear.sort(key=lambda x: abs(x[0]) + abs(x[1]) + abs(x[2]))
            print(f"  Linear relations a*q + b*3 + c = 0 (mod A), |a|,|b|<=50, |c|<=50:")
            for a, b, c in found_linear[:10]:
                print(f"    {a}*q + {b}*3 + {c} = 0 (mod {A})")
        else:
            print(f"  No linear relations with small coefficients found.")

        # Key products
        print(f"\n  Key products mod A:")
        print(f"    q*3 mod A = {(q*3) % A}")
        print(f"    q^2*3 mod A = {(q_pows[2]*3) % A}")
        print(f"    q*9 mod A = {(q*9) % A}")
        print(f"    (q+1)*3 mod A = {((q+1)*3) % A}")
        print(f"    q*(q+1) mod A = {(q*(q+1)) % A} (= A-1 = {A-1})")

        # Search: a*q*3 + b*q + c*3 + d = 0 (mod A), small coeffs
        found_bilinear = []
        for a in range(-20, 21):
            for b in range(-20, 21):
                for c in range(-20, 21):
                    val = (a * q * 3 + b * q + c * 3) % A
                    d = (-val) % A
                    if d <= 20 or d >= A - 20:
                        d_small = d if d <= 20 else d - A
                        total = abs(a) + abs(b) + abs(c) + abs(d_small)
                        if total > 0 and total <= 15:
                            found_bilinear.append((a, b, c, d_small, total))

        if found_bilinear:
            found_bilinear.sort(key=lambda x: x[4])
            print(f"\n  Bilinear relations a*(q*3) + b*q + c*3 + d = 0 (mod A):")
            seen = set()
            for a, b, c, d, tot in found_bilinear[:15]:
                key = (a, b, c, d)
                if key not in seen:
                    seen.add(key)
                    print(f"    {a}*(q*3) + {b}*q + {c}*3 + {d} = 0  [complexity={tot}]")

    # =========================================================================
    # PART 4: What would 3^q = 1 (mod A) imply?
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 4: IMPLICATIONS OF 3^q = 1 (mod A)")
    print("=" * 80)
    print("If 3^q = 1 (mod A), then ord_A(3) | q.")
    print("Since q is prime, ord_A(3) = 1 or q.")
    print("ord = 1 means 3 = 1 (mod A), impossible for A > 2.")
    print("So ord(3) = q, and 3 lies in the unique order-q subgroup of (Z/AZ)*.")
    print("Equivalently: (q+1) | log_g(3).")
    print()

    for q, A, g, log3, logq, ord3 in dlog_data:
        if log3 is None:
            continue
        print(f"q={q}: log_g(3)={log3}, q+1={q+1}, log_g(3) mod (q+1) = {log3 % (q+1)}, "
              f"actual 3^q mod A = {pow(3, q, A)}")

    # =========================================================================
    # PART 5: Frobenius / Norm analysis
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 5: FROBENIUS AND NORM STRUCTURE")
    print("=" * 80)

    for q, A, g, log3, logq, ord3 in dlog_data[:8]:
        if log3 is None:
            continue
        norm = pow(3, 1 + q + q*q, A)
        three_q = pow(3, q, A)
        three_q2 = pow(3, q * q, A)
        trace = (3 + three_q + three_q2) % A
        print(f"q={q}: 3^(1+q+q^2) = {norm} (=3 by Fermat)")
        print(f"  conjugates: 3, {three_q}, {three_q2}")
        print(f"  product = {(3 * three_q * three_q2) % A} (should be 3)")
        print(f"  trace = {trace}")
        # The minimal polynomial of 3 over the "fixed field" is
        # X^3 - trace*X^2 + ... - norm = X^3 - (trace)X^2 + ... - 3
        # Actually the characteristic polynomial is (X-3)(X-3^q)(X-3^{q^2})
        # = X^3 - (3+3^q+3^{q^2})X^2 + (3*3^q + 3*3^{q^2} + 3^q*3^{q^2})X - 3*3^q*3^{q^2}
        s1 = trace
        s2 = (3*three_q + 3*three_q2 + three_q*three_q2) % A
        s3 = (3 * three_q * three_q2) % A
        print(f"  char poly: X^3 - {s1}*X^2 + {s2}*X - {s3}")
        print()

    # =========================================================================
    # PART 6: Check 3^q vs q patterns
    # =========================================================================
    print("=" * 80)
    print("PART 6: PATTERNS IN 3^q mod A")
    print("=" * 80)
    print(f"{'q':>6} {'A':>10} {'3^q mod A':>12} {'3^q mod q':>10} {'3^q mod(q+1)':>12} {'3^(q+1) mod A':>14}")
    print("-" * 70)

    for q in valid_qs:
        A = q * q + q + 1
        tq = pow(3, q, A)
        tqp1 = pow(3, q + 1, A)
        print(f"{q:>6} {A:>10} {tq:>12} {tq % q:>10} {tq % (q+1):>12} {tqp1:>14}")

    # =========================================================================
    # PART 7: Universal polynomial search
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 7: UNIVERSAL POLYNOMIAL RELATIONS")
    print("=" * 80)
    print("Search for P(q, 3) = 0 (mod A) for ALL valid q simultaneously.")
    print("Monomials: q^a * 3^b, a in {0,1}, b in {0,...,5}")

    print("\nMonomial values mod A:")
    mono_labels = []
    for a in range(2):
        for b in range(6):
            mono_labels.append(f"q^{a}*3^{b}")

    header = f"{'q':>6}"
    for label in mono_labels:
        header += f" {label:>10}"
    print(header)

    mono_values = []
    for q in valid_qs[:10]:
        A = q * q + q + 1
        vals = []
        row = f"{q:>6}"
        for a in range(2):
            for b in range(6):
                v = (pow(q, a, A) * pow(3, b, A)) % A
                vals.append(v)
                row += f" {v:>10}"
        mono_values.append((q, A, vals))
        print(row)

    # Check pairs: c1*m_i + c2*m_j = 0 (mod A) for all q
    print("\nSearching for universal pair relations...")
    n_monos = len(mono_labels)

    for i in range(n_monos):
        for j in range(i + 1, n_monos):
            ratios = []
            valid = True
            for q_val, A_val, vals in mono_values:
                vi = vals[i]
                vj = vals[j]
                if vi == 0 and vj == 0:
                    ratios.append("both_zero")
                elif vi == 0:
                    valid = False
                    break
                else:
                    r = (-vj * pow(vi, -1, A_val)) % A_val
                    ratios.append(r)
            if not valid:
                continue
            numeric_ratios = [r for r in ratios if isinstance(r, int)]
            if len(numeric_ratios) < 2:
                continue
            if len(set(numeric_ratios)) == 1 and numeric_ratios[0] <= 20:
                c = numeric_ratios[0]
                print(f"  FOUND: {c}*{mono_labels[i]} + 1*{mono_labels[j]} = 0 (mod A)")

    # =========================================================================
    # PART 8: Quadratic residue analysis
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 8: QUADRATIC/CUBIC RESIDUE ANALYSIS")
    print("=" * 80)

    for q in valid_qs[:15]:
        A = q * q + q + 1
        leg = pow(3, (A - 1) // 2, A)
        leg_val = 1 if leg == 1 else -1
        cub = pow(3, (A - 1) // 3, A)
        is_cubic_res = (cub == 1)
        frob_q = pow(3, (A - 1) // q, A)  # = 3^(q+1) mod A

        print(f"q={q}: (3/A)={leg_val:+d}, 3^((A-1)/3)={cub} ({'cubic res' if is_cubic_res else 'NOT cubic res'}), "
              f"3^(q+1)={frob_q} ({'ord|q' if frob_q==1 else 'ord DOES NOT divide q'})")

    # =========================================================================
    # PART 9: Structural summary
    # =========================================================================
    print("\n" + "=" * 80)
    print("PART 9: STRUCTURAL ANALYSIS SUMMARY")
    print("=" * 80)
    print("""
For A = q^2+q+1 with q prime and q = 8 (mod 9):

GROUP STRUCTURE of (Z/AZ)*:
  - Order = A-1 = q(q+1) = q^2+q
  - Since gcd(q, q+1) = 1: (Z/AZ)* ~ C_q x C_{q+1}
  - q is a primitive cube root of unity mod A (since q^3 = 1, q != 1)
  - So log_g(q) = (A-1)/3 or 2(A-1)/3

KEY EQUIVALENCE:
  3^q = 1 (mod A)  <=>  ord_A(3) | q  <=>  3 in C_q subgroup
                    <=>  (q+1) | log_g(3)  <=>  3^(q+1) = 1 (mod A)

For Feit-Thompson (p=3 case): need to show 3 NEVER lies in C_q.
""")

    # Final: compute 3^(q+1) mod A for all and verify none equal 1
    print("VERIFICATION: 3^(q+1) mod A for all valid q:")
    all_nonone = True
    for q in valid_qs:
        A = q * q + q + 1
        val = pow(3, q + 1, A)
        if val == 1:
            print(f"  *** q={q}: 3^(q+1) = 1 (mod A) -- COUNTEREXAMPLE! ***")
            all_nonone = False
        # else: silent

    if all_nonone:
        print(f"  All {len(valid_qs)} values: 3^(q+1) != 1 (mod A). FT confirmed for all q < 1000.")

    # Bonus: show what 3^(q+1) actually is
    print(f"\n{'q':>6} {'A':>10} {'3^(q+1) mod A':>14} {'as fraction of A':>18}")
    print("-" * 52)
    for q in valid_qs[:15]:
        A = q * q + q + 1
        val = pow(3, q + 1, A)
        print(f"{q:>6} {A:>10} {val:>14} {val/A:>18.6f}")

if __name__ == "__main__":
    t0 = time.time()
    main()
    print(f"\nTotal runtime: {time.time() - t0:.1f}s")
