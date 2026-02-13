#!/usr/bin/env python3
"""
Analyze CM elliptic curve E: y^2 = x^3 - 1 over F_A where A = q^2 + q + 1
for primes q = 8 (mod 9), extending to find more cases where A is prime.
"""

from math import isqrt

def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

def count_points_brute(a_coeff, b_coeff, p):
    """Count points on y^2 = x^3 + a*x + b over F_p, including point at infinity."""
    count = 1
    for x in range(p):
        rhs = (pow(x, 3, p) + a_coeff * x + b_coeff) % p
        if rhs == 0:
            count += 1
        else:
            if pow(rhs, (p - 1) // 2, p) == 1:
                count += 2
    return count

def factorize(n):
    if n == 0:
        return {}
    factors = {}
    d = 2
    temp = abs(n)
    while d * d <= temp:
        while temp % d == 0:
            factors[d] = factors.get(d, 0) + 1
            temp //= d
        d += 1
    if temp > 1:
        factors[temp] = factors.get(temp, 0) + 1
    return factors

def factor_str(n):
    if n == 0:
        return "0"
    sign = "-" if n < 0 else ""
    n = abs(n)
    if n == 1:
        return sign + "1"
    f = factorize(n)
    parts = []
    for p in sorted(f.keys()):
        if f[p] == 1:
            parts.append(str(p))
        else:
            parts.append(f"{p}^{f[p]}")
    return sign + " * ".join(parts)

def find_cm_decomposition(A):
    """Find a, b with A = a^2 + 3*b^2, normalized so a = 1 (mod 3)."""
    for b in range(1, isqrt(A) + 1):
        rem = A - 3 * b * b
        if rem > 0:
            a = isqrt(rem)
            if a * a == rem:
                # Normalize
                if a % 3 == 2:
                    a = -a
                return a, b
    return None, None

def main():
    # Find all primes q = 8 (mod 9) up to 1000 where A = q^2+q+1 is also prime
    print("=" * 95)
    print("FINDING ALL q = 8 (mod 9) prime, q < 1000, with A = q^2+q+1 prime")
    print("=" * 95)
    
    # Original candidates
    original = {71, 107, 179, 251, 359, 431, 467, 503, 539}
    
    good_pairs = []
    composite_pairs = []
    
    for q in range(8, 1000, 9):
        if not is_prime(q):
            if q in original:
                print(f"  q = {q}: NOT PRIME (was in original list)")
            continue
        A = q * q + q + 1
        if is_prime(A):
            good_pairs.append((q, A))
            marker = " <-- ORIGINAL" if q in original else ""
            print(f"  q = {q}, A = {A} -- BOTH PRIME{marker}")
        else:
            if q in original:
                f = factorize(A)
                fstr = " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(f.items()))
                print(f"  q = {q}, A = {A} = {fstr} -- A composite (was in original list)")
            composite_pairs.append((q, A))
    
    print(f"\nTotal: {len(good_pairs)} pairs with both q and A prime (out of {len(good_pairs) + len(composite_pairs)} primes q = 8 mod 9 below 1000)")
    
    # Now analyze each good pair
    print("\n" + "=" * 95)
    print("ELLIPTIC CURVE POINT COUNTS")
    print("=" * 95)
    print(f"\n{'q':>6} | {'A':>10} | {'#E(x3-1)':>10} | {'#E(x3+1)':>10} | {'trace':>7} | {'q|#E-1':>6} | {'q|#E+1':>6} | {'ord_A(3)':>10} | {'3^q=1':>6}")
    print("-" * 95)
    
    for q, A in good_pairs:
        # Point counts
        E_minus = count_points_brute(0, -1, A)  # y^2 = x^3 - 1
        E_plus = count_points_brute(0, 1, A)    # y^2 = x^3 + 1
        
        t_minus = A + 1 - E_minus
        t_plus = A + 1 - E_plus
        
        q_div_Em = (E_minus % q == 0)
        q_div_Ep = (E_plus % q == 0)
        
        # Order of 3 mod A
        order3 = 1
        val = 3 % A
        while val != 1 and order3 <= A:
            val = (val * 3) % A
            order3 += 1
        
        three_q = pow(3, q, A)
        three_test = (three_q == 1)
        
        print(f"{q:>6} | {A:>10} | {E_minus:>10} | {E_plus:>10} | {t_minus:>7} | {'YES' if q_div_Em else 'no':>6} | {'YES' if q_div_Ep else 'no':>6} | {order3:>10} | {'YES!' if three_test else 'no':>6}")
    
    # Detailed analysis
    print("\n" + "=" * 95)
    print("DETAILED ANALYSIS FOR EACH PAIR")
    print("=" * 95)
    
    for q, A in good_pairs:
        E_minus = count_points_brute(0, -1, A)
        E_plus = count_points_brute(0, 1, A)
        t_minus = A + 1 - E_minus
        t_plus = A + 1 - E_plus
        
        # Order of 3
        order3 = 1
        val = 3 % A
        while val != 1 and order3 <= A:
            val = (val * 3) % A
            order3 += 1
        
        # CM decomposition
        a_cm, b_cm = find_cm_decomposition(A)
        
        # Is -1 a cube mod A?
        minus1_cube = (pow(A - 1, (A - 1) // 3, A) == 1) if (A - 1) % 3 == 0 else None
        
        print(f"\n  q = {q}, A = {A}")
        print(f"    A - 1 = {A-1} = {factor_str(A-1)}")
        print(f"    q*(q+1) = {q*(q+1)} = {factor_str(q*(q+1))}")
        print(f"    A - 1 = q*(q+1)? {A - 1 == q*(q+1)}")
        print(f"    CM: A = {a_cm}^2 + 3*{b_cm}^2" if a_cm is not None else "    CM: no decomposition")
        print(f"    -1 is cube mod A: {minus1_cube}")
        if minus1_cube:
            print(f"    => y^2=x^3-1 and y^2=x^3+1 are ISOMORPHIC over F_A")
            print(f"    Verify: #E(x^3-1) = {E_minus}, #E(x^3+1) = {E_plus}, equal? {E_minus == E_plus}")
        print(f"    trace(x^3-1) = {t_minus} = {factor_str(t_minus)}")
        print(f"    trace(x^3+1) = {t_plus} = {factor_str(t_plus)}")
        print(f"    #E(x^3-1) = {E_minus} = {factor_str(E_minus)}")
        print(f"    #E(x^3+1) = {E_plus} = {factor_str(E_plus)}")
        print(f"    ord_A(3) = {order3} = {factor_str(order3)}")
        print(f"    3^q mod A = {pow(3, q, A)}")
        
        # Divisibility analysis
        print(f"    q | #E(x^3-1)? {E_minus % q == 0}  (remainder {E_minus % q})")
        print(f"    q | #E(x^3+1)? {E_plus % q == 0}  (remainder {E_plus % q})")
        
        # Since t = -2a where A = a^2 + 3b^2:
        if a_cm is not None:
            print(f"    Expected trace = -2*{a_cm} = {-2*a_cm}")
            # The six curves y^2 = x^3 + c for c a sixth root of unity representative
            # have traces that are rotated. For j=0, there are at most 6 isomorphism classes.
            # Check all sixth roots
            print(f"    Note: j=0 curves have 6 twists with traces rotated by cube roots of unity")
    
    # The key question: does q ever divide the order?
    print("\n" + "=" * 95)
    print("KEY QUESTION: When does q | #E?")
    print("=" * 95)
    print(f"\n  For E: y^2 = x^3 - 1, #E = A+1-t.")
    print(f"  q | #E iff t = A+1 (mod q) = q^2+q+2 (mod q) = 2 (mod q).")
    print(f"  t = -2a where A = a^2 + 3b^2, a = 1 (mod 3).")
    print(f"  So q | #E iff -2a = 2 (mod q) iff a = -1 (mod q).")
    print(f"  Similarly q | #E' (for the sextic twist with trace 2a) iff 2a = 2 (mod q) iff a = 1 (mod q).")
    
    for q, A in good_pairs:
        a_cm, b_cm = find_cm_decomposition(A)
        if a_cm is not None:
            print(f"\n    q={q}: a = {a_cm}, a mod q = {a_cm % q}")
            print(f"      a = -1 mod q? {a_cm % q == q - 1}")
            print(f"      a = 1 mod q? {a_cm % q == 1}")
    
    # Check the relation between the order of 3 and q more carefully
    print("\n" + "=" * 95)
    print("RELATIONSHIP: ord_A(3) and q")
    print("=" * 95)
    print("  Since A = q^2+q+1, we have A-1 = q(q+1).")
    print("  By Fermat, 3^(q(q+1)) = 1 (mod A).")
    print("  So ord_A(3) | q(q+1).")
    print("  The divisors of q(q+1) involving q are: q, 2q, 3q, ..., q(q+1).")
    print("  3^q = 1 mod A iff ord_A(3) | q iff ord_A(3) = 1 or q (since q prime).")
    print("  ord_A(3) = 1 iff A | 2, impossible. So 3^q = 1 iff ord_A(3) = q.")
    
    for q, A in good_pairs:
        order3 = 1
        val = 3 % A
        while val != 1 and order3 <= A:
            val = (val * 3) % A
            order3 += 1
        
        # What is the relationship?
        ratio = (q * (q + 1)) // order3 if (q * (q + 1)) % order3 == 0 else None
        print(f"\n    q={q}: ord = {order3}, q(q+1)/ord = {ratio}")
        print(f"      q | ord? {order3 % q == 0}")
        print(f"      (q+1) | ord? {order3 % (q+1) == 0}")
    
    # Look at what happens for more primes to find patterns
    print("\n" + "=" * 95)
    print("EXTENDED SEARCH: primes q = 8 (mod 9), q < 5000, A prime")
    print("=" * 95)
    
    count = 0
    q_div_count = 0
    three_q_one_count = 0
    
    for q in range(8, 5000, 9):
        if not is_prime(q):
            continue
        A = q * q + q + 1
        if not is_prime(A):
            continue
        count += 1
        
        # Quick checks without full point count for large A
        three_q = pow(3, q, A)
        three_test = (three_q == 1)
        if three_test:
            three_q_one_count += 1
            print(f"  *** 3^q = 1 (mod A) at q = {q}, A = {A} ***")
        
        # For point counts, only do small A
        if A < 500000:
            E_minus = count_points_brute(0, -1, A)
            if E_minus % q == 0:
                q_div_count += 1
                print(f"  q = {q}, A = {A}: q | #E(x^3-1) = {E_minus} = {factor_str(E_minus)}")
    
    print(f"\n  Total pairs found: {count}")
    print(f"  Cases with 3^q = 1 (mod A): {three_q_one_count}")
    print(f"  Cases with q | #E(x^3-1) (A < 500000): {q_div_count}")

if __name__ == "__main__":
    main()
