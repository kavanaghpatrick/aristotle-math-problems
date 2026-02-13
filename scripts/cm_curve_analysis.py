#!/usr/bin/env python3
"""
Analyze the CM elliptic curve E: y^2 = x^3 - 1 over F_A where A = q^2 + q + 1
for primes q = 8 (mod 9).
Also analyze the twist E': y^2 = x^3 + 1.
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
    count = 1  # point at infinity
    for x in range(p):
        rhs = (pow(x, 3, p) + a_coeff * x + b_coeff) % p
        if rhs == 0:
            count += 1
        else:
            if pow(rhs, (p - 1) // 2, p) == 1:
                count += 2
    return count

def factorize(n):
    if n <= 1:
        return {n: 1}
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
    if n == 1:
        return "1"
    f = factorize(n)
    parts = []
    for p in sorted(f.keys()):
        if f[p] == 1:
            parts.append(str(p))
        else:
            parts.append(f"{p}^{f[p]}")
    return " * ".join(parts)

def main():
    candidates = [71, 107, 179, 251, 359, 431, 467, 503, 539]
    
    print("=" * 90)
    print("CM Elliptic Curve Analysis: E: y^2 = x^3 - 1 over F_A, A = q^2 + q + 1")
    print("=" * 90)
    
    # Step 1: Filter to actual primes and check q = 8 (mod 9)
    print("\n--- Filtering candidates ---")
    primes_q = []
    for q in candidates:
        p = is_prime(q)
        mod9 = q % 9
        status = "PASS" if (p and mod9 == 8) else "FAIL"
        reason = ""
        if not p:
            reason = " (not prime)"
        elif mod9 != 8:
            reason = f" (q mod 9 = {mod9}, not 8)"
        print(f"  q = {q}: prime={p}, q mod 9 = {mod9} => {status}{reason}")
        if p and mod9 == 8:
            primes_q.append(q)
    
    print(f"\nFiltered primes q = 8 (mod 9): {primes_q}")
    
    # Main computation
    print("\n" + "=" * 90)
    sep = " | "
    hdr = f"{'q':>6}{sep}{'A':>10}{sep}{'A prime':>7}{sep}{'#E':>10}{sep}{'q|#E':>5}{sep}{'#E_tw':>10}{sep}{'q|#E_tw':>7}{sep}{'3^q=1?':>7}"
    print(hdr)
    print("-" * 90)
    
    results = []
    
    for q in primes_q:
        A = q * q + q + 1
        A_prime = is_prime(A)
        
        if A_prime:
            E_count = count_points_brute(0, -1, A)
            E_twist_count = count_points_brute(0, 1, A)
            q_div_E = (E_count % q == 0)
            q_div_E_twist = (E_twist_count % q == 0)
            three_pow_q = pow(3, q, A)
            three_test = (three_pow_q == 1)
            
            row = f"{q:>6}{sep}{A:>10}{sep}{'YES':>7}{sep}{E_count:>10}{sep}{'YES' if q_div_E else 'no':>5}{sep}{E_twist_count:>10}{sep}{'YES' if q_div_E_twist else 'no':>7}{sep}{'YES!!!' if three_test else 'no':>7}"
            print(row)
            
            t = A + 1 - E_count
            t_tw = A + 1 - E_twist_count
            print(f"  Details:")
            print(f"    3^q mod A = {three_pow_q}")
            print(f"    trace(E)  = {t},  #E  = A+1-t = {E_count} = {factor_str(E_count)}")
            print(f"    trace(E') = {t_tw}, #E' = A+1-t' = {E_twist_count} = {factor_str(E_twist_count)}")
            print(f"    Verify twist: #E + #E' = {E_count + E_twist_count}, 2(A+1) = {2*(A+1)}, match = {E_count + E_twist_count == 2*(A+1)}")
            print(f"    A mod 3 = {A % 3}, A mod 9 = {A % 9}")
            print()
            
            results.append((q, A, E_count, E_twist_count, t, q_div_E, q_div_E_twist, three_test))
        else:
            row = f"{q:>6}{sep}{A:>10}{sep}{'no':>7}{sep}{'---':>10}{sep}{'---':>5}{sep}{'---':>10}{sep}{'---':>7}{sep}{'---':>7}"
            print(row)
            three_pow_q = pow(3, q, A)
            print(f"  A is composite. 3^q mod A = {three_pow_q}")
            for d in range(2, isqrt(A) + 1):
                if A % d == 0:
                    print(f"  A = {d} * {A // d}")
                    break
            print()
    
    # Order of 3 mod A
    print("\n" + "=" * 90)
    print("ORDER OF 3 MODULO A")
    print("=" * 90)
    
    for q, A, E_count, E_twist_count, t, q_div_E, q_div_E_twist, three_test in results:
        order = 1
        val = 3 % A
        while val != 1:
            val = (val * 3) % A
            order += 1
            if order > A:
                print(f"  q={q}: ERROR")
                break
        phi_A = A - 1  # A is prime
        print(f"\n  q = {q}, A = {A}")
        print(f"    ord_A(3) = {order} = {factor_str(order)}")
        print(f"    phi(A) = A-1 = {phi_A} = {factor_str(phi_A)}")
        print(f"    q*(q+1) = {q*(q+1)} = {factor_str(q*(q+1))}")
        print(f"    ord | phi(A)? {phi_A % order == 0}")
        print(f"    ord = q? {order == q}")
        print(f"    ord = q+1? {order == q + 1}")
        print(f"    ord divisible by q? {order % q == 0}")
        print(f"    3^q mod A = {pow(3, q, A)}")
    
    # CM decomposition: A = a^2 + 3b^2
    print("\n" + "=" * 90)
    print("CM DECOMPOSITION: A = a^2 + 3*b^2")
    print("=" * 90)
    print("For p = 1 (mod 3), the CM curve y^2=x^3+1 has trace t = -2a")
    print("where p = a^2 + 3b^2, a = 1 (mod 3) (Deuring).")
    print("The curve y^2=x^3-1 is isomorphic to y^2=x^3+1 when -1 is a cube mod p.")
    print("Over F_p: y^2=x^3-1 and y^2=x^3+1 differ by x -> zeta*x if cube roots exist.")
    print()
    
    for q, A, E_count, E_twist_count, t, q_div_E, q_div_E_twist, three_test in results:
        # Find a, b such that A = a^2 + 3*b^2
        found = False
        for b in range(1, isqrt(A) + 1):
            rem = A - 3 * b * b
            if rem > 0:
                a = isqrt(rem)
                if a * a == rem:
                    # Normalize: a = 1 mod 3
                    if a % 3 == 1:
                        a_norm = a
                    elif a % 3 == 2:
                        a_norm = -a
                    else:
                        a_norm = a  # a divisible by 3, unusual
                    print(f"  q = {q}, A = {A} = {a}^2 + 3*{b}^2 = {a*a} + {3*b*b}")
                    print(f"    a (normalized, a=1 mod 3): {a_norm}")
                    print(f"    Expected trace for y^2=x^3+1: t = -2a = {-2*a_norm}")
                    print(f"    Actual trace for E (y^2=x^3-1): {A + 1 - E_count}")
                    print(f"    Actual trace for E' (y^2=x^3+1): {A + 1 - E_twist_count}")
                    found = True
                    break
        if not found:
            print(f"  q = {q}, A = {A}: no decomposition found (unexpected!)")
    
    # Final summary
    print("\n" + "=" * 90)
    print("FINAL SUMMARY")
    print("=" * 90)
    
    any_3q = False
    for q, A, E_count, E_twist_count, t, q_div_E, q_div_E_twist, three_test in results:
        if three_test:
            any_3q = True
    
    print(f"\n  3^q = 1 (mod A) for any q? {'YES - SURPRISING!' if any_3q else 'NO (as expected)'}")
    print(f"  If this held, it would mean ord_A(3) | q, which (since q is prime)")
    print(f"  forces ord_A(3) = q. Since A = q^2+q+1 and A-1 = q^2+q = q(q+1),")
    print(f"  this is possible iff q | (A-1), which is always true.")
    print(f"  So 3^q = 1 (mod A) is NUMBER-THEORETICALLY possible but doesn't hold here.")
    
    print(f"\n  q | #E(F_A) results:")
    for q, A, E_count, E_twist_count, t, q_div_E, q_div_E_twist, three_test in results:
        print(f"    q={q}: q | #E = {q_div_E}, q | #E' = {q_div_E_twist}")
    
    print(f"\n  Connection: #E = A+1-t where t is the trace of Frobenius.")
    print(f"  q | #E iff q | (A+1-t) iff t = A+1 (mod q) iff t = q^2+q+2 (mod q) iff t = 2 (mod q).")
    print(f"  q | #E' iff t = -2 (mod q)  [since #E' = A+1+t for the twist].")
    print(f"  Wait, actually #E' = A+1-(-t) = A+1+t only if E' is the quadratic twist.")
    print(f"  Let me check: y^2=x^3-1 vs y^2=x^3+1. These differ by b -> -b.")
    print(f"  If char(F_A) > 3 and -1 is NOT a cube, these are genuinely different curves (not twists).")
    print(f"  If -1 IS a cube, then x -> (-1)^(1/3)*x is an isomorphism.")
    
    # Check if -1 is a cube mod A
    print(f"\n  Is -1 a cube mod A?")
    for q, A, E_count, E_twist_count, t, q_div_E, q_div_E_twist, three_test in results:
        # -1 is a cube mod A iff (-1)^((A-1)/3) = 1 mod A
        # A-1 = q^2+q, so (A-1)/3 = (q^2+q)/3
        if (A - 1) % 3 == 0:
            exp = (A - 1) // 3
            val = pow(A - 1, exp, A)  # (-1)^exp mod A
            # Actually: (-1) mod A = A-1
            val = pow(A - 1, exp, A)
            is_cube = (val == 1)
            print(f"    q={q}, A={A}: (-1)^((A-1)/3) = (-1)^{exp} mod A = {val}, -1 is cube: {is_cube}")
        else:
            print(f"    q={q}, A={A}: (A-1) not divisible by 3 (unexpected)")

if __name__ == "__main__":
    main()
