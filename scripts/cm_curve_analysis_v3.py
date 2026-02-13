#!/usr/bin/env python3
"""
Investigate the remarkable pattern: a = -(q-1)/2 in the CM decomposition
A = q^2+q+1 = a^2 + 3b^2.
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

def find_cm_decomposition(A):
    """Find all (a,b) with A = a^2 + 3*b^2, a > 0."""
    results = []
    for b in range(1, isqrt(A) + 1):
        rem = A - 3 * b * b
        if rem > 0:
            a = isqrt(rem)
            if a * a == rem and a > 0:
                results.append((a, b))
    return results

def main():
    print("=" * 90)
    print("PATTERN IN CM DECOMPOSITION: A = q^2+q+1 = a^2 + 3b^2")
    print("=" * 90)
    
    # Check the identity: q^2+q+1 = ((q+1)/2)^2 + 3*((q+1)/2)^2 when q is odd
    # Wait, let's just check: if q is odd, q = 2m+1, then
    # q^2+q+1 = 4m^2+4m+1 + 2m+1 + 1 = 4m^2+6m+3 = (2m+1)^2 + (2m+1) + 1
    # We want a^2 + 3b^2 = q^2+q+1
    # Try a = (q-1)/2, b = (q+1)/2: a^2+3b^2 = (q-1)^2/4 + 3(q+1)^2/4
    # = [(q-1)^2 + 3(q+1)^2]/4 = [q^2-2q+1+3q^2+6q+3]/4 = [4q^2+4q+4]/4 = q^2+q+1
    # YES! So A = ((q-1)/2)^2 + 3*((q+1)/2)^2 is an IDENTITY.
    
    print("\nIdentity check: q^2+q+1 = ((q-1)/2)^2 + 3*((q+1)/2)^2")
    print("Proof: [(q-1)^2 + 3(q+1)^2]/4 = [q^2-2q+1+3q^2+6q+3]/4 = [4q^2+4q+4]/4 = q^2+q+1")
    print()
    
    print(f"{'q':>6} | {'A':>10} | {'(q-1)/2':>8} | {'(q+1)/2':>8} | {'a_found':>8} | {'b_found':>8} | {'match':>6} | {'trace':>8} | {'t = -(q-1)':>10}")
    print("-" * 100)
    
    for q in range(8, 2000, 9):
        if not is_prime(q):
            continue
        A = q * q + q + 1
        if not is_prime(A):
            continue
        
        # Predicted decomposition
        a_pred = (q - 1) // 2
        b_pred = (q + 1) // 2
        assert a_pred * a_pred + 3 * b_pred * b_pred == A, f"Identity failed for q={q}"
        
        # Found decomposition
        decomps = find_cm_decomposition(A)
        
        # The trace for y^2=x^3+1 is t = -2a where a = 1 (mod 3)
        # Our a_pred = (q-1)/2. For q = 8 (mod 9), q-1 = 7 (mod 9), (q-1)/2 = ... 
        # Let's check a_pred mod 3
        a_mod3 = a_pred % 3
        
        # Normalize: if a_pred = 2 (mod 3), use -a_pred
        a_norm = a_pred if a_mod3 == 1 else (-a_pred if a_mod3 == 2 else a_pred)
        
        # Expected trace = -2 * a_norm
        t_expected = -2 * a_norm
        
        # Verify with brute force for small A
        t_actual = None
        if A < 700000:
            count = 1
            for x in range(A):
                rhs = (pow(x, 3, A) + 1) % A  # y^2 = x^3 + 1
                if rhs == 0:
                    count += 1
                elif pow(rhs, (A - 1) // 2, A) == 1:
                    count += 2
            t_actual = A + 1 - count
        
        match_str = ""
        if t_actual is not None:
            if t_actual == t_expected:
                match_str = "OK"
            elif t_actual == -t_expected:
                match_str = "SIGN"
            else:
                match_str = f"DIFF({t_actual})"
        
        print(f"{q:>6} | {A:>10} | {a_pred:>8} | {b_pred:>8} | {decomps[0][0]:>8} | {decomps[0][1]:>8} | {match_str:>6} | {str(t_actual):>8} | {-(q-1):>10}")
    
    print()
    print("=" * 90)
    print("KEY INSIGHT")
    print("=" * 90)
    print("""
The decomposition A = q^2+q+1 = ((q-1)/2)^2 + 3*((q+1)/2)^2 is an algebraic identity.

So a = (q-1)/2, b = (q+1)/2.

For q = 8 (mod 9): q-1 = 7 (mod 9), so a = (q-1)/2 = (q-1)/2.
  a mod 3: q = 8 (mod 9) => q-1 = 7 (mod 9) => (q-1)/2 mod 3...
  q = 17: a = 8, 8 mod 3 = 2, normalized a = -8, trace = 16
  q = 71: a = 35, 35 mod 3 = 2, normalized a = -35, trace = 70
  q = 89: a = 44, 44 mod 3 = 2, normalized a = -44, trace = 88

So for q = 8 (mod 9), the normalized a = -(q-1)/2, and trace = -2*(-(q-1)/2) = q-1.

But wait, the traces we computed for y^2=x^3+1 were:
  q=17: t = -16 = -(q-1)
  q=71: t = -70 = -(q-1)  [when curves are isomorphic, both have same trace]
  q=89: t = -88 = -(q-1)
  q=701: t = -700 = -(q-1)
  q=773: t = -772 = -(q-1)
  q=827: t = -826 = -(q-1)

THIS IS REMARKABLE: The trace of Frobenius for y^2=x^3+1 over F_A is ALWAYS -(q-1).

So #E(F_A) = A + 1 - (-(q-1)) = A + 1 + q - 1 = q^2 + q + 1 + q = q^2 + 2q + 1 = (q+1)^2.

THE POINT COUNT IS ALWAYS (q+1)^2!
""")
    
    # Verify this
    print("Verification: #E(F_A) for y^2 = x^3 + 1:")
    for q in range(8, 2000, 9):
        if not is_prime(q):
            continue
        A = q * q + q + 1
        if not is_prime(A):
            continue
        if A > 700000:
            continue
        
        count = 1
        for x in range(A):
            rhs = (pow(x, 3, A) + 1) % A
            if rhs == 0:
                count += 1
            elif pow(rhs, (A - 1) // 2, A) == 1:
                count += 2
        
        expected = (q + 1) ** 2
        print(f"  q = {q}: #E = {count}, (q+1)^2 = {expected}, match = {count == expected}")
    
    # And for y^2 = x^3 - 1:
    print("\nVerification: #E(F_A) for y^2 = x^3 - 1:")
    for q in range(8, 2000, 9):
        if not is_prime(q):
            continue
        A = q * q + q + 1
        if not is_prime(A):
            continue
        if A > 700000:
            continue
        
        count = 1
        for x in range(A):
            rhs = (pow(x, 3, A) - 1) % A
            if rhs == 0:
                count += 1
            elif pow(rhs, (A - 1) // 2, A) == 1:
                count += 2
        
        # What's the pattern here?
        # trace for x^3-1: we saw t = -70, 88, 16, etc. Not always -(q-1).
        # When -1 is a cube: curves are isomorphic, so same count = (q+1)^2
        # When -1 is NOT a cube: different curves...
        # Actually -1 IS always a cube here since A = 1 mod 3 and we checked
        
        expected_same = (q + 1) ** 2
        trace = A + 1 - count
        
        print(f"  q = {q}: #E = {count}, (q+1)^2 = {expected_same}, match = {count == expected_same}, trace = {trace}")
    
    # Now the KEY divisibility
    print("\n" + "=" * 90)
    print("DIVISIBILITY: q | #E = (q+1)^2?")
    print("=" * 90)
    print(f"  (q+1)^2 mod q = 1^2 = 1.")
    print(f"  So q NEVER divides #E = (q+1)^2.")
    print(f"  This is consistent with our data: q | #E was always False.")
    
    # What about other twists?
    print("\n" + "=" * 90)
    print("ALL SIX TWISTS of j=0 curve over F_A (A = 1 mod 3)")
    print("=" * 90)
    print("For j=0, there are 6 twists: y^2 = x^3 + c for c in F_A*/F_A*^6")
    print("Their traces are: t, tw*t, tw^2*t, -t, -tw*t, -tw^2*t where tw = e^(2pi*i/3)")
    print("In terms of a, b with A = a^2+3b^2, the six traces are:")
    print("  -(2a), (a-3b), (a+3b), 2a, -(a-3b) = (3b-a), -(a+3b)")
    print()
    
    for q in [17, 71, 89, 701]:
        A = q * q + q + 1
        if not is_prime(A):
            continue
        
        a = (q - 1) // 2
        b = (q + 1) // 2
        
        traces = [-(2*a), (a - 3*b), (a + 3*b), 2*a, (3*b - a), -(a + 3*b)]
        counts = [A + 1 - t for t in traces]
        
        print(f"  q = {q}, a = {a}, b = {b}")
        print(f"    Six traces: {traces}")
        print(f"    Six counts: {counts}")
        print(f"    = simplify:")
        print(f"      -(q-1) = {-(q-1)}")
        print(f"      (q-1)/2 - 3(q+1)/2 = {(q-1)//2 - 3*(q+1)//2} = {-q - 1}")
        print(f"      (q-1)/2 + 3(q+1)/2 = {(q-1)//2 + 3*(q+1)//2} = {2*q + 1}")
        print(f"      (q-1) = {q-1}")
        print(f"      3(q+1)/2 - (q-1)/2 = {3*(q+1)//2 - (q-1)//2} = {q + 2}")
        # Wait let me be more careful
        t1 = -(q - 1)
        t2 = -q - 1
        t3 = 2*q + 1  # Hmm this is > 2*sqrt(A)? Let me check
        t4 = q - 1
        t5 = q + 2  # Hmm
        t6 = -(2*q + 1)
        
        # Actually let me just compute: a-3b = (q-1)/2 - 3(q+1)/2 = (q-1-3q-3)/2 = (-2q-2)/2 = -(q+1)
        # a+3b = (q-1)/2 + 3(q+1)/2 = (q-1+3q+3)/2 = (4q+2)/2 = 2q+1
        print(f"    Exact: a-3b = -(q+1) = {-(q+1)}")
        print(f"    Exact: a+3b = 2q+1 = {2*q+1}")
        print(f"    Six exact traces: {-(q-1)}, {-(q+1)}, {2*q+1}, {q-1}, {q+1}, {-(2*q+1)}")
        counts_exact = [A+1+(q-1), A+1+(q+1), A+1-(2*q+1), A+1-(q-1), A+1-(q+1), A+1+(2*q+1)]
        print(f"    Six exact counts: {counts_exact}")
        print(f"    = {[(q+1)**2, (q+1)*(q+2), q*(q-1), q*(q+2), q*(q+1) if False else 'check', 'check']}")
        
        # Let me compute properly
        c1 = A + 1 - (-(q-1))   # = q^2+q+1+1+q-1 = q^2+2q+1 = (q+1)^2
        c2 = A + 1 - (-(q+1))   # = q^2+q+1+1+q+1 = q^2+2q+3 = (q+1)^2 + 2
        c3 = A + 1 - (2*q+1)    # = q^2+q+1+1-2q-1 = q^2-q+1
        c4 = A + 1 - (q-1)      # = q^2+q+1+1-q+1 = q^2+3 = ...wait
        # Hmm let me just be careful
        c1 = q*q + q + 1 + 1 + (q-1)  # A+1-t where t = -(q-1)
        c2 = q*q + q + 1 + 1 + (q+1)  # t = -(q+1)
        c3 = q*q + q + 1 + 1 - (2*q+1)  # t = 2q+1
        c4 = q*q + q + 1 + 1 - (q-1)  # t = q-1
        c5 = q*q + q + 1 + 1 - (q+1)  # t = q+1
        c6 = q*q + q + 1 + 1 + (2*q+1)  # t = -(2q+1)
        
        print(f"    Recomputed counts:")
        print(f"      t=-(q-1): #E = q^2+2q+1 = (q+1)^2 = {c1}")
        print(f"      t=-(q+1): #E = q^2+2q+3 = {c2}")
        print(f"      t=2q+1:   #E = q^2-q+1 = {c3}")
        print(f"      t=q-1:    #E = q^2+3 = {c4}")
        print(f"      t=q+1:    #E = q^2+1 = {c5}")
        print(f"      t=-(2q+1): #E = q^2+3q+3 = {c6}")
        
        print(f"    q divides which counts?")
        for label, c in [("(q+1)^2", c1), ("q^2+2q+3", c2), ("q^2-q+1", c3), 
                          ("q^2+3", c4), ("q^2+1", c5), ("q^2+3q+3", c6)]:
            print(f"      {label} = {c}, mod q = {c % q}, q | count = {c % q == 0}")
        print()

if __name__ == "__main__":
    main()
