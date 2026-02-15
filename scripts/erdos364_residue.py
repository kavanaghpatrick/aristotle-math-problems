#!/usr/bin/env python3
"""
Erdős 364: Check if 3 consecutive powerful numbers can exist.

A number n is "powerful" if for every prime p dividing n, p² also divides n.

Strategy: For small primes S = {2,3,5,7}, check residue classes mod M = lcm(4,9,25,49) = 44100.
For each r in 0..M-1, check if r, r+1, r+2 can ALL be "S-powerful":
  - For each p in S: if p | (r+i), then p² | (r+i)

If no triple survives, we have a proof that no 3 consecutive integers are powerful.
"""

from math import gcd
from functools import reduce

def lcm(a, b):
    return a * b // gcd(a, b)

def check_locally_powerful(r, M, primes):
    """Check if r mod M is consistent with being powerful for all primes in the list.

    For each prime p: if p | r, then p² | r (working mod M where p² | M).
    Returns True if r COULD be powerful (no contradiction from these primes).
    """
    for p in primes:
        p2 = p * p
        if r % p == 0 and r % p2 != 0:
            # p divides r but p² doesn't -> r cannot be powerful
            return False
    return True

def main():
    primes = [2, 3, 5, 7]

    # M = lcm of p² for p in primes
    M = reduce(lcm, [p*p for p in primes])
    print(f"Modulus M = {M} = lcm({', '.join(str(p*p) for p in primes)})")
    print(f"Checking all {M} residue classes for triples (r, r+1, r+2)...")
    print()

    survivors = []

    for r in range(M):
        r0 = r % M
        r1 = (r + 1) % M
        r2 = (r + 2) % M

        if (check_locally_powerful(r0, M, primes) and
            check_locally_powerful(r1, M, primes) and
            check_locally_powerful(r2, M, primes)):
            survivors.append(r)

    print(f"Survivors: {len(survivors)} out of {M}")

    if len(survivors) == 0:
        print("\n*** NO SURVIVORS! ***")
        print("This means: for primes {2,3,5,7}, no triple (n,n+1,n+2) can have")
        print("all three be locally powerful. Since powerful => locally powerful,")
        print("this PROVES no 3 consecutive integers are all powerful!")
        print("\nThis is a FINITE CERTIFICATE for Erdős 364 (k=3)!")
    else:
        print(f"\nSurvivor residue classes mod {M}:")
        for r in survivors:
            details = []
            for i in range(3):
                ri = (r + i) % M
                factors = []
                for p in primes:
                    if ri % (p*p) == 0:
                        factors.append(f"{p}²|")
                    elif ri % p == 0:
                        factors.append(f"{p}|NOT{p}²")  # should not happen if survivor
                    else:
                        factors.append(f"{p}∤")
                details.append(f"  r+{i}={ri}: {' '.join(factors)}")
            print(f"\nr ≡ {r} (mod {M}):")
            for d in details:
                print(d)

        # Try extending with more primes
        print(f"\n--- Trying with extended prime set ---")
        for extra_p in [11, 13, 17, 19, 23]:
            extended_primes = primes + [extra_p]
            M_ext = reduce(lcm, [p*p for p in extended_primes])

            if M_ext > 10**8:
                print(f"\nWith p={extra_p}: M={M_ext} too large for direct enumeration")
                # Instead, check which survivors from the smaller modulus
                # are eliminated by the new prime
                new_survivors = []
                for r in survivors:
                    # Check all lifts of r mod M to mod M_ext
                    eliminated = True
                    for lift in range(0, M_ext, M):
                        rr = r + lift
                        r0 = rr % M_ext
                        r1 = (rr + 1) % M_ext
                        r2 = (rr + 2) % M_ext
                        if (check_locally_powerful(r0, M_ext, extended_primes) and
                            check_locally_powerful(r1, M_ext, extended_primes) and
                            check_locally_powerful(r2, M_ext, extended_primes)):
                            eliminated = False
                            break
                    if not eliminated:
                        new_survivors.append(r)
                print(f"With p={extra_p}: {len(new_survivors)} survivors remain (from {len(survivors)})")
                if len(new_survivors) < len(survivors):
                    print(f"  Eliminated: {set(survivors) - set(new_survivors)}")
                survivors_for_next = new_survivors
            else:
                count = 0
                for r in range(M_ext):
                    r0 = r % M_ext
                    r1 = (r + 1) % M_ext
                    r2 = (r + 2) % M_ext
                    if (check_locally_powerful(r0, M_ext, extended_primes) and
                        check_locally_powerful(r1, M_ext, extended_primes) and
                        check_locally_powerful(r2, M_ext, extended_primes)):
                        count += 1
                print(f"With p={extra_p}: M={M_ext}, {count} survivors")
                if count == 0:
                    print(f"  *** NO SURVIVORS with primes up to {extra_p}! ***")
                    break

    # Also check: what about r=7,8,9? (known: 8=2³, 9=3², 7 is prime but not powerful)
    print(f"\n--- Sanity check: known triples ---")
    for start in [7, 8, 25, 26, 27, 48, 49]:
        vals = [start, start+1, start+2]
        powerful = []
        for v in vals:
            is_pow = True
            n = v
            d = 2
            while d * d <= n:
                if n % d == 0:
                    count = 0
                    while n % d == 0:
                        n //= d
                        count += 1
                    if count < 2:
                        is_pow = False
                        break
                d += 1
            if n > 1:  # remaining prime factor with exponent 1
                is_pow = False
            powerful.append(is_pow)
        status = ["powerful" if p else "NOT powerful" for p in powerful]
        print(f"  {vals}: {status}")

if __name__ == "__main__":
    main()
