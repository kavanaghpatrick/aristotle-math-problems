#!/usr/bin/env python3
"""
Erdős 364: Deeper analysis of surviving triples.

Key question: Among the 1209 survivors mod 44100, what patterns exist?
Can we prove structural constraints even without a full certificate?
"""

def check_locally_powerful(r, M, primes):
    for p in primes:
        p2 = p * p
        if r % p == 0 and r % p2 != 0:
            return False
    return True

def main():
    primes = [2, 3, 5, 7]
    M = 44100

    survivors = []
    for r in range(M):
        r0 = r % M
        r1 = (r + 1) % M
        r2 = (r + 2) % M
        if (check_locally_powerful(r0, M, primes) and
            check_locally_powerful(r1, M, primes) and
            check_locally_powerful(r2, M, primes)):
            survivors.append(r)

    print(f"Total survivors: {len(survivors)}")

    # Analyze: how many survivors have ALL THREE positions coprime to 2,3,5,7?
    all_coprime = []
    has_square = []
    patterns = {}

    for r in survivors:
        pattern = []
        for i in range(3):
            ri = (r + i) % M
            divisors = []
            for p in primes:
                if ri % (p*p) == 0:
                    divisors.append(f"{p}²")
                elif ri % p != 0:
                    divisors.append("free")
            pattern.append(tuple(divisors))

        pat_key = tuple(tuple(sorted(p)) for p in pattern)

        # Check if any position is forced to have a specific square factor
        forced = []
        for i in range(3):
            ri = (r + i) % M
            facs = []
            for p in primes:
                if ri % (p*p) == 0:
                    facs.append(p)
            forced.append(facs)

        forced_key = tuple(tuple(f) for f in forced)
        if forced_key not in patterns:
            patterns[forced_key] = 0
        patterns[forced_key] += 1

        if all(len(f) == 0 for f in forced):
            all_coprime.append(r)

    print(f"\nSurvivors where ALL THREE are coprime to 2,3,5,7: {len(all_coprime)}")
    print(f"Survivors where at least one has a forced square factor: {len(survivors) - len(all_coprime)}")

    # Show the pattern distribution
    print(f"\nPattern distribution (forced square factors for each position):")
    sorted_patterns = sorted(patterns.items(), key=lambda x: -x[1])
    for pat, count in sorted_patterns[:20]:
        desc = " | ".join(
            f"[{','.join(str(p) for p in pos)}]" if pos else "[free]"
            for pos in pat
        )
        print(f"  {desc}: {count}")

    # Key structural constraint: mod 4 analysis
    print(f"\n--- Mod 4 analysis ---")
    # In any triple (n,n+1,n+2), exactly one is even. If that one is powerful, 4|it.
    # The other two are odd. For odd powerful: all prime factors squared.
    # Among n,n+1,n+2: the even one ≡ 0 mod 2.
    # For powerful: need 4 | even one.

    # Mod 36 analysis (lcm of 4,9) - more manageable
    M36 = 36
    survivors_36 = []
    for r in range(M36):
        r0 = r % M36
        r1 = (r + 1) % M36
        r2 = (r + 2) % M36
        if (check_locally_powerful(r0, M36, [2,3]) and
            check_locally_powerful(r1, M36, [2,3]) and
            check_locally_powerful(r2, M36, [2,3])):
            survivors_36.append(r)

    print(f"Survivors mod 36 (just primes 2,3): {len(survivors_36)} out of 36")
    for r in survivors_36:
        print(f"  r ≡ {r} (mod 36): ({r%36}, {(r+1)%36}, {(r+2)%36})")

    # Mod 4 analysis
    print(f"\n--- Mod 4 analysis ---")
    for r in range(4):
        vals = [r, (r+1)%4, (r+2)%4]
        ok = all(v % 2 != 0 or v % 4 == 0 for v in vals)
        print(f"  r ≡ {r} (mod 4): {vals} -> {'SURVIVES' if ok else 'ELIMINATED'}")

    # Mod 9 analysis
    print(f"\n--- Mod 9 analysis ---")
    for r in range(9):
        vals = [r, (r+1)%9, (r+2)%9]
        ok = all(v % 3 != 0 or v % 9 == 0 for v in vals)
        print(f"  r ≡ {r} (mod 9): {vals} -> {'SURVIVES' if ok else 'ELIMINATED'}")

    # What if we search for actual powerful triples up to 10^8?
    print(f"\n--- Searching for actual 3-consecutive powerful numbers up to 10^8 ---")
    import math

    limit = 10**8
    # Sieve powerful numbers using square factors
    # A number is powerful if for every prime p | n, we have p² | n
    # Equivalently, n = a²b³ for some a,b

    # Generate powerful numbers up to limit
    powerful = set()
    # n is powerful iff n = a²·b³
    b_max = int(limit**(1/3)) + 1
    for b in range(1, b_max + 1):
        b3 = b * b * b
        if b3 > limit:
            break
        a_max = int(math.sqrt(limit // b3)) + 1
        for a in range(1, a_max + 1):
            val = a * a * b3
            if val <= limit:
                powerful.add(val)

    powerful_sorted = sorted(powerful)
    print(f"Powerful numbers up to {limit}: {len(powerful_sorted)}")

    # Check for 3 consecutive
    consecutive_3 = []
    powerful_set = powerful
    for n in powerful_sorted:
        if n + 1 in powerful_set and n + 2 in powerful_set:
            consecutive_3.append(n)

    if consecutive_3:
        print(f"FOUND {len(consecutive_3)} triples of 3 consecutive powerful numbers!")
        for n in consecutive_3[:10]:
            print(f"  {n}, {n+1}, {n+2}")
    else:
        print(f"NO 3-consecutive powerful numbers found up to {limit}")

    # Also count consecutive pairs
    pairs = []
    for n in powerful_sorted:
        if n + 1 in powerful_set:
            pairs.append(n)
    print(f"\nConsecutive PAIRS of powerful numbers up to {limit}: {len(pairs)}")
    for n in pairs[:15]:
        print(f"  ({n}, {n+1})")

    # Density analysis
    print(f"\n--- Density of powerful numbers ---")
    for exp in range(3, 9):
        bound = 10**exp
        count = sum(1 for p in powerful_sorted if p <= bound)
        density = count / bound
        zeta = 6 / (3.14159**2)  # theoretical: c·√n, c = ζ(3/2)/ζ(3)
        print(f"  Up to 10^{exp}: {count} powerful, density = {density:.6f}, √(10^{exp}) = {math.sqrt(bound):.0f}")

if __name__ == "__main__":
    main()
