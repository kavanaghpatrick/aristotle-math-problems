"""
Erdos Problem 1059: Find primes p where p - k! is composite for ALL k with 1 <= k! < p.

Known examples: p = 101, p = 211.
Search up to 10000.
"""

from sympy import isprime, primerange

def precompute_factorials(limit):
    """Compute factorials up to limit."""
    facts = []
    k = 1
    fact = 1
    while fact < limit:
        facts.append((k, fact))
        k += 1
        fact *= k
    return facts

def check_erdos_1059(p, factorials):
    """
    Check if p - k! is composite for ALL k! < p.
    Returns True if p qualifies (all differences are composite).
    Returns (False, k, k!, p-k!) for the first counterexample.
    """
    for k, kfact in factorials:
        if kfact >= p:
            break
        diff = p - kfact
        if diff <= 1:
            # 0 and 1 are not prime, so they count as "not prime" 
            # but 1 is neither prime nor composite. 
            # Convention: we need p - k! to be composite (≥4 and not prime).
            # diff=0 is not composite, diff=1 is not composite.
            if diff <= 1:
                return (False, k, kfact, diff)
        elif isprime(diff):
            return (False, k, kfact, diff)
    return True

def main():
    limit = 10000
    factorials = precompute_factorials(limit)
    
    print(f"Precomputed factorials less than {limit}:")
    for k, kfact in factorials:
        print(f"  {k}! = {kfact}")
    print()
    
    qualifying = []
    
    for p in primerange(2, limit + 1):
        result = check_erdos_1059(p, factorials)
        if result is True:
            qualifying.append(p)
    
    print(f"Primes p <= {limit} where p - k! is composite for all k! < p:")
    print(f"Found {len(qualifying)} such primes:\n")
    for p in qualifying:
        print(f"  p = {p}")
        # Show the details
        for k, kfact in factorials:
            if kfact >= p:
                break
            diff = p - kfact
            status = "COMPOSITE" if (diff > 1 and not isprime(diff)) else "prime" if isprime(diff) else str(diff)
            print(f"    p - {k}! = {p} - {kfact} = {diff}  [{status}]")
        print()

if __name__ == "__main__":
    main()
