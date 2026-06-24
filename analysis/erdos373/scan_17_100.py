"""
Erdős 373 (Hickerson) — extended factorial-decomposition scan for n ∈ [17, 100].

Goal: find all (n, [a_1, ..., a_k]) with
  - 2 <= a_i <= n - 2,
  - a_1 >= a_2 >= ... >= a_k,
  - k <= 8,
  - n! = prod a_i!.

L8 iter1 verified the four known solutions and scanned n ∈ [3, 80].
We extend to n ∈ [17, 100]. Hickerson's conjecture predicts ZERO solutions for n > 16.

Approach (Legendre):
  For each prime p, v_p(n!) = sum_{i>=1} floor(n / p^i).
  Equality n! = prod a_i! forces v_p(n!) = sum_i v_p(a_i!) for every prime p <= n.
  We branch on the largest a (= a_1) and recurse on n!/a_1! using *prime exponents*
  rather than the huge integers (100! has ~158 digits).
"""

from sympy import primerange, factorial
import json
import time


def legendre(n: int, p: int) -> int:
    """Compute v_p(n!) via Legendre's formula."""
    total = 0
    q = p
    while q <= n:
        total += n // q
        q *= p
    return total


def factorial_signature(n: int, primes: list) -> dict:
    """Return {p: v_p(n!)} for primes p <= n."""
    return {p: legendre(n, p) for p in primes if p <= n}


def subtract_sig(sig_n: dict, sig_a: dict) -> dict | None:
    """Return sig_n - sig_a if non-negative on every prime, else None."""
    out = {}
    for p, v in sig_n.items():
        diff = v - sig_a.get(p, 0)
        if diff < 0:
            return None
        if diff > 0:
            out[p] = diff
    # any prime in sig_a not in sig_n -> impossible (sig_a has prime not dividing n!)
    for p in sig_a:
        if p not in sig_n:
            return None
    return out


def is_zero_sig(sig: dict) -> bool:
    return all(v == 0 for v in sig.values())


def scan_n(n: int, k_max: int = 8) -> list:
    """Enumerate decompositions n! = prod a_i! with constraints."""
    primes = list(primerange(2, n + 1))
    sig_target = factorial_signature(n, primes)

    # Pre-compute factorial signatures for a in [2, n-2].
    sig_fact = {a: factorial_signature(a, primes) for a in range(2, n - 1)}

    solutions = []

    def recurse(remaining: dict, max_allowed: int, path: list, depth: int):
        if is_zero_sig(remaining):
            solutions.append(list(path))
            return
        if depth >= k_max:
            return
        # remaining must be a product of factorials with each a <= max_allowed.
        # Largest prime in remaining must be <= max_allowed (since a! contains p iff p <= a).
        max_prime_in_remaining = max((p for p, v in remaining.items() if v > 0), default=0)
        if max_prime_in_remaining > max_allowed:
            return
        for a in range(min(max_allowed, n - 2), 1, -1):
            new_rem = subtract_sig(remaining, sig_fact[a])
            if new_rem is None:
                continue
            path.append(a)
            recurse(new_rem, a, path, depth + 1)
            path.pop()

    recurse(sig_target, n - 2, [], 0)
    return solutions


def main():
    start = time.time()
    results = {}
    total_solutions = 0
    for n in range(17, 101):
        sols = scan_n(n, k_max=8)
        elapsed = time.time() - start
        if sols:
            results[n] = sols
            total_solutions += len(sols)
            print(f"n={n:3d}  SOLUTIONS={sols}  [t={elapsed:.1f}s]")
        else:
            if n % 10 == 0 or n in (17, 18, 19, 20, 25, 30):
                print(f"n={n:3d}  no solutions  [t={elapsed:.1f}s]")

    print(f"\n=== SCAN COMPLETE ===")
    print(f"n range: [17, 100], k_max=8")
    print(f"Total solutions found: {total_solutions}")
    print(f"Total elapsed: {time.time() - start:.1f}s")

    out_path = "/Users/patrickkavanagh/math/analysis/erdos373/scan_17_100_results.json"
    with open(out_path, "w") as f:
        json.dump({
            "n_range": [17, 100],
            "k_max": 8,
            "constraints": {
                "a_min": 2,
                "a_max_formula": "n - 2",
                "ordering": "descending (a_1 >= a_2 >= ... >= a_k)",
            },
            "method": "Legendre v_p prime-exponent recursion (no big-integer multiplication)",
            "total_solutions": total_solutions,
            "solutions_by_n": results,
        }, f, indent=2)
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
