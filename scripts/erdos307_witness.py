#!/usr/bin/env python3
"""
Erdős Problem 307 Witness Search
=================================
Find two finite sets of primes P and Q such that:
    (sum 1/p for p in P) * (sum 1/q for q in Q) = 1

Uses exact rational arithmetic (fractions.Fraction) throughout.
"""

import sys
import time
from fractions import Fraction
from itertools import combinations

# Avoid ValueError on huge fraction denominators
sys.set_int_max_str_digits(100000)

# --- Prime generation via sieve ---
def sieve_primes(limit):
    is_prime = bytearray(b'\x01') * (limit + 1)
    is_prime[0] = is_prime[1] = 0
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            is_prime[i*i::i] = bytearray(len(is_prime[i*i::i]))
    return [i for i in range(2, limit + 1) if is_prime[i]]

# Generate primes
PRIME_LIMIT = 200000
ALL_PRIMES = sieve_primes(PRIME_LIMIT)
PRIME_SET = set(ALL_PRIMES)
RECIP = {p: Fraction(1, p) for p in ALL_PRIMES}

print(f"Generated {len(ALL_PRIMES)} primes up to {PRIME_LIMIT}")
# Compute sum incrementally to avoid huge intermediate
_sum = Fraction(0)
for p in ALL_PRIMES:
    _sum += RECIP[p]
print(f"Sum of all prime reciprocals up to {PRIME_LIMIT}: ~{float(_sum):.6f}")
MAX_PRIME_RECIP_SUM = _sum
del _sum
print()


def frac_str(f):
    """Short string for a fraction: just show float if denominator is huge."""
    if f.denominator < 10**15:
        return f"{f} (~{float(f):.6e})"
    else:
        return f"~{float(f):.10e}"


# --- Greedy decomposition ---
def greedy_decompose(target, excluded_primes, prime_list):
    remaining = target
    used = []
    for p in prime_list:
        if remaining <= 0:
            break
        if p in excluded_primes:
            continue
        rp = Fraction(1, p)
        if rp <= remaining:
            used.append(p)
            remaining -= rp
            if remaining == 0:
                break
    return used, remaining


# --- Backtracking decomposition ---
def backtrack_decompose(target, excluded_primes_orig, prime_list, max_depth=30,
                        branching=4, time_limit=2.0):
    start_time = time.time()
    best_remainder = [target]
    best_solution = [None]

    def _search(remaining, used, start_idx, depth, excluded):
        if time.time() - start_time > time_limit:
            return False
        if remaining == 0:
            best_remainder[0] = Fraction(0)
            best_solution[0] = list(used)
            return True
        if remaining < 0 or depth >= max_depth:
            return False
        if remaining < best_remainder[0]:
            best_remainder[0] = remaining
            best_solution[0] = list(used)

        # 1/p <= remaining means p >= ceil(denom/numer)
        if remaining.numerator <= 0:
            return False
        min_prime = remaining.denominator // remaining.numerator
        if remaining.denominator % remaining.numerator != 0:
            min_prime += 1

        candidates = []
        count = 0
        for i in range(start_idx, len(prime_list)):
            p = prime_list[i]
            if p < min_prime:
                continue
            if p in excluded:
                continue
            candidates.append((i, p))
            count += 1
            if count >= branching:
                break

        for idx, p in candidates:
            used.append(p)
            excluded.add(p)
            if _search(remaining - Fraction(1, p), used, idx + 1, depth + 1, excluded):
                return True
            used.pop()
            excluded.discard(p)
        return False

    excl = set(excluded_primes_orig)
    _search(target, [], 0, 0, excl)
    return best_solution[0], best_remainder[0]


# --- Multi-greedy: try skipping early choices ---
def multi_greedy_decompose(target, excluded_primes, prime_list, num_skips=5):
    results = []
    used, rem = greedy_decompose(target, excluded_primes, prime_list)
    results.append((used, rem))
    if rem == 0:
        return results[0]

    # Find first few greedy choices
    remaining = target
    greedy_choices = []
    for p in prime_list:
        if p in excluded_primes:
            continue
        rp = Fraction(1, p)
        if rp <= remaining:
            greedy_choices.append(p)
            remaining -= rp
            if remaining == 0 or len(greedy_choices) >= num_skips:
                break

    for skip_p in greedy_choices:
        rem2 = target
        used2 = []
        skipped = False
        excl2 = set(excluded_primes)
        for p in prime_list:
            if rem2 <= 0:
                break
            if p in excl2:
                continue
            rp = Fraction(1, p)
            if rp <= rem2:
                if not skipped and p == skip_p:
                    skipped = True
                    continue
                used2.append(p)
                excl2.add(p)
                rem2 -= rp
                if rem2 == 0:
                    break
        results.append((used2, rem2))
        if rem2 == 0:
            return (used2, rem2)

    return min(results, key=lambda x: x[1])


# --- Main search ---
def main():
    P_PRIMES_LIMIT = 50
    p_primes = ALL_PRIMES[:P_PRIMES_LIMIT]

    near_misses = []
    solutions = []
    total_checked = 0
    start_time = time.time()

    # ===== Phase 1: Small P sets (detailed output) =====
    print("=" * 70)
    print("PHASE 1: Quick analysis of small P sets (sizes 1-4, first 15 primes)")
    print("=" * 70)

    for size in range(1, 5):
        for P in combinations(p_primes[:15], size):
            S_P = sum(Fraction(1, p) for p in P)
            target = Fraction(1) / S_P
            t_float = float(target)

            if target <= 0:
                continue

            total_checked += 1
            excluded = set(P)

            # Feasibility check
            if target > MAX_PRIME_RECIP_SUM:
                print(f"P={P}, S_P~{float(S_P):.6f}, target~{t_float:.6f} -> INFEASIBLE")
                continue

            used, rem = greedy_decompose(target, excluded, ALL_PRIMES)
            if rem == 0:
                print(f"*** SOLUTION! P={P}, Q={used}")
                solutions.append((list(P), used))
            else:
                r_float = float(rem)
                print(f"P={P}, S_P~{float(S_P):.6f}, target~{t_float:.6f}, "
                      f"|Q|={len(used)}, remainder~{r_float:.4e}")
                if r_float < 1e-8:
                    near_misses.append((r_float, list(P), rem))

    print()

    # ===== Phase 2: Systematic (sizes 2-6, first 20 primes) =====
    print("=" * 70)
    print("PHASE 2: Systematic search (sizes 2-6, first 20 primes)")
    print("=" * 70)

    for size in range(2, 7):
        pool = p_primes[:20]
        combos = list(combinations(pool, size))
        print(f"\nSize {size}: {len(combos)} combinations")
        checked_this = 0
        found_this = 0

        for P in combos:
            S_P = sum(Fraction(1, p) for p in P)
            target = Fraction(1) / S_P
            if target <= 0 or target > MAX_PRIME_RECIP_SUM:
                continue

            total_checked += 1
            checked_this += 1
            excluded = set(P)

            # Greedy
            used, rem = greedy_decompose(target, excluded, ALL_PRIMES)
            if rem == 0:
                print(f"  *** SOLUTION (greedy)! P={P}, |Q|={len(used)}")
                solutions.append((list(P), used))
                found_this += 1
                continue

            # Multi-greedy
            used2, rem2 = multi_greedy_decompose(target, excluded, ALL_PRIMES, num_skips=5)
            if rem2 == 0:
                print(f"  *** SOLUTION (multi-greedy)! P={P}, |Q|={len(used2)}")
                solutions.append((list(P), used2))
                found_this += 1
                continue

            best_rem = min(rem, rem2)

            # Backtracking if close
            if float(best_rem) < 1e-6:
                sol, bt_rem = backtrack_decompose(target, excluded, ALL_PRIMES,
                                                   max_depth=25, branching=5, time_limit=3.0)
                if bt_rem == 0 and sol is not None:
                    print(f"  *** SOLUTION (backtrack)! P={P}, |Q|={len(sol)}")
                    solutions.append((list(P), sol))
                    found_this += 1
                    continue
                if bt_rem < best_rem:
                    best_rem = bt_rem

            rf = float(best_rem)
            if rf < 1e-8:
                near_misses.append((rf, list(P), best_rem))

            if checked_this % 2000 == 0:
                elapsed = time.time() - start_time
                print(f"  ... {checked_this}/{len(combos)}, {elapsed:.1f}s, {found_this} solutions")

        print(f"  Size {size} done: checked {checked_this}, found {found_this}")

    # ===== Phase 3: Targeted (S_P in [0.5, 2], first 30 primes, sizes 3-5) =====
    print()
    print("=" * 70)
    print("PHASE 3: Targeted (first 30 primes, sizes 3-5, S_P in [0.5, 2])")
    print("=" * 70)

    for size in range(3, 6):
        pool = p_primes[:30]
        combos = list(combinations(pool, size))
        print(f"\nSize {size}: {len(combos)} total combinations")
        checked = 0
        found = 0

        for P in combos:
            S_P = sum(Fraction(1, p) for p in P)
            sp_f = float(S_P)
            if sp_f < 0.5 or sp_f >= 2.0:
                continue

            target = Fraction(1) / S_P
            if target > MAX_PRIME_RECIP_SUM:
                continue

            checked += 1
            total_checked += 1
            excluded = set(P)

            used, rem = greedy_decompose(target, excluded, ALL_PRIMES)
            if rem == 0:
                print(f"  *** SOLUTION! P={P}, |Q|={len(used)}")
                solutions.append((list(P), used))
                found += 1
                continue

            if float(rem) < 1e-4:
                sol, bt_rem = backtrack_decompose(target, excluded, ALL_PRIMES,
                                                   max_depth=30, branching=6, time_limit=5.0)
                if bt_rem == 0 and sol is not None:
                    print(f"  *** SOLUTION (backtrack)! P={P}, |Q|={len(sol)}")
                    solutions.append((list(P), sol))
                    found += 1
                    continue
                rf = float(bt_rem)
                if rf < 1e-8:
                    near_misses.append((rf, list(P), bt_rem))

            if checked % 5000 == 0:
                elapsed = time.time() - start_time
                print(f"  ... {checked} checked, {elapsed:.1f}s, {found} found")

        print(f"  Size {size}: {checked} in range, {found} solutions")

    # ===== Phase 4: S_P near 1 (sizes 4-7) =====
    print()
    print("=" * 70)
    print("PHASE 4: S_P near 1 (sizes 4-7)")
    print("=" * 70)

    for size in range(4, 8):
        pool = p_primes[:25] if size <= 6 else p_primes[:20]
        combos = list(combinations(pool, size))
        print(f"\nSize {size}: {len(combos)} total combinations (pool of {len(pool)})")
        checked = 0
        found = 0

        for P in combos:
            S_P = sum(Fraction(1, p) for p in P)
            sp_f = float(S_P)
            if sp_f < 0.8 or sp_f > 1.2:
                continue

            target = Fraction(1) / S_P
            checked += 1
            total_checked += 1
            excluded = set(P)

            used, rem = greedy_decompose(target, excluded, ALL_PRIMES)
            if rem == 0:
                print(f"  *** SOLUTION! P={P}, S_P~{sp_f:.6f}")
                print(f"     Q (first 10): {used[:10]}... (|Q|={len(used)})")
                solutions.append((list(P), used))
                found += 1
                continue

            if float(rem) < 1e-6:
                sol, bt_rem = backtrack_decompose(target, excluded, ALL_PRIMES,
                                                   max_depth=30, branching=5, time_limit=3.0)
                if bt_rem == 0 and sol is not None:
                    print(f"  *** SOLUTION (backtrack)! P={P}")
                    solutions.append((list(P), sol))
                    found += 1
                    continue
                rf = float(bt_rem)
                if rf < 1e-10:
                    near_misses.append((rf, list(P), bt_rem))

        print(f"  Size {size}: {checked} in [0.8,1.2], {found} solutions")

    # ===== FINAL REPORT =====
    elapsed = time.time() - start_time
    print()
    print("=" * 70)
    print(f"FINAL REPORT  (elapsed: {elapsed:.1f}s, {total_checked} subsets checked)")
    print("=" * 70)

    if solutions:
        print(f"\n{'*'*50}")
        print(f"  {len(solutions)} EXACT SOLUTION(S) FOUND!")
        print(f"{'*'*50}\n")
        for i, (P, Q) in enumerate(solutions):
            S_P = sum(Fraction(1, p) for p in P)
            S_Q = sum(Fraction(1, q) for q in Q)
            product = S_P * S_Q
            print(f"Solution {i+1}:")
            print(f"  P = {P}")
            print(f"  |P| = {len(P)}")
            if len(Q) <= 50:
                print(f"  Q = {Q}")
            else:
                print(f"  Q = {Q[:20]} ... {Q[-5:]}")
            print(f"  |Q| = {len(Q)}")
            print(f"  S_P = {frac_str(S_P)}")
            print(f"  S_Q = {frac_str(S_Q)}")
            print(f"  S_P * S_Q = {product}")
            if product == 1:
                print(f"  VERIFIED EXACTLY: S_P * S_Q = 1")
            else:
                print(f"  *** VERIFICATION FAILED ***")
            overlap = set(P) & set(Q)
            if overlap:
                print(f"  NOTE: P and Q share primes: {overlap}")
            else:
                print(f"  P and Q are disjoint.")
            for x in P + Q:
                assert x in PRIME_SET, f"{x} is not prime!"
            print(f"  All elements verified prime.")
            print()
    else:
        print("\nNo exact solution found.")

    if near_misses:
        near_misses.sort()
        print(f"\nTop 10 near-misses (smallest remainder):")
        for i, (rf, P_nm, rem_nm) in enumerate(near_misses[:10]):
            S_P = sum(Fraction(1, p) for p in P_nm)
            print(f"  {i+1}. P={P_nm}, S_P~{float(S_P):.6f}, remainder~{rf:.6e}")

    print(f"\nDone. {elapsed:.1f}s total.")


if __name__ == "__main__":
    main()
