# Summary of changes for run f0348891-c5a0-41df-99d5-704fd9b99474
## Summary

This problem (Erdős 1108 bounded-support sub-claim) asks to prove that for every fixed K, the set of powerful numbers expressible as sums of at most K distinct factorials is finite. After thorough mathematical analysis, I confirmed this is **genuinely open** for K ≥ 2, as stated in the problem description.

### What was accomplished

The theorem is cleanly decomposed into two parts in `RequestProject/Main.lean`:

1. **`finite_of_max_bounded` (PROVED)**: If there exists a bound N₀ such that every powerful factorial sum with ≤ K summands has all indices below N₀, then the set of such sums is finite.

2. **`max_element_bounded` (OPEN — 1 sorry)**: For each K, there exists such a bound N₀. This is the core open content of the conjecture. For K ≤ 1, it follows from Bertrand's postulate (proved as helper lemmas). For K ≥ 2, this remains unconditionally open; only abc-conditional results exist in the literature (Luca–Sárközy 1996, Bolvardizadeh–Yavari 2025).

The main theorem `bounded_card_powerful_factorial_sums` is proved as a direct consequence of these two lemmas.

### Fully proved supporting results (no sorry)

- **`exists_prime_single_factor`**: For n ≥ 4, Bertrand's postulate gives a prime q with v_q(n!) = 1 exactly.
- **`factorial_not_powerful`**: n! is not powerful for n ≥ 2 (using the Bertrand prime witness).
- **`powerful_factorial_finite`**: The set of powerful factorials is finite ({1}).
- **`single_low_element_not_powerful`**: Key structural result — if a finset S has minimum n ≥ 4 and all other elements are ≥ 2q (for a Bertrand prime q of n), then ∑ s! is not powerful. This establishes that for powerfulness, elements must "cluster" near each other.

### Why the general case is open

The proof outline suggested a primorial dominance argument: that the product of Bertrand primes in (m/2, m] would exceed the factorial sum ratio, yielding a contradiction. However, this argument has a fundamental gap: the primorial grows as e^{m/2} (by Chebyshev), while the factorial ratio can grow as e^{m·log(2m)}, which is much larger. The single-prime Bertrand argument successfully eliminates "isolated minimum" cases, but handling clustered elements (multiple elements in [min, 2·min)) requires controlling simultaneous congruence conditions across many primes — a problem equivalent to the original open conjecture.

Computational verification confirms no powerful factorial sums exist with max element ≥ 9 for K ≤ 3 (checked up to max element 25), strongly suggesting the conjecture is true.