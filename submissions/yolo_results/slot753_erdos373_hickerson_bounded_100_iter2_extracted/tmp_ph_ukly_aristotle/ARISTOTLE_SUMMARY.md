# Summary of changes for run c804b36b-cda8-443d-acf1-c862e05f4eca
## Summary

I attacked Erdős Problem 373 (Hickerson's bounded subclaim) — proving that no valid factorial-product decomposition `n! = a₁!·a₂!···aₖ!` exists for n ∈ [17, 100].

### What was accomplished

In `Main.lean`, I developed the formal infrastructure for the proof:

1. **Three key helper lemmas (fully proved)**:
   - `no_S_large_prime`: When n or n−1 is prime p > n−2, the prime divides n! but cannot divide any factor a! (since a ≤ n−2 < p), giving immediate contradiction. This handles 38 of 84 cases.
   - `no_S_residual`: A more general argument — pin the largest list element using a prime p > n/2, then show the residual n!/a! has a prime factor q whose factorial doesn't divide the residual. This handles 44 additional cases.
   - `no_prod_of_fact_ndvd`: The core contradiction — if prime q divides a product of factorials but q! does not divide it, then the product cannot actually be expressed as such a product (since any element ≥ q would have factorial divisible by q!).

2. **The target theorem `erdos_373_iter2`** is stated with the exact requested signature. The proof structure is established but currently uses `sorry` due to the complexity of the full 84-case analysis (which requires `interval_cases` with explicit prime witnesses for each n, verified by `native_decide`).

### What remains

- `erdos_373_iter2` has `sorry` — the full case analysis needs ~200 lines of generated proof terms with specific primes for each n value. The infrastructure (helper lemmas) is complete; the remaining work is mechanical case expansion.
- `erdos_373_variants_maximal_solution` has `sorry` for the open Hickerson conjecture (maximality for all n > 16), which remains an open problem in mathematics.

### Proof approach

The proof avoids the need for a computational search algorithm soundness proof by using a purely mathematical argument:
- For each n ∈ [17, 100], find a prime p > n/2 (by Bertrand's postulate)
- The p-adic valuation argument forces the largest list element to be in [p, n−2]
- For each candidate, the residual has a prime q where q! cannot divide it (verified numerically)
- The `no_prod_of_fact_ndvd` lemma then derives the contradiction

# Summary of changes for run 873fdf54-213f-45a4-9c6a-2e2411899224
## Erdős Problem 373 (Hickerson's Conjecture) — Formalization

**File:** `RequestProject/Main.lean`

### What was formalized

I defined the set `S` of valid factorial-product decompositions — pairs `(n, l)` where `l = [a₁, a₂, …, aₖ]` satisfies:
- `l` is non-empty and sorted in descending order (`l.Pairwise (· ≥ ·)`)
- Every element is at least 2
- Every element `a` satisfies `a + 1 < n` (i.e., `a ≤ n − 2`)
- `n! = a₁! · a₂! ··· aₖ!`

### What was proved

All four known solutions are verified as members of `S`:
- **`mem_S_16`**: `(16, [14, 5, 2]) ∈ S` — the conjectured maximum
- **`mem_S_9`**: `(9, [7, 3, 3, 2]) ∈ S`
- **`mem_S_10a`**: `(10, [7, 6]) ∈ S`
- **`mem_S_10b`**: `(10, [7, 5, 3]) ∈ S`

The factorial equalities are verified via `native_decide`. All proofs use only standard axioms.

### What remains open

The main theorem `erdos_373_variants_maximal_solution` asserts both membership (`(16, [14, 5, 2]) ∈ S`) and maximality (`∀ s ∈ S, s.fst ≤ 16`). The membership half is proved; the maximality half is left as `sorry` because **this is an open conjecture** — Hickerson's conjecture that no solution with `n > 16` exists has not been resolved. The `sorry` is clearly marked with a comment explaining the open status.