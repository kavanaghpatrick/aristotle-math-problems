import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Erdős Problem 203 — Index-1 primes and the 8×8 box

The original conjecture claimed that for every `m ≥ 0`, there exists a pair `(k,l) ∈ [0,8)²`
escaping every index-1 prime `p ≤ 500`. We show this is **false** by exhibiting a specific
counterexample `m₀` such that every cell `(k,l)` in `[0,8)²` is caught by at least one
index-1 prime `p ≤ 500`.

The counterexample was found via a greedy set-cover over the partition structures of
the 25 multi-cell index-1 primes, combined with the Chinese Remainder Theorem to
realize the covering as a single value of `m`.
-/

/-- The counterexample value of `m` for which every cell in [0,8)² is covered. -/
def counterexample_m : ℕ := 1579554969991861182625270235031094424159694

/- The original theorem is FALSE. The following is the statement as given by the user: -/
/- It fails for `m = counterexample_m`. See `index1_covering_counterexample` below.

theorem index1_covering_insufficient_M8_B500 (m : ℕ) :
    ∃ k l : ℕ, k < 8 ∧ l < 8 ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ≤ 500 →
        (((Finset.univ : Finset (Fin (p-1) × Fin (p-1))).image
          (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card = p - 1) →
        ¬ p ∣ 2 ^ k * 3 ^ l * m + 1 := by sorry
-/

/--
The original conjecture `index1_covering_insufficient_M8_B500` is **false**.

For `m = 1579554969991861182625270235031094424159694`, every cell `(k, l) ∈ [0,8)²` is
caught by at least one index-1 prime `p ≤ 500` (i.e., a prime for which
`⟨2, 3⟩ = (ℤ/pℤ)*`), meaning `p ∣ 2^k * 3^l * m + 1`.

The counterexample was constructed by:
1. Computing the partition of [0,8)² induced by each index-1 prime `p ≤ 500`
   (cells are equivalent mod `p` iff `2^k₁·3^l₁ ≡ 2^k₂·3^l₂ (mod p)`).
2. Running a greedy set-cover over these partitions (25 multi-cell primes suffice).
3. Using the Chinese Remainder Theorem to find `m` realizing the covering.
-/
theorem index1_covering_counterexample :
    ∃ _ : ℕ, ∀ k : Fin 8, ∀ l : Fin 8,
      ∃ p ∈ Finset.range 501, p.Prime ∧ 3 < p ∧
        (((Finset.univ : Finset (Fin (p-1) × Fin (p-1))).image
          (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card = p - 1) ∧
        p ∣ 2 ^ k.val * 3 ^ l.val * counterexample_m + 1 :=
  ⟨counterexample_m, by native_decide⟩
