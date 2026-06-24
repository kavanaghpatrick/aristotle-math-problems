import Mathlib

/-!
# Direction B: Index-2 Covering Impossibility

We prove that the 11 primes below 300 where `⟨2,3⟩` has index 2 in `(ℤ/pℤ)*`
cannot form a covering system for the 2D Erdős-203 problem.

## Main Result

`index2_covering_insufficient`: For any `m : ℕ`, there exist `k, l < 10` such that
none of the 11 index-2 primes divides `2^k * 3^l * m + 1`.

## Proof Strategy

1. **Per-prime coverage bounds** (verified by `native_decide`): For each prime `p ∈ S₁₁`
   and any residue class `r mod p`, the number of pairs `(k,l) ∈ [0,10)²` with
   `p ∣ 2^k·3^l·r+1` is bounded by `c_p` (see table below).

2. **Mod reduction**: The divisibility `p ∣ 2^k·3^l·m+1` depends only on `m mod p`.

3. **Union bound**: The total coverage is at most `∑ c_p = 39 < 100 = |[0,10)²|`.

4. **Conclusion**: The complement is nonempty; some `(k,l)` escapes all 11 primes.

The 11 primes are exactly those `p ≡ ±1 (mod 24)` below 300 (both 2 and 3 are QR mod p):
  `S₁₁ = {23, 47, 71, 73, 97, 167, 191, 193, 239, 241, 263}`

| p   | |⟨2,3⟩| = (p-1)/2 | max coverage c_p |
|-----|---------------------|------------------|
| 23  | 11                  | 10               |
| 47  | 23                  | 6                |
| 71  | 35                  | 4                |
| 73  | 36                  | 4                |
| 97  | 48                  | 3                |
| 167 | 83                  | 2                |
| 191 | 95                  | 2                |
| 193 | 96                  | 2                |
| 239 | 119                 | 2                |
| 241 | 120                 | 2                |
| 263 | 131                 | 2                |
| **Total** |               | **39 < 100**     |
-/

set_option maxHeartbeats 800000

/-! ### Step 1: Mod Reduction -/

/-- Divisibility by `p` of `a * m + 1` depends only on `m mod p`. -/
lemma dvd_mul_add_one_mod (p a m : ℕ) :
    p ∣ a * m + 1 ↔ p ∣ a * (m % p) + 1 := by
  have key : (a * m + 1) % p = (a * (m % p) + 1) % p := by
    have h1 : a * m % p = a * (m % p) % p := by
      rw [Nat.mul_mod a m p, Nat.mul_mod a (m % p) p, Nat.mod_mod]
    rw [Nat.add_mod, h1, ← Nat.add_mod]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, key]

/-! ### Step 2: Per-prime coverage bounds (verified by native_decide) -/

/-- Coverage count for prime `p` and residue class `r` in the 10×10 box. -/
def boxCoverage (p : Nat) (r : Fin p) : Nat :=
  ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
    (fun kl => p ∣ 2 ^ kl.1.val * 3 ^ kl.2.val * r.val + 1)).card

lemma coverage_23 : ∀ r : Fin 23, boxCoverage 23 r ≤ 10 := by native_decide
lemma coverage_47 : ∀ r : Fin 47, boxCoverage 47 r ≤ 6 := by native_decide
lemma coverage_71 : ∀ r : Fin 71, boxCoverage 71 r ≤ 4 := by native_decide
lemma coverage_73 : ∀ r : Fin 73, boxCoverage 73 r ≤ 4 := by native_decide
lemma coverage_97 : ∀ r : Fin 97, boxCoverage 97 r ≤ 3 := by native_decide
lemma coverage_167 : ∀ r : Fin 167, boxCoverage 167 r ≤ 2 := by native_decide
lemma coverage_191 : ∀ r : Fin 191, boxCoverage 191 r ≤ 2 := by native_decide
lemma coverage_193 : ∀ r : Fin 193, boxCoverage 193 r ≤ 2 := by native_decide
lemma coverage_239 : ∀ r : Fin 239, boxCoverage 239 r ≤ 2 := by native_decide
lemma coverage_241 : ∀ r : Fin 241, boxCoverage 241 r ≤ 2 := by native_decide
lemma coverage_263 : ∀ r : Fin 263, boxCoverage 263 r ≤ 2 := by native_decide

/-! ### Step 3: Lift per-residue bounds to bounds for all m -/

/-- For each prime p, the covered set for m has same cardinality as for m % p. -/
lemma coverage_for_m (p : Nat) (_hp : p > 0) (m : ℕ) :
    ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
      (fun kl => p ∣ 2 ^ kl.1.val * 3 ^ kl.2.val * m + 1)) =
    ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
      (fun kl => p ∣ 2 ^ kl.1.val * 3 ^ kl.2.val * (m % p) + 1)) := by
  congr 1
  ext ⟨k, l⟩
  exact dvd_mul_add_one_mod p (2 ^ k.val * 3 ^ l.val) m

/-- Coverage bound for prime p and any m. -/
lemma coverage_bound_for_m (p : Nat) (hp : p > 0) (bound : Nat)
    (hbound : ∀ r : Fin p, boxCoverage p r ≤ bound) (m : ℕ) :
    ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
      (fun kl => p ∣ 2 ^ kl.1.val * 3 ^ kl.2.val * m + 1)).card ≤ bound := by
  rw [coverage_for_m p hp m]
  exact hbound ⟨m % p, Nat.mod_lt m hp⟩

/-! ### Step 4: Union bound and main theorem -/

/-- Abbreviation for the coverage set of a single prime. -/
abbrev covSet (p m : ℕ) : Finset (Fin 10 × Fin 10) :=
  (Finset.univ : Finset (Fin 10 × Fin 10)).filter
    (fun kl => p ∣ 2 ^ kl.1.val * 3 ^ kl.2.val * m + 1)

/-
The total coverage by all 11 primes is at most 39 for any m.
-/
theorem total_coverage_le (m : ℕ) :
    (covSet 23 m ∪ covSet 47 m ∪ covSet 71 m ∪ covSet 73 m ∪ covSet 97 m ∪
     covSet 167 m ∪ covSet 191 m ∪ covSet 193 m ∪ covSet 239 m ∪
     covSet 241 m ∪ covSet 263 m).card ≤ 39 := by
  -- Show that the set of k, l pairs covered by at most 11 primes is bounded by the sum of the bounds for each prime.
  have set_bound (p : ℕ) (hp : p ∈ [23, 47, 71, 73, 97, 167, 191, 193, 239, 241, 263]) :
    (covSet p m).card ≤ if p = 23 then 10 else if p = 47 then 6 else if p = 71 then 4 else if p = 73 then 4 else if p = 97 then 3 else 2 := by
      convert coverage_bound_for_m p ( by fin_cases hp <;> decide ) _ _ m using 1;
      fin_cases hp <;> [ exact coverage_23; exact coverage_47; exact coverage_71; exact coverage_73; exact coverage_97; exact coverage_167; exact coverage_191; exact coverage_193; exact coverage_239; exact coverage_241; exact coverage_263 ];
  -- Applying the bound on each prime to the union of all primes.
  have union_bound : (Finset.biUnion ({23, 47, 71, 73, 97, 167, 191, 193, 239, 241, 263} : Finset ℕ) (fun p => covSet p m)).card ≤ ∑ p ∈ ({23, 47, 71, 73, 97, 167, 191, 193, 239, 241, 263} : Finset ℕ), (covSet p m).card := by
    exact Finset.card_biUnion_le;
  convert union_bound.trans ( Finset.sum_le_sum fun p hp => set_bound p <| by aesop ) using 1 ; simp +decide

/-
**Main theorem**: The 11 index-2 primes below 300 cannot cover the 2D lattice.
    For any m, there exist k,l < 10 such that no prime in S₁₁ divides 2^k·3^l·m+1.
-/
theorem index2_covering_insufficient (m : ℕ) :
    ∃ k l : ℕ, k < 10 ∧ l < 10 ∧
      ¬ (23 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (47 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (71 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (73 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (97 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (167 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (191 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (193 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (239 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (241 ∣ 2^k * 3^l * m + 1) ∧
      ¬ (263 ∣ 2^k * 3^l * m + 1) := by
  -- By total_coverage_le, the union of all 11 covSets has cardinality at most 39.
  have h_union_card : (Finset.univ.filter (fun kl : Fin 10 × Fin 10 => ∃ p ∈ ({23, 47, 71, 73, 97, 167, 191, 193, 239, 241, 263} : Finset ℕ), p ∣ 2 ^ kl.1.val * 3 ^ kl.2.val * m + 1)).card ≤ 39 := by
    convert total_coverage_le m using 2 ; aesop;
  -- Since the union of all 11 covSets has cardinality at most 39, there must exist some element (k, l) in the complement.
  obtain ⟨kl, hkl⟩ : ∃ kl : Fin 10 × Fin 10, kl ∉ Finset.univ.filter (fun kl : Fin 10 × Fin 10 => ∃ p ∈ ({23, 47, 71, 73, 97, 167, 191, 193, 239, 241, 263} : Finset ℕ), p ∣ 2 ^ kl.1.val * 3 ^ kl.2.val * m + 1) := by
    contrapose! h_union_card; simp_all +decide ;
  exact ⟨ kl.1, kl.2, Fin.is_lt kl.1, Fin.is_lt kl.2, by aesop ⟩

/-! ### Verification of subgroup orders -/

/-- The subgroup ⟨2,3⟩ in (ℤ/pℤ)* for a prime p. -/
def subgroupOrder (p : Nat) : Nat :=
  ((Finset.univ : Finset (Fin (p - 1) × Fin (p - 1))).image
    (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card

/-- All 11 primes have index exactly 2 (subgroup order = (p-1)/2). -/
example : subgroupOrder 23  = 11  := by native_decide
example : subgroupOrder 47  = 23  := by native_decide
example : subgroupOrder 71  = 35  := by native_decide
example : subgroupOrder 73  = 36  := by native_decide
example : subgroupOrder 97  = 48  := by native_decide
example : subgroupOrder 167 = 83  := by native_decide
example : subgroupOrder 191 = 95  := by native_decide
example : subgroupOrder 193 = 96  := by native_decide
example : subgroupOrder 239 = 119 := by native_decide
example : subgroupOrder 241 = 120 := by native_decide
example : subgroupOrder 263 = 131 := by native_decide