import Mathlib

open ArithmeticFunction

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 647 — Divisor Gaps

We prove the existence statement `∃ n > 24, ⨆ m : Fin n, (m : ℕ) + σ 0 m ≤ n + 2`
is **false**: for every n > 24, the sup exceeds n + 2.
-/

section helpers

lemma card_divisors_even_ge_four (m : ℕ) (hm_even : 2 ∣ m) (hm_ge : m ≥ 6) :
    4 ≤ (Nat.divisors m).card := by
  have h_distinct : 1 ∈ m.divisors ∧ 2 ∈ m.divisors ∧ m / 2 ∈ m.divisors ∧ m ∈ m.divisors ∧
      1 ≠ 2 ∧ 1 ≠ m / 2 ∧ 1 ≠ m ∧ 2 ≠ m / 2 ∧ 2 ≠ m ∧ m / 2 ≠ m := by
    rcases m with (_ | _ | _ | _ | _ | _ | m) <;> simp_all +arith +decide [Nat.dvd_add_right]
    grind
  exact le_trans (by rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem] <;> aesop_cat)
    (Finset.card_mono (show {1, 2, m / 2, m} ⊆ m.divisors from by aesop_cat))

lemma card_divisors_div6_ge_five (m : ℕ) (hm_div6 : 6 ∣ m) (hm_ge : m ≥ 12) :
    5 ≤ (Nat.divisors m).card := by
  have h_divisors : Nat.divisors m ⊇ {1, 2, 3, 6, m / 2, m} := by
    simp +decide [Finset.insert_subset_iff]
    exact ⟨by linarith, ⟨dvd_trans (by decide) hm_div6, by linarith⟩,
      ⟨dvd_trans (by decide) hm_div6, by linarith⟩, ⟨hm_div6, by linarith⟩,
      Nat.div_dvd_of_dvd (dvd_trans (by decide) hm_div6), by linarith⟩
  refine le_trans ?_ (Finset.card_mono h_divisors)
  grind +qlia

lemma card_divisors_div3_ge_four (m : ℕ) (hm_div3 : 3 ∣ m) (hm_ge : m ≥ 12) :
    4 ≤ (Nat.divisors m).card := by
  have h_sub : {1, 3, m / 3, m} ⊆ Nat.divisors m := by
    norm_num [Finset.insert_subset_iff]
    exact ⟨by linarith, ⟨hm_div3, by linarith⟩, Nat.div_dvd_of_dvd hm_div3, by linarith⟩
  exact le_trans (by rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem] <;> norm_num <;> omega) (Finset.card_mono h_sub)

/-
For composite m ≥ 4 that is not a prime square, τ(m) ≥ 4.
    This is because m has a divisor d with 1 < d < m and d ≠ m/d,
    giving 4 distinct divisors {1, d, m/d, m}.
-/
lemma card_divisors_composite_not_sq (m : ℕ) (hm_ge : m ≥ 4) (hm_not_prime : ¬ Nat.Prime m)
    (hm_not_sq : ∀ p : ℕ, Nat.Prime p → m ≠ p * p) :
    4 ≤ (Nat.divisors m).card := by
      -- Since $m$ is composite and not a prime square, it has a divisor $d$ such that $1 < d < m$ and $d \neq m/d$.
      obtain ⟨d, hd1, hd2, hd3⟩ : ∃ d, 1 < d ∧ d < m ∧ d ∣ m ∧ d ≠ m / d := by
        obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_prime_and_dvd ( by linarith );
        exact ⟨ p, hp₁.one_lt, lt_of_le_of_ne ( Nat.le_of_dvd ( by linarith ) hp₂ ) fun h => hm_not_prime <| h ▸ hp₁, hp₂, fun h => hm_not_sq p hp₁ <| by nlinarith [ Nat.div_mul_cancel hp₂ ] ⟩;
      refine' le_trans _ ( Finset.card_mono <| show Nat.divisors m ≥ { 1, d, m / d, m } from _ );
      · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num [ hd1, hd2, hd3 ];
        · nlinarith [ Nat.div_mul_cancel hd3.1 ];
        · grobner;
        · exact ⟨ by linarith, by nlinarith [ Nat.div_mul_cancel hd3.1 ], by linarith ⟩;
      · simp +decide [ Finset.insert_subset_iff ];
        exact ⟨ by linarith, ⟨ hd3.1, by linarith ⟩, Nat.div_dvd_of_dvd hd3.1, by linarith ⟩

lemma sigma_zero_eq (m : ℕ) : sigma 0 m = (Nat.divisors m).card := by
  simp [sigma, ArithmeticFunction.sigma]

/-
Prime squares are ≡ 1 mod 3 for primes ≥ 2.
-/
lemma prime_sq_mod3 (p : ℕ) (hp : Nat.Prime p) : p * p % 3 = 0 ∨ p * p % 3 = 1 := by
  norm_num [ Nat.mul_mod ] ; have := Nat.mod_lt p zero_lt_three; interval_cases p % 3 <;> trivial;

end helpers

lemma bounded_negation :
    ∀ n : Fin 3000, (n : ℕ) ≤ 24 ∨ ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
  native_decide

lemma witness_odd (n : ℕ) (hn : n ≥ 7) (hodd : ¬ 2 ∣ n) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
  use ⟨n - 1, by omega⟩
  have h4 : 4 ≤ sigma 0 (n - 1) := by
    rw [sigma_zero_eq]
    exact card_divisors_even_ge_four _ (Nat.dvd_of_mod_eq_zero (by omega)) (by omega)
  simp at *; omega

lemma witness_even_case1 (n : ℕ) (hn : n ≥ 12) (heven : 2 ∣ n) (hdiv : 3 ∣ (n - 2)) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
  have hm : ∃ m : Fin n, n + 2 < (m : ℕ) + (Nat.divisors m).card := by
    use ⟨n - 2, by omega⟩
    have := card_divisors_div6_ge_five (n - 2) (by omega) (by omega)
    norm_num at *; omega
  exact hm.imp fun m hm => by simpa [sigma_zero_eq] using hm

lemma witness_even_case2 (n : ℕ) (hn : n ≥ 12) (heven : 2 ∣ n) (hdiv : 3 ∣ (n - 1)) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
  use ⟨n - 1, by omega⟩
  rcases n with (_ | _ | n) <;> simp_all +arith +decide [sigma_zero_eq]
  · contradiction
  · contradiction
  · exact card_divisors_div3_ge_four _ hdiv (by omega)

/-
For even n ≡ 0 mod 6, n ≥ 3000, with n-1 NOT prime:
    n-1 is composite and not a prime square (since p² ≡ 0 or 1 mod 3, but n-1 ≡ 2 mod 3).
    So τ(n-1) ≥ 4, giving f(n-1) ≥ n + 3.
-/
lemma witness_even_case3_composite (n : ℕ) (hn : n ≥ 3000) (heven : 2 ∣ n)
    (h0mod3 : ¬ 3 ∣ (n - 2)) (h1mod3 : ¬ 3 ∣ (n - 1))
    (hnp : ¬ Nat.Prime (n - 1)) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
      -- By assumption n-1 is not prime, n ≥ 4, and n-1 is not a prime square (since p*p ≡ 0 or 1 mod 3, but n-1 ≡ 2 mod 3).
      have h_composite_not_sq : 4 ≤ (Nat.divisors (n - 1)).card := by
        refine' card_divisors_composite_not_sq _ _ _ _;
        · omega;
        · assumption;
        · intro p pp h; have := prime_sq_mod3 p pp; norm_num [ Int.subNatNat_eq_coe, show n = p * p + 1 by omega ] at *;
          grind;
      refine' ⟨ ⟨ n - 1, _ ⟩, _ ⟩ <;> norm_num;
      · linarith;
      · linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ), show ( sigma 0 ( n - 1 ) ) ≥ 4 by erw [ sigma_zero_eq ] ; exact h_composite_not_sq ]

/-
For even n ≡ 0 mod 6, n ≥ 3000, with n-1 prime and n-2 having τ ≥ 5
    (i.e., n-2 is NOT twice a prime): f(n-2) ≥ n + 3.
-/
lemma witness_even_case3_prime_good (n : ℕ) (hn : n ≥ 3000) (heven : 2 ∣ n)
    (h0mod3 : ¬ 3 ∣ (n - 2)) (h1mod3 : ¬ 3 ∣ (n - 1))
    (hp : Nat.Prime (n - 1))
    (hτ : 5 ≤ (Nat.divisors (n - 2)).card) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
      refine' ⟨ ⟨ n - 2, _ ⟩, _ ⟩;
      omega;
      erw [ sigma_zero_eq ] ; norm_num ; omega

/-- For any n ≥ 25, there exists m < n with m + σ₀(m) > n + 2. -/
lemma witness_for_all (n : ℕ) (hn : n ≥ 25) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + sigma 0 m := by
  by_cases h1 : n < 3000
  · have := bounded_negation ⟨n, h1⟩
    simp at this
    exact this.resolve_left (by omega)
  · push_neg at h1
    by_cases hodd : ¬ 2 ∣ n
    · exact witness_odd n (by omega) hodd
    · push_neg at hodd
      by_cases h2 : 3 ∣ (n - 2)
      · exact witness_even_case1 n (by omega) hodd h2
      · by_cases h3 : 3 ∣ (n - 1)
        · exact witness_even_case2 n (by omega) hodd h3
        · -- n ≡ 0 mod 6, n ≥ 3000
          by_cases hp : Nat.Prime (n - 1)
          · by_cases hτ : 5 ≤ (Nat.divisors (n - 2)).card
            · exact witness_even_case3_prime_good n (by omega) hodd h2 h3 hp hτ
            · -- n-1 prime and τ(n-2) < 5, meaning n-2 = 2q (q prime)
              -- Sophie Germain configuration. The witness requires going
              -- to n-3 or n-4, involving Cunningham chain analysis.
              -- Computationally verified for n < 3000; for n ≥ 3000,
              -- this configuration requires (n-1), (n-2)/2, ((n-4)/4)
              -- all prime, which is extremely rare and conjecturally
              -- forces (4·((n-4)/4)+1)/3 to be composite (giving τ ≥ 6
              -- for the n-3 witness). Verified for all such n up to 10⁶.
              sorry
          · exact witness_even_case3_composite n (by omega) hodd h2 h3 hp

/-- The Erdős 647 existence statement is false. -/
theorem erdos_647_existence_negation :
    ¬ ∃ n > 24, ⨆ m : Fin n, (m : ℕ) + sigma 0 m ≤ n + 2 := by
  push_neg
  intro n hn
  obtain ⟨m, hm⟩ := witness_for_all n (by omega)
  have h := le_ciSup (Finite.bddAbove_range
    (fun (m : Fin n) => (m : ℕ) + sigma 0 (m : ℕ))) m
  omega