import Mathlib

set_option maxHeartbeats 800000

open scoped Real

/-! # Erdős Problem 938 — Unconditional Upper Bound

We define *powerful numbers* and prove that if three consecutive powerful numbers
form an arithmetic progression with common difference `d`, then
`d < 2 * √n₀ + 2` where `n₀` is the smallest of the three.
-/

namespace Nat

/-- A natural number `n` is *powerful* if `n > 0` and every prime factor of `n`
appears with exponent at least 2. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-
Every positive perfect square is powerful.
-/
theorem powerful_sq {m : ℕ} (hm : 0 < m) : Powerful (m ^ 2) := by
  exact ⟨ pow_pos hm 2, fun p hp hpn => dvd_trans ( pow_dvd_pow_of_dvd ( hp.dvd_of_dvd_pow hpn ) 2 ) ( pow_dvd_pow _ le_rfl ) ⟩

/-
The set of powerful numbers is infinite.
-/
theorem powerful_infinite : (setOf Powerful).Infinite := by
  exact Set.infinite_of_forall_exists_gt fun n => ⟨ ( n + 1 ) ^ 2, by simpa using powerful_sq ( Nat.succ_pos _ ), by nlinarith ⟩

/-
There is no powerful number strictly between two consecutively enumerated
powerful numbers.
-/
theorem no_powerful_between_consecutive [DecidablePred Powerful]
    (k m : ℕ) (hm : Powerful m)
    (h1 : nth Powerful k < m) (h2 : m < nth Powerful (k + 1)) : False := by
      -- Since $m$ is powerful and $nth Powerful k < m$, it follows that $count Powerful m > k$.
      have h_count : (count Powerful m) > k := by
        contrapose! h1; have := Nat.nth_monotone ( show { n : ℕ | n.Powerful }.Infinite from powerful_infinite ) h1; aesop;
      contrapose! h2; have := Nat.nth_monotone ( show { n : ℕ | n.Powerful }.Infinite from powerful_infinite ) h_count; aesop;

/-
An interval of length greater than `2 * Nat.sqrt a + 1` starting at `a`
contains a positive perfect square.
-/
theorem interval_contains_square (a L : ℕ) (hL : 2 * Nat.sqrt a + 1 < L) :
    ∃ m : ℕ, 0 < m ∧ a < m ^ 2 ∧ m ^ 2 < a + L := by
      exact ⟨ Nat.sqrt a + 1, Nat.succ_pos _, by linarith [ Nat.lt_succ_sqrt a ], by linarith [ Nat.sqrt_le a ] ⟩

end Nat

/-
**Erdős 938 — Unconditional upper bound.**
If `n_k, n_{k+1}, n_{k+2}` are three consecutively enumerated powerful numbers
forming an arithmetic progression, then the common difference satisfies
`d < 2 √n_k + 2`.
-/
theorem erdos_938_unconditional_upper_bound (k : ℕ) :
    let n0 := Nat.nth Nat.Powerful k
    let n1 := Nat.nth Nat.Powerful (k + 1)
    let n2 := Nat.nth Nat.Powerful (k + 2)
    n1 - n0 = n2 - n1 →
    ((n1 - n0 : ℝ) < 2 * Real.sqrt n0 + 2) := by
      intro n0 n1 n2 h_eq
      by_cases h_s : (Nat.sqrt n0 + 1)^2 < n2;
      · -- By trichotomy with both gaps, either n₀ < s < n₁ or n₁ < s < n₂.
        by_cases h_case : n0 < (Nat.sqrt n0 + 1)^2 ∧ (Nat.sqrt n0 + 1)^2 < n1;
        · contrapose! h_case;
          intro h;
          refine' Nat.le_of_not_lt fun h' => _;
          convert Nat.no_powerful_between_consecutive k ( ( Nat.sqrt n0 + 1 ) ^ 2 ) _ _ _ using 1;
          · exact Classical.decPred _;
          · exact Nat.powerful_sq ( Nat.succ_pos _ );
          · grobner;
          · linarith;
        · -- By trichotomy with both gaps, either n₁ < s < n₂ or s = n₁.
          by_cases h_case2 : n1 < (Nat.sqrt n0 + 1)^2 ∧ (Nat.sqrt n0 + 1)^2 < n2;
          · rw [ ← @Nat.cast_lt ℝ ] at * ; norm_num at *;
            nlinarith only [ Real.sqrt_nonneg n0, Real.sq_sqrt <| Nat.cast_nonneg n0, show ( n0.sqrt :ℝ ) ^ 2 ≤ n0 from mod_cast Nat.sqrt_le' n0, h_case, h_case2 ];
          · -- Since these are the only cases, we must have $s = n1$.
            have h_s_eq_n1 : (Nat.sqrt n0 + 1)^2 = n1 := by
              have h_s_eq_n1 : n0 < (Nat.sqrt n0 + 1)^2 ∧ (Nat.sqrt n0 + 1)^2 < n2 := by
                exact ⟨ Nat.lt_succ_sqrt' _, h_s ⟩;
              grind;
            nlinarith only [ Real.sqrt_nonneg n0, Real.sq_sqrt <| Nat.cast_nonneg n0, show ( n0 :ℝ ) ≥ ( Nat.sqrt n0 :ℝ ) ^ 2 by exact_mod_cast Nat.sqrt_le' n0, show ( n1 :ℝ ) = ( Nat.sqrt n0 + 1 ) ^ 2 by exact_mod_cast h_s_eq_n1.symm ];
      · -- Since `n2 ≤ s`, we have `2 * d = n2 - n0 ≤ s - n0`. Expanding this:
        have h2d_le : 2 * (n1 - n0) ≤ (Nat.sqrt n0 + 1)^2 - n0 := by
          omega;
        generalize_proofs at *; (
        rw [ Nat.le_sub_iff_add_le ] at h2d_le;
        · rw [ ← Nat.cast_sub ( show n0 ≤ n1 from Nat.nth_monotone ( Nat.powerful_infinite ) ( Nat.le_succ _ ) ) ] at * ; norm_num at * ; nlinarith only [ Real.sqrt_nonneg n0, Real.sq_sqrt <| Nat.cast_nonneg n0, ( by norm_cast : ( 2 :ℝ ) * ( n1 - n0 :ℕ ) + n0 ≤ ( n0.sqrt + 1 ) ^ 2 ), ( show ( n0.sqrt :ℝ ) ^ 2 ≤ n0 by norm_cast; linarith [ Nat.sqrt_le n0 ] ) ] ;
        · linarith [ Nat.lt_succ_sqrt n0 ])