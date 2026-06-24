import Mathlib

def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-
If x ≡ 2 (mod 4), then x is not powerful.
    Proof: 2 | x (since x mod 4 = 2 means x is even) but 4 ∤ x,
    contradicting that powerful requires 2² | x when 2 | x.
-/
lemma not_powerful_of_mod4_eq2 (x : ℕ) (h : x % 4 = 2) : ¬ Powerful x := by
  exact fun H => absurd ( H 2 Nat.prime_two ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 3 (mod 9), then x is not powerful.
    Proof: 3 | x (since x mod 9 = 3 means 3 | x) but 9 ∤ x,
    contradicting that powerful requires 3² | x when 3 | x.
-/
lemma not_powerful_of_mod9_eq3 (x : ℕ) (h : x % 9 = 3) : ¬ Powerful x := by
  exact fun H => absurd ( H 3 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 6 (mod 9), then x is not powerful.
-/
lemma not_powerful_of_mod9_eq6 (x : ℕ) (h : x % 9 = 6) : ¬ Powerful x := by
  exact fun hx => absurd ( hx 3 Nat.prime_three ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
The filter of Fin 36 × Fin 36 matching a specific pair of residues has cardinality 1.
-/
lemma finset_filter_card_eq_one (n d : ℕ) :
    (Finset.univ.filter (fun p : Fin 36 × Fin 36 =>
       p.1.val = n % 36 ∧ p.2.val = d % 36)).card = 1 := by
  rw [ Finset.card_eq_one ] ; use ⟨ ⟨ n % 36, by omega ⟩, ⟨ d % 36, by omega ⟩ ⟩ ; ext x ; aesop;

theorem powerful_3ap_joint_mod36
    (n d : ℕ) (hd : 0 < d)
    (hn : Powerful n) (hn1 : Powerful (n + d)) (hn2 : Powerful (n + 2 * d)) :
    n % 4 ≠ 2 ∧ (n + d) % 4 ≠ 2 ∧ (n + 2 * d) % 4 ≠ 2 ∧
    n % 9 ≠ 3 ∧ n % 9 ≠ 6 ∧
    (n + d) % 9 ≠ 3 ∧ (n + d) % 9 ≠ 6 ∧
    (n + 2 * d) % 9 ≠ 3 ∧ (n + 2 * d) % 9 ≠ 6 ∧
    (Finset.univ.filter (fun p : Fin 36 × Fin 36 =>
       p.1.val = n % 36 ∧ p.2.val = d % 36)).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, finset_filter_card_eq_one n d⟩
  · exact fun h => not_powerful_of_mod4_eq2 n h hn
  · exact fun h => not_powerful_of_mod4_eq2 (n + d) h hn1
  · exact fun h => not_powerful_of_mod4_eq2 (n + 2 * d) h hn2
  · exact fun h => not_powerful_of_mod9_eq3 n h hn
  · exact fun h => not_powerful_of_mod9_eq6 n h hn
  · exact fun h => not_powerful_of_mod9_eq3 (n + d) h hn1
  · exact fun h => not_powerful_of_mod9_eq6 (n + d) h hn1
  · exact fun h => not_powerful_of_mod9_eq3 (n + 2 * d) h hn2
  · exact fun h => not_powerful_of_mod9_eq6 (n + 2 * d) h hn2