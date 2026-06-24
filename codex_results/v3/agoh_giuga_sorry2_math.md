`1/3 + 1/5 + 1/7 + 1/11 + 1/13 = 12673/15015 < 1` (not `> 1`).  
So the `m = 5` case is already impossible from the reciprocal-sum inequality, before Carmichael.  
Below is a compiled Lean block (checked with `lake env lean`) that gives:

- `primeFactors_card_ge_five_of_recip_identity` (your requested `m ≤ 4` exclusion),
- `primeFactors_card_ge_six_of_recip_identity` (stronger: also excludes `m = 5`),
- `no_five_prime_carmichael_candidate` (the explicit Carmichael failure for `3*5*7*11*13`).

```lean
import Mathlib

lemma odd_prime_ge_three {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p) : 3 ≤ p := by
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hp_even : Even p := by
      refine ⟨1, ?_⟩
      simp [hp2]
    exact (Nat.not_even_iff_odd).2 hodd hp_even
  have hp_ge_two : 2 ≤ p := hp.two_le
  omega

lemma prime_ge_five_of_gt_three {p : ℕ} (hp : Nat.Prime p) (h : 3 < p) : 5 ≤ p := by
  by_contra h5
  have hp_le4 : p ≤ 4 := by omega
  have hp_ge4 : 4 ≤ p := by omega
  have hp_eq4 : p = 4 := by omega
  exact (by decide : ¬ Nat.Prime 4) (hp_eq4 ▸ hp)

lemma prime_ge_seven_of_gt_five {p : ℕ} (hp : Nat.Prime p) (h : 5 < p) : 7 ≤ p := by
  by_contra h7
  have hp_le6 : p ≤ 6 := by omega
  have hp_ge6 : 6 ≤ p := by omega
  have hp_eq6 : p = 6 := by omega
  exact (by decide : ¬ Nat.Prime 6) (hp_eq6 ▸ hp)

lemma prime_ge_eleven_of_gt_seven {p : ℕ} (hp : Nat.Prime p) (h : 7 < p) : 11 ≤ p := by
  by_contra h11
  have hp_le10 : p ≤ 10 := by omega
  have hp_ge8 : 8 ≤ p := by omega
  have hcases : p = 8 ∨ p = 9 ∨ p = 10 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (by decide : ¬ Nat.Prime 8) hp
  · exact (by decide : ¬ Nat.Prime 9) hp
  · exact (by decide : ¬ Nat.Prime 10) hp

lemma prime_ge_thirteen_of_gt_eleven {p : ℕ} (hp : Nat.Prime p) (h : 11 < p) : 13 ≤ p := by
  by_contra h13
  have hp_le12 : p ≤ 12 := by omega
  have hp_ge12 : 12 ≤ p := by omega
  have hp_eq12 : p = 12 := by omega
  exact (by decide : ¬ Nat.Prime 12) (hp_eq12 ▸ hp)

lemma one_div_nat_le_one_div_nat {a b : ℕ} (ha : 0 < a) (h : a ≤ b) :
    (1 : ℚ) / b ≤ 1 / a := by
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have habq : (a : ℚ) ≤ b := by exact_mod_cast h
  exact one_div_le_one_div_of_le haq habq

lemma sum_recip_three_odd_primes_lt_one
    {p₁ p₂ p₃ : ℕ}
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂) (hp₃ : Nat.Prime p₃)
    (hodd₁ : Odd p₁)
    (h12 : p₁ < p₂) (h23 : p₂ < p₃) :
    ((1 : ℚ) / p₁ + 1 / p₂ + 1 / p₃) < 1 := by
  have hp₁_ge3 : 3 ≤ p₁ := odd_prime_ge_three hp₁ hodd₁
  have hp₂_ge5 : 5 ≤ p₂ := prime_ge_five_of_gt_three hp₂ (by omega)
  have hp₃_ge7 : 7 ≤ p₃ := prime_ge_seven_of_gt_five hp₃ (by omega)
  have h₁ : (1 : ℚ) / p₁ ≤ 1 / 3 := one_div_nat_le_one_div_nat (by decide) hp₁_ge3
  have h₂ : (1 : ℚ) / p₂ ≤ 1 / 5 := one_div_nat_le_one_div_nat (by decide) hp₂_ge5
  have h₃ : (1 : ℚ) / p₃ ≤ 1 / 7 := one_div_nat_le_one_div_nat (by decide) hp₃_ge7
  have hconst : (1 / 3 : ℚ) + 1 / 5 + 1 / 7 < 1 := by norm_num
  nlinarith

lemma sum_recip_four_odd_primes_lt_one
    {p₁ p₂ p₃ p₄ : ℕ}
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂) (hp₃ : Nat.Prime p₃) (hp₄ : Nat.Prime p₄)
    (hodd₁ : Odd p₁)
    (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄) :
    ((1 : ℚ) / p₁ + 1 / p₂ + 1 / p₃ + 1 / p₄) < 1 := by
  have hp₁_ge3 : 3 ≤ p₁ := odd_prime_ge_three hp₁ hodd₁
  have hp₂_ge5 : 5 ≤ p₂ := prime_ge_five_of_gt_three hp₂ (by omega)
  have hp₃_ge7 : 7 ≤ p₃ := prime_ge_seven_of_gt_five hp₃ (by omega)
  have hp₄_ge11 : 11 ≤ p₄ := prime_ge_eleven_of_gt_seven hp₄ (by omega)
  have h₁ : (1 : ℚ) / p₁ ≤ 1 / 3 := one_div_nat_le_one_div_nat (by decide) hp₁_ge3
  have h₂ : (1 : ℚ) / p₂ ≤ 1 / 5 := one_div_nat_le_one_div_nat (by decide) hp₂_ge5
  have h₃ : (1 : ℚ) / p₃ ≤ 1 / 7 := one_div_nat_le_one_div_nat (by decide) hp₃_ge7
  have h₄ : (1 : ℚ) / p₄ ≤ 1 / 11 := one_div_nat_le_one_div_nat (by decide) hp₄_ge11
  have hconst : (1 / 3 : ℚ) + 1 / 5 + 1 / 7 + 1 / 11 < 1 := by norm_num
  nlinarith

lemma sum_recip_five_odd_primes_lt_one
    {p₁ p₂ p₃ p₄ p₅ : ℕ}
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂) (hp₃ : Nat.Prime p₃) (hp₄ : Nat.Prime p₄) (hp₅ : Nat.Prime p₅)
    (hodd₁ : Odd p₁)
    (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄) (h45 : p₄ < p₅) :
    ((1 : ℚ) / p₁ + 1 / p₂ + 1 / p₃ + 1 / p₄ + 1 / p₅) < 1 := by
  have hp₁_ge3 : 3 ≤ p₁ := odd_prime_ge_three hp₁ hodd₁
  have hp₂_ge5 : 5 ≤ p₂ := prime_ge_five_of_gt_three hp₂ (by omega)
  have hp₃_ge7 : 7 ≤ p₃ := prime_ge_seven_of_gt_five hp₃ (by omega)
  have hp₄_ge11 : 11 ≤ p₄ := prime_ge_eleven_of_gt_seven hp₄ (by omega)
  have hp₅_ge13 : 13 ≤ p₅ := prime_ge_thirteen_of_gt_eleven hp₅ (by omega)
  have h₁ : (1 : ℚ) / p₁ ≤ 1 / 3 := one_div_nat_le_one_div_nat (by decide) hp₁_ge3
  have h₂ : (1 : ℚ) / p₂ ≤ 1 / 5 := one_div_nat_le_one_div_nat (by decide) hp₂_ge5
  have h₃ : (1 : ℚ) / p₃ ≤ 1 / 7 := one_div_nat_le_one_div_nat (by decide) hp₃_ge7
  have h₄ : (1 : ℚ) / p₄ ≤ 1 / 11 := one_div_nat_le_one_div_nat (by decide) hp₄_ge11
  have h₅ : (1 : ℚ) / p₅ ≤ 1 / 13 := one_div_nat_le_one_div_nat (by decide) hp₅_ge13
  have hconst : (1 / 3 : ℚ) + 1 / 5 + 1 / 7 + 1 / 11 + 1 / 13 < 1 := by norm_num
  nlinarith

lemma sum_over_finset_eq_sum_fin3 {s : Finset ℕ} (hcard : s.card = 3) :
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 3, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ p ∈ Finset.image (s.orderEmbOfFin hcard) Finset.univ, (1 / p : ℚ) := by
      simp [Finset.image_orderEmbOfFin_univ]
    _ = ∑ i ∈ Finset.univ, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
      simpa using (Finset.sum_image (s := Finset.univ) (g := s.orderEmbOfFin hcard)
        (f := fun p : ℕ => (1 / p : ℚ)) ((s.orderEmbOfFin hcard).injective.injOn))
    _ = ∑ i : Fin 3, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by simp

lemma sum_over_finset_eq_sum_fin4 {s : Finset ℕ} (hcard : s.card = 4) :
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 4, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ p ∈ Finset.image (s.orderEmbOfFin hcard) Finset.univ, (1 / p : ℚ) := by
      simp [Finset.image_orderEmbOfFin_univ]
    _ = ∑ i ∈ Finset.univ, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
      simpa using (Finset.sum_image (s := Finset.univ) (g := s.orderEmbOfFin hcard)
        (f := fun p : ℕ => (1 / p : ℚ)) ((s.orderEmbOfFin hcard).injective.injOn))
    _ = ∑ i : Fin 4, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by simp

lemma sum_over_finset_eq_sum_fin5 {s : Finset ℕ} (hcard : s.card = 5) :
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 5, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ p ∈ Finset.image (s.orderEmbOfFin hcard) Finset.univ, (1 / p : ℚ) := by
      simp [Finset.image_orderEmbOfFin_univ]
    _ = ∑ i ∈ Finset.univ, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
      simpa using (Finset.sum_image (s := Finset.univ) (g := s.orderEmbOfFin hcard)
        (f := fun p : ℕ => (1 / p : ℚ)) ((s.orderEmbOfFin hcard).injective.injOn))
    _ = ∑ i : Fin 5, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by simp

lemma sum_recip_lt_one_of_card_eq_three
    {s : Finset ℕ} (hcard : s.card = 3)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, (1 / p : ℚ)) < 1 := by
  let e : Fin 3 → ℕ := s.orderEmbOfFin hcard
  have he_mono : StrictMono e := (s.orderEmbOfFin hcard).strictMono
  have hp₁ : Nat.Prime (e 0) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 3))
  have hp₂ : Nat.Prime (e 1) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (1 : Fin 3))
  have hp₃ : Nat.Prime (e 2) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (2 : Fin 3))
  have hodd₁ : Odd (e 0) := by simpa [e] using hodd _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 3))
  have h12 : e 0 < e 1 := by
    have h := he_mono (show (0 : Fin 3) < 1 by decide)
    simpa [e] using h
  have h23 : e 1 < e 2 := by
    have h := he_mono (show (1 : Fin 3) < 2 by decide)
    simpa [e] using h
  have hbound : (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ)) < 1 := by
    exact sum_recip_three_odd_primes_lt_one hp₁ hp₂ hp₃ hodd₁ h12 h23
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 3, (1 / (e i) : ℚ) := by
      simpa [e] using sum_over_finset_eq_sum_fin3 (s := s) hcard
    _ = (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ)) := by
      simpa [Fin.sum_univ_three]
    _ < 1 := hbound

lemma sum_recip_lt_one_of_card_eq_four
    {s : Finset ℕ} (hcard : s.card = 4)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, (1 / p : ℚ)) < 1 := by
  let e : Fin 4 → ℕ := s.orderEmbOfFin hcard
  have he_mono : StrictMono e := (s.orderEmbOfFin hcard).strictMono
  have hp₁ : Nat.Prime (e 0) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 4))
  have hp₂ : Nat.Prime (e 1) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (1 : Fin 4))
  have hp₃ : Nat.Prime (e 2) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (2 : Fin 4))
  have hp₄ : Nat.Prime (e 3) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (3 : Fin 4))
  have hodd₁ : Odd (e 0) := by simpa [e] using hodd _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 4))
  have h12 : e 0 < e 1 := by
    have h := he_mono (show (0 : Fin 4) < 1 by decide)
    simpa [e] using h
  have h23 : e 1 < e 2 := by
    have h := he_mono (show (1 : Fin 4) < 2 by decide)
    simpa [e] using h
  have h34 : e 2 < e 3 := by
    have h := he_mono (show (2 : Fin 4) < 3 by decide)
    simpa [e] using h
  have hbound : (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ)) < 1 := by
    exact sum_recip_four_odd_primes_lt_one hp₁ hp₂ hp₃ hp₄ hodd₁ h12 h23 h34
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 4, (1 / (e i) : ℚ) := by
      simpa [e] using sum_over_finset_eq_sum_fin4 (s := s) hcard
    _ = (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ)) := by
      simpa [Fin.sum_univ_four]
    _ < 1 := hbound

lemma sum_recip_lt_one_of_card_eq_five
    {s : Finset ℕ} (hcard : s.card = 5)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, (1 / p : ℚ)) < 1 := by
  let e : Fin 5 → ℕ := s.orderEmbOfFin hcard
  have he_mono : StrictMono e := (s.orderEmbOfFin hcard).strictMono
  have hp₁ : Nat.Prime (e 0) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 5))
  have hp₂ : Nat.Prime (e 1) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (1 : Fin 5))
  have hp₃ : Nat.Prime (e 2) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (2 : Fin 5))
  have hp₄ : Nat.Prime (e 3) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (3 : Fin 5))
  have hp₅ : Nat.Prime (e 4) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (4 : Fin 5))
  have hodd₁ : Odd (e 0) := by simpa [e] using hodd _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 5))
  have h12 : e 0 < e 1 := by
    have h := he_mono (show (0 : Fin 5) < 1 by decide)
    simpa [e] using h
  have h23 : e 1 < e 2 := by
    have h := he_mono (show (1 : Fin 5) < 2 by decide)
    simpa [e] using h
  have h34 : e 2 < e 3 := by
    have h := he_mono (show (2 : Fin 5) < 3 by decide)
    simpa [e] using h
  have h45 : e 3 < e 4 := by
    have h := he_mono (show (3 : Fin 5) < 4 by decide)
    simpa [e] using h
  have hbound : (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ)) < 1 := by
    exact sum_recip_five_odd_primes_lt_one hp₁ hp₂ hp₃ hp₄ hp₅ hodd₁ h12 h23 h34 h45
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 5, (1 / (e i) : ℚ) := by
      simpa [e] using sum_over_finset_eq_sum_fin5 (s := s) hcard
    _ = (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ)) := by
      simpa [Fin.sum_univ_five]
    _ < 1 := hbound

lemma rhs_gt_one_of_k_pos {k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) :
    (1 : ℚ) < k + 1 / n := by
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℚ) < (1 / n : ℚ) := by positivity
  nlinarith

lemma primeFactors_card_ge_five_of_recip_identity
    (n k : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hcard_ge3 : 3 ≤ n.primeFactors.card)
    (hk : 1 ≤ k)
    (hsum : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) = k + 1 / n) :
    5 ≤ n.primeFactors.card := by
  by_contra hlt5
  have hcard_le4 : n.primeFactors.card ≤ 4 := by omega
  have hcard : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 := by omega
  have hprime : ∀ p ∈ n.primeFactors, Nat.Prime p := by
    intro p hp; exact Nat.prime_of_mem_primeFactors hp
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    exact hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hgt : (1 : ℚ) < ∑ p ∈ n.primeFactors, (1 / p : ℚ) := by
    rw [hsum]
    exact rhs_gt_one_of_k_pos hk hn
  rcases hcard with h3 | h4
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 := sum_recip_lt_one_of_card_eq_three h3 hprime hodd_pf
    linarith
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 := sum_recip_lt_one_of_card_eq_four h4 hprime hodd_pf
    linarith

lemma primeFactors_card_ge_six_of_recip_identity
    (n k : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hcard_ge3 : 3 ≤ n.primeFactors.card)
    (hk : 1 ≤ k)
    (hsum : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) = k + 1 / n) :
    6 ≤ n.primeFactors.card := by
  by_contra hlt6
  have hcard_le5 : n.primeFactors.card ≤ 5 := by omega
  have hcard : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨ n.primeFactors.card = 5 := by omega
  have hprime : ∀ p ∈ n.primeFactors, Nat.Prime p := by
    intro p hp; exact Nat.prime_of_mem_primeFactors hp
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    exact hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hgt : (1 : ℚ) < ∑ p ∈ n.primeFactors, (1 / p : ℚ) := by
    rw [hsum]
    exact rhs_gt_one_of_k_pos hk hn
  rcases hcard with h3 | h4 | h5
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 := sum_recip_lt_one_of_card_eq_three h3 hprime hodd_pf
    linarith
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 := sum_recip_lt_one_of_card_eq_four h4 hprime hodd_pf
    linarith
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 := sum_recip_lt_one_of_card_eq_five h5 hprime hodd_pf
    linarith

lemma no_five_prime_carmichael_candidate :
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ (3 * 5 * 7 * 11 * 13 : ℕ) → (p - 1) ∣ ((3 * 5 * 7 * 11 * 13 : ℕ) - 1)) := by
  intro hk
  have h13dvd : 13 ∣ (3 * 5 * 7 * 11 * 13 : ℕ) := by norm_num
  have h12dvd : 12 ∣ ((3 * 5 * 7 * 11 * 13 : ℕ) - 1) := by
    simpa using hk 13 (by decide) h13dvd
  norm_num at h12dvd
```

I could not write this into your repo directly because this session is mounted read-only.