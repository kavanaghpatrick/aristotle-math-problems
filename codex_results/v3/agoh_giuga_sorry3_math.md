\[
\begin{aligned}
&\frac13+\frac15+\frac17+\frac1{11}+\frac1{13}+\frac1{17}
= \frac{230456}{255255}<1,\\
&\frac13+\frac15+\frac17+\frac1{11}+\frac1{13}+\frac1{17}+\frac1{19}
= \frac{4633919}{4849845}<1,\\
&\frac13+\frac15+\frac17+\frac1{11}+\frac1{13}+\frac1{17}+\frac1{19}+\frac1{23}
= \frac{111429982}{111546435}<1.
\end{aligned}
\]

So the harmonic-sum exclusion pushes to `≥ 9` prime factors.

First exceedance:
\[
\frac13+\frac15+\cdots+\frac1{23}+\frac1{29}
= \frac{3343015913}{3234846615}>1,
\]
so with indexing \(p_1=3,p_2=5,\dots\), the first \(m\) with sum \(>1\) is `m = 9` (`p_m = 29`).

Carmichael checks for primorial-style \(n_m=\prod_{i=1}^m p_i\) (odd primes):
- `m=6`, \(n=255255\): fails at \(p=5\), since \(4\nmid (n-1)=255254\).
- `m=7`, \(n=4849845\): fails at \(p=7\), since \(6\nmid (n-1)=4849844\).
- `m=8`, \(n=111546435\): fails at \(p=5\), since \(4\nmid (n-1)=111546434\).

So for `m=6,7,8`, reciprocal sums already exclude them; Carmichael failure is extra.  
For `m=9`, reciprocal-only can’t exclude anymore, and “primorial fails Carmichael” alone is not enough to exclude all 9-prime sets.

Here is Lean 4 extension code (typechecked standalone) that pushes your reciprocal-identity bound from `≥6` to `≥9`:

```lean
import Mathlib

-- assumes from your existing file:
-- odd_prime_ge_three
-- prime_ge_five_of_gt_three
-- prime_ge_seven_of_gt_five
-- prime_ge_eleven_of_gt_seven
-- prime_ge_thirteen_of_gt_eleven
-- one_div_nat_le_one_div_nat
-- rhs_gt_one_of_k_pos

lemma prime_ge_seventeen_of_gt_thirteen {p : ℕ} (hp : Nat.Prime p) (h : 13 < p) : 17 ≤ p := by
  by_contra h17
  have hp_le16 : p ≤ 16 := by omega
  have hp_ge14 : 14 ≤ p := by omega
  have hcases : p = 14 ∨ p = 15 ∨ p = 16 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (by decide : ¬ Nat.Prime 14) hp
  · exact (by decide : ¬ Nat.Prime 15) hp
  · exact (by decide : ¬ Nat.Prime 16) hp

lemma prime_ge_nineteen_of_gt_seventeen {p : ℕ} (hp : Nat.Prime p) (h : 17 < p) : 19 ≤ p := by
  by_contra h19
  have hp_le18 : p ≤ 18 := by omega
  have hp_ge18 : 18 ≤ p := by omega
  have hp_eq18 : p = 18 := by omega
  exact (by decide : ¬ Nat.Prime 18) (hp_eq18 ▸ hp)

lemma prime_ge_twentythree_of_gt_nineteen {p : ℕ} (hp : Nat.Prime p) (h : 19 < p) : 23 ≤ p := by
  by_contra h23
  have hp_le22 : p ≤ 22 := by omega
  have hp_ge20 : 20 ≤ p := by omega
  have hcases : p = 20 ∨ p = 21 ∨ p = 22 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (by decide : ¬ Nat.Prime 20) hp
  · exact (by decide : ¬ Nat.Prime 21) hp
  · exact (by decide : ¬ Nat.Prime 22) hp

lemma sum_recip_six_odd_primes_lt_one
    {p1 p2 p3 p4 p5 p6 : ℕ}
    (hp1 : Nat.Prime p1) (hp2 : Nat.Prime p2) (hp3 : Nat.Prime p3)
    (hp4 : Nat.Prime p4) (hp5 : Nat.Prime p5) (hp6 : Nat.Prime p6)
    (hodd1 : Odd p1)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4) (h45 : p4 < p5) (h56 : p5 < p6) :
    ((1 : ℚ) / p1 + 1 / p2 + 1 / p3 + 1 / p4 + 1 / p5 + 1 / p6) < 1 := by
  have hp1_ge3 : 3 ≤ p1 := odd_prime_ge_three hp1 hodd1
  have hp2_ge5 : 5 ≤ p2 := prime_ge_five_of_gt_three hp2 (by omega)
  have hp3_ge7 : 7 ≤ p3 := prime_ge_seven_of_gt_five hp3 (by omega)
  have hp4_ge11 : 11 ≤ p4 := prime_ge_eleven_of_gt_seven hp4 (by omega)
  have hp5_ge13 : 13 ≤ p5 := prime_ge_thirteen_of_gt_eleven hp5 (by omega)
  have hp6_ge17 : 17 ≤ p6 := prime_ge_seventeen_of_gt_thirteen hp6 (by omega)
  have h1 : (1 : ℚ) / p1 ≤ 1 / 3 := one_div_nat_le_one_div_nat (by decide) hp1_ge3
  have h2 : (1 : ℚ) / p2 ≤ 1 / 5 := one_div_nat_le_one_div_nat (by decide) hp2_ge5
  have h3 : (1 : ℚ) / p3 ≤ 1 / 7 := one_div_nat_le_one_div_nat (by decide) hp3_ge7
  have h4 : (1 : ℚ) / p4 ≤ 1 / 11 := one_div_nat_le_one_div_nat (by decide) hp4_ge11
  have h5 : (1 : ℚ) / p5 ≤ 1 / 13 := one_div_nat_le_one_div_nat (by decide) hp5_ge13
  have h6 : (1 : ℚ) / p6 ≤ 1 / 17 := one_div_nat_le_one_div_nat (by decide) hp6_ge17
  have hconst : (1 / 3 : ℚ) + 1 / 5 + 1 / 7 + 1 / 11 + 1 / 13 + 1 / 17 < 1 := by norm_num
  nlinarith

lemma sum_recip_seven_odd_primes_lt_one
    {p1 p2 p3 p4 p5 p6 p7 : ℕ}
    (hp1 : Nat.Prime p1) (hp2 : Nat.Prime p2) (hp3 : Nat.Prime p3)
    (hp4 : Nat.Prime p4) (hp5 : Nat.Prime p5) (hp6 : Nat.Prime p6) (hp7 : Nat.Prime p7)
    (hodd1 : Odd p1)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4) (h45 : p4 < p5) (h56 : p5 < p6)
    (h67 : p6 < p7) :
    ((1 : ℚ) / p1 + 1 / p2 + 1 / p3 + 1 / p4 + 1 / p5 + 1 / p6 + 1 / p7) < 1 := by
  have hp1_ge3 : 3 ≤ p1 := odd_prime_ge_three hp1 hodd1
  have hp2_ge5 : 5 ≤ p2 := prime_ge_five_of_gt_three hp2 (by omega)
  have hp3_ge7 : 7 ≤ p3 := prime_ge_seven_of_gt_five hp3 (by omega)
  have hp4_ge11 : 11 ≤ p4 := prime_ge_eleven_of_gt_seven hp4 (by omega)
  have hp5_ge13 : 13 ≤ p5 := prime_ge_thirteen_of_gt_eleven hp5 (by omega)
  have hp6_ge17 : 17 ≤ p6 := prime_ge_seventeen_of_gt_thirteen hp6 (by omega)
  have hp7_ge19 : 19 ≤ p7 := prime_ge_nineteen_of_gt_seventeen hp7 (by omega)
  have h1 : (1 : ℚ) / p1 ≤ 1 / 3 := one_div_nat_le_one_div_nat (by decide) hp1_ge3
  have h2 : (1 : ℚ) / p2 ≤ 1 / 5 := one_div_nat_le_one_div_nat (by decide) hp2_ge5
  have h3 : (1 : ℚ) / p3 ≤ 1 / 7 := one_div_nat_le_one_div_nat (by decide) hp3_ge7
  have h4 : (1 : ℚ) / p4 ≤ 1 / 11 := one_div_nat_le_one_div_nat (by decide) hp4_ge11
  have h5 : (1 : ℚ) / p5 ≤ 1 / 13 := one_div_nat_le_one_div_nat (by decide) hp5_ge13
  have h6 : (1 : ℚ) / p6 ≤ 1 / 17 := one_div_nat_le_one_div_nat (by decide) hp6_ge17
  have h7 : (1 : ℚ) / p7 ≤ 1 / 19 := one_div_nat_le_one_div_nat (by decide) hp7_ge19
  have hconst : (1 / 3 : ℚ) + 1 / 5 + 1 / 7 + 1 / 11 + 1 / 13 + 1 / 17 + 1 / 19 < 1 := by norm_num
  nlinarith

lemma sum_recip_eight_odd_primes_lt_one
    {p1 p2 p3 p4 p5 p6 p7 p8 : ℕ}
    (hp1 : Nat.Prime p1) (hp2 : Nat.Prime p2) (hp3 : Nat.Prime p3)
    (hp4 : Nat.Prime p4) (hp5 : Nat.Prime p5) (hp6 : Nat.Prime p6)
    (hp7 : Nat.Prime p7) (hp8 : Nat.Prime p8)
    (hodd1 : Odd p1)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4) (h45 : p4 < p5) (h56 : p5 < p6)
    (h67 : p6 < p7) (h78 : p7 < p8) :
    ((1 : ℚ) / p1 + 1 / p2 + 1 / p3 + 1 / p4 + 1 / p5 + 1 / p6 + 1 / p7 + 1 / p8) < 1 := by
  have hp1_ge3 : 3 ≤ p1 := odd_prime_ge_three hp1 hodd1
  have hp2_ge5 : 5 ≤ p2 := prime_ge_five_of_gt_three hp2 (by omega)
  have hp3_ge7 : 7 ≤ p3 := prime_ge_seven_of_gt_five hp3 (by omega)
  have hp4_ge11 : 11 ≤ p4 := prime_ge_eleven_of_gt_seven hp4 (by omega)
  have hp5_ge13 : 13 ≤ p5 := prime_ge_thirteen_of_gt_eleven hp5 (by omega)
  have hp6_ge17 : 17 ≤ p6 := prime_ge_seventeen_of_gt_thirteen hp6 (by omega)
  have hp7_ge19 : 19 ≤ p7 := prime_ge_nineteen_of_gt_seventeen hp7 (by omega)
  have hp8_ge23 : 23 ≤ p8 := prime_ge_twentythree_of_gt_nineteen hp8 (by omega)
  have h1 : (1 : ℚ) / p1 ≤ 1 / 3 := one_div_nat_le_one_div_nat (by decide) hp1_ge3
  have h2 : (1 : ℚ) / p2 ≤ 1 / 5 := one_div_nat_le_one_div_nat (by decide) hp2_ge5
  have h3 : (1 : ℚ) / p3 ≤ 1 / 7 := one_div_nat_le_one_div_nat (by decide) hp3_ge7
  have h4 : (1 : ℚ) / p4 ≤ 1 / 11 := one_div_nat_le_one_div_nat (by decide) hp4_ge11
  have h5 : (1 : ℚ) / p5 ≤ 1 / 13 := one_div_nat_le_one_div_nat (by decide) hp5_ge13
  have h6 : (1 : ℚ) / p6 ≤ 1 / 17 := one_div_nat_le_one_div_nat (by decide) hp6_ge17
  have h7 : (1 : ℚ) / p7 ≤ 1 / 19 := one_div_nat_le_one_div_nat (by decide) hp7_ge19
  have h8 : (1 : ℚ) / p8 ≤ 1 / 23 := one_div_nat_le_one_div_nat (by decide) hp8_ge23
  have hconst : (1 / 3 : ℚ) + 1 / 5 + 1 / 7 + 1 / 11 + 1 / 13 + 1 / 17 + 1 / 19 + 1 / 23 < 1 := by norm_num
  nlinarith

lemma sum_over_finset_eq_sum_fin {s : Finset ℕ} {m : ℕ} (hcard : s.card = m) :
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin m, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ p ∈ Finset.image (s.orderEmbOfFin hcard) Finset.univ, (1 / p : ℚ) := by
      simp [Finset.image_orderEmbOfFin_univ]
    _ = ∑ i ∈ Finset.univ, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by
      simpa using (Finset.sum_image (s := Finset.univ) (g := s.orderEmbOfFin hcard)
        (f := fun p : ℕ => (1 / p : ℚ)) ((s.orderEmbOfFin hcard).injective.injOn))
    _ = ∑ i : Fin m, (1 / (s.orderEmbOfFin hcard i) : ℚ) := by simp

lemma sum_recip_lt_one_of_card_eq_six
    {s : Finset ℕ} (hcard : s.card = 6)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, (1 / p : ℚ)) < 1 := by
  let e : Fin 6 → ℕ := s.orderEmbOfFin hcard
  have he_mono : StrictMono e := (s.orderEmbOfFin hcard).strictMono
  have hp1 : Nat.Prime (e 0) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 6))
  have hp2 : Nat.Prime (e 1) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (1 : Fin 6))
  have hp3 : Nat.Prime (e 2) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (2 : Fin 6))
  have hp4 : Nat.Prime (e 3) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (3 : Fin 6))
  have hp5 : Nat.Prime (e 4) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (4 : Fin 6))
  have hp6 : Nat.Prime (e 5) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (5 : Fin 6))
  have hodd1 : Odd (e 0) := by simpa [e] using hodd _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 6))
  have h12 : e 0 < e 1 := by
    have h := he_mono (show (0 : Fin 6) < 1 by decide)
    simpa [e] using h
  have h23 : e 1 < e 2 := by
    have h := he_mono (show (1 : Fin 6) < 2 by decide)
    simpa [e] using h
  have h34 : e 2 < e 3 := by
    have h := he_mono (show (2 : Fin 6) < 3 by decide)
    simpa [e] using h
  have h45 : e 3 < e 4 := by
    have h := he_mono (show (3 : Fin 6) < 4 by decide)
    simpa [e] using h
  have h56 : e 4 < e 5 := by
    have h := he_mono (show (4 : Fin 6) < 5 by decide)
    simpa [e] using h
  have hbound : (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ) + 1 / (e 5 : ℚ)) < 1 := by
    exact sum_recip_six_odd_primes_lt_one hp1 hp2 hp3 hp4 hp5 hp6 hodd1 h12 h23 h34 h45 h56
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 6, (1 / (e i) : ℚ) := by
      simpa [e] using sum_over_finset_eq_sum_fin (s := s) hcard
    _ = (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ) + 1 / (e 5 : ℚ)) := by
      simpa [Fin.sum_univ_six]
    _ < 1 := hbound

lemma sum_recip_lt_one_of_card_eq_seven
    {s : Finset ℕ} (hcard : s.card = 7)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, (1 / p : ℚ)) < 1 := by
  let e : Fin 7 → ℕ := s.orderEmbOfFin hcard
  have he_mono : StrictMono e := (s.orderEmbOfFin hcard).strictMono
  have hp1 : Nat.Prime (e 0) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 7))
  have hp2 : Nat.Prime (e 1) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (1 : Fin 7))
  have hp3 : Nat.Prime (e 2) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (2 : Fin 7))
  have hp4 : Nat.Prime (e 3) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (3 : Fin 7))
  have hp5 : Nat.Prime (e 4) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (4 : Fin 7))
  have hp6 : Nat.Prime (e 5) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (5 : Fin 7))
  have hp7 : Nat.Prime (e 6) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (6 : Fin 7))
  have hodd1 : Odd (e 0) := by simpa [e] using hodd _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 7))
  have h12 : e 0 < e 1 := by
    have h := he_mono (show (0 : Fin 7) < 1 by decide)
    simpa [e] using h
  have h23 : e 1 < e 2 := by
    have h := he_mono (show (1 : Fin 7) < 2 by decide)
    simpa [e] using h
  have h34 : e 2 < e 3 := by
    have h := he_mono (show (2 : Fin 7) < 3 by decide)
    simpa [e] using h
  have h45 : e 3 < e 4 := by
    have h := he_mono (show (3 : Fin 7) < 4 by decide)
    simpa [e] using h
  have h56 : e 4 < e 5 := by
    have h := he_mono (show (4 : Fin 7) < 5 by decide)
    simpa [e] using h
  have h67 : e 5 < e 6 := by
    have h := he_mono (show (5 : Fin 7) < 6 by decide)
    simpa [e] using h
  have hbound : (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ) + 1 / (e 5 : ℚ) + 1 / (e 6 : ℚ)) < 1 := by
    exact sum_recip_seven_odd_primes_lt_one hp1 hp2 hp3 hp4 hp5 hp6 hp7 hodd1 h12 h23 h34 h45 h56 h67
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 7, (1 / (e i) : ℚ) := by
      simpa [e] using sum_over_finset_eq_sum_fin (s := s) hcard
    _ = (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ) + 1 / (e 5 : ℚ) + 1 / (e 6 : ℚ)) := by
      simpa [Fin.sum_univ_seven]
    _ < 1 := hbound

lemma sum_recip_lt_one_of_card_eq_eight
    {s : Finset ℕ} (hcard : s.card = 8)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, (1 / p : ℚ)) < 1 := by
  let e : Fin 8 → ℕ := s.orderEmbOfFin hcard
  have he_mono : StrictMono e := (s.orderEmbOfFin hcard).strictMono
  have hp1 : Nat.Prime (e 0) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 8))
  have hp2 : Nat.Prime (e 1) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (1 : Fin 8))
  have hp3 : Nat.Prime (e 2) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (2 : Fin 8))
  have hp4 : Nat.Prime (e 3) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (3 : Fin 8))
  have hp5 : Nat.Prime (e 4) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (4 : Fin 8))
  have hp6 : Nat.Prime (e 5) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (5 : Fin 8))
  have hp7 : Nat.Prime (e 6) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (6 : Fin 8))
  have hp8 : Nat.Prime (e 7) := by simpa [e] using hprime _ (Finset.orderEmbOfFin_mem s hcard (7 : Fin 8))
  have hodd1 : Odd (e 0) := by simpa [e] using hodd _ (Finset.orderEmbOfFin_mem s hcard (0 : Fin 8))
  have h12 : e 0 < e 1 := by
    have h := he_mono (show (0 : Fin 8) < 1 by decide)
    simpa [e] using h
  have h23 : e 1 < e 2 := by
    have h := he_mono (show (1 : Fin 8) < 2 by decide)
    simpa [e] using h
  have h34 : e 2 < e 3 := by
    have h := he_mono (show (2 : Fin 8) < 3 by decide)
    simpa [e] using h
  have h45 : e 3 < e 4 := by
    have h := he_mono (show (3 : Fin 8) < 4 by decide)
    simpa [e] using h
  have h56 : e 4 < e 5 := by
    have h := he_mono (show (4 : Fin 8) < 5 by decide)
    simpa [e] using h
  have h67 : e 5 < e 6 := by
    have h := he_mono (show (5 : Fin 8) < 6 by decide)
    simpa [e] using h
  have h78 : e 6 < e 7 := by
    have h := he_mono (show (6 : Fin 8) < 7 by decide)
    simpa [e] using h
  have hbound : (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ) + 1 / (e 5 : ℚ) + 1 / (e 6 : ℚ) + 1 / (e 7 : ℚ)) < 1 := by
    exact sum_recip_eight_odd_primes_lt_one hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hodd1 h12 h23 h34 h45 h56 h67 h78
  calc
    (∑ p ∈ s, (1 / p : ℚ)) = ∑ i : Fin 8, (1 / (e i) : ℚ) := by
      simpa [e] using sum_over_finset_eq_sum_fin (s := s) hcard
    _ = (1 / (e 0 : ℚ) + 1 / (e 1 : ℚ) + 1 / (e 2 : ℚ) + 1 / (e 3 : ℚ) + 1 / (e 4 : ℚ) + 1 / (e 5 : ℚ) + 1 / (e 6 : ℚ) + 1 / (e 7 : ℚ)) := by
      simpa [Fin.sum_univ_eight]
    _ < 1 := hbound

lemma primeFactors_card_ge_nine_of_recip_identity
    (n k : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hcard_ge6 : 6 ≤ n.primeFactors.card)
    (hk : 1 ≤ k)
    (hsum : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) = k + 1 / n) :
    9 ≤ n.primeFactors.card := by
  by_contra hlt9
  have hcard_le8 : n.primeFactors.card ≤ 8 := by omega
  have hcard : n.primeFactors.card = 6 ∨ n.primeFactors.card = 7 ∨ n.primeFactors.card = 8 := by omega
  have hprime : ∀ p ∈ n.primeFactors, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    exact hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hgt : (1 : ℚ) < ∑ p ∈ n.primeFactors, (1 / p : ℚ) := by
    rw [hsum]
    exact rhs_gt_one_of_k_pos hk hn
  rcases hcard with h6 | h7 | h8
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 :=
      sum_recip_lt_one_of_card_eq_six h6 hprime hodd_pf
    linarith
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 :=
      sum_recip_lt_one_of_card_eq_seven h7 hprime hodd_pf
    linarith
  · have hlt : (∑ p ∈ n.primeFactors, (1 / p : ℚ)) < 1 :=
      sum_recip_lt_one_of_card_eq_eight h8 hprime hodd_pf
    linarith
```

What BMS2013 adds beyond reciprocal sums:
- They don’t just bound \(\sum 1/p\) by first \(m\) primes.
- They impose a **normality** condition on candidate prime sets from Carmichael+Giuga structure.
- They use auxiliary \(d\)- and \(j_d\)-quantities and prove a monotonicity theorem to prune a recursive search tree of admissible prime sets.
- This combined structural/computational pruning yields the large bound \(\omega(n)\ge 4771\) (and \(n>10^{19907}\), i.e. at least 19,908 digits).

Sources:
- BMS paper PDF: https://carmamaths.org/jon/giuga2013.pdf  
- Journal page: https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.853/

I couldn’t write directly into your repo in this session because the filesystem is mounted read-only.