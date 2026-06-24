/-
  BBC Corollary 1.3, m = 5 specialization
  ========================================
  Bajpai–Bennett–Chan (2024), IJNT 20:19–45, arXiv:2302.03113

  **Theorem (conditional on abc):**  The set of pairs (N, d) of positive integers
  with gcd(N, d) = 1 such that N, N+d, N+2d, N+3d, N+4d are all powerful is finite.

  The proof reduces to a gcd lower bound (BBC Theorem 1.1 at m = 5, k = 2) which
  contradicts coprimality for large N, d, leaving finitely many pairs.
-/
import Mathlib

open Set

/-! ### Definitions -/

/-- A natural number `n` is **powerful** if n ≥ 1 and for every prime p dividing n,
    p² also divides n. -/
def Nat.Powerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

namespace ABC

/-- The radical of a natural number: the product of its distinct prime factors. -/
noncomputable def radical (n : ℕ) : ℕ :=
  if n = 0 then 0
  else n.primeFactors.prod id

end ABC

/-! ### Helper lemmas -/

/-- For a powerful number, rad(n)² ≤ n. This is BBC Lemma 2.1.

Since n is powerful, for every prime p | n we have p² | n, so the exponent of
p in the factorization of n is ≥ 2.  Therefore
  n = ∏ p^{e_p} ≥ ∏ p² = (∏ p)² = rad(n)². -/
lemma radical_sq_le_of_powerful {n : ℕ} (hn : Nat.Powerful n) :
    ABC.radical n ^ 2 ≤ n := by
  by_cases hn0 : n = 0 <;> simp +decide [*, ABC.radical]
  have h_exp : ∀ p ∈ n.primeFactors, 2 ≤ (Nat.factorization n) p := by
    exact fun p hp => Nat.le_of_not_gt fun h =>
      hn.2 p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      |> fun h' => absurd (Nat.dvd_trans (pow_dvd_pow p h) h')
        (Nat.pow_succ_factorization_not_dvd hn0 (Nat.prime_of_mem_primeFactors hp))
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
  simpa only [← Finset.prod_pow] using
    Finset.prod_le_prod' fun p hp =>
      Nat.pow_le_pow_right (Nat.pos_of_mem_primeFactors hp) (h_exp p hp)

/-- For a coprime pair (N,d), the triple {N, d, N+d} is pairwise coprime.

gcd(N, d) = 1 by hypothesis; gcd(N, N+d) | d and gcd(d, N+d) | N, so both are 1. -/
lemma coprime_triple_of_coprime {N d : ℕ}
    (hcop : Nat.Coprime N d) :
    ({N, d, N + d} : Set ℕ).Pairwise Nat.Coprime := by
  simp +decide [Set.Pairwise, *]
  simp_all +decide [Nat.Coprime, Nat.gcd_comm]

/-- A subset of a bounded region in ℕ × ℕ is finite. -/
lemma finite_of_max_bounded (K : ℕ) :
    {p : ℕ × ℕ | max p.1 p.2 < K}.Finite := by
  apply Set.Finite.subset ((Set.finite_Iio K).prod (Set.finite_Iio K))
  intro ⟨a, b⟩ h
  simp only [Set.mem_setOf_eq] at h
  exact ⟨lt_of_le_of_lt (le_max_left a b) h, lt_of_le_of_lt (le_max_right a b) h⟩

/-! ### BBC Theorem 1.1 (m = 5, k = 2) — the gcd lower bound

This is the deep number-theoretic content of the proof. BBC prove that, under abc,
for any 5-term powerful arithmetic progression (N, N+d, …, N+4d) with gcd(N,d) = 1,
the parameter max(N, d) is bounded by an absolute constant.

**Full proof chain (from BBC §2):**
1. `radical_sq_le_of_powerful` (proved above): for n powerful, rad(n)² ≤ n.
2. BBC Lemma 2.2: for m ≥ 2k−1 terms of a k-full AP, the product of radicals
   satisfies a refined bound involving the gcd.
3. The 5-term identity a₀ − 4a₁ + 6a₂ − 4a₃ + a₄ = 0 reduces to an S-unit
   equation. The abc conjecture (via the Evertse–Schlickewei theorem for
   n-term S-unit equations, derivable from 3-term abc by induction) bounds
   the number of non-degenerate solutions.
4. Combining (1)–(3) yields: gcd(N,d) ≥ c · max(N,d)^{2/7−ε} for all but
   finitely many (N,d). Coprimality (gcd = 1) then forces max(N,d) < K
   for some absolute K.

This derivation is beyond the scope of the current formalization (it requires
the full Evertse–Schlickewei theorem as an intermediate step). We leave it as
the single `sorry` in the development.
-/
lemma bbc_thm_1_1_m5_bound
    (abc : ∀ ε : ℝ, 0 < ε →
      {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
        ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
        (ABC.radical (a * b * c) : ℝ)^(1 + ε) < c}.Finite) :
    ∃ K : ℕ, ∀ N d : ℕ, 0 < N → 0 < d → Nat.Coprime N d →
      (∀ i, i < 5 → Nat.Powerful (N + i * d)) → max N d < K := by
  sorry

/-! ### Main theorem -/

/--
**BBC Corollary 1.3 at m = 5** (conditional on abc):
Only finitely many coprime 5-term powerful arithmetic progressions exist.

*Proof.* By `bbc_thm_1_1_m5_bound`, there exists an absolute bound K such that
every coprime 5-term powerful AP (N, d) satisfies max(N, d) < K.  The set of
pairs (N, d) with max(N, d) < K is finite (`finite_of_max_bounded`), and our
target set is a subset of it.

*Sharpness.* The threshold m ≥ 5 is sharp: BBC Theorem 1.2 constructs infinitely
many coprime 4-term powerful APs via parametric families on x² + y² = 2z².
-/
theorem bbc_cor_1_3_m5_coprime_finite
    (abc : ∀ ε : ℝ, 0 < ε →
      {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
        ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
        (ABC.radical (a * b * c) : ℝ)^(1 + ε) < c}.Finite) :
    {(N, d) : ℕ × ℕ | 0 < N ∧ 0 < d ∧ Nat.Coprime N d ∧
      ∀ i, i < 5 → Nat.Powerful (N + i * d)}.Finite := by
  obtain ⟨K, hK⟩ := bbc_thm_1_1_m5_bound abc
  apply (finite_of_max_bounded K).subset
  intro ⟨N, d⟩ ⟨hN, hd, hcop, hpow⟩
  exact hK N d hN hd hcop hpow
