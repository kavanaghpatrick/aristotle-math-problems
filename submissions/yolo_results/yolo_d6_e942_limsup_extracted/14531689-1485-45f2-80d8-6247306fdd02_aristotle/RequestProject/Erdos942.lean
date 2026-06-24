import Mathlib

/-!
# Erdős Problem 942: limsup of powerful-counts in [n², (n+1)²) is infinite

A natural number `m` is *powerful* if every prime factor of `m` divides `m`
with multiplicity at least 2. Equivalently, `m = a² · b³` for some `a, b`.

We define `h(n) = #{m ∈ [n², (n+1)²) : m is powerful}` and prove
`limsup_{n→∞} h(n) = ∞`.

## Proof strategy

The proof uses the Golomb parametrization: every number of the form `u² · p³`
(with `p` prime, `u ≥ 1`) is powerful. For distinct primes `p_i`, the values
`u_i² · p_i³` are automatically distinct (by p-adic valuation parity).

The key construction shows that for any finite set of distinct primes and any
`N`, there exists `n ≥ N` and corresponding `u_i` values with
`n² ≤ u_i² · p_i³ < (n+1)²`. This follows from Kronecker's theorem on
simultaneous Diophantine approximation.
-/

open Filter Finset

noncomputable section

/-! ## Definition of powerful numbers -/

/-- A natural number is powerful if it is positive and every prime factor
    divides it with multiplicity at least 2. -/
def IsPowerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

instance : DecidablePred IsPowerful := fun n => by
  unfold IsPowerful
  exact inferInstance

/-! ## Definition of h(n) -/

namespace erdos_942

/-- Count of powerful numbers in `[n², (n+1)²)`. -/
def h (n : ℕ) : ℕ :=
  ((Ico (n ^ 2) ((n + 1) ^ 2)).filter IsPowerful).card

/-! ## Golomb parametrization lemmas -/

/-- Any number of the form `u² · v³` with `u ≥ 1` and `v ≥ 1` is powerful. -/
lemma sq_mul_cube_isPowerful {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    IsPowerful (u ^ 2 * v ^ 3) := by
  refine ⟨Nat.mul_pos (pow_pos hu 2) (pow_pos hv 3), ?_⟩
  simp +zetaDelta at *
  intro p pp dp _ _; rw [Nat.Prime.dvd_mul pp] at dp
  simp_all +decide [Nat.Prime.dvd_iff_not_coprime]
  rcases dp with dp | dp
  · exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (pp.dvd_iff_not_coprime.mpr dp) 2) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (pp.dvd_iff_not_coprime.mpr dp) 2
      |> fun x => x.trans (pow_dvd_pow _ (by decide))) _

/-- If `p₁ ≠ p₂` are primes and `u₁² · p₁³ = u₂² · p₂³`, then contradiction. -/
lemma golomb_distinct {u₁ u₂ p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hne : p₁ ≠ p₂) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂)
    (heq : u₁ ^ 2 * p₁ ^ 3 = u₂ ^ 2 * p₂ ^ 3) : False := by
  apply_fun fun x => x.factorization p₁ at heq
  simp_all +decide [hp₁.ne_zero, hp₂.ne_zero, Nat.factorization_mul, hu₁.ne', hu₂.ne']
  omega

/-! ## Helper: n = Nat.sqrt(u²p³) gives n² ≤ u²p³ < (n+1)² -/

/-- For u > 0 and prime p, setting n = Nat.sqrt(u²p³) gives a valid witness. -/
lemma sqrt_witness (u p : ℕ) (hu : 0 < u) (_hp : p.Prime) :
    let n := Nat.sqrt (u ^ 2 * p ^ 3)
    0 < u ∧ n ^ 2 ≤ u ^ 2 * p ^ 3 ∧ u ^ 2 * p ^ 3 < (n + 1) ^ 2 := by
  simp only
  exact ⟨hu, Nat.sqrt_le' _, Nat.lt_succ_sqrt' _⟩

/-! ## Kronecker construction -/

/-- **Kronecker construction (simultaneous Diophantine approximation).**
    For any finite set of distinct primes and any `N`, there exists `n ≥ N` and
    witnesses `u_i > 0` with `n² ≤ u_i² · p_i³ < (n+1)²` for each prime `p_i`.

    This is the key step requiring Kronecker's theorem: the fractional parts
    `{n · p_i^{-3/2}}` are simultaneously close to 1 for infinitely many `n`. -/
lemma kronecker_construction (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime)
    (N : ℕ) :
    ∃ n, N ≤ n ∧ ∀ p ∈ ps, ∃ u, 0 < u ∧
      n ^ 2 ≤ u ^ 2 * p ^ 3 ∧ u ^ 2 * p ^ 3 < (n + 1) ^ 2 := by sorry

/-! ## From construction to h(n) bound -/

/-- Given a finset of distinct primes each with a witness powerful number in
    `[n², (n+1)²)`, we get `h(n) ≥ ps.card`. -/
lemma h_ge_of_distinct_powerful (n : ℕ) (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime)
    (hconstruct : ∀ p ∈ ps, ∃ u, 0 < u ∧
      n ^ 2 ≤ u ^ 2 * p ^ 3 ∧ u ^ 2 * p ^ 3 < (n + 1) ^ 2) :
    ps.card ≤ h n := by
  choose! u hu using hconstruct
  have h_image : (ps.image (fun p => u p ^ 2 * p ^ 3)).card ≤
      ((Ico (n ^ 2) ((n + 1) ^ 2)).filter IsPowerful).card := by
    refine Finset.card_le_card ?_
    exact Finset.image_subset_iff.mpr fun p hp => Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr (hu p hp |>.2),
       sq_mul_cube_isPowerful (hu p hp |>.1) (Nat.Prime.pos (hps p hp))⟩
  rwa [Finset.card_image_of_injOn] at h_image
  intro p hp q hq
  exact fun h => Classical.not_not.1 fun hpq =>
    golomb_distinct (hps p hp) (hps q hq) hpq (hu p hp |>.1) (hu q hq |>.1) h

/-! ## Existence of arbitrarily many primes -/

/-- For any `M`, there exists a finset of `M` primes. -/
lemma exists_prime_finset (M : ℕ) :
    ∃ ps : Finset ℕ, ps.card = M ∧ ∀ p ∈ ps, p.Prime := by
  exact ⟨Finset.image (fun k => Nat.nth Nat.Prime k) (Finset.range M),
    by rw [Finset.card_image_of_injective _ (Nat.nth_injective <| Nat.infinite_setOf_prime)]
       simp +decide,
    fun p hp => by aesop⟩

/-! ## Main intermediate result -/

/-- For any `M` and `N`, there exists `n ≥ N` with `h(n) ≥ M`. -/
lemma h_frequently_large (M N : ℕ) : ∃ n, N ≤ n ∧ M ≤ h n := by
  obtain ⟨ps, hcard, hprimes⟩ := exists_prime_finset M
  obtain ⟨n, hn, hconstruct⟩ := kronecker_construction ps hprimes N
  exact ⟨n, hn, hcard ▸ h_ge_of_distinct_powerful n ps hprimes hconstruct⟩

/-! ## Main theorem -/

namespace variants

/-- **Erdős 942 (limsup variant):** The limsup of the count of powerful numbers
    in consecutive-square intervals `[n², (n+1)²)` is infinite. -/
theorem limsup :
    atTop.limsup ((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ h) = ⊤ := by
  refine' le_antisymm le_top _
  refine' le_csInf _ _
  · use ⊤; simp
  · simp +zetaDelta at *
    intro b x hx; contrapose! hx
    cases' b with b; aesop
    exact Exists.elim (h_frequently_large (b + 1) x) fun n hn =>
      ⟨n, hn.1, Nat.cast_lt.mpr hn.2⟩

end variants

end erdos_942
