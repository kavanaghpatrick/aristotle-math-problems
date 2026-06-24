import Mathlib

/-!
# Feit-Thompson Divisibility Conjecture

For distinct odd primes p, q: Φ_p(q) does not divide Φ_q(p),
where Φ_p(q) = (q^p - 1)/(q - 1).

This is an **open conjecture** in number theory, originally arising from
Feit and Thompson's work on the odd order theorem (1962).

- Stephens (1971) disproved the stronger gcd=1 form:
  gcd(Φ₁₇(3313), Φ₃₃₁₃(17)) = 112643.
- Le (2012) proved the p=3 case: q²+q+1 ∤ (3^q-1)/2 for all odd primes q≠3.
- The full divisibility conjecture remains open for p ≥ 5.

## Results in this file

- `feit_thompson_p3_qmod3eq1`: The p=3, q ≡ 1 (mod 3) sub-case (proved).
  When q ≡ 1 (mod 3), 3 | q²+q+1 but 3 ∤ 3^q-1, giving an immediate contradiction.

- `feit_thompson_p3_qmod3eq2`: The p=3, q ≡ 2 (mod 3) sub-case (sorry — requires
  cubic reciprocity / Eisenstein integer arguments from Le 2012).

- `feit_thompson_p3`: The full p=3 case, combining the two sub-cases.

- `feit_thompson_divisibility`: The full conjecture (sorry — open problem).
-/

-- ============================================================================
-- Part 1: The p=3 case, sub-case q ≡ 1 (mod 3)
-- ============================================================================

/-- When q ≡ 1 (mod 3), we have 3 | q² + q + 1, but 3 ∤ 3^q - 1,
    so q² + q + 1 cannot divide (3^q - 1)/2. -/
theorem feit_thompson_p3_qmod3eq1 (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hqmod : q % 3 = 1) :
    ¬ ((q ^ 3 - 1) / (q - 1)) ∣ ((3 ^ q - 1) / (3 - 1)) := by
      -- By contradiction, assume that $(q^3 - 1)/(q - 1)$ divides $(3^q - 1)/(3 - 1)$.
      by_contra h_contra
      have h_div : 3 ∣ (3^q - 1) / (3 - 1) := by
        refine dvd_trans ?_ h_contra ; norm_num [ show q^3 - 1 = ( q - 1 ) * ( q^2 + q + 1 ) by zify ; cases q <;> norm_num ; linarith ]
        exact mul_dvd_mul_left _ ( Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div q 3, hqmod ] ; norm_num [ Nat.add_mod, Nat.pow_mod ] ) )
      obtain ⟨ k, hk ⟩ := h_div; rw [ Nat.div_eq_iff_eq_mul_right ( by decide ) ] at hk; have := congr_arg ( · % 3 ) hk; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hq.ne_zero ] at this
      · zify at *; norm_num [ Int.sub_emod, Int.mul_emod, pow_succ ] at *
        cases q <;> norm_num [ pow_succ' ] at *
      · simp_all +decide [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ]

-- ============================================================================
-- Part 2: The p=3 case, sub-case q ≡ 2 (mod 3) [Le 2012, harder case]
-- ============================================================================

/-- When q ≡ 2 (mod 3), we have 3 ∤ q² + q + 1, and every prime factor r of
    q² + q + 1 has ord_r(q) = 3. If q² + q + 1 | (3^q - 1)/2, then
    every such r satisfies ord_r(3) = q, giving r ≡ 1 (mod 3q), which forces
    q² + q + 1 to be prime. The final contradiction requires cubic reciprocity
    in the Eisenstein integers, following Le (2012).

    This sub-case is left as `sorry` as formalizing cubic reciprocity is beyond
    the scope of current Mathlib coverage. -/
theorem feit_thompson_p3_qmod3eq2 (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hqmod : q % 3 = 2) :
    ¬ ((q ^ 3 - 1) / (q - 1)) ∣ ((3 ^ q - 1) / (3 - 1)) := by sorry

-- ============================================================================
-- Part 3: Combining the p=3 sub-cases
-- ============================================================================

/-- Le (2012): The p=3 case of the Feit-Thompson divisibility conjecture.
    For any odd prime q ≠ 3, (q² + q + 1) does not divide (3^q - 1)/2.

    The q ≡ 1 (mod 3) sub-case is proved directly (3 | q²+q+1 but 3 ∤ 3^q-1).
    The q ≡ 2 (mod 3) sub-case requires deeper machinery (sorry). -/
theorem feit_thompson_p3 (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    ¬ ((q ^ 3 - 1) / (q - 1)) ∣ ((3 ^ q - 1) / (3 - 1)) := by
  have hq3' : q % 3 ≠ 0 := by
    intro h
    have := Nat.dvd_of_mod_eq_zero h
    have := hq.eq_one_or_self_of_dvd 3 this
    omega
  have : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases this with h | h
  · exact feit_thompson_p3_qmod3eq1 q hq hq2 hq3 h
  · exact feit_thompson_p3_qmod3eq2 q hq hq2 hq3 h

-- ============================================================================
-- Part 4: The full conjecture (OPEN PROBLEM)
-- ============================================================================

/-- **Feit-Thompson Divisibility Conjecture** (Open Problem).
    For distinct odd primes p, q: Φ_p(q) does not divide Φ_q(p),
    where Φ_p(q) = (q^p - 1)/(q - 1).

    This conjecture remains open as of 2024. Key partial results:
    - The p=3 case was proved by Le (2012) — see `feit_thompson_p3`.
    - Any common prime factor r of Φ_p(q) and Φ_q(p) (with r ≠ p, r ≠ q)
      satisfies r ≡ 1 (mod pq), severely constraining possible counterexamples.
    - Computational verification has been done for all primes up to 10^14.

    The full conjecture for p ≥ 5 remains open and is left as `sorry`. -/
theorem feit_thompson_divisibility (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ¬ ((q ^ p - 1) / (q - 1)) ∣ ((p ^ q - 1) / (p - 1)) := by sorry
