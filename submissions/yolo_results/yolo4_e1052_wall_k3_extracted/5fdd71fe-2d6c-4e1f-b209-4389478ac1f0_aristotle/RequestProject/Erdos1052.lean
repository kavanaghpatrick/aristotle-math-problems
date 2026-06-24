/-
# Erdős Problem 1052 / Wall k=3 — Lehmer Pair Primitive Divisor Theorem

This file formalizes the statement and proof structure of the Bilu-Hanrot-Voutier
theorem restricted to indices divisible by 3 (the "Wall k=3 stratum").

## Mathematical Result

For every Lehmer pair (α,β) and every n > 30 with 3 ∣ n, the n-th Lehmer number
U_n(α,β) has a primitive prime divisor — a prime q that divides U_n but does not
divide U_m for any 0 < m < n.

## Status

**Mathematically settled**: This follows from the Bilu-Hanrot-Voutier theorem (2001).
**Formalization status**: OPEN. The proof requires Baker's theory of linear forms in
logarithms, which is not currently available in Mathlib. The key missing pieces are:

1. **Cyclotomic factorization of Lehmer numbers**: U_n = ∏_{d|n} Φ*_d(α,β)
2. **Lower bounds on Φ*_n**: Using Baker's theorem on linear forms in logarithms
3. **Integrality of Lehmer terms**: Proof that U_n ∈ ℤ for Lehmer pairs

Below we provide the formal statement, definitions, and a decomposition into
key lemmas that constitute the proof structure. The main theorem is proved
modulo the key lemma `lehmer_primitive_part_nontrivial`.

## References

- Y. Bilu, G. Hanrot, P.M. Voutier, "Existence of primitive divisors of Lucas
  and Lehmer numbers", J. reine angew. Math. 539 (2001), 75-122.
  DOI: 10.1515/crll.2001.080
-/

import Mathlib

open scoped BigOperators Classical

set_option maxHeartbeats 8000000

/-! ## Core Definitions -/

/-- A complex number z is a root of unity if z^n = 1 for some positive integer n. -/
def IsRootOfUnity' (z : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

/-- The n-th Lehmer number U_n(α,β) as a complex number.

For odd n: U_n = (αⁿ - βⁿ)/(α - β)
For even n: U_n = (αⁿ - βⁿ)/(α² - β²)

When (α,β) is a Lehmer pair, these expressions are always rational integers. -/
noncomputable def lehmer_term_complex (α β : ℂ) (n : ℕ) : ℂ :=
  if n % 2 = 1
  then (α ^ n - β ^ n) / (α - β)
  else (α ^ n - β ^ n) / (α ^ 2 - β ^ 2)

/-- The n-th Lehmer number as an integer, extracted via floor of the real part.
For a valid Lehmer pair, Lehmer terms are always integers, so this agrees
with the actual value. -/
noncomputable def lehmer_term (α β : ℂ) (n : ℕ) : ℤ :=
  ⌊(lehmer_term_complex α β n).re⌋

/-- A prime q is a **primitive divisor** of U_n if q divides U_n but does not
divide U_m for any 0 < m < n. -/
def IsPrimitiveDivisor (q : ℕ) (α β : ℂ) (n : ℕ) : Prop :=
  q.Prime ∧ (q : ℤ) ∣ lehmer_term α β n ∧
    ∀ m, 0 < m → m < n → ¬ ((q : ℤ) ∣ lehmer_term α β m)

/-! ## Key Lemmas (Proof Structure)

The following lemmas decompose the BHV proof into its main components.
All are stated with `sorry` as they require mathematical infrastructure
not yet available in Mathlib. -/

/-
**Integrality**: For a Lehmer pair, U_n is always an integer, i.e.,
the complex expression has zero imaginary part and integer real part.
This is a classical result following from the recurrence relations
U_n satisfies with integer coefficients.
-/
lemma lehmer_term_is_integer
    (α β : ℂ) (hα : α + β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ : α * β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hne : α * β ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    ∃ z : ℤ, (z : ℂ) = lehmer_term_complex α β n := by
  -- For odd n, let's use the recurrence relation and induction to show U_n is an integer.
  by_cases hn_odd : Odd n;
  · -- By induction on $n$, � we� can show that $U_n$ is an algebraic integer.
    have h_alg_int : ∀ n : ℕ, 0 < n → (∃ z : ℤ, (z : ℂ) = ((α ^ n - β ^ n) / (α - β) : ℂ)) := by
      intro n hn; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ] ;
      · by_cases h : α = β <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · obtain ⟨ z₁, hz₁ ⟩ := ih ( n + 1 ) ( by linarith ) ( Nat.succ_pos _ ) ; obtain ⟨ z₂, hz₂ ⟩ := if h : n = 0 then ⟨ 0, by aesop ⟩ else ih n ( by linarith ) ( Nat.pos_of_ne_zero h ) ; simp_all +decide [ pow_succ', ← mul_assoc, sub_mul, mul_sub ] ;
        -- Using the recurrence relation, we � have� $(α^{n+2} - β^{n �+�2}) / (α - β) = (α + β)(α^{n+1} - β^{n+1}) / (α - β) - αβ(α^n - β^n) / (α - β)$.
        obtain ⟨ y, hy ⟩ := hα; obtain ⟨ z, hz ⟩ := hαβ; use y * z₁ - z * z₂; push_cast [ * ] ; ring;
    convert h_alg_int n hn;
    exact if_pos ( Nat.odd_iff.mp hn_odd );
  · -- For even n, let �'s� use the � recurrence� relation and induction to show U_n is an integer.
    have h_even : ∀ k : ℕ, 0 < k → ∃ z : ℤ, z = (α^(2*k) - β^(2*k)) / (α^2 - β^2) := by
      intro k hk_pos
      induction' k using Nat.strong_induction_on with k ih;
      rcases k with ( _ | _ | _ | k ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
      · by_cases h : α * α - β * β = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · by_cases h : α ^ 2 - β ^ 2 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add, ← mul_assoc, ← pow_two ];
        exact ⟨ hα.choose ^ 2 - 2 * hαβ.choose, by push_cast [ hα.choose_spec, hαβ.choose_spec ] ; rw [ eq_div_iff ( sub_ne_zero_of_ne h ) ] ; ring ⟩;
      · -- Use the recurrence relation for even terms: $ �U�_{2(k+3)} = (\alpha^2 + \beta^2) U_{2(k+2)} - \alpha^2 \ �beta�^2 U_{2(k+1)}$
        obtain ⟨z₁, hz₁⟩ := ih (k + 1) (by linarith) (by linarith)
        obtain ⟨z₂, hz₂⟩ := ih (k + 2) (by linarith) (by linarith)
        use (hα.choose^2 - 2 * hαβ.choose) * z₂ - hαβ.choose^2 * z₁;
        push_cast [ hz₁, hz₂ ];
        rw [ hα.choose_spec, hαβ.choose_spec ] ; ring;
    rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ lehmer_term_complex ]

/-
**Non-vanishing**: If α/β is not a root of unity and αβ ≠ 0,
then U_n ≠ 0 for all n ≥ 1. This follows from (α/β)^n ≠ 1.
-/
lemma lehmer_term_ne_zero
    (α β : ℂ) (hne : α * β ≠ 0)
    (hrat : ¬ IsRootOfUnity' (α / β))
    (n : ℕ) (hn : 0 < n) :
    lehmer_term_complex α β n ≠ 0 := by
  contrapose! hrat; unfold IsRootOfUnity' at *; simp_all +decide [ div_eq_iff ] ;
  unfold lehmer_term_complex at hrat;
  split_ifs at hrat <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · cases' hrat with hrat hrat <;> use n <;> simp_all +decide [ div_pow, hn.ne' ];
  · cases' hrat with hrat hrat <;> [ refine' ⟨ n, hn, _ ⟩ ; refine' ⟨ 2, by decide, _ ⟩ ] <;> simp_all +decide [ div_pow, ← mul_pow ]

/-- **BHV primitive part bound**: For n > 30, there exists an integer P with
|P| > 1 that divides U_n and all of whose prime factors are primitive
divisors of U_n.

This is the core of the Bilu-Hanrot-Voutier theorem. It combines:
- The cyclotomic factorization U_n = ∏_{d|n} Φ*_d(α,β)
- Baker's lower bound on |Φ*_n(α,β)| showing it exceeds 1 for n > 30
- The fact that prime factors of Φ*_n are primitive for U_n -/
lemma lehmer_primitive_part_nontrivial
    (α β : ℂ) (hα : α + β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ : α * β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hne : α * β ≠ 0)
    (hrat : ¬ IsRootOfUnity' (α / β))
    (n : ℕ) (hn : 30 < n) :
    ∃ P : ℤ, 1 < P.natAbs ∧ P ∣ lehmer_term α β n ∧
      ∀ q : ℕ, q.Prime → (q : ℤ) ∣ P →
        ∀ m, 0 < m → m < n → ¬ ((q : ℤ) ∣ lehmer_term α β m) := by
  sorry

/-! ## Main Theorem -/

/-- **Erdős 1052 / Wall k=3**: For every Lehmer pair (α,β) and every n > 30
with 3 ∣ n, the Lehmer number U_n has a primitive prime divisor.

**Proof**: By `lehmer_primitive_part_nontrivial`, the primitive part
P = Φ*_n(α,β) satisfies |P| > 1 for n > 30. Since |P| > 1, P has a prime
factor q (by `Int.exists_prime_and_dvd`). This q is a ℕ-prime that divides
U_n (since P ∣ U_n) and is primitive (by the property of P).

Note: The hypothesis `h3 : 3 ∣ n` is not needed for the proof (the BHV theorem
holds for ALL n > 30), but is included to match the k=3 stratum statement. -/
theorem erdos_1052_wall_k3
    (α β : ℂ) (hα : α + β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ : α * β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hne : α * β ≠ 0)
    (hrat : ¬ IsRootOfUnity' (α / β))
    (n : ℕ) (hn : 30 < n) (h3 : 3 ∣ n) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ lehmer_term α β n ∧
      ∀ m, 0 < m → m < n → ¬ ((q : ℤ) ∣ lehmer_term α β m) := by
  -- Step 1: Obtain the primitive part with |P| > 1
  obtain ⟨P, hP_large, hP_dvd, hP_prim⟩ :=
    lehmer_primitive_part_nontrivial α β hα hαβ hne hrat n hn
  -- Step 2: Since |P| > 1, P has a prime factor in ℤ
  obtain ⟨p, hp_prime, hp_dvd_P⟩ := Int.exists_prime_and_dvd (by omega : P.natAbs ≠ 1)
  -- Step 3: Convert to a ℕ-prime and verify all conditions
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp hp_prime, ?_, ?_⟩
  · -- p.natAbs divides U_n since p | P and P | U_n
    exact dvd_trans (Int.natAbs_dvd.mpr hp_dvd_P) hP_dvd
  · -- p.natAbs is primitive: it doesn't divide U_m for 0 < m < n
    intro m hm_pos hm_lt hm_dvd
    exact hP_prim p.natAbs (Int.prime_iff_natAbs_prime.mp hp_prime)
      (Int.natAbs_dvd.mpr hp_dvd_P) m hm_pos hm_lt hm_dvd