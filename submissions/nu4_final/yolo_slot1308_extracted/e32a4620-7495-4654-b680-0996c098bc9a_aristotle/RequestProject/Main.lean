import Mathlib

open scoped BigOperators
open Finset

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# Erdős Problem 672 (k=4, l=3)

For any positive integers n and d with gcd(n, d) = 1, the product
n(n+d)(n+2d)(n+3d) is never a perfect cube.

## References

* Hajdu, Tengely, Tijdeman (2009), "Cubes in products of terms in arithmetic progression"
* Győry, Hajdu, Pintér (2009), "Perfect powers from products of consecutive terms in
  arithmetic progression"

## Proof strategy

The proof has two main components:

### Component 1: Factorization and GCD analysis (proved)
The AP product n(n+d)(n+2d)(n+3d) factors as n(n+3d)·(n+d)(n+2d), and these two halves
have GCD dividing 2 when gcd(n,d) = 1. For primes p ≥ 5, at most one AP term is divisible
by p. Together, these facts constrain each AP term's cube-free part to involve only 2 and 3.

### Component 2: Key Diophantine lemma (open)
The factorization analysis (after case splits on factors of 2 and 3) reduces the problem
to showing x³ + y³ = 2z³ has only the trivial solution x = y = z. This is equivalent to
the rank-0 property of the elliptic curve X³ + Y³ = 2Z³ over ℚ.

### Gap: The key lemma requires Eisenstein integer descent
The proof of x³ + y³ = 2z³ ⟹ x = y requires descent in ℤ[ω] (Eisenstein integers),
extending the FLT for n=3 approach. While FLT for n=3 is in Mathlib
(`fermatLastTheoremThree`), its internal machinery (`FermatLastTheoremForThreeGen`)
handles a³ + b³ ≠ u·c³ only for *units* u in 𝒪_K. Since 2 is a prime (not a unit)
in ℤ[ω], a separate descent argument is needed. This descent is structurally similar
to the FLT proof but requires adapting the ℤ[ω] coprimality analysis for the factor of 2.
-/

section Identities

/-- Product identity: n(n+d)(n+2d)(n+3d) = (n²+3nd+d²)² - d⁴ -/
lemma ap_product_identity (n d : ℤ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) =
    (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 - d ^ 4 := by
  ring

/-- The AP product factors as n(n+3d) · (n+d)(n+2d) -/
lemma ap_product_factor (n d : ℤ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) =
    (n * (n + 3 * d)) * ((n + d) * (n + 2 * d)) := by
  ring

/-- The two halves of the factorization differ by 2d² -/
lemma ap_factor_diff (n d : ℤ) :
    (n + d) * (n + 2 * d) - n * (n + 3 * d) = 2 * d ^ 2 := by
  ring

/-- The product of the range simplifies to the explicit product -/
lemma prod_range_four (n d : ℕ) :
    (∏ i ∈ Finset.range 4, (n + i * d)) =
    n * (n + d) * (n + 2 * d) * (n + 3 * d) := by
  simp [Finset.prod_range_succ]

/-- The substitution identity for the half-sum/half-difference -/
lemma cube_sum_subst (u v : ℤ) :
    (u + v) ^ 3 + (u - v) ^ 3 = 2 * u * (u ^ 2 + 3 * v ^ 2) := by
  ring

end Identities

section FLT

/-- FLT for n=3 over ℤ: a³ + b³ ≠ c³ for nonzero integers.
    Proved by reduction to the ℕ version via sign analysis. -/
lemma flt_three_int (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  by_contra h_contra
  have h_abs :
      Int.natAbs a ^ 3 + Int.natAbs b ^ 3 = Int.natAbs c ^ 3 ∨
      Int.natAbs a ^ 3 + Int.natAbs c ^ 3 = Int.natAbs b ^ 3 ∨
      Int.natAbs b ^ 3 + Int.natAbs c ^ 3 = Int.natAbs a ^ 3 := by
    rw [← Int.natAbs_pow, ← Int.natAbs_pow, ← Int.natAbs_pow]
    grind
  have := fermatLastTheoremThree
  rcases h_abs with h | h | h <;>
    exact this _ _ _ (by positivity) (by positivity) (by positivity) h

end FLT

section KeyLemma

/-- Key number-theoretic lemma: x³ + y³ = 2z³ implies x = y for positive naturals.

    **Status: Open.** This requires Eisenstein integer descent, which extends the FLT
    for n=3 proof infrastructure but is not available in Mathlib.

    The proof would proceed as follows:
    1. WLOG gcd(x,y) = 1 (otherwise divide out and induct)
    2. Both x,y are odd (parity argument)
    3. Set u = (x+y)/2, v = (x-y)/2; then u(u²+3v²) = z³
    4. Factor u²+3v² = (u+v·ω·(ω-ω²)⁻¹)·(conjugate) in ℤ[ω]
    5. Analyze coprimality in ℤ[ω] (PID) to show factors are cubes
    6. Extract a strictly smaller solution, contradicting minimality -/
lemma sum_cubes_eq_double_cube {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : x = y := by
  sorry

end KeyLemma

section GCDAnalysis

/-- When gcd(n,d) = 1, the GCD of n(n+3d) and (n+d)(n+2d) divides 2.
    This follows because their difference is 2d² and gcd(n(n+3d), d) = 1. -/
lemma gcd_factor_dvd_two (n d : ℕ) (_hn : 0 < n) (_hd : 0 < d) (hcoprime : n.gcd d = 1) :
    (n * (n + 3 * d)).gcd ((n + d) * (n + 2 * d)) ∣ 2 := by
  have h_diff :
      Nat.gcd (n * (n + 3 * d)) ((n + d) * (n + 2 * d)) ∣ 2 * d ^ 2 := by
    convert Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _) using 1
    rw [Nat.sub_eq_of_eq_add]; ring
  refine Nat.Coprime.dvd_of_dvd_mul_right ?_ h_diff
  simp_all +decide [Nat.Coprime, Nat.gcd_comm]
  simp_all +decide [← Nat.gcd_assoc]
  simp_all +decide [Nat.coprime_mul_iff_left, Nat.Coprime, Nat.Coprime.symm]

/-- For primes p ≥ 5 not dividing d, at most one AP term is divisible by p.
    This is because if p | (n+id) and p | (n+jd), then p | (j-i)d, but
    p ∤ d and p > 3 ≥ j-i, so p ∤ (j-i), contradiction. -/
lemma ap_prime_divides_atmost_one {n d p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hpd : ¬(p ∣ d)) (_hcoprime : n.gcd d = 1) :
    ((Finset.range 4).filter (fun i => p ∣ (n + i * d))).card ≤ 1 := by
  by_contra h_contra
  obtain ⟨i, hi, j, hj, hij, h_div⟩ :
      ∃ i j, i < j ∧ i ∈ Finset.range 4 ∧ j ∈ Finset.range 4 ∧
      p ∣ n + i * d ∧ p ∣ n + j * d := by
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (lt_of_not_ge h_contra)
    cases lt_trichotomy i j <;> aesop
  have h_div_diff : p ∣ (hi - i) * d := by
    simpa [tsub_mul, add_tsub_add_eq_tsub_left] using Nat.dvd_sub h_div.2 h_div.1
  simp_all +decide [Nat.Prime.dvd_mul]
  exact absurd (Nat.le_of_dvd (Nat.sub_pos_of_lt j) h_div_diff) (by omega)

end GCDAnalysis

/-- **Erdős Problem 672 (k=4, l=3)**: For any positive integers n and d with gcd(n, d) = 1,
    the product n(n+d)(n+2d)(n+3d) is never a perfect cube.

    **Status: Open.** The proof infrastructure (algebraic identities, GCD analysis, FLT for
    n=3 over ℤ, prime divisibility bounds) is in place. The remaining gap is the key lemma
    `sum_cubes_eq_double_cube` (x³ + y³ = 2z³ ⟹ x = y), which requires Eisenstein integer
    descent not yet available in Mathlib.

    **Proof outline** (assuming `sum_cubes_eq_double_cube`):
    1. Factor the product as n(n+3d) · (n+d)(n+2d) via `ap_product_factor`
    2. Their GCD divides 2 by `gcd_factor_dvd_two`
    3. For primes p ≥ 5, p divides at most one AP term by `ap_prime_divides_atmost_one`
    4. Each term's cube-free part involves only primes 2 and 3 (9 possibilities per term)
    5. Case analysis on the 2,3-valuations yields equations of the form α³+δ³ = 2γ³
    6. By `sum_cubes_eq_double_cube`, α = δ, forcing d = 0, contradiction -/
theorem erdos_672_k4_l3 :
    ∀ n d : ℕ, n > 0 → d > 0 → n.gcd d = 1 →
    ¬ ∃ m : ℕ, (∏ i ∈ Finset.range 4, (n + i * d)) = m ^ 3 := by
  sorry
