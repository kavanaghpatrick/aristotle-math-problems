import Mathlib

/-!
# No three positive cubes in arithmetic progression (Erdős 672)

This is a classical result due to Euler: if x³ + y³ = 2z³ with x, y, z > 0,
then x = y (= z).

## Status
The main theorem `no_three_cubes_in_ap` is reduced to `descent_step`,
the key descent lemma. The descent step requires factorization in the
Eisenstein integers ℤ[ζ₃] (a PID, whose properties are available in
Mathlib via `IsCyclotomicExtension.Rat.three_pid`).

## References
- Euler's original proof (1770)
- Hardy & Wright, "An Introduction to the Theory of Numbers", §13.5
- Edwards, "Fermat's Last Theorem", Chapter 2
-/

/-! ## Helper lemmas -/

/-- If d divides both x and y, and x³ + y³ = 2z³, then d divides z. -/
lemma div_z_of_div_xy {x y z d : ℕ} (hx : d ∣ x) (hy : d ∣ y)
    (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : d ∣ z := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨m, hm⟩ := hy
  have h_div : d ^ 3 ∣ 2 * z ^ 3 := h ▸ ⟨k ^ 3 + m ^ 3, by rw [hk, hm]; ring⟩
  by_contra h_not_div_z
  obtain ⟨p, hp_prime, hp_val⟩ : ∃ p : ℕ, Nat.Prime p ∧
      (Nat.factorization d) p > (Nat.factorization z) p := by
    exact not_forall_not.mp fun h => h_not_div_z <|
      Nat.factorization_le_iff_dvd (by aesop) (by aesop) |>.1 <|
      fun p => by by_cases hp : Nat.Prime p <;> aesop
  have h_contra : (Nat.factorization (2 * z ^ 3)) p < 3 * (Nat.factorization d) p := by
    rcases eq_or_ne z 0 <;> simp_all +decide [Nat.factorization_mul]
    by_cases h : 2 = p <;> simp_all +decide; linarith
  exact h_contra.not_le (by rw [← Nat.factorization_le_iff_dvd] at h_div <;> aesop)

/-- If gcd(x,y) = 1 and x³ + y³ = 2z³, then x and y are both odd. -/
lemma both_odd_of_coprime {x y z : ℕ} (hx : x > 0) (hy : y > 0)
    (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) (hcop : Nat.Coprime x y) :
    ¬ 2 ∣ x ∧ ¬ 2 ∣ y := by
  constructor <;> intro h2 <;> replace h := congr_arg Even h <;>
    simp_all +decide [← even_iff_two_dvd, parity_simps]
  · exact absurd (Nat.dvd_gcd (even_iff_two_dvd.mp h2) (even_iff_two_dvd.mp h)) (by aesop)
  · exact absurd (Nat.dvd_gcd (even_iff_two_dvd.mp h) (even_iff_two_dvd.mp h2)) (by aesop)

/-! ## The descent step

This is the hardest part of the proof. It requires showing that any
coprime solution (x,y,z) with x ≠ y gives rise to a strictly smaller
solution. The classical proof uses:

1. Substitution: s = (x+y)/2, t = (x-y)/2 → s(s²+3t²) = z³
2. Coprimality analysis: gcd(s, s²+3t²) | 3
3. Cube extraction: s and s²+3t² are both cubes (in the coprime case)
4. Factorization in ℤ[ζ₃] (Eisenstein integers, a PID):
   u⁶+3t² = v³ → parameterization by (c,d) with v = c²-cd+d²
5. New equation: 2u³ = (c+d)(2c-d)(c-2d) → new x'³+y'³=2z'³
6. Descent: z' < z

The factorization step (4) requires unique factorization in ℤ[ζ₃],
which is available in Mathlib as `IsCyclotomicExtension.Rat.three_pid`.
-/

/-- **Descent step**: any nontrivial coprime solution yields a strictly
smaller nontrivial one. This is the core of Euler's theorem.

The proof requires factorization in the Eisenstein integers ℤ[ζ₃].
See the module docstring for a detailed outline. -/
lemma descent_step (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) (hcop : Nat.Coprime x y) (hne : x ≠ y) :
    ∃ x' y' z' : ℕ, x' > 0 ∧ y' > 0 ∧ z' > 0 ∧
      x' ^ 3 + y' ^ 3 = 2 * z' ^ 3 ∧ x' ≠ y' ∧ z' < z := by
  sorry

/-! ## Main theorem -/

/-- **No three distinct positive cubes form an arithmetic progression.**

Equivalently: x³ + y³ = 2z³ with x, y, z > 0 implies x = y.

This is the key reduction for Erdős Problem 672 (product of 4 coprime
AP terms is never a cube). The proof uses infinite descent: by
`descent_step`, any nontrivial coprime solution would yield an infinite
descending chain of solutions, contradicting well-foundedness of ℕ.
The non-coprime case reduces to the coprime case by dividing out gcd. -/
theorem no_three_cubes_in_ap (x y z : ℕ)
    (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : x = y := by
  induction' z using Nat.strong_induction_on with z ih generalizing x y
  by_cases hxy : x = y
  · exact hxy
  · obtain ⟨d, hd_pos, hd_div_x, hd_div_y⟩ : ∃ d, d > 1 ∧ d ∣ x ∧ d ∣ y := by
      by_cases h_coprime : Nat.Coprime x y
      · obtain ⟨x', y', z', hx', hy', hz', h_eq', h_ne', h_lt⟩ :=
          descent_step x y z hx hy hz h h_coprime hxy
        exact absurd (ih z' h_lt x' y' hx' hy' hz' h_eq') h_ne'
      · exact ⟨_, lt_of_le_of_ne (Nat.gcd_pos_of_pos_left _ hx) (Ne.symm h_coprime),
          Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩
    have hd_div_z : d ∣ z := div_z_of_div_xy hd_div_x hd_div_y h
    obtain ⟨k, hk⟩ := hd_div_x; obtain ⟨l, hl⟩ := hd_div_y; obtain ⟨m, hm⟩ := hd_div_z
    simp_all +decide [mul_pow]
    exact hxy.1 (ih m (by nlinarith [pow_pos hx.1 3]) k l hx.2 hy hz
      (by nlinarith [pow_pos hx.1 3]))
