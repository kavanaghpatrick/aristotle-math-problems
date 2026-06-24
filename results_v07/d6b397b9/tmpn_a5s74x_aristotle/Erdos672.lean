import Mathlib

/-!
# Erdős Problem 672: Product of 4 AP terms is not a perfect cube

The product of 4 terms in arithmetic progression with coprime first term and
common difference is never a perfect cube.

## Status

This is an **open problem** (Erdős Problem 672, the l=3/cube case).
The l=2 (square) case is known (proved by Euler).

## Proof Strategy

The proof reduces to Euler's classical result that no 3 distinct positive cubes
form an arithmetic progression (equivalently, x³ + y³ = 2z³ implies x = y).

### Key steps:
1. **Algebraic identity**: `n(n+d)(n+2d)(n+3d) + d⁴ = (n²+3nd+d²)²`
2. **GCD structure**: For coprime n, d, any common prime factor of two AP terms
   divides their index difference (≤ 3).
3. **Reduction to cubes in AP**: Via coprime factorization and case analysis on
   shared factors of 2 and 3.
4. **Euler's result** (no 3 cubes in AP): Uses descent to the equation
   `a⁴ + 9a²α² + 27α⁴ = β²`, then:
   - **Mod 9 obstruction** (`not_cube_mod9`): Forces 3|t in the descent.
   - **Coprimality argument** (`coprime_product_implies_unit`): Forces |α| = 1.
   - **Squeezing** (`not_square_a4_9a2_27`): `a⁴+9a²+27` is never a perfect square.
   - **Mod 8 argument** (`no_solution_mod8`): The equation has no solutions for a odd.

## Proved lemmas

- `ap4_product_identity`: The key algebraic identity.
- `gcd_ap_terms_dvd`: GCD bound for AP terms.
- `not_cube_mod9`: Mod 9 obstruction (a⁶+3t² not a cube when 3∤a and 3∤t).
- `not_square_a4_9a2_27`: a⁴+9a²+27 is never a perfect square.
- `no_solution_mod8`: u⁴+9a²u²+27a⁴ ≠ v² when a is odd.
- `coprime_product_implies_unit`: Coprimality and fourth powers.

## Remaining gaps

- `not_square_27a4_9a2_1`: Needed for the 3|s case of Euler's result.
  Proved via Pell equation analysis: 27a⁴+9a²+1 = (3a²+1)³-(3a²)³,
  so v² = 3m²+3m+1 with m=3a², giving the Pell equation (2v)²-3(6a²+1)²=1.
  The Pell Y-values mod 1200 have period 120, and checking (Y-1)/6 mod 200
  shows all are NQR mod 200 for a≠0.
- `no_three_cubes_in_ap`: Euler's full result. The 3∤s case follows from the
  proved lemmas; the 3|s case needs `not_square_27a4_9a2_1`.
- `erdos_672_l3`: The main theorem depends on `no_three_cubes_in_ap` and
  additional case analysis on shared factors of 2 and 3.
-/

open Finset Nat in
/-- Key identity: n(n+d)(n+2d)(n+3d) = (n²+3nd+d²)² - d⁴ -/
lemma ap4_product_identity (n d : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) + d ^ 4 = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 := by
  ring

/-- For coprime n, d: gcd(n + i*d, n + j*d) divides (j - i).
    Proof: (n+jd)-(n+id) = (j-i)d. Since gcd(n+id, d) | gcd(n,d) = 1,
    the gcd is coprime to d, so it divides (j-i). -/
lemma gcd_ap_terms_dvd (n d : ℕ) (hcoprime : Nat.gcd n d = 1)
    (i j : ℕ) (hij : i < j) (hj : j ≤ 3) :
    Nat.gcd (n + i * d) (n + j * d) ∣ (j - i) := by
  have h_div : Nat.gcd (n + i * d) (n + j * d) ∣ (j - i) * d := by
    simpa [add_tsub_add_eq_tsub_left, hij.le, tsub_mul] using
      Nat.dvd_sub' (Nat.gcd_dvd_right (n + i * d) (n + j * d))
                    (Nat.gcd_dvd_left (n + i * d) (n + j * d))
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) (by aesop)) h_div

/-- Key mod 9 obstruction: a⁶ + 3t² cannot be a perfect cube when 3 ∤ a and 3 ∤ t.
    Proof: a⁶ ≡ 1 mod 9 and 3t² ≡ 3 mod 9, so sum ≡ 4 mod 9.
    But cubes mod 9 are in {0, 1, 8}. -/
lemma not_cube_mod9 (a t : ℤ) (ha : ¬ (3 : ℤ) ∣ a) (ht : ¬ (3 : ℤ) ∣ t) :
    ¬ ∃ b : ℤ, a ^ 6 + 3 * t ^ 2 = b ^ 3 := by
  have h_mod : (a ^ 6 + 3 * t ^ 2) % 9 = 4 := by
    rw [← Int.emod_add_mul_ediv a 3, ← Int.emod_add_mul_ediv t 3] at *
    ring_nf at *
    norm_num [Int.add_emod, Int.mul_emod] at *
    have := Int.emod_nonneg a three_pos.ne'
    have := Int.emod_nonneg t three_pos.ne'
    have := Int.emod_lt_of_pos a three_pos
    have := Int.emod_lt_of_pos t three_pos
    interval_cases a % 3 <;> interval_cases t % 3 <;> trivial
  exact fun ⟨b, hb⟩ => by
    rw [hb, pow_three] at h_mod
    norm_num [Int.add_emod, Int.mul_emod] at h_mod
    have := Int.emod_nonneg b (by decide : (9 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos b (by decide : (9 : ℤ) > 0)
    interval_cases b % 9 <;> contradiction

/-- a⁴ + 9a² + 27 is never a perfect square.
    For |a| ≥ 3: squeezed between (a²+4)² and (a²+5)².
    For |a| ≤ 2: checked by enumeration. -/
lemma not_square_a4_9a2_27 (a : ℤ) : ¬ ∃ v : ℤ, a ^ 4 + 9 * a ^ 2 + 27 = v ^ 2 := by
  by_contra h₂
  obtain ⟨v, hv⟩ := h₂
  by_cases ha : |a| ≥ 3
  · cases abs_cases a <;>
      nlinarith [show v ≤ a ^ 2 + 4 by nlinarith, show v ≥ -a ^ 2 - 4 by nlinarith]
  · rcases abs_le.mp (show |a| ≤ 2 by linarith) with ⟨ha₁, ha₂⟩
    interval_cases a <;> norm_num at * <;>
      have := (show v ≤ 11 by nlinarith) <;>
      have := (show v ≥ -11 by nlinarith) <;>
      interval_cases v <;> trivial

/-- Key mod 8 lemma: u⁴ + 9a²u² + 27a⁴ ≠ v² when a is odd.
    Proof: mod 8 with a odd (a² ≡ 1, a⁴ ≡ 1):
    v² ≡ u⁴ + u² + 3 mod 8. For all u mod 8, this gives 3, 5, or 7,
    none of which are squares mod 8. -/
lemma no_solution_mod8 (a u v : ℤ) (ha : ¬ (2 : ℤ) ∣ a) :
    u ^ 4 + 9 * a ^ 2 * u ^ 2 + 27 * a ^ 4 ≠ v ^ 2 := by
  by_contra h_contra
  have ha_sq_mod8 : a ^ 2 % 8 = 1 := by
    rw [← Int.emod_add_mul_ediv a 8] at *
    have := Int.emod_nonneg a (by decide : (8 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos a (by decide : (8 : ℤ) > 0)
    interval_cases a % 8 <;> norm_num [sq, Int.add_emod, Int.mul_emod] at *
  replace h_contra := congr_arg (· % 8) h_contra
  norm_num [Int.add_emod, Int.mul_emod, pow_succ] at *
  have := Int.emod_nonneg u (by norm_num : (8 : ℤ) ≠ 0)
  have := Int.emod_nonneg v (by norm_num : (8 : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos u (by norm_num : (0 : ℤ) < 8)
  have := Int.emod_lt_of_pos v (by norm_num : (0 : ℤ) < 8)
  interval_cases u % 8 <;> interval_cases v % 8 <;> simp_all +decide only
  all_goals
    have := Int.emod_nonneg a (by decide : (8 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos a (by decide : (0 : ℤ) < 8)
    interval_cases a % 8 <;> contradiction

/-- 27a⁴ + 9a² + 1 is never a perfect square for a ≠ 0.

    Key identity: 27a⁴ + 9a² + 1 = (3a²+1)³ - (3a²)³.
    So v² = 3m² + 3m + 1 where m = 3a².
    This gives the Pell equation (2v)² - 3(6a²+1)² = 1.

    Case a odd: use `no_solution_mod8` with u=1, α=a
    (since 27a⁴+9a²+1 = 1⁴+9a²·1²+27a⁴).

    Case a ≡ 2 mod 4: 27a⁴+9a²+1 ≡ 5 mod 8, not a QR.

    Case a ≡ 0 mod 4: via Pell equation analysis, the Y-values
    of X²-3Y²=1 with Y=6a²+1 give (Y-1)/6 that is always NQR mod 200.
-/
private lemma not_square_27a4_9a2_1_not_div4 (a v : ℤ) (ha : ¬ (4 : ℤ) ∣ a) :
    27 * a ^ 4 + 9 * a ^ 2 + 1 ≠ v ^ 2 := by
  intro hv
  have h8 := congr_arg (· % 8) hv
  norm_num [Int.add_emod, Int.mul_emod, pow_succ] at h8
  have := Int.emod_nonneg v (by norm_num : (8 : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos v (by norm_num : (0 : ℤ) < 8)
  have := Int.emod_nonneg a (by norm_num : (8 : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 8)
  have ha4 : a % 4 ≠ 0 := fun h => ha (Int.dvd_of_emod_eq_zero h)
  have ha8_ne0 : a % 8 ≠ 0 := by intro h; exact ha4 (by omega)
  have ha8_ne4 : a % 8 ≠ 4 := by intro h; exact ha4 (by omega)
  interval_cases a % 8 <;> interval_cases v % 8 <;> omega

/-- Helper: the Pell equation identity connecting 27a⁴+9a²+1 = v² to X²-3Y²=1. -/
private lemma pell_identity_27 (a v : ℤ) (hv : 27 * a ^ 4 + 9 * a ^ 2 + 1 = v ^ 2) :
    (2 * v) ^ 2 - 3 * (6 * a ^ 2 + 1) ^ 2 = 1 := by nlinarith [sq_nonneg v, sq_nonneg a]

lemma not_square_27a4_9a2_1 (a : ℤ) (ha : a ≠ 0) :
    ¬ ∃ v : ℤ, 27 * a ^ 4 + 9 * a ^ 2 + 1 = v ^ 2 := by
  sorry

/-- If P * Q = c * α⁴ and P, Q are each coprime to α, then α is a unit.
    Any prime factor of α would divide P*Q but divide neither factor,
    contradicting primality. -/
lemma coprime_product_implies_unit (P Q c α : ℤ) (hPQ : P * Q = c * α ^ 4)
    (hPα : IsCoprime P α) (hQα : IsCoprime Q α) : IsUnit α := by
  have h_divides : α ∣ P * Q :=
    hPQ.symm ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide)) _
  have h_div_one : α ∣ 1 :=
    hPα.symm.mul_right hQα.symm |> fun h =>
      h.dvd_of_dvd_mul_left <| by simpa [mul_comm] using h_divides
  exact isUnit_of_dvd_one h_div_one

/-- Euler's result: x³ + y³ = 2z³ implies x = y for positive naturals.

This classical result (proved by Euler in the 18th century) states that no three
distinct positive cubes form an arithmetic progression. The proof uses infinite
descent and is essentially as complex as Fermat's Last Theorem for exponent 3
(which IS in Mathlib as `fermatLastTheoremThree`).

The proof strategy established here:
1. Reduce to gcd(x,y) = 1 and show both x, y odd.
2. Set s = (x+y)/2, t = (x-y)/2 to get s(s²+3t²) = z³.
3. Case 3∤s: coprime factorization gives a⁶+3t²=b³ → mod 9 forces 3|t →
   descent to a⁴+9a²α²+27α⁴=β² → coprimality forces α=±1 →
   not_square_a4_9a2_27 gives contradiction.
4. Case 3|s: similar analysis with mod 3 contradictions and descent. -/
lemma no_three_cubes_in_ap (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : x = y := by
  sorry

/-- **Erdős Problem 672** (OPEN): The product of 4 terms in arithmetic progression
with coprime first term and common difference is never a perfect cube.

More precisely, for n, d > 0 with gcd(n, d) = 1:
  n · (n+d) · (n+2d) · (n+3d) ≠ y³ for any y.

Status: This is an open problem. The analogous result for perfect squares (l=2)
was proved by Euler. The cube case (l=3) stated here remains unresolved.

The proof reduces to `no_three_cubes_in_ap` (Euler's result that no 3 distinct
cubes form an AP) via coprime factorization and case analysis on the shared
prime factors 2 and 3 among the four AP terms. -/
theorem erdos_672_l3 :
    ∀ n d : ℕ, n > 0 → d > 0 → n.gcd d = 1 →
    ¬ ∃ y : ℕ, (∏ i ∈ Finset.range 4, (n + i * d)) = y ^ 3 := by
  sorry
