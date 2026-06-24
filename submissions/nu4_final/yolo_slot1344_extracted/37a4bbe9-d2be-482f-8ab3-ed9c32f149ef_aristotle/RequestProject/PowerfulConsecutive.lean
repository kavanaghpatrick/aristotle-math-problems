import Mathlib

/-!
# Infinitely many consecutive powerful number pairs

A natural number `n` is *powerful* if every prime `p` dividing `n` satisfies `p² ∣ n`.
We show that the set `{n : ℕ | Powerful' n ∧ Powerful' (n+1)}` is infinite.

## Strategy

Use the Pell equation `x² - 8y² = 1`. For any solution `(x, y)`:
- `8y²` is powerful (the only prime factor beyond those of `y` is `2`, which appears to the 3rd power).
- `8y² + 1 = x²` is a perfect square, hence powerful.

The fundamental solution generates solutions with `y → ∞`, giving arbitrarily large `n = 8y²`.
-/

namespace Nat

/-- A natural number is powerful if every prime factor appears with exponent ≥ 2. -/
def Powerful' (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-
Perfect squares are powerful.
-/
lemma powerful_sq (n : ℕ) : Powerful' (n ^ 2) := by
  intro p pp dp;
  exact pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2

/-
`8 * n²` is powerful for any `n`.
-/
lemma powerful_eight_mul_sq (n : ℕ) : Powerful' (8 * n ^ 2) := by
  intro p pp; by_cases h : p = 2 <;> simp_all +decide [ Nat.Prime.dvd_mul ] ;
  · exact dvd_mul_of_dvd_left ( by decide ) _;
  · rintro ( h | h );
    · have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> trivial;
    · exact dvd_mul_of_dvd_right ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow h ) 2 ) _

end Nat

/-
8 is not a perfect square in ℤ.
-/
lemma not_isSquare_eight : ¬ IsSquare (8 : ℤ) := by
  native_decide +revert

/-
The Pell equation identity `x² - 8y² = 1` transferred to natural numbers via `natAbs`.
-/
lemma pell_eight_natAbs_identity (a : Pell.Solution₁ (8 : ℤ)) :
    a.x.natAbs ^ 2 = 8 * a.y.natAbs ^ 2 + 1 := by
      grind +suggestions

/-
A strictly monotone function `ℤ → ℤ` is unbounded above.
-/
lemma int_strictMono_unbounded {f : ℤ → ℤ} (hf : StrictMono f) :
    ∀ M : ℤ, ∃ k : ℤ, M < f k := by
      -- For a strictly monotone f : ℤ → ℤ, given M, we know f(M+1) > f(M), and by induction f(M+n) ≥ f(M) + n for all n ≥ 0.
      have h_ind : ∀ M : ℤ, ∀ n : ℕ, n ≥ 0 → f (M + n) ≥ f M + n := by
        intro M n; induction n <;> simp_all +decide [← add_assoc] ;
        linarith [ hf ( show M + ↑‹ℕ› < M + ↑‹ℕ› + 1 by linarith ) ];
      exact fun M => ⟨ _, by have := h_ind M ( Int.toNat ( M - f M + 1 ) ) ( by positivity ) ; linarith [ Int.self_le_toNat ( M - f M + 1 ) ] ⟩

/-
For every `N`, there exists `n > N` such that both `n` and `n + 1` are powerful.
Uses solutions to the Pell equation `x² - 8y² = 1`: if `(x,y)` is a solution,
then `n = 8y²` is powerful and `n + 1 = x²` is powerful.
-/
theorem powerful_consecutive_pairs_unbounded (N : ℕ) :
    ∃ n, N < n ∧ Nat.Powerful' n ∧ Nat.Powerful' (n + 1) := by
      by_contra! h_contra;
      -- By Pell's equation, there are infinitely many solutions � $(�x, y)$ such that $x^2 - � �8y^2 = 1$.
      obtain ⟨a₁, ha₁⟩ : ∃ a₁ : Pell.Solution₁ (8 : ℤ), Pell.IsFundamental a₁ := by
        exact Pell.IsFundamental.exists_of_not_isSquare ( by decide ) not_isSquare_eight;
      -- Use `int_strictMono �_un�bounded` with `ha₁.y_strictMono` and `M = ↑N` to get `k : ℤ` with `↑N < (a₁ ^ k).y`.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, ↑N < (a₁ ^ k).y := by
        exact int_strictMono_unbounded ha₁.y_strictMono N;
      -- Set `y := (a₁ ^ k).y.natAbs`. Note `(a₁^k).y > 0` (since `> ↑N ≥ 0`), so `y = (a₁^k).y.toNat` � and� `(↑y :) = (a₁^k).y`.
      set y := (a₁ ^ k).y.natAbs with hy
      have hy_pos : 0 < y := by
        exact Int.natAbs_pos.mpr ( by linarith )
      have hy_eq : (y : ℤ) = (a₁ ^ k).y := by
        grind +locals;
      -- Claim n = 8 * y ^ 2 works.
      have hn : N < 8 * y ^ 2 := by
        nlinarith
      have hn_powerful : Nat.Powerful' (8 * y ^ 2) := by
        exact Nat.powerful_eight_mul_sq y
      have hn1_powerful : Nat.Powerful' (8 * y ^ 2 + 1) := by
        convert Nat.powerful_sq ( Int.natAbs ( a₁ ^ k |> Pell.Solution₁.x ) ) using 1;
        nlinarith [ pell_eight_natAbs_identity ( a₁ ^ k ) ]
      exact h_contra (8 * y ^ 2) hn hn_powerful hn1_powerful

/-
The set of naturals `n` with both `n` and `n + 1` powerful is infinite.
-/
theorem powerful_consecutive_pairs_infinite :
    {n : ℕ | Nat.Powerful' n ∧ Nat.Powerful' (n + 1)}.Infinite := by
      exact Set.infinite_iff_exists_gt.mpr fun N => by rcases powerful_consecutive_pairs_unbounded N with ⟨ n, hn₁, hn₂, hn₃ ⟩ ; exact ⟨ n, ⟨ hn₂, hn₃ ⟩, hn₁ ⟩ ;