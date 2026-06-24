/-
# Erdős Problem 1055 — Selfridge's bounded-class conjecture

A prime `p` has Erdős–Selfridge class 1 if every prime factor of `p + 1` lies in `{2, 3}`;
recursively, `p` has class `r` if every prime factor of `p + 1` has class `≤ r − 1`, with
equality for at least one factor.

More precisely, we define `selfridgeClass p` for prime `p` as:
  `1 + max{selfridgeClass q : q prime, q ∣ p + 1, q > 3}`
where the max of an empty set is 0. Non-primes are assigned class 0.

Let `p_r` be the least prime of class `r`. Selfridge conjectured that there exists a
uniform constant `M` such that `p_r^(1/r) ≤ M` for all `r`.

Numerically: p₁ = 2, p₂ = 13, p₃ = 37, p₄ = 73, ...

**Status: OPEN.** This conjecture cannot be resolved by finite computation; an
asymptotic argument controlling the growth of least-class-r primes is required.
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ## Definition of the Erdős–Selfridge class -/

/-- The Erdős–Selfridge class of a natural number.
For a prime `p`, this is `1 + sup{selfridgeClass q : q ∣ p+1, q prime, q > 3}`.
For non-primes, the class is defined to be `0`. -/
noncomputable def selfridgeClass (p : ℕ) : ℕ :=
  if Nat.Prime p then
    1 + ((p + 1).primeFactors.filter (· > 3)).sup (fun q =>
      if q < p then selfridgeClass q else 0)
  else 0
termination_by p

/-
A prime `p` has class 1 if and only if `p + 1` is 3-smooth
(all prime factors are at most 3).
-/
theorem selfridgeClass_eq_one_iff {p : ℕ} (hp : Nat.Prime p) :
    selfridgeClass p = 1 ↔ ∀ q ∈ (p + 1).primeFactors, q ≤ 3 := by
  constructor;
  · unfold selfridgeClass;
    contrapose!;
    norm_num +zetaDelta at *;
    intro q hq hq' hq''; split_ifs ;
    rcases hq' with ⟨ _ | _ | k, hk ⟩ <;> rcases p with ( _ | _ | p ) <;> simp_all +arith +decide;
    · cases Nat.Prime.eq_two_or_odd hp <;> cases Nat.Prime.eq_two_or_odd hq <;> omega;
    · grind +suggestions;
  · unfold selfridgeClass;
    split_ifs ; aesop

/-! ## Least prime of each class -/

/-- The least prime of Erdős–Selfridge class `r`, defined as the infimum of the set
of primes with that class. Returns `0` if the set is empty. -/
noncomputable def leastPrimeOfClass (r : ℕ) : ℕ :=
  sInf {p | Nat.Prime p ∧ selfridgeClass p = r}

/-! ## The conjecture -/

/-- **Selfridge's bounded-class conjecture** (Erdős Problem 1055).

There exists a uniform constant `M` such that for every positive natural number `r`,
if there exists a prime of Selfridge class `r`, then the least such prime `p_r`
satisfies `p_r^{1/r} ≤ M`.

Note: Erdős conjectured the opposite — that `p_r^{1/r} → ∞` as `r → ∞`.

**Status: OPEN.** -/
theorem selfridge_limit :
    ∃ M : ℝ, ∀ r : ℕ, r ≥ 1 →
      (∀ p, Nat.Prime p → selfridgeClass p ≠ r) ∨
      ((leastPrimeOfClass r : ℝ) ^ ((1 : ℝ) / (r : ℝ)) ≤ M) := by
  sorry