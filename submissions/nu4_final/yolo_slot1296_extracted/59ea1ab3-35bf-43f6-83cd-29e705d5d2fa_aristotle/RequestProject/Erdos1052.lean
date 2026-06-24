import Mathlib
import RequestProject.LucasU
import RequestProject.LucasV
import RequestProject.CyclotomicFactor

/-!
# Erdős Problem 1052 — Wall k=3: Lehmer/Lucas Primitive Divisor

## Statement

For every Lucas pair `(α, β)` with `α + β ∈ ℤ`, `α * β ∈ ℤ \ {0}`, and `α / β` not
a root of unity, and every `n > 30` with `3 ∣ n`, the Lucas term `U_n(α,β)` admits
a **primitive prime divisor**: a prime `q` dividing `U_n` but not `U_m` for any `0 < m < n`.

## Background

This is a consequence of the Bilu–Hanrot–Voutier theorem (2001), which resolved the
full primitive divisor problem for Lucas and Lehmer sequences: for `n > 30`, `U_n` always
has a primitive divisor (with finitely many known exceptions for `n ≤ 30`).

The proof requires Baker's theory of linear forms in logarithms of algebraic numbers,
which is not currently available in Mathlib. The formalization below defines the required
objects and states the theorem; the proof remains open in Lean.

## Status

**OPEN in Lean.** The proof requires:
- Baker's theory of linear forms in logarithms, OR
- Silverman's primitive divisor theorem for elliptic divisibility sequences
Neither is currently formalized in Mathlib.
-/

open Classical

/-- The Lehmer/Lucas term associated to complex algebraic integers `α, β`.
    When `α + β` and `α * β` are integers `P, Q` respectively, this returns
    the Lucas U-sequence value `U_n(P, Q)`. -/
noncomputable def lehmer_term (α β : ℂ) (n : ℕ) : ℤ :=
  let P : ℤ := if h : ∃ p : ℤ, (p : ℂ) = α + β then h.choose else 0
  let Q : ℤ := if h : ∃ q : ℤ, (q : ℂ) = α * β then h.choose else 0
  lucasU P Q n

/-- When `α + β = P` as integers, the P parameter is correctly extracted. -/
lemma lehmer_term_P_eq {α β : ℂ} {P : ℤ} (hP : (P : ℂ) = α + β) :
    (if h : ∃ p : ℤ, (p : ℂ) = α + β then h.choose else (0 : ℤ)) = P := by
  have hex : ∃ p : ℤ, (p : ℂ) = α + β := ⟨P, hP⟩
  simp [hex]
  have := hex.choose_spec
  exact_mod_cast Int.cast_injective (this.trans hP.symm)

/-- When `α * β = Q` as integers, the Q parameter is correctly extracted. -/
lemma lehmer_term_Q_eq {α β : ℂ} {Q : ℤ} (hQ : (Q : ℂ) = α * β) :
    (if h : ∃ q : ℤ, (q : ℂ) = α * β then h.choose else (0 : ℤ)) = Q := by
  have hex : ∃ q : ℤ, (q : ℂ) = α * β := ⟨Q, hQ⟩
  simp [hex]
  have := hex.choose_spec
  exact_mod_cast Int.cast_injective (this.trans hQ.symm)

/-- `lehmer_term` equals `lucasU P Q n` when `α + β = P` and `α * β = Q`. -/
lemma lehmer_term_eq_lucasU {α β : ℂ} {P Q : ℤ}
    (hP : (P : ℂ) = α + β) (hQ : (Q : ℂ) = α * β) (n : ℕ) :
    lehmer_term α β n = lucasU P Q n := by
  unfold lehmer_term
  have hP' := lehmer_term_P_eq hP
  have hQ' := lehmer_term_Q_eq hQ
  simp only [hP', hQ']

/-- A prime `q` is a **primitive prime divisor** of the integer sequence term `a_n`
    if `q ∣ a_n` but `q ∤ a_m` for all `0 < m < n`. -/
def IsPrimitivePrimeDivisor (a : ℕ → ℤ) (n : ℕ) (q : ℕ) : Prop :=
  q.Prime ∧ (q : ℤ) ∣ a n ∧ ∀ m, 0 < m → m < n → ¬ ((q : ℤ) ∣ a m)

/-- Under our hypotheses (α/β not a root of unity, αβ ≠ 0), the Lucas term U_n
    is nonzero for all n > 0. This follows because U_n = 0 iff (α/β)^n = 1. -/
lemma lehmer_term_ne_zero
    (α β : ℂ) (hα : α + β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ : α * β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ_ne : α * β ≠ 0)
    (hrat : ∀ k : ℕ, 0 < k → (α / β) ^ k ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    lehmer_term α β n ≠ 0 := by
  by_contra h_contra
  have h_div : (lucasU (hα.choose) (hαβ.choose) n :) = 0 := by
    grind +locals
  have h_div : (α ^ n - β ^ n) / (α - β) = 0 := by
    rw [← lucasU_eq_div_sub]
    rw [h_div, Int.cast_zero]
    · exact hα.choose_spec.symm
    · exact hαβ.choose_spec.symm
    · intro h; specialize hrat 1; simp_all +decide
  by_cases h : α = β <;> simp_all +decide [sub_eq_iff_eq_add]
  exact
    hrat n hn
      (by rw [div_pow, div_eq_iff (pow_ne_zero _ hαβ_ne.2)]; linear_combination' h_div)

/-- **Erdős Problem 1052 / Wall k=3 — Primitive Divisor Theorem (Lucas case)**

For every pair `(α, β)` of complex numbers with `α + β ∈ ℤ`, `αβ ∈ ℤ \ {0}`, and `α/β`
not a root of unity, and for every `n > 30` with `3 ∣ n`, the Lucas term `U_n` has a
primitive prime divisor.

This is a special case of the Bilu–Hanrot–Voutier theorem (2001). The k=3 stratum
(multiples of 3) is the simplest case of Wall's conjecture on periodic properties of
divisibility sequences.

**Status: OPEN in Lean** — requires Baker's theory of linear forms in logarithms or
equivalent deep number-theoretic machinery not yet available in Mathlib.
-/
theorem erdos_1052_wall_k3
    (α β : ℂ) (hα : α + β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ : α * β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ_ne : α * β ≠ 0)
    (hrat : ∀ k : ℕ, 0 < k → (α / β) ^ k ≠ 1)
    (n : ℕ) (hn : 30 < n) (h3 : 3 ∣ n) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ lehmer_term α β n ∧
      ∀ m, 0 < m → m < n → ¬ ((q : ℤ) ∣ lehmer_term α β m) := by
  sorry
