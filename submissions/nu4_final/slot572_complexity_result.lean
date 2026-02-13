/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7bddba3e-e710-4871-b04f-284b713ac210

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Integer Complexity: complexity(1) = 1 and complexity(2) = 2

The Mahler-Popken complexity of n is the minimum number of 1s needed to
express n using addition and multiplication.

Reference: MathOverflow 75792, OEIS A5245
-/

import Mathlib


namespace Mathoverflow75792

/-- The inductively defined predicate that `m` is reachable in `n` steps. -/
inductive Reachable : ℕ → ℕ → Prop
  | one : Reachable 1 1
  | add {m n a b} : Reachable m a → Reachable n b → Reachable (m + n) (a + b)
  | mul {m n a b} : Reachable m a → Reachable n b → Reachable (m * n) (a + b)

theorem not_reachable_zero_fst (n : ℕ) : ¬ Reachable 0 n := by
  intro h; generalize hm : 0 = m at h; induction h with
  | one => exact absurd hm (by decide)
  | add h₁ h₂ => rw [eq_comm, add_eq_zero] at hm; aesop
  | mul h₁ h₂ => rw [eq_comm, mul_eq_zero] at hm; aesop

theorem not_reachable_zero_snd (m : ℕ) : ¬ Reachable m 0 := by
  intro h; generalize hn : 0 = n at h; induction h with
  | one => exact absurd hn (by decide)
  | add h₁ h₂ => rw [eq_comm, add_eq_zero] at hn; aesop
  | mul h₁ h₂ => rw [eq_comm, add_eq_zero] at hn; aesop

theorem Reachable.dec {m n : ℕ} (h : Reachable m n) :
    ∃ m' n', m' + 1 = m ∧ n' + 1 = n := by
  obtain _ | m := m
  · exact absurd h (not_reachable_zero_fst _)
  obtain _ | n := n
  · exact absurd h (not_reachable_zero_snd _)
  exact ⟨_, _, rfl, rfl⟩

theorem Reachable.le {m n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (hm : Reachable m n₁) : Reachable m n₂ := by
  induction hn with
  | refl => exact hm
  | step h ih => convert ih.mul .one; simp

theorem Reachable.self (n : ℕ) (hn : 0 < n) : Reachable n n :=
  Nat.le_induction .one (fun _ _ ih ↦ .add ih .one) n hn

theorem reachable_iff_of_two_le (m n : ℕ) (hm : 2 ≤ m) :
    Reachable m n ↔ ∃ m₁, ∃ _ : m₁ < m, ∃ m₂, ∃ _ : m₂ < m, ∃ n₁, ∃ _ : n₁ < n, ∃ n₂, ∃ _ : n₂ < n,
      n₁ + n₂ = n ∧ Reachable m₁ n₁ ∧ Reachable m₂ n₂ ∧ (m₁ + m₂ = m ∨ m₁ * m₂ = m) := by
  refine ⟨fun hmn ↦ ?_, fun ⟨m₁, hm₁, m₂, hm₂, n₁, hn₁, n₂, hn₂, h₁, h₂, h₃, h₄⟩ ↦
    h₁ ▸ h₄.casesOn (· ▸ .add h₂ h₃) (· ▸ .mul h₂ h₃)⟩
  induction hmn with
  | one => exact absurd hm (by decide)
  | @add m₃ m₄ n₃ n₄ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨m₃, n₃, rfl, rfl⟩ := h₁.dec
      obtain ⟨m₄, n₄, rfl, rfl⟩ := h₂.dec
      refine ⟨m₃ + 1, ?_, m₄ + 1, ?_, n₃ + 1, ?_, n₄ + 1, ?_, rfl, h₁, h₂, .inl rfl⟩ <;> omega
  | @mul m₃ m₄ n₃ n₄ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨m₃, n₃, rfl, rfl⟩ := h₁.dec
      obtain ⟨m₄, n₄, rfl, rfl⟩ := h₂.dec
      obtain _ | m₃ := m₃
      · obtain ⟨m₅, hm₅, m₆, hm₆, n₅, hn₅, n₆, hn₆, h₃, h₄, h₅, h₆⟩ := ih₂ (by omega)
        refine ⟨m₅, ?_, m₆, ?_, n₅+n₃+1, ?_, n₆, ?_, by rw [← h₃]; ring, h₄.le ?_, h₅, ?_⟩
        all_goals omega
      obtain _ | m₄ := m₄
      · obtain ⟨m₅, hm₅, m₆, hm₆, n₅, hn₅, n₆, hn₆, h₃, h₄, h₅, h₆⟩ := ih₁ (by omega)
        refine ⟨m₅, ?_, m₆, ?_, n₅, ?_, n₆+n₄+1, ?_, by rw [← h₃]; ring, h₄, h₅.le ?_, ?_⟩
        all_goals omega
      refine ⟨m₃+2, ?_, m₄+2, ?_, _, ?_, _, ?_, rfl, h₁, h₂, .inr rfl⟩
      · refine (Nat.lt_mul_iff_one_lt_right ?_).2 ?_ <;> omega
      · refine (Nat.lt_mul_iff_one_lt_left ?_).2 ?_ <;> omega
      all_goals omega

instance Reachable.decide : ∀ m n, Decidable (Reachable m n)
  | 0, n => isFalse (not_reachable_zero_fst n)
  | 1, 0 => isFalse (not_reachable_zero_snd 1)
  | 1, n+1 => isTrue (Reachable.one.le (by omega))
  | m+2, n => by
      let d : ∀ {m₁} (h : m₁ < m + 2) {n}, Decidable (Reachable m₁ n) :=
        fun h ↦ Reachable.decide _ _
      refine @decidable_of_iff' _ _ (reachable_iff_of_two_le (m+2) n (by omega)) ?_
      refine Nat.decidableExistsLT' (I := fun m₁ hm₁ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun m₂ hm₂ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun n₁ hn₁ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun n₂ hn₂ ↦ ?_)
      refine instDecidableAnd (dq := ?_)
      refine instDecidableAnd (dp := d hm₁) (dq := ?_)
      exact instDecidableAnd (dp := d hm₂)

/-- The complexity of n: minimum number of 1s to express n using + and ×. -/
def complexity (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else Nat.find ⟨n, Reachable.self n <| n.pos_of_ne_zero h⟩

theorem Reachable.complexity_le {m n : ℕ} (h : Reachable m n) : complexity m ≤ n := by
  unfold complexity
  split_ifs with h'
  · subst h'; exact absurd h (not_reachable_zero_fst n)
  exact Nat.find_min' _ h

theorem Reachable.complexity_eq {m n : ℕ} (h : Reachable m n)
    (min : ∀ n' < n, ¬ Reachable m n') : complexity m = n := by
  refine le_antisymm h.complexity_le ?_
  unfold complexity
  split_ifs with h'
  · subst h'; exact absurd h (not_reachable_zero_fst n)
  exact (Nat.le_find_iff _ _).2 min

/-- The complexity of 1 is 1: we need exactly one '1'. -/
theorem complexity_one : complexity 1 = 1 := by
  apply Reachable.complexity_eq
  · exact .one
  · intro n hn
    interval_cases n
    exact not_reachable_zero_snd 1

/-- The complexity of 2 is 2: we need exactly two '1's (2 = 1 + 1). -/
theorem complexity_two : complexity 2 = 2 := by
  apply Reachable.complexity_eq
  · exact .add .one .one
  · intro n hn
    interval_cases n
    · exact not_reachable_zero_snd 2
    · intro h
      have := h.dec
      obtain ⟨m', n', hm', hn'⟩ := this
      omega

end Mathoverflow75792