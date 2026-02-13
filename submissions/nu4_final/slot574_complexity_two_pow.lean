/-
Integer Complexity: Is ‖2^n‖ = 2n for all n > 0?

This is an OPEN problem (answer unknown). The Mahler-Popken complexity of n
is the minimum number of 1s needed to express n using addition and multiplication.

It is known that ‖3^n‖ = 3n (Selfridge). The corresponding conjecture for 5 is
FALSE: 5^6 = 15625 = 1 + 2^3 * 3^2 * (1 + 2^3 * 3^3), giving ‖5^6‖ ≤ 29 < 30.

For powers of 2: ‖2^n‖ ≤ 2n is clear (just multiply n copies of 1+1).
The conjecture is that equality holds, i.e., no shortcut exists.

PROVIDED SOLUTION HINT: The upper bound ‖2^n‖ ≤ 2n follows from Reachable.pow.
For the lower bound, one approach is strong induction: if 2^n = a*b with a,b > 1,
then a = 2^i and b = 2^j with i+j = n, so complexity(a) + complexity(b) ≥ 2i + 2j = 2n
by induction. Similarly for 2^n = a + b. The key insight is that 2^n has no "shortcuts"
because its only factorizations are into smaller powers of 2.

Reference: MathOverflow 75792, OEIS A5245, arXiv:1207.4841
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

theorem Reachable.complexity {n : ℕ} (hn : 0 < n) : Reachable n (complexity n) := by
  unfold Mathoverflow75792.complexity
  rw [dif_neg (ne_of_gt hn)]
  exact Nat.find_spec _

theorem Reachable.pow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : Reachable (m ^ n) (m * n) := by
  induction hn with
  | refl => convert Reachable.self m hm <;> simp
  | step hn ih => exact .mul ih (.self m hm)

/-- Is ‖2^n‖ = 2n for all n > 0? This is an OPEN problem. -/
theorem complexity_two_pow : ∀ n : ℕ, 0 < n → complexity (2 ^ n) = 2 * n := by
  sorry

end Mathoverflow75792
