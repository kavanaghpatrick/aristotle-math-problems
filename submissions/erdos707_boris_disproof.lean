/-
Erdős Problem #707 - Embedding Sidon Sets in Perfect Difference Sets
DISPROVED by Boris Alexeev and Dustin G. Mixon (2025)

BORIS PATTERN MATCH:
- Pre-formalized in FC: ✅
- SOLVED (actually DISPROVED): ✅ (6 solved variants!)
- Undergraduate examples: ✅ (5!)
- No asymptotics: ✅
- Boris's own work: ✅ ← LITERALLY HIS SOLUTION

PROBLEM: Let A ⊆ ℕ be a finite Sidon set. Is there some set B with A ⊆ B
which is a perfect difference set modulo p² + p + 1 for some prime p?

ANSWER: FALSE - Counterexamples exist:
- {1, 2, 4, 8} cannot extend to any p²+p+1 modulus (Alexeev-Mixon 2025)
- {1, 2, 4, 8, 13} cannot extend to ANY perfect difference set
- {1, 3, 9, 10, 13} cannot extend (Hall 1947 - predates Erdős!)
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Function Set Finset

noncomputable section

namespace Erdos707

/-- A set A is a Sidon set if all pairwise sums are distinct -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d, a ∈ A → b ∈ A → c ∈ A → d ∈ A → a + b = c + d → ({a, b} : Set ℕ) = {c, d}

/-- A perfect difference set B modulo n has the property that every nonzero
    residue appears exactly once as a difference b - b' mod n -/
def IsPerfectDifferenceSet (B : Set ℕ) (n : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k < n →
    ∃! (p : ℕ × ℕ), p.1 ∈ B ∧ p.2 ∈ B ∧ (p.1 - p.2) % n = k

/--
The main theorem: It is FALSE that any finite Sidon set can be embedded
in a perfect difference set.

DISPROVED by Hall (1947), rediscovered by Alexeev-Mixon (2025).
-/
theorem erdos_707 : (∀ (A : Set ℕ) (h : A.Finite), IsSidon A →
    ∃ (B : Set ℕ) (n : ℕ), 0 < n ∧ A ⊆ B ∧ IsPerfectDifferenceSet B n) ↔ False := by
  sorry

/--
Counterexample from Hall (1947): {1, 3, 9, 10, 13} cannot extend to any
perfect difference set modulo any n.
-/
theorem erdos_707_counterexample_hall :
    let A : Set ℕ := {1, 3, 9, 10, 13}
    A.Finite ∧ IsSidon A ∧
    ∀ (B : Set ℕ) (n : ℕ), A ⊆ B → ¬IsPerfectDifferenceSet B n := by
  sorry

/--
Counterexample from Alexeev-Mixon (2025): {1, 2, 4, 8} cannot extend to a
perfect difference set modulo p² + p + 1 for any prime p.
-/
theorem erdos_707_counterexample_prime :
    let A : Set ℕ := {1, 2, 4, 8}
    A.Finite ∧ IsSidon A ∧
    ∀ (B : Set ℕ) (p : ℕ), Nat.Prime p → A ⊆ B →
      ¬IsPerfectDifferenceSet B (p^2 + p + 1) := by
  sorry

/--
Counterexample: {1, 2, 4, 8, 13} (Mian-Chowla prefix) cannot extend to
ANY perfect difference set.
-/
theorem erdos_707_counterexample_mian_chowla :
    let A : Set ℕ := {1, 2, 4, 8, 13}
    A.Finite ∧ IsSidon A ∧
    ∀ (B : Set ℕ) (n : ℕ), A ⊆ B → ¬IsPerfectDifferenceSet B n := by
  sorry

/-- The set {1, 2, 4} is a Sidon set -/
theorem sidon_124 : IsSidon ({1, 2, 4} : Set ℕ) := by
  sorry

/-- Small Sidon sets (size ≤ 3) CAN be embedded in perfect difference sets -/
theorem small_sidon_embeddable (A : Set ℕ) (hA : A.Finite) (h : A.ncard ≤ 3)
    (hSidon : IsSidon A) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ A ⊆ B ∧
      IsPerfectDifferenceSet B (p^2 + p + 1) := by
  sorry

end Erdos707
