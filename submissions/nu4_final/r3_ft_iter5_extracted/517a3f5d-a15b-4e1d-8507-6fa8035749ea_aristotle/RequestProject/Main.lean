import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

theorem feit_thompson_p3_q71_family_2000 :
    ∀ q : ℕ, q.Prime → 3 < q → q ≡ 71 [MOD 72] → q ≤ 2000 →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 := by
  intro q hprime hlt hmod hle
  have hq_bound : q ∈ Finset.range 2001 := by
    simp [Finset.mem_range]; omega
  suffices h : ∀ q ∈ Finset.range 2001,
    q.Prime → 3 < q → q % 72 = 71 → ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 by
    have hmod' : q % 72 = 71 := by
      have := hmod
      unfold Nat.ModEq at this
      simp at this
      exact this
    exact h q hq_bound hprime hlt hmod'
  native_decide
