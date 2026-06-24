import Mathlib

set_option maxHeartbeats 40000000 in
private lemma e647_witness_table : ∀ n ∈ Finset.Icc 3000 1000000,
    6 ∣ n → Nat.Prime (n - 1) → Nat.Prime ((n - 2) / 2) →
    Nat.Prime (((n - 2) / 2 - 1) / 2) →
    Nat.Prime ((2 * ((n - 2) / 2) - 1) / 3) →
    (n + 2 < (n - 5) + ArithmeticFunction.sigma 0 (n - 5)) ∨
    (n + 2 < (n - 6) + ArithmeticFunction.sigma 0 (n - 6)) := by
  native_decide

theorem erdos_647_residual_bounded_iter2
    (n : ℕ) (hn_lo : 3000 ≤ n) (hn_hi : n ≤ 1000000) (h6 : 6 ∣ n)
    (hp1 : Nat.Prime (n - 1)) (hq : Nat.Prime ((n - 2) / 2))
    (hr : Nat.Prime (((n - 2) / 2 - 1) / 2))
    (hp : Nat.Prime ((2 * ((n - 2) / 2) - 1) / 3)) :
    ∃ m : Fin n, n + 2 < (m : ℕ) + ArithmeticFunction.sigma 0 m := by
  have hmem : n ∈ Finset.Icc 3000 1000000 := Finset.mem_Icc.mpr ⟨hn_lo, hn_hi⟩
  have hw := e647_witness_table n hmem h6 hp1 hq hr hp
  rcases hw with h5 | h6
  · exact ⟨⟨n - 5, by omega⟩, h5⟩
  · exact ⟨⟨n - 6, by omega⟩, h6⟩
