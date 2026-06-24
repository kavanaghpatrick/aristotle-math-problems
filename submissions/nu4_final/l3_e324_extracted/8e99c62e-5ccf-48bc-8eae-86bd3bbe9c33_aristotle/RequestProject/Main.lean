import Mathlib

set_option maxHeartbeats 8000000

theorem erdos_324_quintic_bounded :
    ∀ a b c d : ℕ, a < b → c < d →
      a ≤ 50 → b ≤ 50 → c ≤ 50 → d ≤ 50 →
      a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5 → a = c ∧ b = d := by
  -- Reduce to a decidable finite check over Fin 51
  suffices h : ∀ a b c d : Fin 51, a < b → c < d →
      (a : ℕ) ^ 5 + (b : ℕ) ^ 5 = (c : ℕ) ^ 5 + (d : ℕ) ^ 5 → a = c ∧ b = d by
    intro a b c d hab hcd ha hb hc hd heq
    have ha' : a < 51 := by omega
    have hb' : b < 51 := by omega
    have hc' : c < 51 := by omega
    have hd' : d < 51 := by omega
    have := h ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨c, hc'⟩ ⟨d, hd'⟩ hab hcd heq
    exact ⟨congrArg Fin.val this.1, congrArg Fin.val this.2⟩
  native_decide
