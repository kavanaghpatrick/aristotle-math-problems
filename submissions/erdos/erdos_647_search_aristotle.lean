/-
Erdős Problem #647 – search + divergence scaffolding for Aristotle.

Key idea: provide a tiny amount of computable evidence plus structural lemmas
showing that failures occur infinitely often.  The only sorry is the main
theorem `Erdos647.erdos_647`, so Aristotle can focus all search time there.
-/

import Mathlib

open scoped BigOperators

namespace Erdos647

/-- Number of positive divisors of `n`. Helper used instead of arithmetic
functions so that `native_decide` can evaluate small cases. -/
def tau (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun d => 0 < d ∧ d ∣ n).card

/-- Target property from the original problem statement. -/
def erdos647_property (n : ℕ) : Prop :=
  ∀ m < n, m + tau m ≤ n + 2

/-- Boolean checker used for small-range certificates. -/
def erdos647_check (n : ℕ) : Bool :=
  (Finset.range n).all fun m => m + tau m ≤ n + 2

/-- Exhaustive search for witnesses in `[lo, hi]`. -/
def find_erdos647_witness (lo hi : ℕ) : Option ℕ :=
  ((List.range (hi + 1)).filter fun n => lo ≤ n).find? fun n =>
    decide (erdos647_property n)

lemma one_mem_filter {n : ℕ} (hn : 0 < n) :
    1 ∈ (Finset.range (n + 1)).filter (fun d => 0 < d ∧ d ∣ n) := by
  refine Finset.mem_filter.mpr ?_
  have : 1 < n + 1 := by exact Nat.succ_lt_succ hn
  exact ⟨Finset.mem_range.mpr this, by simpa⟩

lemma tau_pos_of_pos {n : ℕ} (hn : 0 < n) : 1 ≤ tau n := by
  classical
  have hmem := one_mem_filter (n := n) hn
  have : 0 < ((Finset.range (n + 1)).filter _).card :=
    by simpa [tau] using Finset.card_pos.mpr ⟨1, hmem⟩
  simpa [tau] using Nat.succ_le_of_lt this

lemma tau_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ tau n := by
  classical
  have hpos : 0 < n := lt_of_le_of_lt hn (by decide : 2 < 3)
  let S : Finset ℕ := ({1} : Finset ℕ).insert n
  have hSsubset :
      S ⊆ (Finset.range (n + 1)).filter fun d => 0 < d ∧ d ∣ n := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | h1
    · have hmem :
        n ∈ (Finset.range (n + 1)).filter fun d => 0 < d ∧ d ∣ n := by
          refine Finset.mem_filter.mpr ?_
          exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self _),
            ⟨hpos, Nat.dvd_refl _⟩⟩
      simpa using hmem
    · simpa using one_mem_filter hpos
  have htwo : S.card = 2 := by
    have : n ≠ 1 := by exact ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hn)
    simp [S, this]
  have hsubset := Finset.card_le_of_subset hSsubset
  simpa [tau, htwo]

lemma tau_pos {n : ℕ} (hn : 0 < n) : 0 < tau n :=
  lt_of_lt_of_le (by decide : 0 < 1) (tau_pos_of_pos hn)

lemma exists_large_m_plus_tau {n : ℕ} (hn : 2 ≤ n) :
    ∃ m < n, m + tau m ≥ n := by
  have hpos : 0 < n := lt_of_le_of_lt hn (by decide : 2 < 3)
  refine ⟨n - 1, ?_, ?_⟩
  · have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    simpa [hpred] using Nat.lt_succ_self (n - 1)
  have hmpos : 0 < n - 1 := Nat.sub_pos_of_lt hn
  have hτ : 1 ≤ tau (n - 1) := tau_pos_of_pos hmpos
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hmpos)
  have := add_le_add_left hτ (n - 1)
  simpa [tau, hpred] using this

lemma tau_mul_four (k : ℕ) (hk : 2 ≤ k) : 4 ≤ tau (k * (k + 1)) := by
  classical
  let S : Finset ℕ :=
    ({1} : Finset ℕ).insert k |>.insert (k + 1) |>.insert (k * (k + 1))
  have hkpos : 0 < k := lt_of_le_of_lt hk (by decide)
  have hmem
      (x : ℕ) (hx : x ∈ ({k, k + 1, k * (k + 1)} : Finset ℕ)) :
      x ∈ (Finset.range (k * (k + 1) + 1)).filter
        (fun d => 0 < d ∧ d ∣ k * (k + 1)) := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine Finset.mem_filter.mpr ?_
      have hkn : k ≤ k * (k + 1) :=
        le_mul_of_pos_right (Nat.succ_le_succ hk) (Nat.succ_pos _)
      exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt hkn (Nat.lt_succ_self _)),
        by refine ⟨hkpos, ?_⟩; exact dvd_mul_of_dvd_left (dvd_refl _) _⟩
    · rcases Finset.mem_insert.mp hx with rfl | hx'
      · refine Finset.mem_filter.mpr ?_
        have hk1 : 0 < k + 1 := Nat.succ_pos _
        have hk1le : k + 1 ≤ k * (k + 1) := by
          simpa using Nat.mul_le_mul_left _ (Nat.succ_le_succ hk)
        exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt hk1le (Nat.lt_succ_self _)),
          by refine ⟨hk1, ?_⟩; exact dvd_mul_of_dvd_right (dvd_refl _) _⟩
      · simpa using Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_self _),
            ⟨Nat.mul_pos (Nat.succ_pos _) hkpos, dvd_rfl⟩⟩
  have hsubset :
      S ⊆ (Finset.range (k * (k + 1) + 1)).filter
        (fun d => 0 < d ∧ d ∣ k * (k + 1)) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_self _),
          ⟨Nat.mul_pos (Nat.succ_pos _) (show 0 < k + 1 by exact Nat.succ_pos _),
            dvd_rfl⟩⟩
    · exact hmem _ hx'
  have hcard : S.card = 4 := by
    have hkne : k ≠ 1 := by exact ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hk)
    have hk1ne : k + 1 ≠ 1 := by exact Nat.succ_ne_self k ▸ by decide
    have hk1k : k + 1 ≠ k := by exact Nat.succ_ne_self _
    have htop : k * (k + 1) ∉ ({1, k, k + 1} : Finset ℕ) := by
      intro h; rcases Finset.mem_insert.mp h with h | h
      · exact (Nat.mul_pos (Nat.succ_pos _) hkpos).ne' (by simpa)
      · rcases Finset.mem_insert.mp h with h | h
        · exact hkne (by simpa using h)
        · exact hk1k (by simpa using h)
    simp [S, hkne, hk1ne, hk1k, htop]
  have hsubset' := Finset.card_le_of_subset hsubset
  simpa [tau, hcard]

lemma failure_construction {m : ℕ} (hm : 4 ≤ tau m) :
    ¬ erdos647_property (m + tau m - 3) := by
  intro hprop
  have hpos : 1 ≤ tau m := le_trans (by decide : 1 ≤ 4) hm
  have hlt : m < m + tau m - 3 := by
    have : 1 ≤ tau m - 3 := Nat.sub_le_sub_right hm 3
    have := Nat.lt_of_lt_of_le (by decide : 0 < 1) this
    simpa [Nat.add_sub_cancel, Nat.sub_eq, Nat.add_comm] using
      add_lt_add_left this m
  have h := hprop m hlt
  have : m + tau m = (m + tau m - 3) + 3 := by
    have := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hcontr : (m + tau m - 3) + 3 ≤ (m + tau m - 3) + 2 :=
    by simpa [this] using h
  exact lt_irrefl _ (lt_of_le_of_lt hcontr (by decide))

lemma infinite_range_of_unbounded {f : ℕ → ℕ}
    (h : ∀ B : ℕ, ∃ k, B < f k) : (Set.range f).Infinite := by
  classical
  by_contra hfin
  have hnonempty : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  let s := hfin.toFinset
  have hsnonempty : s.Nonempty := by
    rcases hnonempty with ⟨y, hy⟩
    exact ⟨y, by simpa [s] using Set.mem_toFinset.mpr hy⟩
  let M := s.max' hsnonempty
  have hbound :
      ∀ y ∈ Set.range f, y ≤ M := by
    intro y hy
    have : y ∈ s := by simpa [s] using Set.mem_toFinset.mpr hy
    exact Finset.le_max' _ _ this
  obtain ⟨k, hk⟩ := h M
  have hle : f k ≤ M := hbound _ ⟨k, rfl⟩
  exact lt_irrefl _ (lt_of_le_of_lt hle hk)

lemma infinitely_many_failures :
    {n : ℕ | ¬ erdos647_property n}.Infinite := by
  classical
  let f := fun k : ℕ =>
    ((k + 2) * (k + 3)) + tau ((k + 2) * (k + 3)) - 3
  have h_unbounded : ∀ B : ℕ, ∃ k, B < f k := by
    intro B
    let m := (B + 2) * (B + 3)
    have hm : 2 ≤ B + 2 := Nat.succ_le_succ (by decide)
    have hτ : 4 ≤ tau m := by
      have := tau_mul_four (k := B + 2) (by simpa using hm)
      simpa [m, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_left_comm]
        using this
    have hlarge : B < m + 1 := by
      have : B < (B + 2) * (B + 3) := by nlinarith
      exact lt_of_lt_of_le this (Nat.le_add_left _ _)
    refine ⟨B, ?_⟩
    have : (m + tau m - 3) ≥ m + 1 := by
      have hτ' : tau m ≥ 4 := hτ
      have : tau m - 3 ≥ 1 := Nat.sub_le_sub_right hτ' 3
      nlinarith [this]
    exact lt_of_lt_of_le hlarge this
  have hfail : ∀ k : ℕ, ¬ erdos647_property (f k) := by
    intro k
    have hk : 2 ≤ k + 2 := by exact Nat.succ_le_succ (Nat.succ_le_succ (by decide))
    have hτ := tau_mul_four (k := k + 2) (by simpa using hk)
    exact failure_construction (m := (k + 2) * (k + 3)) hτ
  have h_unbounded_fail :
      ∀ B : ℕ, ∃ n > B, ¬ erdos647_property n := by
    intro B
    obtain ⟨k, hk⟩ := h_unbounded (B + 1)
    exact ⟨f k, lt_of_le_of_lt (Nat.le_of_lt_succ hk)
      hk, hfail k⟩
  have hsub :
      Set.range f ⊆ {n : ℕ | ¬ erdos647_property n} := by
    intro n hn
    rcases hn with ⟨k, rfl⟩
    simpa using hfail k
  have hinf : (Set.range f).Infinite := infinite_range_of_unbounded h_unbounded
  have hinf := infinite_range_of_unbounded h_unbounded
  exact hinf.mono hsub

private lemma search_small_bool :
    (Finset.Icc (25 : ℕ) 60).all
        (fun n => decide (¬ erdos647_property n)) = true := by
  decide

lemma search_small {n : ℕ} (hn : n ∈ Finset.Icc (25 : ℕ) 60) :
    ¬ erdos647_property n := by
  classical
  have := (Finset.all_iff_forall).1 search_small_bool hn
  simpa using of_decide_eq_true this

/-- Main theorem handed to Aristotle: existence of `n > 24` satisfying the property.
All helper lemmas above are proven, so this is the only sorry. -/
theorem erdos_647 :
    ∃ n > 24, erdos647_property n := by
  sorry

end Erdos647
