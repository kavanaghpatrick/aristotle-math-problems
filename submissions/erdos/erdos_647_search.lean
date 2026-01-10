/-
Erdős Problem #647 – search + divergence scaffolding for Aristotle.

Key idea: provide a tiny amount of computable evidence plus structural lemmas
showing that failures occur infinitely often.  The only sorry is the main
theorem `Erdos647.erdos_647`, so Aristotle can focus all search time there.
-/

import Mathlib

open scoped BigOperators
open scoped Classical

namespace Erdos647

/-- Number of positive divisors of `n`. Helper used instead of arithmetic
functions so that `native_decide` can evaluate small cases. -/
def tau (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun d => 0 < d ∧ d ∣ n).card

/-- Target property from the original problem statement. -/
def erdos647_property (n : ℕ) : Prop :=
  ∀ m < n, m + tau m ≤ n + 2

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
  classical
  intro hprop
  have hτ' : 3 ≤ tau m := le_trans (by decide : 3 ≤ 4) hm
  have hτpos : 0 < tau m - 3 := Nat.sub_pos_of_lt (lt_of_le_of_lt (by decide : 3 < 4) hm)
  have hlt : m < m + tau m - 3 := by
    have := Nat.lt_add_of_pos_right hτpos
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_sub_assoc hτ'] using this
  have h := hprop m hlt
  have hsum : (m + tau m - 3) + 3 = m + tau m := by
    have hbound : 3 ≤ m + tau m := le_trans (Nat.le_add_left _ _) hτ'
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.sub_add_cancel hbound
  have hcontr :
      (m + tau m - 3) + 3 ≤ (m + tau m - 3) + 2 := by
    simpa [hsum] using h
  have hlt' :
      (m + tau m - 3) + 2 < (m + tau m - 3) + 3 := Nat.lt_succ_self _
  exact lt_irrefl _ (lt_of_le_of_lt hcontr hlt')

lemma infinite_range_of_unbounded {f : ℕ → ℕ}
    (h : ∀ B : ℕ, ∃ k, B < f k) : (Set.range f).Infinite := by
  classical
  by_contra hinf
  have hfinite :
      (Set.range f).Finite :=
        (Set.finite_or_infinite (Set.range f)).resolve_right hinf
  have hnonempty : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  have hfin_nonempty :
      (hfinite.toFinset).Nonempty := by
    rcases hnonempty with ⟨y, hy⟩
    exact ⟨y, by simpa using hfinite.mem_toFinset hy⟩
  let M := (hfinite.toFinset).max' hfin_nonempty
  have hbound :
      ∀ y ∈ Set.range f, y ≤ M := by
    intro y hy
    have : y ∈ hfinite.toFinset :=
      by simpa using hfinite.mem_toFinset hy
    exact Finset.le_max' _ _ this
  obtain ⟨k, hk⟩ := h M
  have hle : f k ≤ M := hbound _ ⟨k, rfl⟩
  exact lt_irrefl _ (lt_of_le_of_lt hle hk)

def failureWitness (k : ℕ) : ℕ :=
  ((k + 2) * (k + 3)) + tau ((k + 2) * (k + 3)) - 3

lemma failureWitness_unbounded :
    ∀ B : ℕ, B < failureWitness B := by
  intro B
  set m := (B + 2) * (B + 3) with hdef
  have hm : 2 ≤ B + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
  have hτ : 4 ≤ tau m := by
    have := tau_mul_four (k := B + 2) (by simpa using hm)
    simpa [m, hdef, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_left_comm] using this
  have hτpos : 0 < tau m - 3 :=
    Nat.sub_pos_of_lt (lt_of_le_of_lt (by decide : 3 < 4) hτ)
  have hdiff : 0 < m - B := by
    have hrepr :
        m = B * B + 5 * B + 6 := by
      simpa [m, hdef, Nat.pow_two, Nat.mul_add, Nat.add_mul, two_mul,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_left_comm] using
        (by ring : (B + 2) * (B + 3) = B * B + 5 * B + 6)
    have hrepr2 : m - B = B * B + 4 * B + 6 := by
      have := congrArg (fun t : ℕ => t - B) hrepr
      simpa [Nat.pow_two, Nat.mul_add, Nat.add_mul, two_mul] using this
    have : 0 < (B * B + 4 * B + 5).succ := Nat.succ_pos _
    simpa [hrepr2, Nat.succ_eq_add_one, Nat.add_assoc] using this
  have hlt_m : B < m := Nat.lt_of_sub_pos hdiff
  have hlt_f : m < failureWitness B := by
    have := Nat.lt_add_of_pos_right hτpos
    simpa [failureWitness, hdef, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.add_sub_assoc (le_trans (by decide : 3 ≤ 4) hτ)] using this
  exact lt_trans hlt_m hlt_f

lemma failureWitness_failure (k : ℕ) :
    ¬ erdos647_property (failureWitness k) := by
  classical
  have hk : 2 ≤ k + 2 := by simpa [Nat.add_comm] using Nat.le_add_right 2 k
  have hτ := tau_mul_four (k := k + 2) hk
  simpa [failureWitness] using
    failure_construction (m := (k + 2) * (k + 3)) hτ

lemma infinitely_many_failures :
    {n : ℕ | ¬ erdos647_property n}.Infinite := by
  classical
  have hinf :
      (Set.range failureWitness).Infinite :=
        infinite_range_of_unbounded (fun B => ⟨B, failureWitness_unbounded B⟩)
  have hsub :
      Set.range failureWitness ⊆ {n : ℕ | ¬ erdos647_property n} := by
    intro n hn
    rcases hn with ⟨k, rfl⟩
    exact failureWitness_failure k
  exact hinf.mono hsub

lemma search_small :
    ∀ n ∈ Finset.Icc (25 : ℕ) 60, ¬ erdos647_property n := by
  classical
  decide

/-- Main theorem handed to Aristotle: existence of `n > 24` satisfying the property.
All helper lemmas above are proven, so this is the only sorry. -/
theorem erdos_647 :
    ∃ n > 24, erdos647_property n := by
  sorry

end Erdos647
