/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 87ecdf18-dbac-42a6-afbd-9cce650d8b74

The following was proved by Aristotle:

- lemma tau_ge_two (n : ℕ) (hn : n ≥ 2) : tau n ≥ 2

- lemma exists_large_m_plus_tau (n : ℕ) (hn : n ≥ 100) :
    ∃ m < n, m + tau m ≥ n

- lemma max_m_plus_tau_unbounded :
    ∀ K : ℕ, ∃ n : ℕ, ∀ m < n, m + tau m ≤ n + 2 → K ≤ n

The following was negated by Aristotle:

- lemma hcn_tau_near_max (n : ℕ) (hn : n ≥ 2) :
    ∃ h ∈ hcn_sequence.filter (· ≤ n), ∀ m ≤ n, tau m ≤ tau h + 2

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
Erdős Problem #647: Divisor function bounds

STRATEGY (from Grok-4 + Gemini):
1. Use native_decide for computational search over n ∈ [25, 500]
2. Provide scaffolding lemmas about τ(n) = σ_0(n) (divisor count)
3. If direct search fails, use bounds on highly composite numbers

PROBLEM STATEMENT:
Let τ(n) count the number of divisors of n.
- erdos_647: ∃ n > 24, max_{m<n}(m + τ(m)) ≤ n + 2
- erdos_647.variants.lim: lim_{n→∞} max_{m<n}(τ(m) + m - n) = ∞
- erdos_647.variants.infinite: ∀ k, infinitely many n where max_{n-k<m<n}(m+τ(m)) ≤ n+2

KEY FACT: τ(24) = 8, so 24 + τ(24) = 32 > 24 + 2 = 26.
But for n = 24: max_{m<24}(m + τ(m)) = 23 + τ(23) = 23 + 2 = 25 ≤ 26 ✓

We need n > 24 where the same property holds.
-/

import Mathlib


open Filter ArithmeticFunction Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS AND NOTATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- The divisor counting function τ(n) = σ_0(n) -/
abbrev tau (n : ℕ) : ℕ := σ 0 n

/-- Check if n satisfies the Erdős 647 property: max_{m<n}(m + τ(m)) ≤ n + 2 -/
def erdos647_property (n : ℕ) : Prop :=
  ∀ m < n, m + tau m ≤ n + 2

/-- Computable version for native_decide -/
def erdos647_check (n : ℕ) : Bool :=
  (Finset.range n).toList.all (fun m => m + sigma 0 m ≤ n + 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Basic properties of τ(n)
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ(1) = 1 -/
lemma tau_one : tau 1 = 1 := by
  simp [tau, sigma_one]

/-- τ(p) = 2 for prime p -/
lemma tau_prime (p : ℕ) (hp : p.Prime) : tau p = 2 := by
  simp [tau]
  exact ArithmeticFunction.sigma_zero_prime hp

/-- τ(p^k) = k + 1 for prime p -/
lemma tau_prime_pow (p k : ℕ) (hp : p.Prime) : tau (p ^ k) = k + 1 := by
  simp [tau]
  exact ArithmeticFunction.sigma_zero_prime_pow hp k

/-- τ is multiplicative: τ(ab) = τ(a)τ(b) for coprime a,b -/
lemma tau_multiplicative (a b : ℕ) (hab : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0) :
    tau (a * b) = tau a * tau b := by
  simp only [tau]
  exact ArithmeticFunction.sigma_zero_mul hab

/-- Upper bound: τ(n) ≤ n for all n ≥ 1 -/
lemma tau_le_self (n : ℕ) (hn : n ≥ 1) : tau n ≤ n := by
  simp only [tau]
  exact ArithmeticFunction.sigma_zero_le_id hn

/-- τ(n) ≥ 2 for n ≥ 2 (has at least divisors 1 and n) -/
lemma tau_ge_two (n : ℕ) (hn : n ≥ 2) : tau n ≥ 2 := by
  -- By definition of $τ$, we know that $τ(n) = (σ_0 n)$, where $σ_0$ is the number of divisors function.
  have h_tau_def : tau n = (Nat.divisors n).card := by
    exact?;
  exact h_tau_def.symm ▸ Finset.one_lt_card.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SMALL VALUES: Verify τ(n) for small n using native_decide
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ values for small n -/
lemma tau_values_small :
    tau 2 = 2 ∧ tau 3 = 2 ∧ tau 4 = 3 ∧ tau 6 = 4 ∧
    tau 12 = 6 ∧ tau 24 = 8 ∧ tau 36 = 9 ∧ tau 48 = 10 ∧
    tau 60 = 12 ∧ tau 120 = 16 := by
  native_decide

/-- Highly composite numbers have large τ -/
lemma tau_highly_composite :
    tau 1 = 1 ∧ tau 2 = 2 ∧ tau 4 = 3 ∧ tau 6 = 4 ∧
    tau 12 = 6 ∧ tau 24 = 8 ∧ tau 36 = 9 ∧ tau 48 = 10 ∧
    tau 60 = 12 ∧ tau 120 = 16 ∧ tau 180 = 18 ∧ tau 240 = 20 := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- COMPUTATIONAL SEARCH: Find n > 24 satisfying the property
-- ══════════════════════════════════════════════════════════════════════════════

/-- The property holds for n = 24 (known) -/
theorem erdos_647_at_24 : ⨆ m : Fin 24, (m : ℕ) + σ 0 m ≤ 26 := by
  exact ciSup_le <| by decide

/-- Check the property for specific values using computation -/
lemma erdos647_check_values :
    erdos647_check 25 = false ∧
    erdos647_check 26 = false ∧
    erdos647_check 30 = false := by
  native_decide

/-- Search for witnesses in range [25, N] -/
def find_erdos647_witness (N : ℕ) : Option ℕ :=
  (Finset.Icc 25 N).toList.find? erdos647_check

/-- Check if any n in [25, 100] satisfies the property -/
lemma erdos647_search_100 : find_erdos647_witness 100 = none := by
  native_decide

/-- Check if any n in [25, 200] satisfies the property -/
lemma erdos647_search_200 : find_erdos647_witness 200 = none := by
  native_decide

-- Note: If the above searches return none, the conjecture may be false
-- for finite n > 24, or we need larger search ranges.

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE: Bounds approach for variants
-- ══════════════════════════════════════════════════════════════════════════════

/-- For large n, there exists m < n with m + τ(m) large -/
lemma exists_large_m_plus_tau (n : ℕ) (hn : n ≥ 100) :
    ∃ m < n, m + tau m ≥ n := by
  -- Key: highly composite numbers grow faster
  -- For n ≥ 100, take m to be the largest HCN < n
  -- Let's choose m = n - 1. We need to verify that m < n and m + τ(m) ≥ n.
  use n - 1;
  exact ⟨ Nat.pred_lt ( ne_bot_of_gt hn ), by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ), tau_ge_two ( n - 1 ) ( Nat.le_sub_one_of_lt ( by linarith ) ) ] ⟩

/-- The maximum grows unboundedly -/
lemma max_m_plus_tau_unbounded :
    ∀ K : ℕ, ∃ n : ℕ, ∀ m < n, m + tau m ≤ n + 2 → K ≤ n := by
  exact fun K => ⟨ K, fun m hm₁ hm₂ => by linarith ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREMS (targets for Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

namespace Erdos647

/- Aristotle failed to find a proof. -/
/-- Main theorem: Existence of n > 24 with the property -/
theorem erdos_647 : (∃ n > 24, ⨆ m : Fin n, m + σ 0 m ≤ n + 2) := by
  -- Try computational approach first
  -- If that fails, may need different approach
  sorry

/- Aristotle failed to find a proof. -/
/-- The limit variant: max_{m<n}(τ(m) + m - n) → ∞ -/
theorem erdos_647_variants_lim :
    atTop.Tendsto (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop := by
  -- This says the maximum excess grows without bound
  -- Follows from HCN density arguments
  sorry

/- Aristotle failed to find a proof. -/
/-- The infinite variant: for each k, infinitely many good n -/
theorem erdos_647_variants_infinite :
    (∀ k, { n | ⨆ m : Set.Ioo (n - k) n, ↑m + σ 0 m ≤ n + 2 }.Infinite) := by
  -- For small k, can find explicit sequences
  -- For general k, use density argument
  sorry

end Erdos647

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Bounds on highly composite numbers
-- ══════════════════════════════════════════════════════════════════════════════

/-- Highly composite number sequence (first few) -/
def hcn_sequence : List ℕ := [1, 2, 4, 6, 12, 24, 36, 48, 60, 120, 180, 240, 360, 720]

/-- τ at HCNs forms a strictly increasing sequence -/
lemma tau_hcn_increasing :
    List.Pairwise (· < ·) (hcn_sequence.map tau) := by
  native_decide

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

lemma tau_1260 : tau 1260 = 36 := by
  native_decide +revert

lemma hcn_max_tau : ∀ h ∈ hcn_sequence, tau h ≤ 30 := by
  native_decide

lemma hcn_tau_near_max_counterexample :
  ¬ (∀ n, n ≥ 2 → ∃ h ∈ hcn_sequence.filter (· ≤ n), ∀ m ≤ n, tau m ≤ tau h + 2) := by
    simp +zetaDelta at *;
    use 1260;
    native_decide

end AristotleLemmas

/-
For any n, there's an HCN h ≤ n with τ(h) close to maximal
-/
lemma hcn_tau_near_max (n : ℕ) (hn : n ≥ 2) :
    ∃ h ∈ hcn_sequence.filter (· ≤ n), ∀ m ≤ n, tau m ≤ tau h + 2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose n = 2520, which is the next highly composite number after 1260.
  use 2520;
  -- We'll use that 2520 is the next highly composite number after 1260.
  native_decide +revert

-/
/-- For any n, there's an HCN h ≤ n with τ(h) close to maximal -/
lemma hcn_tau_near_max (n : ℕ) (hn : n ≥ 2) :
    ∃ h ∈ hcn_sequence.filter (· ≤ n), ∀ m ≤ n, tau m ≤ tau h + 2 := by
  sorry

end