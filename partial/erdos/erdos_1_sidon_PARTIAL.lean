/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aed38afd-b58a-48f5-b75f-f5755709bbb9

The following was proved by Aristotle:

- theorem expected_collisions (N n : ℕ) (hn : n ≤ N) :
    ∃ (E_collisions : ℝ), E_collisions ≤ 2^(2*n) / (n * N^2 : ℝ)

- theorem probabilistic_existence (N : ℕ) (hN : 2 ≤ N) :
    ∃ (A : Finset ℕ) (n : ℕ), A.card = n ∧ IsSumDistinctSet A N ∧
    n ≥ Real.log N / Real.log 2 - Real.log (Real.log N)

- lemma second_moment_collision (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    ∑ k ∈ Finset.range (A.sum id + 1),
      ((A.powerset.filter (fun S => S.sum id = k)).card : ℝ)^2 = 2^A.card

- theorem erdos_moser_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (1/4 : ℝ) * 2^A.card / Real.sqrt A.card ≤ N

- theorem lb_variance : ∃ (o : ℕ → ℝ),
    (∀ᶠ n in Filter.atTop, |o n| ≤ 1/n) ∧
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1/Real.sqrt 3 - o A.card) * 2^A.card / Real.sqrt A.card ≤ N

The following was negated by Aristotle:

- lemma sum_distinct_implies_sidon (A : Finset ℕ) (N : ℕ)
    (h : IsSumDistinctSet A N) :
    IsSidonSet A

- theorem erdos_1 : ∃ (C : ℝ) (hC : C > 0),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      C * 2^A.card ≤ N

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
Erdős Problem #1: SIDON SETS / PROBABILISTIC APPROACH

STRATEGY (from Grok + Gemini multi-agent consultation):
Sum-distinct sets are closely related to Sidon sets (B_2 sequences).

Key connections:
1. A Sidon set has all pairwise sums distinct
2. A sum-distinct set has ALL subset sums distinct (stronger)
3. Known: Sidon sets in [1,N] have size ≤ √N + O(N^{1/4})
4. Sum-distinct is MUCH stronger than Sidon

Probabilistic approach:
- Random subset of [1,N] of size n has ~2^n subset sums in [0, nN]
- For sum-distinctness, need 2^n ≤ nN (pigeonhole must not apply)
- This gives N ≥ 2^n / n, close to the conjecture!

The gap: Pigeonhole gives weak bound; need tighter collision analysis.

FORMALIZATION PATH:
1. Define Sidon property and relate to sum-distinct
2. Use counting argument for random subsets
3. Apply probabilistic method to show optimal constructions exist
4. Derive bounds from expectation calculations
-/

import Mathlib


open Finset BigOperators Nat

namespace Erdos1Sidon

-- Sum-distinct definition
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- SIDON SETS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A Sidon set (B_2 sequence): all pairwise sums are distinct -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Sum-distinct implies Sidon (stronger property)
-/
lemma sum_distinct_implies_sidon (A : Finset ℕ) (N : ℕ)
    (h : IsSumDistinctSet A N) :
    IsSidonSet A := by
  intro a b c d ha hb hc hd heq
  -- If a + b = c + d, then {a,b} and {c,d} have equal sums
  -- By sum-distinctness, {a,b} = {c,d}
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the set $A = \{2, 3, 4\}$.
  use {2, 3, 4};
  -- Let's choose $N = 4$.
  use 4;
  -- Let's choose $a = 2$, $b = 4$, $c = 3$, and $d = 3$.
  simp +decide [Erdos1Sidon.IsSumDistinctSet]

-/
/-- Sum-distinct implies Sidon (stronger property) -/
lemma sum_distinct_implies_sidon (A : Finset ℕ) (N : ℕ)
    (h : IsSumDistinctSet A N) :
    IsSidonSet A := by
  intro a b c d ha hb hc hd heq
  -- If a + b = c + d, then {a,b} and {c,d} have equal sums
  -- By sum-distinctness, {a,b} = {c,d}
  sorry

/- Aristotle failed to find a proof. -/
/-- Classical Sidon bound: |A| ≤ √N + O(N^{1/4}) -/
theorem sidon_bound (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (h : IsSidonSet A) (hsub : A ⊆ Finset.Icc 1 N) :
    (A.card : ℝ) ≤ Real.sqrt N + N^(1/4 : ℝ) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COUNTING ARGUMENT
-- ══════════════════════════════════════════════════════════════════════════════

/-- All subset sums lie in [0, Σa] -/
lemma subset_sum_range (A : Finset ℕ) :
    ∀ S ∈ A.powerset, S.sum id ≤ A.sum id := by
  intro S hS
  apply sum_le_sum_of_subset
  exact mem_powerset.mp hS

/-- For A ⊆ [1,N], the sum is at most n·N -/
lemma sum_le_card_mul_N (A : Finset ℕ) (N : ℕ) (h : A ⊆ Finset.Icc 1 N) :
    A.sum id ≤ A.card * N := by
  calc A.sum id = ∑ a ∈ A, a := rfl
    _ ≤ ∑ _ ∈ A, N := by
        apply sum_le_sum
        intro a ha
        have hacc : a ∈ Finset.Icc 1 N := h ha
        simp only [mem_Icc] at hacc
        exact hacc.2
    _ = A.card * N := by simp [mul_comm]

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Nat.card (↑(?m.55 '' ?s) : Type ?u.19101)
in the target expression
  #(Finset.image (fun (S : Finset ℕ) => S.sum id) A.powerset) = 2 ^ #A

A✝ : Finset ℕ
N✝ : ℕ
h✝ : Erdos1Sidon.IsSumDistinctSet A✝ N✝
hcard : 0 < #A✝
A : Finset ℕ
N : ℕ
h : Erdos1Sidon.IsSumDistinctSet A N
⊢ #(Finset.image (fun (S : Finset ℕ) => S.sum id) A.powerset) = 2 ^ #A-/
/-- Pigeonhole bound: if sum-distinct then 2^n ≤ nN + 1 -/
theorem pigeonhole_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    2^A.card ≤ A.card * N + 1 := by
  -- Sum-distinct means 2^n distinct values in [0, sum A] ⊆ [0, nN]
  have hdist := sum_distinct_uniform_distribution A N h
  have hrange : A.sum id ≤ A.card * N := sum_le_card_mul_N A N h.1
  -- Number of possible values is at most nN + 1 (including 0)
  -- But we have 2^n distinct values
  sorry
where
  sum_distinct_uniform_distribution (A : Finset ℕ) (N : ℕ)
      (h : IsSumDistinctSet A N) :
      (A.powerset.image (fun S => S.sum id)).card = 2^A.card := by
    rw [card_image_of_injective]
    · exact card_powerset A
    · intro S hS T hT heq
      have := h.2 ⟨S, hS⟩ ⟨T, hT⟩ heq
      simp only [Subtype.mk.injEq] at this
      exact this

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `pigeonhole_bound`
unsolved goals
A : Finset ℕ
N : ℕ
h : Erdos1Sidon.IsSumDistinctSet A N
hcard : 0 < #A
hN : 0 < N
⊢ (2 ^ #A - 1) / (↑(#A) : ℝ) ≤ (↑N : ℝ)-/
/-- Corollary: N ≥ (2^n - 1) / n -/
theorem N_lower_bound_pigeonhole (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) (hN : 0 < N) :
    (2^A.card - 1 : ℝ) / A.card ≤ N := by
  have hpig := pigeonhole_bound A N h hcard
  -- From 2^n ≤ nN + 1, get N ≥ (2^n - 1) / n
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- PROBABILISTIC METHOD
-- ══════════════════════════════════════════════════════════════════════════════

/-- Expected number of collisions in random subset sums -/
-- For random A ⊆ [1,N] of size n, expected collision count depends on variance
theorem expected_collisions (N n : ℕ) (hn : n ≤ N) :
    ∃ (E_collisions : ℝ), E_collisions ≤ 2^(2*n) / (n * N^2 : ℝ) := by
  -- Each pair of subsets has probability ~1/(nN) of collision
  -- There are (2^n choose 2) pairs
  exact ⟨ _, le_rfl ⟩

/-- Probabilistic existence: there exist sum-distinct sets of size ~log N -/
theorem probabilistic_existence (N : ℕ) (hN : 2 ≤ N) :
    ∃ (A : Finset ℕ) (n : ℕ), A.card = n ∧ IsSumDistinctSet A N ∧
    n ≥ Real.log N / Real.log 2 - Real.log (Real.log N) := by
  -- Random subset of appropriate size has positive probability of being sum-distinct
  revert hN N;
  intro N hN
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card ≥ Real.log N / Real.log 2 - Real.log (Real.log N) ∧ ∀ S T : Finset ℕ, S ∈ A.powerset → T ∈ A.powerset → S ≠ T → S.sum id ≠ T.sum id := by
    refine' ⟨ Finset.image ( fun n => 2 ^ n ) ( Finset.range ( Nat.log 2 N + 1 ) ), _, _, _ ⟩ <;> norm_num;
    · exact Finset.image_subset_iff.mpr fun n hn => Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( by decide ), Nat.pow_le_of_le_log ( by linarith ) ( by linarith [ Finset.mem_range.mp hn ] ) ⟩;
    · field_simp;
      rw [ Finset.card_image_of_injective _ fun a b h => by simpa using h ] ; norm_num [ mul_comm ];
      have := Real.log_le_log ( by positivity ) ( show ( N : ℝ ) ≤ 2 ^ ( Nat.log 2 N + 1 ) by exact_mod_cast Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ) ; norm_num at *;
      by_cases h₂ : Real.log (Real.log N) ≥ 0;
      · nlinarith [ Real.log_pos one_lt_two ];
      · rcases N with ( _ | _ | _ | N ) <;> norm_num at *;
        · have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_inv ( Real.log 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( Real.log_pos one_lt_two ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ];
        · exact False.elim <| h₂.not_le <| Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num ; linarith;
    · -- By definition of exponentiation, the sum of distinct powers of 2 is unique.
      have h_unique_sum : ∀ S T : Finset ℕ, S ⊆ Finset.range (Nat.log 2 N + 1) → T ⊆ Finset.range (Nat.log 2 N + 1) → S ≠ T → ∑ x ∈ S, 2 ^ x ≠ ∑ x ∈ T, 2 ^ x := by
        intros S T hS hT hne hsum
        have h_binary : ∀ (S : Finset ℕ), S ⊆ Finset.range (Nat.log 2 N + 1) → (∑ x ∈ S, 2 ^ x) = Nat.ofDigits 2 (List.map (fun x => if x ∈ S then 1 else 0) (List.range (Nat.log 2 N + 1))) := by
          intro S hS
          have h_binary : ∑ x ∈ S, 2 ^ x = ∑ x ∈ Finset.range (Nat.log 2 N + 1), (if x ∈ S then 2 ^ x else 0) := by
            simp +decide [ Finset.sum_ite, hS ];
            rw [ Finset.inter_eq_right.mpr hS ];
          rw [ h_binary ];
          induction ( Nat.log 2 N + 1 ) <;> simp_all +decide [ Nat.ofDigits, Finset.sum_range_succ' ];
          simp_all +decide [ Finset.range_add_one, Nat.ofDigits_append, List.range_succ ];
          by_cases h : ‹_› ∈ S <;> simp_all +decide [ Finset.sum_insert, Nat.ofDigits_append ];
          ring;
        have h_binary_eq : Nat.ofDigits 2 (List.map (fun x => if x ∈ S then 1 else 0) (List.range (Nat.log 2 N + 1))) = Nat.ofDigits 2 (List.map (fun x => if x ∈ T then 1 else 0) (List.range (Nat.log 2 N + 1))) := by
          rw [ ← h_binary S hS, ← h_binary T hT, hsum ];
        have h_binary_eq : List.map (fun x => if x ∈ S then 1 else 0) (List.range (Nat.log 2 N + 1)) = List.map (fun x => if x ∈ T then 1 else 0) (List.range (Nat.log 2 N + 1)) := by
          have h_binary_eq : ∀ (L L' : List ℕ), (∀ x ∈ L, x = 0 ∨ x = 1) → (∀ x ∈ L', x = 0 ∨ x = 1) → List.length L = List.length L' → Nat.ofDigits 2 L = Nat.ofDigits 2 L' → L = L' := by
            intros L L' hL hL' hlen hsum; induction' L with x L ih generalizing L' <;> induction' L' with y L' ih' <;> simp_all +decide [ Nat.ofDigits ] ;
            exact ⟨ by omega, ih L' hL'.2 ( by linarith ) ( by omega ) ⟩;
          exact h_binary_eq _ _ ( fun x hx => by rw [ List.mem_map ] at hx; rcases hx with ⟨ x, _, rfl ⟩ ; by_cases hx' : x ∈ S <;> simp +decide [ hx' ] ) ( fun x hx => by rw [ List.mem_map ] at hx; rcases hx with ⟨ x, _, rfl ⟩ ; by_cases hx' : x ∈ T <;> simp +decide [ hx' ] ) ( by simp +decide ) ‹_›;
        have h_binary_eq : ∀ x ∈ Finset.range (Nat.log 2 N + 1), x ∈ S ↔ x ∈ T := by
          intro x hx; replace h_binary_eq := congr_arg ( fun l => l.get! x ) h_binary_eq; simp_all +decide [ List.get! ] ;
          grind;
        exact hne <| Finset.Subset.antisymm ( fun x hx => by have := h_binary_eq x ( hS hx ) ; aesop ) ( fun x hx => by have := h_binary_eq x ( hT hx ) ; aesop );
      intros S T hS hT hne hsum;
      -- Let $S'$ and $T'$ be the preimages of $S$ and $T$ under the function $n \mapsto 2^n$.
      obtain ⟨S', hS'⟩ : ∃ S' : Finset ℕ, S = Finset.image (fun n => 2 ^ n) S' ∧ S' ⊆ Finset.range (Nat.log 2 N + 1) := by
        use Finset.filter (fun n => 2 ^ n ∈ S) (Finset.range (Nat.log 2 N + 1));
        grind
      obtain ⟨T', hT'⟩ : ∃ T' : Finset ℕ, T = Finset.image (fun n => 2 ^ n) T' ∧ T' ⊆ Finset.range (Nat.log 2 N + 1) := by
        use Finset.filter (fun n => 2 ^ n ∈ T) (Finset.range (Nat.log 2 N + 1));
        grind;
      simp_all +decide [ Finset.sum_image ];
      exact h_unique_sum S' T' hS'.2 hT'.2 ( by contrapose! hne; aesop ) ( by rw [ Finset.sum_image <| by aesop, Finset.sum_image <| by aesop ] at *; linarith );
  refine' ⟨ A, _, rfl, ⟨ hA.1, _ ⟩, hA.2.1 ⟩;
  exact fun x y hxy => Classical.not_not.1 fun h => hA.2.2 _ _ x.2 y.2 ( by contrapose! h; aesop ) hxy

-- ══════════════════════════════════════════════════════════════════════════════
-- REFINED COUNTING
-- ══════════════════════════════════════════════════════════════════════════════

/-- Second moment method for collisions -/
lemma second_moment_collision (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    ∑ k ∈ Finset.range (A.sum id + 1),
      ((A.powerset.filter (fun S => S.sum id = k)).card : ℝ)^2 = 2^A.card := by
  -- For sum-distinct, each count is 0 or 1, so count² = count
  -- Since the sums are distinct, each term in the sum is 1, and there are 2^|A| terms.
  have h_distinct_sums : ∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T := by
    have := h.2;
    exact fun S hS T hT hST => by simpa using @this ⟨ S, hS ⟩ ⟨ T, hT ⟩ hST;
  -- Since the sums are distinct, each term in the sum is 1, and there are $2^{|A|}$ terms.
  have h_count : ∑ k ∈ Finset.range (A.sum id + 1), (Finset.card (A.powerset.filter (fun S => S.sum id = k)) : ℝ) = 2 ^ (Finset.card A) := by
    rw_mod_cast [ ← Finset.card_eq_sum_card_fiberwise ];
    · rw [ Finset.card_powerset ];
    · exact fun S hS => Finset.mem_coe.mpr <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Finset.sum_le_sum_of_subset <| Finset.mem_powerset.mp hS;
  -- Since the sums are distinct, each term in the sum is 1, and there are $2^{|A|}$ terms. Therefore, the sum of the squares of the counts is equal to the sum of the counts.
  have h_square : ∀ k ∈ Finset.range (A.sum id + 1), (Finset.card (A.powerset.filter (fun S => S.sum id = k)) : ℝ) ^ 2 = (Finset.card (A.powerset.filter (fun S => S.sum id = k)) : ℝ) := by
    intros k hk
    have h_card : Finset.card (A.powerset.filter (fun S => S.sum id = k)) ≤ 1 := by
      exact Finset.card_le_one.mpr fun x hx y hy => h_distinct_sums x ( Finset.mem_filter.mp hx |>.1 ) y ( Finset.mem_filter.mp hy |>.1 ) ( by linarith [ Finset.mem_filter.mp hx |>.2, Finset.mem_filter.mp hy |>.2 ] );
    interval_cases _ : Finset.card ( Finset.filter ( fun S => S.sum id = k ) ( Finset.powerset A ) ) <;> norm_num;
  rw [ Finset.sum_congr rfl h_square, h_count ]

/- The main variance identity gives the Erdős-Moser bound -/
noncomputable section AristotleLemmas

/-
Identity for the sum of squared subset sums: 4 * sum(S_sum^2) = 2^n * (sum(A)^2 + sum(a^2)).
-/
section
open Finset BigOperators Nat
lemma Erdos1Sidon.sum_subset_sum_sq (A : Finset ℕ) :
    4 * ∑ S ∈ A.powerset, (S.sum id)^2 = 2^A.card * ((A.sum id)^2 + A.sum (fun x => x^2)) := by
      induction A using Finset.induction <;> norm_num at *;
      rw [ Finset.sum_powerset_insert ];
      · have h_expand : ∑ x ∈ Finset.powerset ‹Finset ℕ›, (∑ x ∈ Insert.insert ‹_› x, x) ^ 2 = ∑ x ∈ Finset.powerset ‹Finset ℕ›, (∑ x ∈ x, x) ^ 2 + 2 * ‹_› * ∑ x ∈ Finset.powerset ‹Finset ℕ›, ∑ x ∈ x, x + 2 ^ Finset.card ‹Finset ℕ› * ‹_› ^ 2 := by
          rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_insert ( Finset.notMem_mono ( Finset.mem_powerset.mp hx ) ‹_› ) ] ];
          norm_num [ add_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;
        -- Let's simplify the expression $\sum_{x \in \text{powerset}(s)} \sum_{y \in x} y$.
        have h_sum_simplify : ∑ x ∈ Finset.powerset ‹Finset ℕ›, ∑ x ∈ x, x = ∑ x ∈ ‹Finset ℕ›, x * 2 ^ (Finset.card ‹Finset ℕ› - 1) := by
          have h_sum_simplify : ∀ x ∈ ‹Finset ℕ›, ∑ y ∈ Finset.powerset ‹Finset ℕ›, (if x ∈ y then x else 0) = x * 2 ^ (Finset.card ‹Finset ℕ› - 1) := by
            intros x hx
            have h_count : Finset.card (Finset.filter (fun y => x ∈ y) (Finset.powerset ‹Finset ℕ›)) = 2 ^ (Finset.card ‹Finset ℕ› - 1) := by
              have h_count : Finset.card (Finset.filter (fun y => x ∈ y) (Finset.powerset ‹Finset ℕ›)) = Finset.card (Finset.powerset (‹Finset ℕ› \ {x})) := by
                refine' Finset.card_bij ( fun y hy => y \ { x } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
                · intro a₁ ha₁ hx₁ a₂ ha₂ hx₂ h; ext y; by_cases hy : y = x <;> simp_all +decide [ Finset.ext_iff ] ;
                · exact fun b hb => ⟨ Insert.insert x b, ⟨ fun y hy => by cases Finset.mem_insert.mp hy <;> aesop, by aesop ⟩, by aesop ⟩;
              simp_all +decide [ Finset.card_sdiff ];
            simp_all +decide [ mul_comm, Finset.sum_ite ];
          rw [ ← Finset.sum_congr rfl h_sum_simplify, Finset.sum_comm ];
          simp +decide [ Finset.sum_ite ];
          exact Finset.sum_congr rfl fun x hx => by rw [ Finset.inter_eq_right.mpr ( Finset.mem_powerset.mp hx ) ] ;
        simp_all +decide [ ← Finset.sum_mul _ _ _, Finset.sum_insert ];
        cases k : Finset.card ‹_› <;> simp_all +decide [ pow_succ' ] ; linarith;
        grind;
      · assumption
end

/-
Lower bound for the variance of a set of k distinct natural numbers: 12 * (k * sum(x^2) - sum(x)^2) >= k^2 * (k^2 - 1).
-/
section
open Finset BigOperators Nat

/-- Lower bound for the variance of a set of k distinct natural numbers -/
lemma Erdos1Sidon.variance_lower_bound (s : Finset ℕ) (k : ℕ) (hk : s.card = k) :
    12 * (k * ∑ x ∈ s, x^2 - (∑ x ∈ s, x)^2) ≥ k^2 * (k^2 - 1) := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide;
      -- By the properties of the sum of squares and the sum of elements in a set, we can derive the inequality.
      have h_ineq : ∑ x ∈ s, ∑ y ∈ s, (x - y : ℤ)^2 ≥ ∑ x ∈ Finset.range (k + 2), ∑ y ∈ Finset.range (k + 2), (x - y : ℤ)^2 := by
        -- Since $s$ contains $k+2$ distinct elements, we can order them as $s = \{a_1, a_2, \ldots, a_{k+2}\}$ with $a_1 < a_2 < \cdots < a_{k+2}$.
        obtain ⟨a, ha⟩ : ∃ a : Fin (k + 2) → ℕ, StrictMono a ∧ s = Finset.image a Finset.univ := by
          use fun i => s.orderEmbOfFin ( by aesop ) i;
          simp +decide [ StrictMono ];
        simp +decide [ Finset.sum_image, ha.1.injective.eq_iff, Finset.sum_range, ha.2 ];
        -- Since $a$ is strictly monotone, we have $a i - a j \geq i - j$ for all $i, j$.
        have h_diff_ge : ∀ i j : Fin (k + 2), i ≤ j → (a j - a i : ℤ) ≥ (j - i : ℤ) := by
          intro i j hij; induction' j using Fin.inductionOn with j ih ih ; induction' i using Fin.inductionOn with i ih ih ; aesop;
          · tauto;
          · cases hij.eq_or_lt <;> simp_all +decide [ Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val ];
            linarith [ ih ( Nat.le_of_lt_succ ‹_› ), ha.1 ( Fin.castSucc_lt_succ j ) ];
        refine' Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => _;
        by_cases hij : i ≤ j;
        · nlinarith only [ h_diff_ge i j hij, show ( i : ℤ ) ≤ j from mod_cast hij ];
        · nlinarith only [ h_diff_ge _ _ ( le_of_not_ge hij ), show ( i : ℤ ) ≥ j + 1 by exact_mod_cast lt_of_not_ge hij ];
      simp_all +decide [ Finset.sum_add_distrib, sub_sq, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
      have h_sum_sq : ∑ i ∈ Finset.range (k + 2), (i : ℤ)^2 = (k + 2) * (k + 1) * (2 * k + 3) / 6 ∧ ∑ i ∈ Finset.range (k + 2), (i : ℤ) = (k + 2) * (k + 1) / 2 := by
        exact ⟨ Eq.symm <| Int.ediv_eq_of_eq_mul_left ( by norm_num ) <| Nat.recOn k ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith, Eq.symm <| Int.ediv_eq_of_eq_mul_left ( by norm_num ) <| Nat.recOn k ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith ⟩;
      zify at *;
      rw [ Nat.cast_sub ] <;> push_cast <;> repeat nlinarith only [ hk, h_ineq, h_sum_sq ] ;
      rw [ Nat.cast_sub ] <;> push_cast;
      · nlinarith [ Int.ediv_mul_cancel ( show 6 ∣ ( ( k : ℤ ) + 2 ) * ( ( k : ℤ ) + 1 ) * ( 2 * ( k : ℤ ) + 3 ) from Int.dvd_of_emod_eq_zero ( by norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] ; have := Int.emod_nonneg k ( by norm_num : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos k ( by norm_num : ( 6 : ℤ ) > 0 ) ; interval_cases ( k % 6 : ℤ ) <;> trivial ) ), Int.ediv_mul_cancel ( show 2 ∣ ( ( k : ℤ ) + 2 ) * ( ( k : ℤ ) + 1 ) from even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) ) ];
      · have h_cauchy_schwarz : ∀ (u v : Finset ℕ), (∑ x ∈ u, x) ^ 2 ≤ (u.card : ℤ) * ∑ x ∈ u, x ^ 2 := by
          intros u v; norm_cast; have := Finset.sum_le_sum fun x ( hx : x ∈ u ) => pow_two_nonneg ( x - ( ∑ y ∈ u, y : ℝ ) / u.card ) ; simp_all +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ;
          by_cases hu : u = ∅ <;> simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
          rw [ ← @Nat.cast_le ℝ ] ; push_cast ; nlinarith [ mul_div_cancel₀ ( ∑ i ∈ u, ( i : ℝ ) ) ( show ( u.card : ℝ ) ≠ 0 by exact Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <| Classical.choose_spec <| Finset.nonempty_of_ne_empty hu ) ];
        exact_mod_cast hk ▸ h_cauchy_schwarz s s

end

/-
Sum of squares upper bound: sum(a^2) <= n * N^2.
-/
section
open Finset BigOperators Nat

/-- Upper bound for sum of squares in A -/
lemma Erdos1Sidon.sum_sq_le_card_mul_sq (A : Finset ℕ) (N : ℕ) (h : A ⊆ Finset.Icc 1 N) :
    A.sum (fun x => x^2) ≤ A.card * N^2 := by
      exact le_trans ( Finset.sum_le_sum fun x hx => Nat.pow_le_pow_left ( Finset.mem_Icc.mp ( h hx ) |>.2 ) 2 ) ( by norm_num )

end

end AristotleLemmas

theorem erdos_moser_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hcard : 0 < A.card) :
    (1/4 : ℝ) * 2^A.card / Real.sqrt A.card ≤ N := by
  -- From Σa² ≥ (4^n - 1)/3 and Σa² ≤ n·N²
  -- Applying the variance_lower_bound lemma to the set of subset sums of A.
  have h_var : 12 * (2 ^ A.card * ∑ x ∈ Finset.image (fun S => S.sum id) (Finset.powerset A), x^2 - (∑ x ∈ Finset.image (fun S => S.sum id) (Finset.powerset A), x)^2) ≥ (2 ^ A.card)^2 * ((2 ^ A.card)^2 - 1) := by
    have h_var : ∀ (s : Finset ℕ), s.card = 2 ^ A.card → 12 * (2 ^ A.card * ∑ x ∈ s, x^2 - (∑ x ∈ s, x)^2) ≥ (2 ^ A.card)^2 * ((2 ^ A.card)^2 - 1) := by
      exact?;
    apply h_var;
    rw [ Finset.card_image_of_injOn, Finset.card_powerset ];
    have := h.2;
    exact fun x hx y hy hxy => by have := @this ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
  -- Using the fact that the sum of squares of subset sums is bounded by $2^{n-2} (\sum A)^2 + 2^{n-2} \sum A^2$, we can further simplify the inequality.
  have h_simplify : 12 * (2 ^ A.card * (2 ^ A.card * ((A.sum id)^2 + A.sum (fun x => x^2)) / 4) - (2 ^ (A.card - 1) * (A.sum id))^2) ≥ (2 ^ A.card)^2 * ((2 ^ A.card)^2 - 1) := by
    convert h_var using 3;
    · have h_subset_sums_sq : ∑ x ∈ Finset.image (fun S => S.sum id) (Finset.powerset A), x^2 = ∑ S ∈ Finset.powerset A, (S.sum id)^2 := by
        rw [ Finset.sum_image ];
        have := h.2;
        exact fun x hx y hy hxy => by have := @this ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
      rw [ h_subset_sums_sq, ← Erdos1Sidon.sum_subset_sum_sq ];
      norm_num [ mul_div_cancel_left₀ ];
    · rw [ Finset.sum_image ];
      · -- By definition of subset sums, we can rewrite the left-hand side as the sum of the sums of all subsets of A.
        have h_subset_sums : ∑ x ∈ Finset.powerset A, x.sum id = ∑ x ∈ A, x * 2^(A.card - 1) := by
          have h_subset_sums : ∀ x ∈ A, ∑ S ∈ Finset.powerset A, (if x ∈ S then x else 0) = x * 2^(A.card - 1) := by
            intro x hx; simp +decide [ Finset.sum_ite, mul_comm ] ;
            -- The number of subsets of $A$ containing $x$ is $2^{A.card - 1}$.
            have h_subsets_containing_x : Finset.card (Finset.filter (fun S => x ∈ S) (Finset.powerset A)) = Finset.card (Finset.powerset (A \ {x})) := by
              refine' Finset.card_bij ( fun S hS => S \ { x } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
              · intro a₁ ha₁ hx₁ a₂ ha₂ hx₂ h; ext y; by_cases hy : y = x <;> simp_all +decide [ Finset.ext_iff ] ;
              · exact fun b hb => ⟨ Insert.insert x b, ⟨ fun y hy => by cases Finset.mem_insert.mp hy <;> aesop, by aesop ⟩, by aesop ⟩;
            simp_all +decide [ Finset.card_sdiff ];
          rw [ ← Finset.sum_congr rfl h_subset_sums, Finset.sum_comm ];
          simp +decide [ Finset.sum_ite ];
          exact Finset.sum_congr rfl fun x hx => by rw [ Finset.inter_eq_right.mpr ( Finset.mem_powerset.mp hx ) ] ;
        simp_all +decide [ mul_comm, Finset.mul_sum _ _ _ ];
      · have := h.2;
        exact fun x hx y hy hxy => by have := @this ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
  -- Using the fact that $\sum A^2 \leq n N^2$, we can further simplify the inequality.
  have h_final : 3 * A.card * N^2 ≥ (2 ^ A.card)^2 - 1 := by
    have h_final : 3 * A.sum (fun x => x^2) ≥ (2 ^ A.card)^2 - 1 := by
      rcases n : Finset.card A with ( _ | _ | n ) <;> simp_all +decide [ pow_succ', Nat.mul_assoc ];
      · rw [ Finset.card_eq_one ] at n ; aesop;
      · ring_nf at *;
        norm_num [ Nat.mul_assoc, Nat.mul_div_assoc ] at *;
        norm_num [ Nat.add_div, Nat.mul_div_assoc, pow_mul ] at *;
        split_ifs at h_simplify <;> norm_num [ Nat.add_mod, Nat.mul_mod ] at *;
        nlinarith [ Nat.sub_add_cancel ( show 1 ≤ ( 2 ^ ‹_› ) ^ 2 * 16 from Nat.one_le_iff_ne_zero.mpr <| by positivity ), Nat.sub_add_cancel ( show ( ∑ x ∈ A, x ) ^ 2 * ( ( 2 ^ ‹_› ) ^ 2 * 4 ) ≤ ( ( ∑ x ∈ A, x ^ 2 ) * 2 ^ ‹_› + ( ∑ x ∈ A, x ) ^ 2 * 2 ^ ‹_› ) * ( 2 ^ ‹_› * 4 ) from by nlinarith [ show 0 ≤ ∑ x ∈ A, x ^ 2 from Nat.zero_le _, show 0 ≤ ∑ x ∈ A, x from Nat.zero_le _, show 0 ≤ ( 2 ^ ‹_› : ℕ ) from Nat.zero_le _ ] ) ];
    exact h_final.trans ( by simpa [ mul_assoc ] using mul_le_mul_of_nonneg_left ( Erdos1Sidon.sum_sq_le_card_mul_sq A N h.1 ) zero_le_three );
  rw [ div_le_iff₀ ];
  · rw [ ← Real.sqrt_sq ( Nat.cast_nonneg N ) ];
    rw [ ← Real.sqrt_mul <| by positivity ];
    refine Real.le_sqrt_of_sq_le ?_;
    rw [ div_mul_eq_mul_div, div_pow, div_le_iff₀ ] <;> norm_cast;
    rw [ ge_iff_le, tsub_le_iff_right ] at h_final ; nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) hcard ];
  · positivity

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/- The proven Erdős-Moser bound (1956): N ≥ (1/√3 - o(1))·2^n/√n -/
noncomputable section AristotleLemmas

/-
Identity for the sum of squares of centered subset sums.
-/
open Finset BigOperators Nat

lemma Erdos1Sidon.variance_eq (A : Finset ℕ) :
    ∑ S ∈ A.powerset, ((2 * (∑ x ∈ S, (x : ℝ))) - (∑ x ∈ A, (x : ℝ)))^2 = 2^A.card * ∑ a ∈ A, (a : ℝ)^2 := by
      induction' A using Finset.induction with x A hx ih;
      · norm_num;
      · -- Let's split the sum into two parts: one over subsets that include $x$ and one over subsets that do not.
        have h_split : ∑ S ∈ (Insert.insert x A).powerset, (2 * (∑ x ∈ S, (x : ℝ)) - (∑ x ∈ Insert.insert x A, (x : ℝ)))^2 =
                      (∑ S ∈ A.powerset, (2 * (∑ x ∈ S, (x : ℝ)) - (∑ x ∈ A, (x : ℝ) + x))^2) +
                      (∑ S ∈ A.powerset, (2 * (∑ x ∈ S, (x : ℝ)) - (∑ x ∈ A, (x : ℝ) - x))^2) := by
                        rw [ Finset.sum_powerset_insert hx ];
                        simp +decide [ Finset.sum_insert hx, add_comm, mul_add, mul_sub, sub_sq ];
                        exact Finset.sum_congr rfl fun y hy => by rw [ Finset.sum_insert ( Finset.notMem_mono ( Finset.mem_powerset.mp hy ) hx ) ] ; ring;
        simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_sq, add_sq ] ; ring;
        simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_mul _ _ _ ] ; ring;
        norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, sq ] at * ; linarith

/-
The sum of squares of `m` integers with the same parity is at least `m(m^2-1)/3`.
-/
open Finset BigOperators Nat

lemma sum_sq_ge_of_distinct_parity (s : Finset ℤ) (m : ℕ) (h_card : s.card = m)
    (h_parity : ∃ p, ∀ x ∈ s, x % 2 = p) :
    ∑ x ∈ s, (x : ℝ)^2 ≥ (m : ℝ) * ((m : ℝ)^2 - 1) / 3 := by
      revert h_card h_parity;
      -- Let's assume without loss of generality that the elements of $s$ are centered around zero.
      intro hs_card hs_parity
      obtain ⟨p, hp⟩ : ∃ p : ℤ, ∀ x ∈ s, x % 2 = p := hs_parity
      obtain ⟨a, ha⟩ : ∃ a : Fin m → ℤ, (∀ i, a i ∈ s) ∧ (∀ i j, i < j → a i < a j) ∧ (∀ i j, a i % 2 = a j % 2) ∧ (∑ x ∈ s, (x : ℝ) ^ 2) = ∑ i, (a i : ℝ) ^ 2 := by
        use fun i => s.orderEmbOfFin ( by aesop ) i;
        field_simp;
        refine' ⟨ _, _, _, _ ⟩;
        · exact fun i => Finset.orderEmbOfFin_mem _ _ _;
        · aesop;
        · aesop;
        · have h_sum_eq : ∑ x ∈ s, (x : ℝ) ^ 2 = ∑ x ∈ Finset.image (fun i => s.orderEmbOfFin (by aesop) i) (Finset.univ : Finset (Fin m)), (x : ℝ) ^ 2 := by
            rw [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => Finset.mem_coe.mpr <| Finset.orderEmbOfFin_mem _ _ _ ) <| by rw [ Finset.card_image_of_injective _ <| fun i j hij => by simpa [ Fin.ext_iff ] using hij ] ; aesop ];
          rw [ h_sum_eq, Finset.sum_image ] ; aesop;
      -- Since $a_i$ are integers with the same parity, we have $a_{i+1} - a_i \geq 2$ for all $i$.
      have h_diff : ∀ i j : Fin m, i < j → a j - a i ≥ 2 * (j - i) := by
        intros i j hij;
        induction' j with j hj generalizing i;
        induction' j with j ih generalizing i;
        · tauto;
        · rcases eq_or_lt_of_le ( show i ≤ ⟨ j, by linarith ⟩ from Nat.le_of_lt_succ hij ) with rfl | hi <;> norm_num at *;
          · have := ha.2.1 ⟨ j, by linarith ⟩ ⟨ j + 1, hj ⟩ ( Nat.lt_succ_self _ ) ; have := ha.2.2.1 ⟨ j, by linarith ⟩ ⟨ j + 1, hj ⟩ ; omega;
          · linarith [ ih ( by linarith ) i hi, ha.2.1 ⟨ j, by linarith ⟩ ⟨ j + 1, hj ⟩ ( Nat.lt_succ_self _ ), show a ⟨ j + 1, hj ⟩ - a ⟨ j, by linarith ⟩ ≥ 2 from by { have := ha.2.2.1 ⟨ j, by linarith ⟩ ⟨ j + 1, hj ⟩ ; have := ha.2.1 ⟨ j, by linarith ⟩ ⟨ j + 1, hj ⟩ ( Nat.lt_succ_self _ ) ; omega } ];
      -- Let's denote the sum of squares of the differences as $S = \sum_{i < j} (a_j - a_i)^2$.
      set S := ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (a j - a i : ℝ) ^ 2;
      -- We can expand $S$ using the identity $\sum_{i < j} (a_j - a_i)^2 = m \sum_{i} a_i^2 - (\sum_{i} a_i)^2$.
      have h_expand : S = m * ∑ i, (a i : ℝ) ^ 2 - (∑ i, (a i : ℝ)) ^ 2 := by
        have h_expand : ∀ (n : ℕ) (a : Fin n → ℝ), ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (a j - a i) ^ 2 = n * ∑ i, a i ^ 2 - (∑ i, a i) ^ 2 := by
          intro n a; induction' n with n ih <;> simp +decide [ Fin.sum_univ_succ, * ] ; ring;
          simpa [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] using by ring;
        exact h_expand m fun i => a i;
      -- Since $a_i$ are integers with the same parity, we have $S \geq \sum_{i < j} (2(j - i))^2$.
      have h_S_ge : S ≥ ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (2 * (j - i) : ℝ) ^ 2 := by
        exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => by exact pow_le_pow_left₀ ( mul_nonneg zero_le_two <| sub_nonneg.mpr <| Nat.cast_le.mpr <| le_of_lt <| by aesop ) ( by exact_mod_cast h_diff i j <| by aesop ) _;
      -- Let's simplify the right-hand side of the inequality.
      have h_simplify : ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (2 * (j - i) : ℝ) ^ 2 = (m : ℝ) * (m ^ 2 - 1) / 3 * m := by
        clear h_expand h_S_ge h_diff ha hp hs_card;
        induction' m with m ih <;> norm_num [ Fin.sum_univ_succ ] at *;
        rw [ ih ] ; ring;
        exact Nat.recOn m ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith;
      rcases m with ( _ | _ | m ) <;> norm_num at *;
      · norm_num [ hs_card ];
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _;
      · nlinarith [ sq_nonneg ( ∑ i : Fin ( m + 1 + 1 ), ( a i : ℝ ) ) ]

open Finset BigOperators Nat Erdos1Sidon

lemma variance_lower_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    ∑ S ∈ A.powerset, ((2 * (∑ x ∈ S, (x : ℝ))) - (∑ x ∈ A, (x : ℝ)))^2 ≥
    (2^A.card : ℝ) * ((2^A.card : ℝ)^2 - 1) / 3 := by
      -- Let `f (S : Finset ℕ) : ℤ := 2 * (∑ x ∈ S, (x : ℤ)) - (∑ x ∈ A, (x : ℤ))`.
      set f := fun S : Finset ℕ => 2 * (∑ x ∈ S, (x : ℤ)) - (∑ x ∈ A, (x : ℤ));
      -- Since `h` implies subset sums are distinct, `f` is injective on `A.powerset`.
      have h_inj : Set.InjOn f (Finset.powerset A) := by
        intros S hS T hT h_eq;
        have := h.2;
        -- Apply the injectivity of the function that maps a subset to its sum.
        have h_sum_eq : S.sum id = T.sum id := by
          norm_num +zetaDelta at *;
          rw [ ← @Nat.cast_inj ℤ ] ; aesop;
        have := @this ⟨ S, hS ⟩ ⟨ T, hT ⟩ ; aesop;
      -- Let `T = A.powerset.image f`.
      set T := Finset.image f (Finset.powerset A);
      -- Since `T.card = 2^A.card`, we can apply `sum_sq_ge_of_distinct_parity` to `T`.
      have h_card_T : T.card = 2 ^ A.card := by
        rw [ Finset.card_image_of_injOn h_inj, Finset.card_powerset ];
      -- Since all elements of `T` have the same parity, we can apply `sum_sq_ge_of_distinct_parity` to `T`.
      have h_parity_T : ∃ p : ℤ, ∀ x ∈ T, x % 2 = p := by
        aesop;
      have := sum_sq_ge_of_distinct_parity T ( 2 ^ A.card ) ?_ h_parity_T <;> aesop

end AristotleLemmas

theorem lb_variance : ∃ (o : ℕ → ℝ),
    (∀ᶠ n in Filter.atTop, |o n| ≤ 1/n) ∧
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1/Real.sqrt 3 - o A.card) * 2^A.card / Real.sqrt A.card ≤ N := by
  refine' ⟨ fun n => 1 / n, _, _ ⟩ <;> norm_num;
  intro N A hA h_inj
  by_cases h_card : 0 < A.card;
  · -- By combining the results from the variance lower bound and the sum of squares inequality, we get the desired inequality.
    have h_combined : (N : ℝ) ^ 2 ≥ (4 ^ A.card - 1) / (3 * A.card) := by
      have h_combined : (A.card : ℝ) * (N : ℝ) ^ 2 ≥ (4 ^ A.card - 1) / 3 := by
        have h_combined : ∑ a ∈ A, (a : ℝ)^2 ≥ (4^A.card - 1) / 3 := by
          have h_combined : (2 ^ A.card : ℝ) * (∑ a ∈ A, (a : ℝ)^2) ≥ (2 ^ A.card : ℝ) * ((2 ^ A.card : ℝ)^2 - 1) / 3 := by
            have := variance_lower_bound A N ⟨ hA, h_inj ⟩;
            exact this.trans ( by rw [ variance_eq ] );
          rw [ show ( 4 : ℝ ) ^ #A = ( 2 ^ #A ) ^ 2 by norm_num [ sq, ← mul_pow ] ] ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) #A ] ;
        exact h_combined.trans ( le_trans ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( show ( x : ℝ ) ≤ N by exact_mod_cast Finset.mem_Icc.mp ( hA hx ) |>.2 ) 2 ) ( by norm_num ) );
      rw [ ge_iff_le, div_le_iff₀ ] <;> first | positivity | linarith;
    -- By combining the results from the variance lower bound and the sum of squares inequality, we get the desired inequality. Let's simplify the expression.
    suffices h_simplified : ((Real.sqrt 3)⁻¹ - (A.card : ℝ)⁻¹) ^ 2 * 4 ^ A.card / A.card ≤ (4 ^ A.card - 1) / (3 * A.card) by
      rw [ div_le_iff₀ ( by positivity ) ] at *;
      rw [ show ( 4 : ℝ ) ^ A.card = ( 2 ^ A.card ) ^ 2 by rw [ pow_right_comm ] ; norm_num ] at *;
      nlinarith [ show 0 ≤ ( N : ℝ ) * Real.sqrt ( A.card : ℝ ) by positivity, Real.mul_self_sqrt ( Nat.cast_nonneg A.card ) ];
    -- By simplifying, we can see that the inequality holds for sufficiently large $n$.
    have h_simplified : ∀ n : ℕ, 1 ≤ n → ((Real.sqrt 3)⁻¹ - (n : ℝ)⁻¹) ^ 2 * 4 ^ n ≤ (4 ^ n - 1) / 3 := by
      intro n hn
      field_simp;
      induction hn <;> norm_num [ pow_succ' ] at *;
      · nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
      · ring_nf at *;
        norm_num at * ; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), pow_le_pow_right₀ ( show ( 1 : ℝ ) ≤ 4 by norm_num ) ‹1 ≤ _› ];
    convert div_le_div_of_nonneg_right ( h_simplified _ h_card ) ( Nat.cast_nonneg _ ) using 1 ; ring;
  · aesop

/- Aristotle failed to find a proof. -/
/-- Target: The Elkies-Gleason bound with √(2/π) constant -/
theorem lb_strong : ∃ (o : ℕ → ℝ) (_ : o =o[Filter.atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (Real.sqrt (2 / Real.pi) - o A.card) * 2^A.card / Real.sqrt A.card ≤ N := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Ultimate goal: The $500 Erdős conjecture
-/
theorem erdos_1 : ∃ (C : ℝ) (hC : C > 0),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      C * 2^A.card ≤ N := by
  -- Gap from current bound: factor of √n
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- For any $x > 0$, we can choose $N = 0$ and $A = \emptyset$. Then $N < x \cdot 2^{|A|}$ simplifies to $0 < x \cdot 1$, which is true.
  intro x hx
  use 0, ∅
  simp [hx];
  decide +revert

-/
/-- Ultimate goal: The $500 Erdős conjecture -/
theorem erdos_1 : ∃ (C : ℝ) (hC : C > 0),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      C * 2^A.card ≤ N := by
  -- Gap from current bound: factor of √n
  sorry

end Erdos1Sidon