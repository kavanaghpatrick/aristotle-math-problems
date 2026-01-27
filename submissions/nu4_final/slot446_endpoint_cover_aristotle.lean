/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9a618a8a-171e-4229-9f92-45103da87d41

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem endpoint_adaptive_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V) (B : Finset V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ B = {v₁})
    (h_6pack : SixPackingEndpoint G {a₁, a₂, v₁} B a₁ a₂ v₁) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2

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
  slot446_endpoint_cover.lean

  ENDPOINT ADAPTIVE COVER: 2 edges suffice for endpoint elements (A or D)

  Endpoints are SIMPLER than middle elements:
  - Only ONE neighbor (A has B, D has C)
  - Only ONE shared vertex
  - By slot412 (6-packing), at most 2 of 3 S_e types nonempty

  THEOREM: For endpoint A = {a1, a2, v1} with neighbor B,
  there exist 2 edges from A that cover:
  1. A itself
  2. All S_e externals of A
  3. All A-B bridges (because they all contain v1)

  TIER: 2 (uses proven scaffolding from slot436)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING FROM slot436 (Aristotle-proven)
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    ext x; simp only [mem_inter, mem_singleton]; constructor
    · intro ⟨⟨hxT, hxE⟩, _, hxF⟩
      have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE, hxF⟩
      rw [hEF] at hx_both
      exact ⟨hxT, mem_singleton.mp hx_both⟩
    · intro ⟨hxT, hxv⟩
      have hv_mem : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      subst hxv
      exact ⟨⟨hxT, (mem_inter.mp hv_mem).1⟩, hxT, (mem_inter.mp hv_mem).2⟩
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx; simp only [mem_union, mem_inter] at hx
    cases hx with | inl h => exact h.1 | inr h => exact h.1
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
      calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
        _ = 3 := hT_card
    omega
  rw [card_pos] at h_pos
  obtain ⟨x, hx⟩ := h_pos
  simp only [mem_inter, mem_singleton] at hx
  exact hx.2 ▸ hx.1

lemma sym2_mem_of_both_mem (a b : V) (T : Finset V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- S_e external of A: shares edge with A but not with B -/
def isSeExternal_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  2 ≤ (T ∩ A).card ∧
  (T ∩ B).card ≤ 1

/-- 6-packing constraint for endpoint: at most 2 of 3 S_e types nonempty -/
def SixPackingEndpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (a₁ a₂ v₁ : V) : Prop :=
  (∀ T, isSeExternal_A G A B T → ¬(a₁ ∈ T ∧ a₂ ∈ T)) ∨  -- No base type
  (∀ T, isSeExternal_A G A B T → ¬(a₁ ∈ T ∧ v₁ ∈ T)) ∨  -- No left spoke type
  (∀ T, isSeExternal_A G A B T → ¬(a₂ ∈ T ∧ v₁ ∈ T))

-- No right spoke type

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: One of three edges covers any interacting triangle
-- ══════════════════════════════════════════════════════════════════════════════

theorem endpoint_one_of_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTA : 2 ≤ (T ∩ {a₁, a₂, v₁}).card) :
    s(a₁, a₂) ∈ T.sym2 ∨ s(a₁, v₁) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
  -- T contains ≥ 2 of {a₁, a₂, v₁}, so T contains at least one edge
  by_cases ha1 : a₁ ∈ T
  · by_cases ha2 : a₂ ∈ T
    · left; exact sym2_mem_of_both_mem a₁ a₂ T ha1 ha2
    · -- a₁ ∈ T, a₂ ∉ T, |T ∩ A| ≥ 2 → v₁ ∈ T
      have hv1 : v₁ ∈ T := by
        by_contra hv1_not
        have h_sub : T ∩ {a₁, a₂, v₁} ⊆ {a₁} := by
          intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · rfl
          · exact absurd hx.1 ha2
          · exact absurd hx.1 hv1_not
        have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
          calc (T ∩ {a₁, a₂, v₁}).card ≤ ({a₁} : Finset V).card := card_le_card h_sub
            _ = 1 := card_singleton _
        omega
      right; left; exact sym2_mem_of_both_mem a₁ v₁ T ha1 hv1
  · -- a₁ ∉ T
    by_cases ha2 : a₂ ∈ T
    · -- a₂ ∈ T, a₁ ∉ T → v₁ ∈ T
      have hv1 : v₁ ∈ T := by
        by_contra hv1_not
        have h_sub : T ∩ {a₁, a₂, v₁} ⊆ {a₂} := by
          intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · exact absurd hx.1 ha1
          · rfl
          · exact absurd hx.1 hv1_not
        have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
          calc (T ∩ {a₁, a₂, v₁}).card ≤ ({a₂} : Finset V).card := card_le_card h_sub
            _ = 1 := card_singleton _
        omega
      right; right; exact sym2_mem_of_both_mem a₂ v₁ T ha2 hv1
    · -- a₁ ∉ T, a₂ ∉ T, |T ∩ A| ≥ 2 → impossible
      exfalso
      have h_sub : T ∩ {a₁, a₂, v₁} ⊆ {v₁} := by
        intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 ha1
        · exact absurd hx.1 ha2
        · rfl
      have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
        calc (T ∩ {a₁, a₂, v₁}).card ≤ ({v₁} : Finset V).card := card_le_card h_sub
          _ = 1 := card_singleton _
      omega

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
If the Six Packing property holds for an endpoint configuration, then the triangle {a1, a2, v1} cannot be a clique (i.e., at least one edge is missing).
-/
lemma six_packing_implies_missing_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V) (B : Finset V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ B = {v₁})
    (h_6pack : SixPackingEndpoint G {a₁, a₂, v₁} B a₁ a₂ v₁) :
    ¬(G.Adj a₁ a₂ ∧ G.Adj a₁ v₁ ∧ G.Adj a₂ v₁) := by
      unfold SixPackingEndpoint at h_6pack;
      unfold isSeExternal_A at h_6pack; simp_all +decide ;
      contrapose! h_6pack;
      refine' ⟨ ⟨ { a₁, a₂, v₁ }, _, _, _, _, _ ⟩, ⟨ { a₁, a₂, v₁ }, _, _, _, _, _ ⟩, ⟨ { a₁, a₂, v₁ }, _, _, _, _, _ ⟩ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ]

/-
If the base edge (a1, a2) is missing, then any interacting triangle must be covered by one of the spoke edges.
-/
lemma endpoint_cover_aux_base (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₁ a₂) :
    ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
    s(a₁, v₁) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
      intro T hT h_inter
      have h_one_of_three : s(a₁, a₂) ∈ T.sym2 ∨ s(a₁, v₁) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
        exact?;
      have h_not_base : s(a₁, a₂) ∉ T.sym2 := by
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        exact fun ha₁ ha₂ => h_missing <| hT.1 ha₁ ha₂ <| by aesop;
      aesop

/-
If the left spoke edge (a1, v1) is missing, then any interacting triangle must be covered by the base edge or the right spoke edge.
-/
lemma endpoint_cover_aux_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₁ v₁) :
    ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
    s(a₁, a₂) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
      intro T hT hTA;
      have h_cases : s(a₁, a₂) ∈ T.sym2 ∨ s(a₁, v₁) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
        exact?;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      have := hT.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      rcases h_cases with ( ⟨ ha₁, ha₂ ⟩ | ⟨ ha₁, hv₁ ⟩ | ⟨ ha₂, hv₁ ⟩ ) <;> simp_all +decide [ SimpleGraph.isClique_iff, Set.Pairwise ]

/-
If the right spoke edge (a2, v1) is missing, then any interacting triangle must be covered by the base edge or the left spoke edge.
-/
lemma endpoint_cover_aux_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₂ v₁) :
    ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
    s(a₁, a₂) ∈ T.sym2 ∨ s(a₁, v₁) ∈ T.sym2 := by
      intros T hT hTA
      have h_cases : s(a₁, a₂) ∈ T.sym2 ∨ s(a₁, v₁) ∈ T.sym2 ∨ s(a₂, v₁) ∈ T.sym2 := by
        exact?;
      contrapose! h_missing; simp_all +decide [ Sym2.mem_iff ] ;
      have := hT.1; aesop;

/-
If the base edge is missing, the two spoke edges form a valid adaptive cover.
-/
lemma endpoint_adaptive_cover_of_missing_base (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₁ a₂) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
          refine' ⟨ s(a₁, v₁), s(a₂, v₁), _, _, _ ⟩ <;> simp +decide [ * ];
          intro T hT hT';
          have := Finset.one_lt_card.1 hT'; simp_all +decide [ Finset.ext_iff ] ;
          rcases this with ⟨ x, hx, y, hy, hxy ⟩ ; rcases hx with ⟨ hx₁, rfl | rfl | rfl ⟩ <;> rcases hy with ⟨ hy₁, rfl | rfl | rfl ⟩ <;> simp_all +decide ;
          · have := hT.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact False.elim ( h_missing ( this hx₁ hy₁ ( by tauto ) ) );
          · have := hT.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact False.elim ( h_missing ( this hy₁ hx₁ ( by tauto ) ) )

/-
If the left spoke edge is missing, the base edge and the right spoke edge form a valid adaptive cover.
-/
lemma endpoint_adaptive_cover_of_missing_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₁ v₁) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
          refine' ⟨ _, _, Or.inl rfl, Or.inr <| Or.inr rfl, _ ⟩;
          exact?

/-
If the right spoke edge is missing, the base edge and the left spoke edge form a valid adaptive cover.
-/
lemma endpoint_adaptive_cover_of_missing_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_missing : ¬G.Adj a₂ v₁) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
          -- Choose $e_1 = s(a_1, a_2)$ and $e_2 = s(a_1, v_1)$.
          use s(a₁, a₂), s(a₁, v₁);
          -- Apply the lemma endpoint_cover_aux_right to conclude the proof.
          apply And.intro (by simp) (And.intro (by simp) (fun T hT hTA => endpoint_cover_aux_right G a₁ a₂ v₁ h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 h_missing T hT hTA))

end AristotleLemmas

/-
══════════════════════════════════════════════════════════════════════════════
MAIN THEOREM: Endpoint adaptive cover
══════════════════════════════════════════════════════════════════════════════

PROOF SKETCH:
1. By endpoint_one_of_three, every A-interacting T uses one of 3 edges
2. By 6-packing, at least one S_e type is empty
3. The 2 edges covering nonempty types suffice for S_e externals
4. For A-B bridges: they all contain v₁ (by bridge_contains_shared)
5. At least one of the 2 chosen edges is incident to v₁ (spokes)
   - If we pick both spokes: both contain v₁ ✓
   - If we pick base + spoke: spoke contains v₁ ✓
6. Since bridge contains v₁ and shares edge with A, the v₁-incident edge hits it

KEY INSIGHT: Unlike middle elements, endpoint's 2-edge selection ALWAYS
includes at least one v₁-incident edge (spoke), so bridges are automatic!
-/
theorem endpoint_adaptive_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V) (B : Finset V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ B = {v₁})
    (h_6pack : SixPackingEndpoint G {a₁, a₂, v₁} B a₁ a₂ v₁) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  unfold SixPackingEndpoint at h_6pack
  rcases h_6pack with h_no_base | h_no_left | h_no_right

  · -- Case: No base S_e externals → use both spokes
    use s(a₁, v₁), s(a₂, v₁)
    refine ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), ?_⟩
    intro T hT hTA
    obtain h1 | h2 | h3 := endpoint_one_of_three G a₁ a₂ v₁
        h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 T hT hTA
    · -- T uses base {a₁, a₂}, but we have spokes
      -- T must be S_e external (using base) or bridge
      rw [Finset.mk_mem_sym2_iff] at h1
      by_cases hTB : 2 ≤ (T ∩ B).card
      · -- A-B bridge: contains v₁
        have hv1T : v₁ ∈ T := bridge_contains_shared G {a₁, a₂, v₁} B v₁ hAB T hT hTA hTB
        -- T contains a₁, a₂, v₁ → uses left spoke
        left; exact sym2_mem_of_both_mem a₁ v₁ T h1.1 hv1T
      · -- S_e external using base - contradicts h_no_base
        push_neg at hTB
        have hTB' : (T ∩ B).card ≤ 1 := by omega
        exfalso
        exact h_no_base T ⟨hT, hTA, hTB'⟩ ⟨h1.1, h1.2⟩
    · left; exact h2
    · right; exact h3

  · -- Case: No left spoke S_e externals → use base + right spoke
    use s(a₁, a₂), s(a₂, v₁)
    refine ⟨Or.inl rfl, Or.inr (Or.inr rfl), ?_⟩
    intro T hT hTA
    obtain h1 | h2 | h3 := endpoint_one_of_three G a₁ a₂ v₁
        h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 T hT hTA
    · left; exact h1
    · -- T uses left spoke {a₁, v₁}, but we have base + right
      rw [Finset.mk_mem_sym2_iff] at h2
      by_cases hTB : 2 ≤ (T ∩ B).card
      · -- A-B bridge: contains v₁, and we have a₁ ∈ T
        -- Need to show base or right spoke hits T
        -- T = {v₁, a₁, x} for some x ∈ B
        -- If x = a₂: T = {v₁, a₁, a₂}, base hits ✓
        -- If x ≠ a₂: T doesn't use base, but uses right spoke only if a₂ ∈ T
        -- Actually, T has a₁, v₁. If a₂ ∈ T, base or right hits.
        -- If a₂ ∉ T, T = {a₁, v₁, x} where x ∈ B, x ≠ a₂
        -- Then T uses only left spoke from A - but it's a bridge!
        -- Bridges must be covered somehow...
        -- The right spoke s(a₂, v₁) has v₁, and T has v₁, a₁, x
        -- s(a₂, v₁) ∈ T.sym2 iff a₂ ∈ T ∧ v₁ ∈ T
        -- If a₂ ∉ T, right spoke doesn't hit
        -- Need base: s(a₁, a₂) ∈ T.sym2 iff a₁ ∈ T ∧ a₂ ∈ T
        -- If a₂ ∉ T, base doesn't hit either!
        -- This is a GAP for bridges using only left spoke!
        -- Wait, there's a mistake. We can actually prove the opposite.
        negate_state;
        -- Proof starts here:
        norm_num +zetaDelta at *;
        use ULift ( Fin 4 );
        refine' ⟨ inferInstance, inferInstance, _, _, _ ⟩;
        refine' SimpleGraph.mk fun x y => x ≠ y ∧ ( x.down = 0 ∨ y.down = 0 ∨ x.down = 1 ∨ y.down = 1 );
        infer_instance;
        refine' ⟨ ⟨ 0 ⟩, ⟨ 2 ⟩, _, ⟨ 3 ⟩, _, _, _ ⟩ <;> simp +decide [ isSeExternal_A ];
        refine' ⟨ { ⟨ 3 ⟩, ⟨ 1 ⟩ }, _, _, _ ⟩ <;> simp +decide [ SimpleGraph.isNClique_iff ]
      · -- S_e external using left spoke - contradicts h_no_left
        push_neg at hTB
        have hTB' : (T ∩ B).card ≤ 1 := by omega
        exfalso
        exact h_no_left T ⟨hT, hTA, hTB'⟩ ⟨h2.1, h2.2⟩
    · right; exact h3

  · -- Case: No right spoke S_e externals → use base + left spoke
    use s(a₁, a₂), s(a₁, v₁)
    refine ⟨Or.inl rfl, Or.inr (Or.inl rfl), ?_⟩
    intro T hT hTA
    obtain h1 | h2 | h3 := endpoint_one_of_three G a₁ a₂ v₁
        h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 T hT hTA
    · left; exact h1
    · right; exact h2
    · -- T uses right spoke {a₂, v₁}, but we have base + left
      rw [Finset.mk_mem_sym2_iff] at h3
      by_cases hTB : 2 ≤ (T ∩ B).card
      · -- A-B bridge: contains v₁
        -- Similar gap as above for bridges using only right spoke
        sorry
      · -- S_e external using right spoke - contradicts h_no_right
        push_neg at hTB
        have hTB' : (T ∩ B).card ≤ 1 := by omega
        exfalso
        exact h_no_right T ⟨hT, hTA, hTB'⟩ ⟨h3.1, h3.2⟩

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Endpoint adaptive cover
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. By endpoint_one_of_three, every A-interacting T uses one of 3 edges
2. By 6-packing, at least one S_e type is empty
3. The 2 edges covering nonempty types suffice for S_e externals
4. For A-B bridges: they all contain v₁ (by bridge_contains_shared)
5. At least one of the 2 chosen edges is incident to v₁ (spokes)
   - If we pick both spokes: both contain v₁ ✓
   - If we pick base + spoke: spoke contains v₁ ✓
6. Since bridge contains v₁ and shares edge with A, the v₁-incident edge hits it

KEY INSIGHT: Unlike middle elements, endpoint's 2-edge selection ALWAYS
includes at least one v₁-incident edge (spoke), so bridges are automatic!
-/

theorem endpoint_adaptive_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ : V) (B : Finset V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ B = {v₁})
    (h_6pack : SixPackingEndpoint G {a₁, a₂, v₁} B a₁ a₂ v₁) :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ = s(a₁, a₂) ∨ e₁ = s(a₁, v₁) ∨ e₁ = s(a₂, v₁)) ∧
      (e₂ = s(a₁, a₂) ∨ e₂ = s(a₁, v₁) ∨ e₂ = s(a₂, v₁)) ∧
      ∀ T ∈ G.cliqueFinset 3, 2 ≤ (T ∩ {a₁, a₂, v₁}).card →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  unfold SixPackingEndpoint at h_6pack
  rcases h_6pack with h_no_base | h_no_left | h_no_right

  · -- Case: No base S_e externals → use both spokes
    use s(a₁, v₁), s(a₂, v₁)
    refine ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), ?_⟩
    intro T hT hTA
    obtain h1 | h2 | h3 := endpoint_one_of_three G a₁ a₂ v₁
        h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 T hT hTA
    · -- T uses base {a₁, a₂}, but we have spokes
      -- T must be S_e external (using base) or bridge
      rw [Finset.mk_mem_sym2_iff] at h1
      by_cases hTB : 2 ≤ (T ∩ B).card
      · -- A-B bridge: contains v₁
        have hv1T : v₁ ∈ T := bridge_contains_shared G {a₁, a₂, v₁} B v₁ hAB T hT hTA hTB
        -- T contains a₁, a₂, v₁ → uses left spoke
        left; exact sym2_mem_of_both_mem a₁ v₁ T h1.1 hv1T
      · -- S_e external using base - contradicts h_no_base
        push_neg at hTB
        have hTB' : (T ∩ B).card ≤ 1 := by omega
        exfalso
        exact h_no_base T ⟨hT, hTA, hTB'⟩ ⟨h1.1, h1.2⟩
    · left; exact h2
    · right; exact h3

  · -- Case: No left spoke S_e externals → use base + right spoke
    use s(a₁, a₂), s(a₂, v₁)
    refine ⟨Or.inl rfl, Or.inr (Or.inr rfl), ?_⟩
    intro T hT hTA
    obtain h1 | h2 | h3 := endpoint_one_of_three G a₁ a₂ v₁
        h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 T hT hTA
    · left; exact h1
    · -- T uses left spoke {a₁, v₁}, but we have base + right
      rw [Finset.mk_mem_sym2_iff] at h2
      by_cases hTB : 2 ≤ (T ∩ B).card
      · -- A-B bridge: contains v₁, and we have a₁ ∈ T
        -- Need to show base or right spoke hits T
        -- T = {v₁, a₁, x} for some x ∈ B
        -- If x = a₂: T = {v₁, a₁, a₂}, base hits ✓
        -- If x ≠ a₂: T doesn't use base, but uses right spoke only if a₂ ∈ T
        -- Actually, T has a₁, v₁. If a₂ ∈ T, base or right hits.
        -- If a₂ ∉ T, T = {a₁, v₁, x} where x ∈ B, x ≠ a₂
        -- Then T uses only left spoke from A - but it's a bridge!
        -- Bridges must be covered somehow...
        -- The right spoke s(a₂, v₁) has v₁, and T has v₁, a₁, x
        -- s(a₂, v₁) ∈ T.sym2 iff a₂ ∈ T ∧ v₁ ∈ T
        -- If a₂ ∉ T, right spoke doesn't hit
        -- Need base: s(a₁, a₂) ∈ T.sym2 iff a₁ ∈ T ∧ a₂ ∈ T
        -- If a₂ ∉ T, base doesn't hit either!
        -- This is a GAP for bridges using only left spoke!
        sorry
      · -- S_e external using left spoke - contradicts h_no_left
        push_neg at hTB
        have hTB' : (T ∩ B).card ≤ 1 := by omega
        exfalso
        exact h_no_left T ⟨hT, hTA, hTB'⟩ ⟨h2.1, h2.2⟩
    · right; exact h3

  · -- Case: No right spoke S_e externals → use base + left spoke
    use s(a₁, a₂), s(a₁, v₁)
    refine ⟨Or.inl rfl, Or.inr (Or.inl rfl), ?_⟩
    intro T hT hTA
    obtain h1 | h2 | h3 := endpoint_one_of_three G a₁ a₂ v₁
        h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 T hT hTA
    · left; exact h1
    · right; exact h2
    · -- T uses right spoke {a₂, v₁}, but we have base + left
      rw [Finset.mk_mem_sym2_iff] at h3
      by_cases hTB : 2 ≤ (T ∩ B).card
      · -- A-B bridge: contains v₁
        -- Similar gap as above for bridges using only right spoke
        sorry
      · -- S_e external using right spoke - contradicts h_no_right
        push_neg at hTB
        have hTB' : (T ∩ B).card ≤ 1 := by omega
        exfalso
        exact h_no_right T ⟨hT, hTA, hTB'⟩ ⟨h3.1, h3.2⟩

end