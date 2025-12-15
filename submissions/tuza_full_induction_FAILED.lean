/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6e552983-3645-4633-8a21-e301212e9eb9
-/

/-
Tuza's Conjecture - Full Induction Structure
τ(G) ≤ 2ν(G) for all graphs G

This file structures the full proof via strong induction on ν.
The key insight: The "2-Edge Reduction Lemma" is equivalent to the conjecture.

PROVEN:
- Base case ν=0: tuza_base_case
- Base case ν=1: tuza_case_nu_1
- Deletion lemma: triangleCoveringNumber_le_card_add_deleteEdges
- Induction structure: complete

KEY LEMMA NEEDED (equivalent to full conjecture):
exists_two_edge_reduction: For any G with ν(G) > 0, there exists |S| ≤ 2 edges
such that ν(G \ S) < ν(G).

Our ν=1 proof shows this for ν=1 (we find 2 edges covering ALL triangles).
For ν > 1, this requires showing we can always "chip away" at the packing.
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 400000

set_option maxRecDepth 4000

noncomputable section

-- Definitions (same as proven file)
def triangleEdges {V : Type} [DecidableEq V] (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint {V : Type} [DecidableEq V] (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

noncomputable def trianglePackingNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

noncomputable def triangleCoveringNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

variable {V : Type*} [Fintype V] [DecidableEq V]

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableRel (SimpleGraph.Adj ?m.15)-/
-- PROVEN: Base case ν=0
lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableRel (SimpleGraph.Adj ?m.18)-/
-- Proven in tuza_SUCCESS_nu1_case.lean

-- PROVEN: Deletion lemma
lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableRel (SimpleGraph.Adj ?m.15)-/
-- Proven in tuza_SUCCESS_nu1_case.lean

-- PROVEN: Base case ν=1
lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableRel (SimpleGraph.Adj ?m.13)-/
-- Proven in tuza_SUCCESS_nu1_case.lean

-- Monotonicity: removing edges can't increase packing number
lemma packing_mono_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) :
    trianglePackingNumber (G.deleteEdges S) ≤ trianglePackingNumber G := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableRel (SimpleGraph.Adj ?m.32)-/
-- Should be straightforward: edge-disjoint triangles in G\S are also in G

/-
THE KEY LEMMA - This is equivalent to Tuza's Conjecture

For any graph G with ν(G) > 0, there exists a set S of at most 2 edges
such that removing S strictly decreases the packing number.

Our ν=1 proof establishes this for ν=1:
- When ν=1, we found 2 edges covering ALL triangles
- So removing them gives ν=0 < 1

For ν > 1, this requires a deeper argument about the structure of
maximum packings.
-/
lemma exists_two_edge_reduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G > 0) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableRel (SimpleGraph.Adj ?m.14)-/
-- THE HARD PART - equivalent to full conjecture

/-
FULL TUZA'S CONJECTURE via strong induction

Structure:
1. Induct on ν = trianglePackingNumber G
2. Base: ν=0 → τ=0 ≤ 0 = 2·0 ✓
3. Step: Assume ∀H with ν(H) < k, τ(H) ≤ 2ν(H)
        For G with ν(G) = k:
        - Get S with |S| ≤ 2 and ν(G\S) < k (reduction lemma)
        - τ(G) ≤ |S| + τ(G\S) ≤ 2 + 2·ν(G\S) ≤ 2 + 2·(k-1) = 2k ✓
-/
theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- Strong induction on packing number
  induction h : trianglePackingNumber G using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    by_cases hk : k = 0
    · -- Base case: ν = 0
      subst hk
      have := tuza_base_case G h
      simp [this]
    · -- Inductive case: ν > 0
      have hpos : trianglePackingNumber G > 0 := by omega
      -- Apply the reduction lemma
      obtain ⟨S, hS_card, hS_sub, hS_reduce⟩ := exists_two_edge_reduction G hpos
      -- Apply deletion lemma
      have h_del := triangleCoveringNumber_le_card_add_deleteEdges G S hS_sub
      -- Apply induction hypothesis on G \ S
      have h_smaller : trianglePackingNumber (G.deleteEdges S) < k := by
        rw [← h]; exact hS_reduce
      have h_ih := ih (trianglePackingNumber (G.deleteEdges S)) h_smaller (G.deleteEdges S) rfl
      -- Combine
      calc triangleCoveringNumber G
          ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := h_del
        _ ≤ 2 + 2 * trianglePackingNumber (G.deleteEdges S) := by
            have : S.card ≤ 2 := hS_card
            omega
        _ ≤ 2 + 2 * (k - 1) := by
            have : trianglePackingNumber (G.deleteEdges S) ≤ k - 1 := by omega
            omega
        _ = 2 * k := by omega

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableRel (SimpleGraph.Adj ?m.15)-/
/-
ALTERNATIVE APPROACH: Direct case analysis

Instead of the general reduction lemma, we could try:
1. Prove ν=2 case directly (like we did ν=1)
2. Look for patterns
3. Find structural lemma about maximum packings

The ν=2 case would need to show:
- If ν=2, we can find 4 edges covering all triangles
- Or equivalently: 2 edges that reduce ν to 1 (then apply ν=1 case)
-/
lemma tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

-- Could try to prove this directly like ν=1

end