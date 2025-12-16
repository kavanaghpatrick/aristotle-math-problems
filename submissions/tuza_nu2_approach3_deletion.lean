/-
TUZA ν=2 - APPROACH 3: Deletion + Induction
Strategy: Find ≤2 edges that reduce to ν=1 subproblems, then apply known result

KEY INSIGHT: Use the deletion inequality τ(G) ≤ |S| + τ(G\S)
- Find S with |S|≤2 such that ν(G\S) ≤ 1
- Then τ(G\S) ≤ 2 by the ν=1 theorem
- So τ(G) ≤ 2 + 2 = 4

PROOF OUTLINE:
1. Get two edge-disjoint triangles T1, T2 from ν=2
2. Find 2 edges S that "separate" them
3. After deleting S, any remaining triangle intersects at most one of T1\S, T2\S
4. This gives ν(G\S) ≤ 1, hence τ(G\S) ≤ 2
5. Apply deletion lemma: τ(G) ≤ |S| + τ(G\S) ≤ 2 + 2 = 4
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

/-! ## Known Results -/

/-- Base case: ν=0 implies τ=0 -/
lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  sorry

/-- ν=1 case (proven by Aristotle via K₄ argument) -/
lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

/-- ν≤1 implies τ≤2 (combines base and ν=1) -/
lemma tuza_nu_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 1) : triangleCoveringNumber G ≤ 2 := by
  rcases Nat.lt_or_eq_of_le h with h_lt | h_eq
  · -- ν = 0
    have h0 : trianglePackingNumber G = 0 := by omega
    rw [tuza_base_case G h0]; norm_num
  · -- ν = 1
    exact tuza_case_nu_1 G h_eq

/-! ## Deletion Lemma -/

/-- THE DELETION LEMMA: τ(G) ≤ |S| + τ(G\S) -/
lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  -- Any cover T of G\S plus S covers G
  -- So τ(G) ≤ |S ∪ T| ≤ |S| + |T|
  sorry

/-- Monotonicity: ν(G\S) ≤ ν(G) -/
lemma packing_mono_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) :
    trianglePackingNumber (G.deleteEdges S) ≤ trianglePackingNumber G := by
  unfold trianglePackingNumber
  apply Finset.sup_mono
  intro P hP
  simp only [Finset.mem_filter, Finset.mem_powerset] at hP ⊢
  constructor
  · intro t ht
    have := hP.1 ht
    simp only [SimpleGraph.mem_cliqueFinset_iff] at this ⊢
    exact ⟨this.1.mono (SimpleGraph.deleteEdges_le _ _), this.2⟩
  · exact hP.2

/-! ## The Key Reduction Lemma -/

/-- Extract two triangles from a ν=2 packing -/
lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  sorry

/-- KEY LEMMA: There exist ≤2 edges whose deletion reduces ν to ≤1 -/
lemma exists_reducing_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) ≤ 1 := by
  -- Get the two edge-disjoint triangles
  obtain ⟨t1, t2, ht1, ht2, hne, h_edge_disj⟩ := packing_two_triangles G h
  -- Pick one edge from each triangle
  have h1_card : t1.card = 3 := ht1.2
  have h2_card : t2.card = 3 := ht2.2
  -- t1 has ≥1 edge
  have h1_edges : (triangleEdges t1).Nonempty := by
    simp [triangleEdges]
    have : t1.offDiag.Nonempty := Finset.offDiag_nonempty.mpr (by omega)
    exact this.image _
  obtain ⟨e1, he1⟩ := h1_edges
  -- t2 has ≥1 edge
  have h2_edges : (triangleEdges t2).Nonempty := by
    simp [triangleEdges]
    have : t2.offDiag.Nonempty := Finset.offDiag_nonempty.mpr (by omega)
    exact this.image _
  obtain ⟨e2, he2⟩ := h2_edges
  -- S = {e1, e2} has size ≤2 and destroys both triangles
  use {e1, e2}
  constructor
  · -- |S| ≤ 2
    by_cases h_eq : e1 = e2
    · simp [h_eq]
    · rw [Finset.card_pair h_eq]
  constructor
  · -- S ⊆ G.edgeFinset
    intro e he
    simp at he
    rcases he with rfl | rfl
    · -- e1 is an edge of t1 which is a clique in G
      simp [triangleEdges] at he1
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := he1
      simp [Finset.mem_offDiag] at hab
      have := ht1.1; simp [SimpleGraph.isClique_iff] at this
      exact G.mem_edgeFinset.mpr (this hab.1 hab.2.1 hab.2.2)
    · -- e2 is an edge of t2
      simp [triangleEdges] at he2
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := he2
      simp [Finset.mem_offDiag] at hab
      have := ht2.1; simp [SimpleGraph.isClique_iff] at this
      exact G.mem_edgeFinset.mpr (this hab.1 hab.2.1 hab.2.2)
  · -- ν(G\S) ≤ 1
    -- After deleting e1, t1 is no longer a triangle in G\S
    -- After deleting e2, t2 is no longer a triangle in G\S
    -- Any max packing in G\S has size ≤ 1
    sorry

/-! ## Alternative: Component-Based Reduction -/

/-- If deletion disconnects into components, handle each separately -/
lemma component_reduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (h_reduces : trianglePackingNumber (G.deleteEdges S) ≤ 1) :
    triangleCoveringNumber (G.deleteEdges S) ≤ 2 := by
  exact tuza_nu_le_1 (G.deleteEdges S) h_reduces

/-! ## Main Theorem -/

/-- MAIN: τ ≤ 4 when ν = 2 via deletion + induction -/
theorem tuza_nu_2_deletion (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    triangleCoveringNumber G ≤ 4 := by
  -- Get the reducing edge set S
  obtain ⟨S, hS_card, hS_sub, h_reduces⟩ := exists_reducing_edges G h
  -- Apply deletion lemma
  have h_del := triangleCoveringNumber_le_card_add_deleteEdges G S hS_sub
  -- Apply ν≤1 result to G\S
  have h_cover := tuza_nu_le_1 (G.deleteEdges S) h_reduces
  -- Combine: τ(G) ≤ |S| + τ(G\S) ≤ 2 + 2 = 4
  omega

/-! ## Bonus: The Full Conjecture via Strong Induction -/

/-- If we had the reduction lemma for all ν, we'd get the full conjecture -/
theorem tuza_conjecture_sketch (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- Strong induction on ν
  induction h : trianglePackingNumber G using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    rcases k with _ | _ | k
    · -- ν = 0
      simp [tuza_base_case G h]
    · -- ν = 1
      have := tuza_case_nu_1 G h; omega
    · -- ν = k+2 ≥ 2
      -- Would need: exists_reducing_edges for general ν
      -- Then: τ(G) ≤ 2 + τ(G\S) ≤ 2 + 2(k+1) = 2(k+2)
      sorry

end
