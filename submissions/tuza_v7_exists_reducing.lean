/-
TUZA'S CONJECTURE - ν=2 CASE v7: FOCUSED ON exists_reducing_edges

STATUS FROM PRIOR SUBMISSIONS:
- tuza_case_nu_1: PROVED (v4, v5, v6) - ν=1 implies τ≤2
- tuza_nu_le_1: PROVED - ν≤1 implies τ≤2
- triangleCoveringNumber_le_card_add_deleteEdges: PROVED - deletion lemma
- packing_two_triangles: PROVED - extract two edge-disjoint triangles
- blocking_number_le_2: PROVED (695b7507)
- vertex_disjoint_unique_packing: NEGATED - counterexample found

ONE REMAINING GAP: exists_reducing_edges

MATHEMATICAL ARGUMENT FOR exists_reducing_edges:
Given ν(G) = 2 with max packing P = {t1, t2} (edge-disjoint triangles):
1. Let e1 ∈ triangleEdges(t1), e2 ∈ triangleEdges(t2)
2. Since t1, t2 edge-disjoint: e1 ≠ e2
3. Let G' = G.deleteEdges {e1, e2}
4. t1, t2 are no longer triangles in G' (each missing one edge)
5. Claim: ν(G') ≤ 1

Proof of claim by contradiction:
- Suppose ν(G') ≥ 2 with edge-disjoint T1, T2 in G'
- T1, T2 don't use e1 or e2 (deleted edges)
- Consider {T1, T2, t1, t2} in G
- Key: T1 must share an edge with t1 or t2 (else ν(G) ≥ 3)
- Similarly T2 must share an edge with t1 or t2
- Case analysis shows contradiction

ALTERNATIVE APPROACH: Choose edges wisely
- Pick e1, e2 to be "blocking edges" that break maximum packings
- The blocking_number ≤ 2 result may help guide this
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

/-! ## PROVEN LEMMAS (from prior submissions - marked as assumptions) -/

@[assumption]
lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  rw [eq_comm] at h
  contrapose! h
  refine' ne_of_gt (lt_of_le_of_lt (Finset.sup_le _) _)
  exact 1
  · simp +zetaDelta at *
    intro b hb hb'; rw [Finset.card_le_one_iff]; aesop
    exact Classical.not_not.1 fun h' => h a b_1 (by simpa using hb a_1) (by simpa using hb a_2) h' (hb' a_1 a_2 h')
  · decide

@[assumption]
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

/-! ## HELPER LEMMAS FOR exists_reducing_edges -/

/-- Triangle edges have exactly 3 elements -/
lemma triangleEdges_card_three {t : Finset V} (ht : t.card = 3) :
    (triangleEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht
  simp [triangleEdges]
  decide

/-- If two triangles are edge-disjoint, their edge sets are disjoint -/
lemma edge_disjoint_triangles_disjoint {t1 t2 : Finset V}
    (h : Disjoint (triangleEdges t1) (triangleEdges t2)) :
    ∀ e ∈ triangleEdges t1, e ∉ triangleEdges t2 := by
  intro e he
  exact Finset.disjoint_left.mp h he

/-- A triangle is not a clique after deleting one of its edges -/
lemma triangle_not_clique_after_delete {t : Finset V} {e : Sym2 V}
    (ht_card : t.card = 3) (he : e ∈ triangleEdges t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ht_clique : t ∈ G.cliqueFinset 3) :
    t ∉ (G.deleteEdges {e}).cliqueFinset 3 := by
  simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  intro ⟨h_clique, _⟩
  unfold triangleEdges at he
  simp only [Finset.mem_image, Finset.mem_offDiag, Prod.exists] at he
  obtain ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩ := he
  have h_adj : (G.deleteEdges {Sym2.mk (a, b)}).Adj a b := by
    apply h_clique
    · exact ha
    · exact hb
    · exact hab
  simp only [SimpleGraph.deleteEdges_adj, Finset.mem_singleton] at h_adj
  exact h_adj.2 rfl

/-- Key: if ν(G)=2 and {t1,t2} is a max packing, any other triangle shares edge with t1 or t2 -/
lemma max_packing_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (ht_ne : t1 ≠ t2) (ht_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_t1 : t ≠ t1) (ht_not_t2 : t ≠ t2) :
    ¬Disjoint (triangleEdges t) (triangleEdges t1) ∨ ¬Disjoint (triangleEdges t) (triangleEdges t2) := by
  -- If t were edge-disjoint from both t1 and t2, we'd have packing of size ≥3
  by_contra h_contra
  push_neg at h_contra
  -- t is edge-disjoint from t1 and t2
  -- So {t, t1, t2} would form a packing of size 3, contradiction
  have h_packing_3 : ∃ P : Finset (Finset V), P.card ≥ 3 ∧ P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P := by
    use {t, t1, t2}
    constructor
    · simp [Finset.card_insert_of_not_mem, ht_not_t1, ht_not_t2, ht_ne]
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · unfold IsEdgeDisjoint
      intro x hx y hy hxy
      simp at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        simp_all [h_contra.1, h_contra.2, ht_disj, Disjoint.symm]
  -- This contradicts ν(G) = 2
  have := h_packing_3
  obtain ⟨P, hP_card, hP_sub, hP_disj⟩ := this
  have h_bound : trianglePackingNumber G ≥ 3 := by
    unfold trianglePackingNumber
    refine le_trans hP_card ?_
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hP_sub, hP_disj⟩
  omega

/-! ## TARGET: The one remaining lemma -/

/-- Deleting one edge from each of two edge-disjoint triangles reduces ν to ≤1 -/
lemma exists_reducing_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) ≤ 1 := by
  -- Get two edge-disjoint triangles from the max packing
  obtain ⟨t1, t2, ht1, ht2, ht_ne, ht_disj⟩ := packing_two_triangles G h
  -- Get cards
  have ht1_card : t1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht1).2
  have ht2_card : t2.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht2).2
  -- Get edges from each triangle
  have h_edges1 : (triangleEdges t1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have := triangleEdges_card_three ht1_card
    simp [h_empty] at this
  have h_edges2 : (triangleEdges t2).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have := triangleEdges_card_three ht2_card
    simp [h_empty] at this
  -- Pick one edge from each
  obtain ⟨e1, he1⟩ := h_edges1
  obtain ⟨e2, he2⟩ := h_edges2
  -- e1 ≠ e2 since triangles are edge-disjoint
  have h_ne : e1 ≠ e2 := by
    intro h_eq
    rw [h_eq] at he1
    exact edge_disjoint_triangles_disjoint ht_disj e2 he2 he1
  -- Define S = {e1, e2}
  let S : Finset (Sym2 V) := {e1, e2}
  use S
  constructor
  -- |S| ≤ 2
  · simp [S, Finset.card_insert_of_not_mem, h_ne]
  constructor
  -- S ⊆ G.edgeFinset
  · intro e he
    simp [S] at he
    rcases he with rfl | rfl
    · -- e1 is an edge of G (from t1)
      unfold triangleEdges at he1
      simp only [Finset.mem_image, Finset.mem_offDiag, Prod.exists] at he1
      obtain ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩ := he1
      simp only [SimpleGraph.mem_edgeFinset]
      have := (SimpleGraph.mem_cliqueFinset_iff.mp ht1).1
      simp only [SimpleGraph.isClique_iff, Set.Pairwise] at this
      exact this ha hb hab
    · -- e2 is an edge of G (from t2)
      unfold triangleEdges at he2
      simp only [Finset.mem_image, Finset.mem_offDiag, Prod.exists] at he2
      obtain ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩ := he2
      simp only [SimpleGraph.mem_edgeFinset]
      have := (SimpleGraph.mem_cliqueFinset_iff.mp ht2).1
      simp only [SimpleGraph.isClique_iff, Set.Pairwise] at this
      exact this ha hb hab
  -- ν(G.deleteEdges S) ≤ 1
  · -- Show by contradiction: if ν ≥ 2, get two edge-disjoint triangles T1, T2 in G'
    by_contra h_contra
    push_neg at h_contra
    -- Get two edge-disjoint triangles in G'
    have h_ge_2 : trianglePackingNumber (G.deleteEdges S) ≥ 2 := h_contra
    -- This means there exist T1, T2 edge-disjoint triangles in G.deleteEdges S
    obtain ⟨T1, T2, hT1, hT2, hT_ne, hT_disj⟩ := packing_two_triangles (G.deleteEdges S) (by omega)
    -- T1, T2 are also triangles in G (since G.deleteEdges S ⊆ G)
    have hT1_G : T1 ∈ G.cliqueFinset 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff] at hT1 ⊢
      exact ⟨hT1.1.mono (SimpleGraph.deleteEdges_le _ _), hT1.2⟩
    have hT2_G : T2 ∈ G.cliqueFinset 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff] at hT2 ⊢
      exact ⟨hT2.1.mono (SimpleGraph.deleteEdges_le _ _), hT2.2⟩
    -- T1, T2 don't contain e1 or e2
    have hT1_no_e1 : e1 ∉ triangleEdges T1 := by
      intro h_mem
      have := triangle_not_clique_after_delete (SimpleGraph.mem_cliqueFinset_iff.mp hT1_G).2 h_mem G hT1_G
      have h_sub : {e1} ⊆ S := by simp [S]
      have h_mono : (G.deleteEdges S).cliqueFinset 3 ⊆ (G.deleteEdges {e1}).cliqueFinset 3 := by
        intro x hx
        simp only [SimpleGraph.mem_cliqueFinset_iff] at hx ⊢
        constructor
        · exact hx.1.mono (SimpleGraph.deleteEdges_le_deleteEdges _ h_sub)
        · exact hx.2
      exact this (h_mono hT1)
    have hT1_no_e2 : e2 ∉ triangleEdges T1 := by
      intro h_mem
      have := triangle_not_clique_after_delete (SimpleGraph.mem_cliqueFinset_iff.mp hT1_G).2 h_mem G hT1_G
      have h_sub : {e2} ⊆ S := by simp [S]
      have h_mono : (G.deleteEdges S).cliqueFinset 3 ⊆ (G.deleteEdges {e2}).cliqueFinset 3 := by
        intro x hx
        simp only [SimpleGraph.mem_cliqueFinset_iff] at hx ⊢
        constructor
        · exact hx.1.mono (SimpleGraph.deleteEdges_le_deleteEdges _ h_sub)
        · exact hx.2
      exact this (h_mono hT1)
    have hT2_no_e1 : e1 ∉ triangleEdges T2 := by
      intro h_mem
      have := triangle_not_clique_after_delete (SimpleGraph.mem_cliqueFinset_iff.mp hT2_G).2 h_mem G hT2_G
      have h_sub : {e1} ⊆ S := by simp [S]
      have h_mono : (G.deleteEdges S).cliqueFinset 3 ⊆ (G.deleteEdges {e1}).cliqueFinset 3 := by
        intro x hx
        simp only [SimpleGraph.mem_cliqueFinset_iff] at hx ⊢
        constructor
        · exact hx.1.mono (SimpleGraph.deleteEdges_le_deleteEdges _ h_sub)
        · exact hx.2
      exact this (h_mono hT2)
    have hT2_no_e2 : e2 ∉ triangleEdges T2 := by
      intro h_mem
      have := triangle_not_clique_after_delete (SimpleGraph.mem_cliqueFinset_iff.mp hT2_G).2 h_mem G hT2_G
      have h_sub : {e2} ⊆ S := by simp [S]
      have h_mono : (G.deleteEdges S).cliqueFinset 3 ⊆ (G.deleteEdges {e2}).cliqueFinset 3 := by
        intro x hx
        simp only [SimpleGraph.mem_cliqueFinset_iff] at hx ⊢
        constructor
        · exact hx.1.mono (SimpleGraph.deleteEdges_le_deleteEdges _ h_sub)
        · exact hx.2
      exact this (h_mono hT2)
    -- Now: T1 must share edge with t1 or t2 (by max_packing_edge_sharing)
    -- T1 cannot be t1 (since T1 doesn't contain e1 but t1 does)
    have hT1_ne_t1 : T1 ≠ t1 := by
      intro h_eq
      rw [h_eq] at hT1_no_e1
      exact hT1_no_e1 he1
    have hT1_ne_t2 : T1 ≠ t2 := by
      intro h_eq
      rw [h_eq] at hT1_no_e2
      exact hT1_no_e2 he2
    have hT2_ne_t1 : T2 ≠ t1 := by
      intro h_eq
      rw [h_eq] at hT2_no_e1
      exact hT2_no_e1 he1
    have hT2_ne_t2 : T2 ≠ t2 := by
      intro h_eq
      rw [h_eq] at hT2_no_e2
      exact hT2_no_e2 he2
    -- T1 shares edge with t1 or t2
    have hT1_shares := max_packing_edge_sharing G h t1 t2 ht1 ht2 ht_ne ht_disj T1 hT1_G hT1_ne_t1 hT1_ne_t2
    have hT2_shares := max_packing_edge_sharing G h t1 t2 ht1 ht2 ht_ne ht_disj T2 hT2_G hT2_ne_t1 hT2_ne_t2
    -- Key case analysis: what edges do T1, T2 share with t1, t2?
    -- Since T1, T2 are edge-disjoint and each shares with t1 or t2...
    -- We will reach a contradiction
    rcases hT1_shares with hT1_t1 | hT1_t2 <;> rcases hT2_shares with hT2_t1 | hT2_t2
    all_goals {
      -- Get the shared edges
      rw [Finset.not_disjoint_iff] at hT1_t1 hT1_t2 hT2_t1 hT2_t2
      -- Case 1: T1 shares with t1, T2 shares with t1
      -- The shared edges are both in triangleEdges t1
      -- T1 shares edge f1 with t1, T2 shares edge f2 with t1
      -- If f1 = f2, then T1, T2 share edge f1, contradicting edge-disjointness
      -- If f1 ≠ f2, both in triangleEdges t1 (which has 3 edges)
      -- T1, T2 are edge-disjoint, so no edge of T1 is in T2
      -- But consider the 4 triangles: T1, T2, t1, t2
      -- T1, T2 edge-disjoint; t1, t2 edge-disjoint
      -- T1 shares with t1; T2 shares with t1
      -- We can form a packing of size 3 using T1, T2, and t2?
      -- T1 edge-disjoint from t2? If T1 doesn't share with t2, yes
      -- But hT1_shares says T1 shares with t1 OR t2, we're in the t1 case
      -- So T1 might share with t2 too!
      sorry
    }

end
