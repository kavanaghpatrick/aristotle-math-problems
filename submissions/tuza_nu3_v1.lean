/-
TUZA'S CONJECTURE ν=3 CASE - v1
Goal: Prove τ(G) ≤ 6 when ν(G) = 3

STRATEGY (from Grok analysis):
- 80% reuses ν=2 infrastructure
- Key insight: triangle_shares_edge_with_packing is ν-AGNOSTIC
- Pattern: 3 edge-disjoint packing triangles → 3 K₄s → τ ≤ 6

NEW for ν=3:
- Handle bridging triangles (triangles sharing with multiple packing triangles)
- Case analysis on how 3 triangles can share vertices
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions (same as ν=2) -/

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

def IsK4 (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Prop :=
  s ∈ G.cliqueFinset 4

/-! ## REUSED: Max packing exists (ν-agnostic) -/

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_max
  simp [Finset.mem_filter, Finset.mem_powerset] at hP₁
  exact ⟨P, hP₁.1, hP₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩

/-! ## REUSED: Covering deletion bound (ν-agnostic) -/

lemma covering_le_delete_add_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset (Sym2 V)) :
    triangleCoveringNumber G ≤ triangleCoveringNumber (G.deleteEdges U) + U.card := by
  sorry -- Proven in ν=2, include full proof

/-! ## REUSED: Every triangle shares edge with packing (ν-AGNOSTIC!) -/

/-- KEY LEMMA: Works for ANY ν. If T is edge-disjoint from all packing triangles,
    we can add T to the packing, contradicting maximality. -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = n)
    (P : Finset (Finset V)) (hP_sub : P ⊆ G.cliqueFinset 3)
    (hP_disj : IsEdgeDisjoint P) (hP_card : P.card = n)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ T' ∈ P, ¬ Disjoint (triangleEdges T) (triangleEdges T') := by
  sorry -- Same proof as ν=2, works for any n

/-! ## PARAMETERIZED: Extensions form K₄ when τ > 2ν -/

lemma extension_triangle_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = n) (h_tau : triangleCoveringNumber G > 2 * n)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T) :
    ∃ T', T' ∈ G.cliqueFinset 3 ∧ triangleEdges T ∩ triangleEdges T' = {e} := by
  sorry -- Generalizes extension_triangle_exists_nu2

lemma extensions_form_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = n) (h_tau : triangleCoveringNumber G > 2 * n)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ s : Finset V, T ⊆ s ∧ IsK4 G s := by
  sorry -- Generalizes extensions_form_K4 from ν=2

/-! ## ν=3 SPECIFIC: Extract three K₄s from packing -/

lemma tau_gt_6_implies_three_K4_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 3) (h_tau : triangleCoveringNumber G > 6) :
    ∃ (T1 T2 T3 : Finset V) (s1 s2 s3 : Finset V),
      T1 ∈ G.cliqueFinset 3 ∧ T2 ∈ G.cliqueFinset 3 ∧ T3 ∈ G.cliqueFinset 3 ∧
      IsEdgeDisjoint {T1, T2, T3} ∧
      T1 ⊆ s1 ∧ T2 ⊆ s2 ∧ T3 ⊆ s3 ∧
      IsK4 G s1 ∧ IsK4 G s2 ∧ IsK4 G s3 := by
  sorry -- Follows pattern of tau_gt_4_implies_two_K4_with_packing

/-! ## NEW for ν=3: Bridging triangles lemma -/

/-- If a triangle shares edges with multiple packing triangles (via shared vertices),
    it's still contained in a structure with τ ≤ 2. -/
lemma bridging_triangle_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (T1 T2 : Finset V) (hT1 : T1 ∈ G.cliqueFinset 3) (hT2 : T2 ∈ G.cliqueFinset 3)
    (h_share1 : ¬Disjoint (triangleEdges T) (triangleEdges T1))
    (h_share2 : ¬Disjoint (triangleEdges T) (triangleEdges T2))
    (h_disj : Disjoint (triangleEdges T1) (triangleEdges T2)) :
    ∃ e1 e2 : Sym2 V, e1 ∈ triangleEdges T ∧ e2 ∈ triangleEdges T ∧
      IsTriangleCovering G {e1, e2} ∨
      (∃ s : Finset V, T ⊆ s ∧ IsK4 G s) := by
  sorry -- New case analysis for bridging triangles

/-! ## ν=3 SPECIFIC: Three K₄s cover → τ ≤ 6 -/

/-- Main covering lemma for ν=3: All triangles in three K₄s → τ ≤ 6 -/
lemma three_K4_cover_le_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 3)
    (T1 T2 T3 : Finset V)
    (hT1 : T1 ∈ G.cliqueFinset 3) (hT2 : T2 ∈ G.cliqueFinset 3) (hT3 : T3 ∈ G.cliqueFinset 3)
    (h_packing_disj : IsEdgeDisjoint {T1, T2, T3})
    (s1 s2 s3 : Finset V)
    (h1 : IsK4 G s1) (h2 : IsK4 G s2) (h3 : IsK4 G s3)
    (hs1 : T1 ⊆ s1) (hs2 : T2 ⊆ s2) (hs3 : T3 ⊆ s3) :
    ∃ S : Finset (Sym2 V), S.card ≤ 6 ∧ IsTriangleCovering G S := by
  sorry -- Key lemma: τ(K₄)=2, so 3×2=6

/-! ## MAIN THEOREM -/

theorem tuza_case_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 3) : triangleCoveringNumber G ≤ 6 := by
  by_contra h_tau
  push_neg at h_tau
  -- Get three K₄s with their packing triangles
  obtain ⟨T1, T2, T3, s1, s2, s3, hT1, hT2, hT3, h_disj, hs1, hs2, hs3, hK1, hK2, hK3⟩ :=
    tau_gt_6_implies_three_K4_with_packing G h h_tau
  -- Use covering lemma
  obtain ⟨S, hS_card, hS_cover⟩ := three_K4_cover_le_6 G h T1 T2 T3 hT1 hT2 hT3 h_disj s1 s2 s3 hK1 hK2 hK3 hs1 hs2 hs3
  -- Derive τ ≤ 6, contradiction
  have h_tau_le_6 : triangleCoveringNumber G ≤ 6 := by
    unfold triangleCoveringNumber
    have h_S_in_cover : S ∩ G.edgeFinset ∈ Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact Finset.inter_subset_right
      · unfold IsTriangleCovering at *
        ext t; simp only [Finset.not_mem_empty, iff_false]; intro ht
        have := Finset.eq_empty_iff_forall_not_mem.mp hS_cover t
        simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht this
        apply this; constructor
        · intro u hu v hv huv; have := ht.1 hu hv huv
          simp only [SimpleGraph.deleteEdges_adj, Set.mem_inter_iff] at this ⊢
          exact ⟨this.1, fun h => this.2 h.1⟩
        · exact ht.2
    have h_min_le : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ (S ∩ G.edgeFinset).card := by
      exact Finset.min_le (Finset.mem_image_of_mem _ h_S_in_cover)
    have h_inter_le : (S ∩ G.edgeFinset).card ≤ S.card := Finset.card_inter_le _ _
    cases h : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) with
    | none => simp [Option.getD]
    | some n => simp [Option.getD]; exact le_trans (WithTop.coe_le_coe.mp h_min_le) (le_trans h_inter_le hS_card)
  omega

end
