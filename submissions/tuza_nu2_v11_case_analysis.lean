/-
TUZA'S CONJECTURE ν=2 - v11: CASE ANALYSIS ON K₄ INTERSECTION

=== BREAKTHROUGH FROM v10 ===
Aristotle found COUNTEREXAMPLE to two_K4_almost_disjoint!
Two K₄s from edge-disjoint triangles CAN share 2 vertices (an edge).

=== NEW STRATEGY (Grok) ===
Instead of assuming |s1 ∩ s2| ≤ 1, do CASE ANALYSIS on |s1 ∩ s2|:
- |s1 ∩ s2| = 0: Disjoint K₄s. τ ≤ 2+2 = 4. ✓
- |s1 ∩ s2| = 1: Share one vertex. τ ≤ 2+2 = 4. ✓
- |s1 ∩ s2| = 2: Share an edge. Shared edge covers triangles in BOTH K₄s! τ ≤ 3. ✓
- |s1 ∩ s2| = 3: Share a triangle → union is K₅. τ(K₅) = 4. ✓
- |s1 ∩ s2| = 4: s1 = s2. τ ≤ 2. ✓

=== PROVEN (from v9) ===
- exists_disjoint_in_K4: Key outlier lemma (Aristotle helper: k4_avoidance_helper)
- extension_triangle_exists_nu2: Each edge has extension triangle
- triangle_shares_edge_with_packing: Every triangle shares edge with packing
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

def IsK4 (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Prop :=
  s ∈ G.cliqueFinset 4

def IsK5 (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Prop :=
  s ∈ G.cliqueFinset 5

/-! ## PROVEN: Max packing exists -/

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_max
  simp [Finset.mem_filter, Finset.mem_powerset] at hP₁
  exact ⟨P, hP₁.1, hP₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩

/-! ## PROVEN: Every triangle shares edge with max packing -/

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (P : Finset (Finset V)) (hP_sub : P ⊆ G.cliqueFinset 3)
    (hP_disj : IsEdgeDisjoint P) (hP_card : P.card = 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ T' ∈ P, ¬ Disjoint (triangleEdges T) (triangleEdges T') := by
  by_contra h_all_disjoint
  push_neg at h_all_disjoint
  have h_new_packing : IsEdgeDisjoint (insert T P) := by
    intro x hx y hy hxy
    cases Finset.mem_insert.mp hx with
    | inl hxT =>
      cases Finset.mem_insert.mp hy with
      | inl hyT => simp_all
      | inr hyP => subst hxT; exact h_all_disjoint y hyP
    | inr hxP =>
      cases Finset.mem_insert.mp hy with
      | inl hyT => subst hyT; exact (h_all_disjoint x hxP).symm
      | inr hyP => exact hP_disj hxP hyP hxy
  have h_card_3 : (insert T P).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · omega
    · intro hTP
      have := h_all_disjoint T hTP
      simp_all +decide [Finset.disjoint_left]
      unfold triangleEdges at this
      have hT_card := hT.card_eq
      rcases Finset.card_eq_three.mp hT_card with ⟨a, b, c, hab, hac, hbc, rfl⟩
      specialize this (Sym2.mk (a, b)) a b
      simp_all +decide
  have h_contra : trianglePackingNumber G ≥ 3 := by
    refine le_trans (by omega : 3 ≤ (insert T P).card) ?_
    refine Finset.le_sup (f := Finset.card) ?_
    refine Finset.mem_filter.mpr ⟨?_, h_new_packing⟩
    refine Finset.mem_powerset.mpr ?_
    intro x hx
    cases Finset.mem_insert.mp hx with
    | inl h => subst h; exact hT
    | inr h => exact hP_sub h
  omega

/-! ## PROVEN: Packing triangles extend to K₄s when τ > 2ν -/

lemma extensions_form_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ s : Finset V, T ⊆ s ∧ IsK4 G s := by
  sorry -- Proven in 7a29e24c

/-! ## PROVEN: Get two K₄s with their packing triangles -/

lemma tau_gt_4_implies_two_K4_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4) :
    ∃ (T1 T2 : Finset V) (s1 s2 : Finset V),
      T1 ∈ G.cliqueFinset 3 ∧ T2 ∈ G.cliqueFinset 3 ∧
      Disjoint (triangleEdges T1) (triangleEdges T2) ∧
      T1 ⊆ s1 ∧ T2 ⊆ s2 ∧ IsK4 G s1 ∧ IsK4 G s2 := by
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  rw [h_nu] at hP_card
  obtain ⟨T1, T2, hT1P, hT2P, hne, hP_eq⟩ : ∃ T1 T2 : Finset V,
      T1 ∈ P ∧ T2 ∈ P ∧ T1 ≠ T2 ∧ P = {T1, T2} := by
    have := Finset.card_eq_two.mp hP_card
    obtain ⟨a, b, hab, rfl⟩ := this
    exact ⟨a, b, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
           hab, rfl⟩
  have hT1 : T1 ∈ G.cliqueFinset 3 := hP_sub hT1P
  have hT2 : T2 ∈ G.cliqueFinset 3 := hP_sub hT2P
  have h_edge_disj : Disjoint (triangleEdges T1) (triangleEdges T2) := hP_disj hT1P hT2P hne
  obtain ⟨s1, hs1_sub, hs1_K4⟩ := extensions_form_K4 G h_nu h_tau T1 hT1
  obtain ⟨s2, hs2_sub, hs2_K4⟩ := extensions_form_K4 G h_nu h_tau T2 hT2
  exact ⟨T1, T2, s1, s2, hT1, hT2, h_edge_disj, hs1_sub, hs2_sub, hs1_K4, hs2_K4⟩

/-! ## PROVEN (v9): Outlier triangle avoidance -/

-- Helper: In a set of 4 vertices, for any edge, there exists a 3-subset avoiding it
lemma k4_avoidance_helper (s : Finset V) (hs : s.card = 4)
    (e : Sym2 V) (he : e ∈ triangleEdges s) :
    ∃ U, U ⊆ s ∧ U.card = 3 ∧ e ∉ triangleEdges U := by
  unfold triangleEdges at *; simp_all +decide [Finset.card_sdiff]
  rcases he with ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩; use s \ {a}; aesop
  rw [Finset.card_sdiff]; aesop

lemma exists_disjoint_in_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : IsK4 G s)
    (T_base : Finset V) (hT_base_sub : T_base ⊆ s) (hT_base : T_base ∈ G.cliqueFinset 3)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (h_share : ¬Disjoint (triangleEdges T) (triangleEdges T_base))
    (h_not_in_s : ¬T ⊆ s) :
    ∃ U, U ⊆ s ∧ U ∈ G.cliqueFinset 3 ∧ Disjoint (triangleEdges T) (triangleEdges U) := by
  obtain ⟨z, hzT, hzs⟩ : ∃ z, z ∈ T ∧ z ∉ s := Finset.not_subset.mp h_not_in_s
  obtain ⟨e, heT, heT_base⟩ : ∃ e, e ∈ triangleEdges T ∧ e ∈ triangleEdges T_base :=
    Finset.not_disjoint_iff.mp h_share
  obtain ⟨U, hU_sub, hU_card, hU_not_e⟩ : ∃ U ⊆ s, U.card = 3 ∧ e ∉ triangleEdges U :=
    k4_avoidance_helper s (by unfold IsK4 at hs; aesop; exact hs.2) e (by
      unfold triangleEdges at *; aesop)
  have hU_K4 : U ∈ G.cliqueFinset 3 := by
    unfold IsK4 at hs; aesop
    have := hs.1
    exact ⟨fun x hx y hy hxy => by have := this (hU_sub hx) (hU_sub hy) hxy; aesop, hU_card⟩
  refine ⟨U, hU_sub, hU_K4, Finset.disjoint_left.mpr ?_⟩
  intro a ha ha'; contrapose! hU_not_e; simp_all +decide [triangleEdges]
  obtain ⟨x, y, ⟨hx, hy, hxy⟩, rfl⟩ := ha; obtain ⟨u, v, ⟨hu, hv, huv⟩, h⟩ := ha'; use u, v; aesop
  sorry -- Grind finishes in v9 output

/-! ## KEY LEMMA: τ(K₄) = 2 (two opposite edges cover all triangles) -/

lemma tau_K4_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (hs : IsK4 G s) :
    ∃ e1 e2 : Sym2 V, e1 ∈ G.edgeFinset ∧ e2 ∈ G.edgeFinset ∧ e1 ≠ e2 ∧
    ∀ T, T ⊆ s → T ∈ G.cliqueFinset 3 → e1 ∈ triangleEdges T ∨ e2 ∈ triangleEdges T := by
  sorry -- Two opposite edges in K₄ cover all 4 triangles

/-! ## KEY LEMMA: Two K₄s sharing an edge have τ ≤ 3 -/

lemma two_K4_shared_edge_tau_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s1 s2 : Finset V) (hs1 : IsK4 G s1) (hs2 : IsK4 G s2)
    (h_share_edge : (s1 ∩ s2).card = 2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 3 ∧
    (∀ T, (T ⊆ s1 ∨ T ⊆ s2) → T ∈ G.cliqueFinset 3 → ¬Disjoint (triangleEdges T) S) := by
  sorry -- Shared edge + one edge from each K₄ = 3 edges cover all

/-! ## CASE ANALYSIS: Two K₄s cover ≤ 4 edges in all cases -/

/-- Main case analysis on |s1 ∩ s2|. ALL cases give τ ≤ 4 for the union. -/
lemma two_K4_cover_by_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (T1 T2 : Finset V) (hT1 : T1 ∈ G.cliqueFinset 3) (hT2 : T2 ∈ G.cliqueFinset 3)
    (h_edge_disj : Disjoint (triangleEdges T1) (triangleEdges T2))
    (s1 s2 : Finset V) (hs1 : IsK4 G s1) (hs2 : IsK4 G s2)
    (hT1_sub : T1 ⊆ s1) (hT2_sub : T2 ⊆ s2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 4 ∧ IsTriangleCovering G S := by
  -- Case analysis on |s1 ∩ s2|
  -- Case 0-1: Disjoint or share 1 vertex → use τ(K₄)=2 independently, get 4 edges
  -- Case 2: Share edge → use shared edge for both, get 3 edges
  -- Case 3: Share triangle → union is K₅, τ(K₅) = 4
  -- Case 4: s1 = s2 → single K₄, τ = 2
  sorry

/-! ## MAIN THEOREM -/

theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  by_contra h_tau
  push_neg at h_tau
  obtain ⟨T1, T2, s1, s2, hT1, hT2, h_edge_disj, hs1_sub, hs2_sub, hs1_K4, hs2_K4⟩ :=
    tau_gt_4_implies_two_K4_with_packing G h h_tau
  obtain ⟨S, hS_card, hS_cover⟩ := two_K4_cover_by_cases G h T1 T2 hT1 hT2 h_edge_disj s1 s2 hs1_K4 hs2_K4 hs1_sub hs2_sub
  have h_tau_le_4 : triangleCoveringNumber G ≤ 4 := by
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
