/-
TUZA'S CONJECTURE - ν=2 CASE
Target: Prove τ(G) ≤ 4 when ν(G) = 2

PROVEN RESULTS (from tuza_SUCCESS_nu1_case.lean):
- ν=0 → τ=0 (base case)
- ν=1 → τ≤2 (K₄ structure argument)
- Deletion lemma: τ(G) ≤ |S| + τ(G-S)

STRATEGY FOR ν=2:
Two edge-disjoint triangles T₁, T₂. Case on |T₁ ∩ T₂|:
- Case 0 (disjoint): 6 vertices → cover each with ≤2 edges = 4 total
- Case 1 (bowtie): 5 vertices → explicit 4-edge cover
- Case ≥2: Impossible (would share edge)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

/-! ## Core Definitions -/

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

/-! ## Foundational Lemmas (proven in tuza_SUCCESS_nu1_case.lean) -/

lemma tuza_base_case {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h;
    refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ( Classical.choose_spec ( Finset.card_pos.mp ( Nat.pos_of_ne_zero h ) ) ) ), _ ⟩ ) ) ) <;> norm_num;
    intro x hx y hy; aesop;
  unfold triangleCoveringNumber;
  unfold IsTriangleCovering; aesop;
  rw [ show ( Finset.image Finset.card ( Finset.filter ( fun S : Finset ( Sym2 V ) => ( G.deleteEdges ( S : Set ( Sym2 V ) ) ).CliqueFree 3 ) ( G.edgeFinset.powerset ) ) ).min = some 0 from ?_ ];
  · rfl;
  · refine' le_antisymm _ _;
    · refine' Finset.min_le _ ; aesop;
    · simp +decide [ Finset.min ];
      exact fun _ _ _ => WithTop.coe_le_coe.mpr ( Nat.zero_le _ )

lemma triangleCoveringNumber_le_card_add_deleteEdges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧ IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop;
    have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering ( G.deleteEdges ( S : Set ( Sym2 V ) ) ) ) ( G.deleteEdges ( S : Set ( Sym2 V ) ) |> SimpleGraph.edgeFinset |> Finset.powerset ) ) ) from ?_ ) ; aesop;
    · have := Finset.mem_of_min h; aesop;
    · simp +zetaDelta at *;
      use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering];
  have h_union : IsTriangleCovering G (S ∪ T) := by
    unfold IsTriangleCovering at *; aesop;
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber;
    have h_union_card : (S ∪ T).card ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [ Finset.subset_iff, SimpleGraph.deleteEdges ];
      exact ⟨ S ∪ T, ⟨ fun x hx => by aesop, h_union ⟩, rfl ⟩;
    have := Finset.min_le h_union_card; aesop;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
  exact h_union_card.trans ( Finset.card_union_le _ _ ) |> le_trans <| by rw [ hT.2.2 ] ;

lemma exists_max_packing {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_exists_packing : ∃ P : Finset (Finset V), P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
    have h_finite : (G.cliqueFinset 3).powerset.Nonempty := by
      exact ⟨ ∅, Finset.mem_powerset.mpr <| Finset.empty_subset _ ⟩
    have h_exists_packing : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧ ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card := by
      exact Finset.exists_max_image _ _ ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide [ IsEdgeDisjoint ] ⟩ ⟩;
    obtain ⟨ P, hP₁, hP₂ ⟩ := h_exists_packing; use P; aesop;
    exact le_antisymm ( Finset.le_sup ( f := Finset.card ) ( by aesop ) ) ( Finset.sup_le fun Q hQ => by aesop );
  exact h_exists_packing

lemma packing_one_implies_intersect {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  contrapose! h;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨ h1, Finset.singleton_subset_iff.mpr h2 ⟩, _ ⟩ ) );
  · rw [ Finset.card_pair ] ; aesop;
    unfold triangleEdges at h; aesop;
    simp_all +decide [ Finset.ext_iff ];
    have := Finset.card_eq_three.mp h2.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; specialize h a b; aesop;
  · intro x hx y hy hxy; aesop;
    exact h.symm

/-! ## ν=1 Case (proven in tuza_SUCCESS_nu1_case.lean) -/

/-- ν=1 implies τ≤2 via K₄ structure analysis -/
lemma tuza_case_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  -- Proof by contradiction (300+ lines in full version):
  -- 1. Assume τ > 2
  -- 2. Find triangles T1, T2, T3 each avoiding some pair of edges
  -- 3. T1, T2, T3 pairwise share edges (by packing_one_implies_intersect)
  -- 4. This forces K₄ structure with 4th vertex x
  -- 5. K₄ can be covered by 2 opposite edges, so τ ≤ 2, contradiction
  sorry

/-! ## Helper Lemmas for ν=2 Case -/

/-- A packing of size 2 gives exactly 2 edge-disjoint triangles -/
lemma packing_two_triangles {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  have hP_card_2 : P.card = 2 := by rw [← h]; exact hP_card
  -- Finset.card_eq_two.mp gives: ∃ x y, x ≠ y ∧ P = {x, y}
  obtain ⟨t1, t2, hne, hP_eq⟩ := Finset.card_eq_two.mp hP_card_2
  use t1, t2
  -- Derive membership from subset relation
  have ht1_mem : t1 ∈ P := hP_eq ▸ Finset.mem_insert_self t1 {t2}
  have ht2_mem : t2 ∈ P := hP_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t2)
  constructor
  · exact hP_sub ht1_mem
  constructor
  · exact hP_sub ht2_mem
  constructor
  · exact hne
  · unfold IsEdgeDisjoint at hP_disj
    exact hP_disj ht1_mem ht2_mem hne

/-- Two triangles sharing ≥2 vertices share an edge (hence not edge-disjoint) -/
lemma shared_two_vertices_implies_not_disjoint {V : Type} [DecidableEq V] (t1 t2 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h_inter : (t1 ∩ t2).card ≥ 2) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  rw [Finset.not_disjoint_iff]
  -- Get two distinct elements from the intersection
  obtain ⟨a, ha⟩ : ∃ a, a ∈ t1 ∩ t2 := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ t1 ∩ t2, b ≠ a := by
    obtain ⟨b, hb⟩ := Finset.exists_ne_of_one_lt_card (by omega) a
    exact ⟨b, hb.1, hb.2⟩
  -- The edge {a,b} is in both triangles' edge sets
  use Sym2.mk (a, b)
  constructor
  -- {a,b} ∈ triangleEdges t1
  · unfold triangleEdges
    simp only [Finset.mem_image, Finset.mem_offDiag]
    use (a, b)
    exact ⟨⟨Finset.mem_of_mem_inter_left ha, Finset.mem_of_mem_inter_left hb, hab⟩, rfl⟩
  -- {a,b} ∈ triangleEdges t2
  · unfold triangleEdges
    simp only [Finset.mem_image, Finset.mem_offDiag]
    use (a, b)
    exact ⟨⟨Finset.mem_of_mem_inter_right ha, Finset.mem_of_mem_inter_right hb, hab⟩, rfl⟩

/-- Monotonicity: Deleting edges cannot increase packing number -/
lemma packing_mono_deleteEdges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) :
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

/-! ## Main Target: ν=2 Case -/

/--
MAIN THEOREM: When ν(G) = 2, we have τ(G) ≤ 4

PROOF STRATEGY (analogous to ν=1):
1. Get two edge-disjoint triangles t1, t2 from packing_two_triangles
2. Case on |t1 ∩ t2|:
   - Case 0 (vertex-disjoint): 6 vertices
     → Triangles on vertices of t1 have ν≤1 after restricting
     → Similarly for t2
     → Cover each with ≤2 edges, total ≤4
   - Case 1 (bowtie): 5 vertices with shared vertex v
     → t1 = {a,b,v}, t2 = {v,c,d}
     → All triangles share edge with t1 or t2 (since ν=2)
     → Construct explicit 4-edge cover
   - Case ≥2: Impossible by shared_two_vertices_implies_not_disjoint
-/
theorem tuza_case_nu_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  -- Step 1: Get the two edge-disjoint triangles
  obtain ⟨t1, t2, ht1, ht2, hne, hdisj⟩ := packing_two_triangles G h
  -- Step 2: Extract card properties from membership (use mem_cliqueFinset_iff)
  have ht1_card : t1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht1).2
  have ht2_card : t2.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht2).2
  -- Step 3: They share at most 1 vertex (≥2 would contradict hdisj)
  have h_inter_le_1 : (t1 ∩ t2).card ≤ 1 := by
    by_contra h_contra; push_neg at h_contra
    exact hdisj (shared_two_vertices_implies_not_disjoint t1 t2 ht1_card ht2_card h_contra)
  -- Step 4: Case analysis
  -- Case 0: Disjoint triangles → use deletion lemma with each triangle's edges
  -- Case 1: Bowtie → construct explicit 4-edge cover using shared vertex structure
  sorry

end
