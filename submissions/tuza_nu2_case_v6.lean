/-
TUZA'S CONJECTURE - ν=2 CASE (Enhanced Scaffolding)
Target: Prove τ(G) ≤ 4 when ν(G) = 2

This version includes MORE scaffolding based on what helped ν=1:
- Explicit structure lemmas for both cases (disjoint/bowtie)
- Cover construction lemmas
- Constraint lemmas about triangle structure

KEY INSIGHT: With ν=2, every triangle must share an edge with t1 OR t2.
This is analogous to how ν=1 forced K₄ structure.
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

/-! ## ν=1 Case (proven, used as building block) -/

lemma tuza_case_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

/-! ## Core Helper Lemmas for ν=2 -/

/-- A packing of size 2 gives exactly 2 edge-disjoint triangles -/
lemma packing_two_triangles {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  have hP_card_2 : P.card = 2 := by rw [← h]; exact hP_card
  obtain ⟨t1, t2, hne, hP_eq⟩ := Finset.card_eq_two.mp hP_card_2
  use t1, t2
  have ht1_mem : t1 ∈ P := hP_eq ▸ Finset.mem_insert_self t1 {t2}
  have ht2_mem : t2 ∈ P := hP_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t2)
  constructor; · exact hP_sub ht1_mem
  constructor; · exact hP_sub ht2_mem
  constructor; · exact hne
  · unfold IsEdgeDisjoint at hP_disj
    exact hP_disj ht1_mem ht2_mem hne

/-- Two triangles sharing ≥2 vertices share an edge -/
lemma shared_two_vertices_implies_not_disjoint {V : Type} [DecidableEq V] (t1 t2 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h_inter : (t1 ∩ t2).card ≥ 2) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  rw [Finset.not_disjoint_iff]
  obtain ⟨a, ha⟩ : ∃ a, a ∈ t1 ∩ t2 := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ t1 ∩ t2, b ≠ a := by
    obtain ⟨b, hb⟩ := Finset.exists_ne_of_one_lt_card (by omega) a
    exact ⟨b, hb.1, hb.2⟩
  use Sym2.mk (a, b)
  constructor
  · unfold triangleEdges
    simp only [Finset.mem_image, Finset.mem_offDiag]
    use (a, b)
    exact ⟨⟨Finset.mem_of_mem_inter_left ha, Finset.mem_of_mem_inter_left hb, hab⟩, rfl⟩
  · unfold triangleEdges
    simp only [Finset.mem_image, Finset.mem_offDiag]
    use (a, b)
    exact ⟨⟨Finset.mem_of_mem_inter_right ha, Finset.mem_of_mem_inter_right hb, hab⟩, rfl⟩

/-! ## KEY CONSTRAINT: All triangles share edge with packing -/

/-- When ν=2, every triangle shares an edge with t1 or t2.
    This is the ν=2 analogue of packing_one_implies_intersect from ν=1.
    Proof: If triangle t is edge-disjoint from both t1 and t2,
    then {t1, t2, t} would be a packing of size 3, contradicting ν=2. -/
lemma triangle_shares_edge_with_packing {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hne : t1 ≠ t2) (hdisj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t) (triangleEdges t1) ∨
    ¬ Disjoint (triangleEdges t) (triangleEdges t2) := by
  -- If t is edge-disjoint from both, {t1, t2, t} has size 3, contradicting ν=2
  by_contra h_contra
  push_neg at h_contra
  obtain ⟨hdisj_t1, hdisj_t2⟩ := h_contra
  -- The set {t1, t2, t} is edge-disjoint with 3 elements
  have h_three : ({t1, t2, t} : Finset (Finset V)).card ≥ 3 := by
    simp_all +decide [Finset.card_insert_of_not_mem]
    -- Need t ∉ {t1, t2} - if t = t1 or t = t2, the disjointness is violated
    sorry
  have h_packing_3 : trianglePackingNumber G ≥ 3 := by
    sorry
  omega

/-! ## CASE 0: Vertex-Disjoint Triangles (6 vertices) -/

/-- When t1 and t2 are vertex-disjoint, they have 6 distinct vertices.
    Covering: Each triangle can be covered independently. -/
lemma disjoint_triangles_cover {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (h_vertex_disj : Disjoint t1 t2) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (h_nu : trianglePackingNumber G = 2) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 4 ∧ IsTriangleCovering G S := by
  -- Strategy: Pick 2 edges from t1, 2 edges from t2
  -- These 4 edges cover all triangles because:
  -- - Every triangle shares edge with t1 or t2 (triangle_shares_edge_with_packing)
  -- - 2 edges from a triangle cover all triangles sharing an edge with it
  sorry

/-! ## CASE 1: Bowtie Configuration (5 vertices, shared vertex v) -/

/-- In a bowtie, t1 = {a,b,v} and t2 = {v,c,d} share exactly vertex v.
    The 5 vertices are a, b, v, c, d.
    t1 has edges: {a,b}, {a,v}, {b,v}
    t2 has edges: {v,c}, {v,d}, {c,d}
    These 6 edges are all distinct (edge-disjoint). -/
lemma bowtie_structure {V : Type} [DecidableEq V]
    (t1 t2 : Finset V) (h1 : t1.card = 3) (h2 : t2.card = 3)
    (h_inter_1 : (t1 ∩ t2).card = 1) :
    ∃ (a b v c d : V),
      a ≠ b ∧ a ≠ v ∧ b ≠ v ∧ v ≠ c ∧ v ≠ d ∧ c ≠ d ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      t1 = {a, b, v} ∧ t2 = {v, c, d} := by
  -- The shared vertex is v, extract a,b from t1\{v} and c,d from t2\{v}
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h_inter_1
  have hv_t1 : v ∈ t1 := by rw [hv] at *; exact Finset.mem_inter.mp (Finset.mem_singleton_self v) |>.1
  have hv_t2 : v ∈ t2 := by rw [hv] at *; exact Finset.mem_inter.mp (Finset.mem_singleton_self v) |>.2
  -- t1 \ {v} has exactly 2 elements
  have h_t1_minus : (t1 \ {v}).card = 2 := by simp_all +decide [Finset.card_sdiff]
  obtain ⟨a, b, hab, h_t1_eq⟩ := Finset.card_eq_two.mp h_t1_minus
  -- t2 \ {v} has exactly 2 elements
  have h_t2_minus : (t2 \ {v}).card = 2 := by simp_all +decide [Finset.card_sdiff]
  obtain ⟨c, d, hcd, h_t2_eq⟩ := Finset.card_eq_two.mp h_t2_minus
  use a, b, v, c, d
  sorry

/-- In a bowtie configuration, 4 edges suffice to cover all triangles.
    Cover: {a,b}, {c,d}, {a,v}, {c,v} or similar combinations. -/
lemma bowtie_cover {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (h_inter_1 : (t1 ∩ t2).card = 1) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (h_nu : trianglePackingNumber G = 2) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 4 ∧ IsTriangleCovering G S := by
  -- Get bowtie structure
  obtain ⟨a, b, v, c, d, h_distinct, ht1_eq, ht2_eq⟩ := bowtie_structure t1 t2 ht1.2 ht2.2 h_inter_1
  -- Every triangle shares an edge with t1 or t2
  -- Construct cover using edges that hit all sharing patterns
  sorry

/-! ## MAIN THEOREM -/

/-- MAIN THEOREM: When ν(G) = 2, we have τ(G) ≤ 4 -/
theorem tuza_case_nu_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  -- Step 1: Get the two edge-disjoint triangles
  obtain ⟨t1, t2, ht1, ht2, hne, hdisj⟩ := packing_two_triangles G h
  -- Step 2: They share at most 1 vertex
  have h_inter_le_1 : (t1 ∩ t2).card ≤ 1 := by
    by_contra h_contra; push_neg at h_contra
    exact hdisj (shared_two_vertices_implies_not_disjoint t1 t2 ht1.2 ht2.2 h_contra)
  -- Step 3: Case split on intersection
  rcases Nat.lt_or_ge (t1 ∩ t2).card 1 with h_case0 | h_case1
  -- Case 0: Vertex-disjoint (|t1 ∩ t2| = 0)
  · have h_vertex_disj : Disjoint t1 t2 := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.card_eq_zero.mp (Nat.lt_one_iff.mp h_case0)
    obtain ⟨S, hS_card, hS_cover⟩ := disjoint_triangles_cover G t1 t2 ht1 ht2 h_vertex_disj hdisj h
    -- τ ≤ |S| ≤ 4
    unfold triangleCoveringNumber
    sorry
  -- Case 1: Bowtie (|t1 ∩ t2| = 1)
  · have h_inter_1 : (t1 ∩ t2).card = 1 := by omega
    obtain ⟨S, hS_card, hS_cover⟩ := bowtie_cover G t1 t2 ht1 ht2 h_inter_1 hdisj h
    -- τ ≤ |S| ≤ 4
    unfold triangleCoveringNumber
    sorry

end
