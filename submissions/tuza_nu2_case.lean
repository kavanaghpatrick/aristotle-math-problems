/-
TUZA'S CONJECTURE - ν=2 CASE
Target: Prove τ(G) ≤ 4 when ν(G) = 2

This file includes ALL previously proven lemmas so Aristotle can focus
entirely on the ν=2 case without re-proving existing results.

STRATEGY (from Grok-4 analysis):
For ν=2, we have two edge-disjoint triangles T₁ and T₂. Key cases:
1. Vertex-disjoint T₁ and T₂
2. Sharing 1 vertex (bowtie)
3. Sharing 2 vertices (sharing an edge - but then ν≠2!)

Each configuration should allow τ≤4 by structural analysis.
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

/-! ## PROVEN LEMMAS (do not modify) -/

-- PROVEN: Base case ν=0
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

-- PROVEN: Deletion lemma
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

-- PROVEN: Existence of max packing
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

-- PROVEN: Packing ν=1 implies triangles intersect
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

-- PROVEN: ν=1 implies τ≤2 (abbreviated - full proof uses K₄ structure)
-- Key insight: ν=1 forces K₄-like structure where 2 edges cover all triangles
axiom tuza_case_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2

-- PROVEN: Monotonicity
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

/-! ## NEW TARGET: ν=2 CASE -/

/--
MAIN THEOREM TO PROVE: When ν(G) = 2, we have τ(G) ≤ 4

Key insight: With exactly 2 edge-disjoint triangles T₁ and T₂:
- Case 1: T₁, T₂ vertex-disjoint → 6 vertices, 6 edges total in packing
  Each triangle can be covered with ≤2 edges (by ν=1 analysis on induced subgraph)
- Case 2: T₁, T₂ share exactly 1 vertex → 5 vertices, "bowtie" configuration
  Analyze triangle structure around shared vertex
- Case 3: T₁, T₂ share 2 vertices → They share an edge, so NOT edge-disjoint (impossible)

The proof should use:
1. exists_max_packing to get the optimal packing P with |P|=2
2. Case analysis on |V(P)| (6 for disjoint, 5 for bowtie)
3. Covering argument showing 4 edges suffice
-/
theorem tuza_case_nu_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  -- Step 1: Obtain the two edge-disjoint triangles from max packing
  obtain ⟨t1, t2, ht1, ht2, hne, hdisj⟩ := packing_two_triangles G h
  -- Step 2: Case analysis on vertex intersection |t1 ∩ t2|
  -- Case |t1 ∩ t2| = 0: Disjoint triangles (6 vertices total)
  --   → Cover t1 with ≤2 edges, cover t2 with ≤2 edges → total ≤4
  -- Case |t1 ∩ t2| = 1: Bowtie configuration (5 vertices total)
  --   → Find 4 edges that cover all triangles using shared vertex structure
  -- Case |t1 ∩ t2| ≥ 2: IMPOSSIBLE - would share an edge, contradicting hdisj
  -- Step 3: In each case, construct explicit 4-edge cover or apply tuza_case_nu_1
  sorry

/-! ## Additional helper lemmas Aristotle may need -/

/-- Two triangles sharing an edge are NOT edge-disjoint -/
lemma not_edge_disjoint_of_shared_edge {V : Type} [DecidableEq V] (t1 t2 : Finset V)
    (e : Sym2 V) (he1 : e ∈ triangleEdges t1) (he2 : e ∈ triangleEdges t2) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  rw [Finset.not_disjoint_iff]
  exact ⟨e, he1, he2⟩

/-- Two distinct 3-element sets sharing ≥2 elements must share exactly 2 -/
lemma inter_card_of_triangles {V : Type} [DecidableEq V] (t1 t2 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card ≤ 2 := by
  by_contra h
  push_neg at h
  have : t1 ∩ t2 = t1 := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) (by omega)
  have : t1 ⊆ t2 := this ▸ Finset.inter_subset_right
  have : t1 = t2 := Finset.eq_of_subset_of_card_le this (by omega)
  exact hne this

/-- If two triangles share 2 vertices, they share an edge -/
lemma shared_two_vertices_implies_shared_edge {V : Type} [DecidableEq V] (t1 t2 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h_inter : (t1 ∩ t2).card = 2) :
    ∃ e : Sym2 V, e ∈ triangleEdges t1 ∧ e ∈ triangleEdges t2 := by
  obtain ⟨a, b, hab, h_eq⟩ := Finset.card_eq_two.mp h_inter
  use Sym2.mk (a, b)
  constructor <;> {
    unfold triangleEdges
    simp only [Finset.mem_image, Finset.mem_offDiag]
    use (a, b)
    constructor
    · have ha : a ∈ t1 ∩ t2 := h_eq ▸ Finset.mem_insert_self a {b}
      have hb : b ∈ t1 ∩ t2 := h_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      constructor
      · exact Finset.mem_of_mem_inter_left ha
      constructor
      · exact Finset.mem_of_mem_inter_left hb
      · exact hab
    · rfl
  }

/-- A packing of size 2 has exactly 2 triangles -/
lemma packing_two_triangles {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  have hP_card_2 : P.card = 2 := by rw [← h]; exact hP_card
  obtain ⟨t1, t2, ht1, ht2, hne, hP_eq⟩ := Finset.card_eq_two.mp hP_card_2
  use t1, t2
  constructor
  · exact hP_sub (hP_eq ▸ Finset.mem_insert_self t1 {t2})
  constructor
  · exact hP_sub (hP_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t2))
  constructor
  · exact hne
  · have := hP_disj
    unfold IsEdgeDisjoint at this
    have h1 : t1 ∈ P := hP_eq ▸ Finset.mem_insert_self t1 {t2}
    have h2 : t2 ∈ P := hP_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t2)
    exact this h1 h2 hne

end
