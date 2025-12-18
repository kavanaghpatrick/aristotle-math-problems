/-
TUZA ν=2 VERSION 2: Building on YOUR proven lemmas

=== YOUR PROVEN WORK (fed back with full proofs) ===
1. packing_two_triangles - extract two edge-disjoint triangles
2. shared_vertices_implies_shared_edge - geometry lemma
3. vertex_disjoint_blocking - blocking for disjoint case
4. blocking_implies_nu_decrease - GENERAL tool
5. exists_two_edge_reduction_nu_2 - THE REDUCTION LEMMA

=== KEY TARGETS (focus your effort here) ===
1. vertex_disjoint_unique_packing - THE CRITICAL BLOCKER
   Strategy: Assume another packing P exists, show it must share edges with {t1,t2}

2. bowtie_alternatives - characterize alternative packings
3. bowtie_center_edges_block - center edges block in bowtie
4. blocking_number_le_2_when_nu_2 - unifies both cases

Priority: vertex_disjoint_unique_packing is the key - solve it first!
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

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  IsTrianglePacking G P ∧ P.card = trianglePackingNumber G

def maxPackings (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Finset V)) :=
  (G.cliqueFinset 3).powerset.filter (fun P => IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G)

def BlocksAllMaxPackings (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∀ P ∈ maxPackings G, ∃ t ∈ P, ¬ Disjoint (triangleEdges t) S

def blockingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (BlocksAllMaxPackings G)).image Finset.card
    |>.min.getD G.edgeFinset.card

/-! ## YOUR PROVEN LEMMAS (from v1) -/

/-- When ν=2, extract the two triangles [YOU PROVED THIS] -/
lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  aesop;
  obtain ⟨P, hP⟩ : ∃ P : Finset (Finset V), P ∈ Finset.powerset (G.cliqueFinset 3) ∧ IsEdgeDisjoint P ∧ P.card = 2 := by
    by_contra h_contra;
    have h_contra : ∀ P ∈ Finset.powerset (G.cliqueFinset 3), IsEdgeDisjoint P → P.card ≤ 1 := by
      intro P hP hP'; exact Nat.le_of_not_lt fun hP'' => h_contra ⟨ P, hP, hP', by linarith [ show P.card ≤ 2 from h ▸ Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ hP, hP' ⟩ ) ] ⟩ ;
    exact absurd h ( ne_of_lt ( lt_of_le_of_lt ( Finset.sup_le fun P hP => h_contra P ( Finset.mem_filter.mp hP |>.1 ) ( Finset.mem_filter.mp hP |>.2 ) ) ( by decide ) ) );
  rcases Finset.card_eq_two.mp hP.2.2 with ⟨ t1, t2, ht1, ht2, h ⟩ ; use t1, ?_, t2, ?_, ?_, ?_ <;> aesop;
  · exact Finset.mem_filter.mp ( left ( Finset.mem_insert_self _ _ ) ) |>.2;
  · simp_all +decide [ Finset.insert_subset_iff ]

/-- Two triangles sharing ≥2 vertices share an edge [YOU PROVED THIS] -/
lemma shared_vertices_implies_shared_edge (t1 t2 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h_inter : 2 ≤ (t1 ∩ t2).card) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  bound;
  obtain ⟨v1, v2, hv1, hv2⟩ : ∃ v1 v2 : V, v1 ∈ t1 ∧ v2 ∈ t1 ∧ v1 ≠ v2 ∧ v1 ∈ t2 ∧ v2 ∈ t2 := by
    have := Finset.one_lt_card.1 ( lt_of_lt_of_le ( by decide ) h_inter ) ; aesop;
  exact Finset.disjoint_left.mp a ( Finset.mem_image.mpr ⟨ ( v1, v2 ), by aesop ⟩ ) ( Finset.mem_image.mpr ⟨ ( v1, v2 ), by aesop ⟩ )

/-- Blocking all max packings → ν decreases [YOU PROVED THIS - GENERAL TOOL] -/
lemma blocking_implies_nu_decrease (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (h_blocks : BlocksAllMaxPackings G S) :
    trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  refine' Nat.lt_of_le_of_lt ( Finset.sup_le _ ) _;
  exact trianglePackingNumber G - 1;
  · intro b hb
    have h_b_max_packing : b.card ≤ trianglePackingNumber G := by
      refine' Finset.le_sup ( f := Finset.card ) _;
      aesop;
      intro t ht; specialize left ht; aesop;
      rw [ SimpleGraph.isNClique_iff ] at * ; aesop;
      intro x hx y hy hxy; specialize left hx hy hxy; aesop;
    cases lt_or_eq_of_le h_b_max_packing <;> aesop;
    · exact Nat.le_sub_one_of_lt h;
    · have := h_blocks b ?_ <;> simp_all +decide [ Finset.subset_iff ];
      · obtain ⟨ t, ht₁, ht₂ ⟩ := this; specialize left ht₁; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        rw [ Finset.disjoint_left ] at ht₂ ; aesop;
        unfold triangleEdges at left_1; aesop;
        have := left left_1 left_2; simp_all +decide [ SimpleGraph.deleteEdges ] ;
      · unfold maxPackings; aesop;
        intro x hx; specialize left hx; rw [ SimpleGraph.isNClique_iff ] at left; aesop;
        rw [ SimpleGraph.isNClique_iff ] ; aesop;
        intro u hu v hv huv; specialize left hu hv; aesop;
  · contrapose! h_blocks;
    rcases n : trianglePackingNumber G with ( _ | _ | n ) <;> simp_all +decide;
    unfold BlocksAllMaxPackings;
    unfold maxPackings;
    simp +decide [ n, IsEdgeDisjoint ]

/-! ## KEY TARGET 1: vertex_disjoint_unique_packing (CRITICAL) -/

/-- THE CRITICAL LEMMA: Vertex-disjoint triangles form UNIQUE max packing.

PROOF STRATEGY:
- Assume another packing P exists with |P| = 2
- P must contain two edge-disjoint triangles s1, s2
- If s1 ∉ {t1, t2}, then s1 uses vertices outside t1 ∪ t2 (since t1, t2 vertex-disjoint)
- But then s1 can't share edges with t1 or t2
- So {t1, t2, s1} would be 3 edge-disjoint triangles, contradicting ν = 2

Alternative: Use that any triangle in G either IS t1 or t2, or shares a vertex with one of them.
If it shares a vertex, by vertex-disjointness of t1,t2, it shares with exactly one.
-/
lemma vertex_disjoint_unique_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hne : t1 ≠ t2) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (h_vertex_disj : Disjoint t1 t2) :
    maxPackings G = {{t1, t2}} := by
  -- Key insight: Any other triangle must share a vertex with t1 or t2
  -- If it shares with t1, it shares an edge (since triangles share ≥2 vertices → share edge)
  -- Wait, sharing 1 vertex doesn't imply sharing edge. Need different approach.
  --
  -- Better: If there's another max packing P = {s1, s2}, then either:
  -- - s1 = t1 or s1 = t2 (then s2 must be the other, so P = {t1,t2})
  -- - s1 ∉ {t1, t2}, meaning s1 is edge-disjoint from both t1 AND t2
  --   But then {t1, t2, s1} would give ν ≥ 3, contradiction
  sorry

/-- For vertex-disjoint case: edges block all max packings [YOU PROVED THIS] -/
lemma vertex_disjoint_blocking (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (h_vertex_disj : Disjoint t1 t2)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ triangleEdges t1) (he2 : e2 ∈ triangleEdges t2) :
    BlocksAllMaxPackings G {e1, e2} := by
  have h_unique : maxPackings G = {{t1, t2}} := by
    apply vertex_disjoint_unique_packing G h t1 t2 ht1 ht2;
    · aesop;
    · unfold triangleEdges; aesop;
      simp_all +decide [ Finset.disjoint_left, Sym2.forall ];
      grind;
    · assumption;
  unfold BlocksAllMaxPackings; aesop;

/-! ## KEY TARGET 2: Bowtie Case -/

/-- Structure of a bowtie: two triangles sharing exactly one vertex -/
structure Bowtie (G : SimpleGraph V) [DecidableRel G.Adj] where
  center : V
  left1 : V
  left2 : V
  right1 : V
  right2 : V
  h_distinct : ({center, left1, left2, right1, right2} : Finset V).card = 5
  h_left_triangle : G.Adj center left1 ∧ G.Adj center left2 ∧ G.Adj left1 left2
  h_right_triangle : G.Adj center right1 ∧ G.Adj center right2 ∧ G.Adj right1 right2

/-- Characterize alternative packings in bowtie case -/
lemma bowtie_alternatives (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (bow : Bowtie G) :
    (∃ P ∈ maxPackings G, P ≠ {{bow.center, bow.left1, bow.left2}, {bow.center, bow.right1, bow.right2}}) ↔
    (G.Adj bow.left1 bow.right1 ∨ G.Adj bow.left1 bow.right2 ∨
     G.Adj bow.left2 bow.right1 ∨ G.Adj bow.left2 bow.right2) := by
  sorry

/-- For bowtie: center edges block all max packings -/
lemma bowtie_center_edges_block (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (bow : Bowtie G) :
    let e1 := s(bow.center, bow.left1)
    let e2 := s(bow.center, bow.right1)
    BlocksAllMaxPackings G {e1, e2} := by
  sorry

/-! ## MAIN STRUCTURAL THEOREM -/

/-- When ν(G) = 2, blocking number ≤ 2 -/
theorem blocking_number_le_2_when_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    blockingNumber G ≤ 2 := by
  obtain ⟨t1, t2, ht1, ht2, hne, h_edge_disj⟩ := packing_two_triangles G h
  by_cases h_vertex_disj : Disjoint t1 t2
  · -- Case 1: Vertex-disjoint → use vertex_disjoint_blocking
    -- Need to show blockingNumber ≤ 2
    -- We know {e1, e2} blocks for any e1 ∈ t1, e2 ∈ t2
    sorry
  · -- Case 2: Share vertex(es) → bowtie structure
    -- By shared_vertices_implies_shared_edge, if share ≥2 vertices, share edge
    -- So they share exactly 1 vertex (bowtie)
    sorry

/-! ## THE REDUCTION LEMMA (builds on above) -/

/-- THE REDUCTION LEMMA FOR ν=2 [YOU PROVED THIS] -/
theorem exists_two_edge_reduction_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < 2 := by
  have h_block := blocking_number_le_2_when_nu_2 G h
  obtain ⟨S, hS⟩ : ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ BlocksAllMaxPackings G S ∧ S.card = blockingNumber G := by
    unfold blockingNumber;
    have h_exists_S : Finset.Nonempty (Finset.filter (BlocksAllMaxPackings G) G.edgeFinset.powerset) := by
      refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ BlocksAllMaxPackings ];
      intro P hP
      obtain ⟨t, ht⟩ : ∃ t ∈ P, t ∈ G.cliqueFinset 3 := by
        unfold maxPackings at hP; aesop;
        exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun t ht => ⟨ t, ht, by simpa using left ht ⟩;
      simp_all +decide [ Finset.disjoint_left, SimpleGraph.cliqueFinset ];
      rcases ht.2 with ⟨ ht₁, ht₂ ⟩;
      rcases Finset.card_eq_three.mp ht₂ with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; use t, ht.1 ; use s(x, y) ; simp_all +decide [ SimpleGraph.isNClique_iff ];
      exact Finset.mem_image.mpr ⟨ ( x, y ), by aesop ⟩;
    have := Finset.min_of_mem ( Finset.mem_image_of_mem Finset.card h_exists_S.choose_spec );
    cases' this with b hb; have := Finset.mem_of_min hb; aesop;
  exact ⟨ S, hS.2.2.symm ▸ h_block, hS.1, by linarith [ blocking_implies_nu_decrease G S hS.1 hS.2.1 ] ⟩

end
