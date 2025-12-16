/-
TRIANGLE PACKING STRUCTURE FOR ν=2
Focus: Characterize all maximum packings when ν(G) = 2

INSIGHT: The reduction lemma for ν=2 requires proving that
≤2 edges can hit ALL maximum packings, not just one.

STRATEGY: Prove structural lemmas about when alternative packings exist,
then show 2 edges always suffice to hit them all.

CASE ANALYSIS (from Grok/literature):
1. Two vertex-disjoint triangles: Only ONE max packing exists
2. Bowtie (share 1 vertex): Alternatives only if 4-cycle allows "flip"
3. General connected: Alternatives rare, constrained structure

KEY LEMMA TO PROVE:
For any graph G with ν(G) = 2, the "blocking number" b(G) ≤ 2,
where b(G) = min edges to hit every maximum packing.
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

/-! ## The Family of All Maximum Packings -/

/-- The set of all maximum triangle packings in G -/
def maxPackings (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Finset V)) :=
  (G.cliqueFinset 3).powerset.filter (fun P => IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G)

/-- An edge set S "blocks" all maximum packings if every max packing uses at least one edge from S -/
def BlocksAllMaxPackings (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∀ P ∈ maxPackings G, ∃ t ∈ P, ¬ Disjoint (triangleEdges t) S

/-- The blocking number: minimum edges to hit all maximum packings -/
def blockingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (BlocksAllMaxPackings G)).image Finset.card
    |>.min.getD G.edgeFinset.card

/-! ## Structural Lemmas for ν=2 -/

/-- When ν=2, extract the two triangles in a max packing -/
lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  sorry

/-- Two triangles sharing ≥2 vertices share an edge -/
lemma shared_vertices_implies_shared_edge (t1 t2 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h_inter : 2 ≤ (t1 ∩ t2).card) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  sorry

/-! ## Case 1: Vertex-Disjoint Triangles -/

/-- When the two packing triangles are vertex-disjoint, they form the UNIQUE max packing
    (any other triangle must share edge with one of them, so can't form size-2 packing) -/
lemma vertex_disjoint_unique_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hne : t1 ≠ t2) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (h_vertex_disj : Disjoint t1 t2) :
    maxPackings G = {{t1, t2}} := by
  sorry

/-- For vertex-disjoint case: ANY 2 edges from t1 ∪ t2 block all max packings
    (since there's only one max packing) -/
lemma vertex_disjoint_blocking (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (h_vertex_disj : Disjoint t1 t2)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ triangleEdges t1) (he2 : e2 ∈ triangleEdges t2) :
    BlocksAllMaxPackings G {e1, e2} := by
  sorry

/-! ## Case 2: Bowtie (Shared Vertex) -/

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

/-- When two triangles share exactly one vertex, characterize alternative packings -/
lemma bowtie_alternatives (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (bow : Bowtie G) :
    -- Alternative packing exists iff certain 4-cycle structure exists
    (∃ P ∈ maxPackings G, P ≠ {{bow.center, bow.left1, bow.left2}, {bow.center, bow.right1, bow.right2}}) ↔
    -- There's a "crossing" triangle using vertices from both wings
    (G.Adj bow.left1 bow.right1 ∨ G.Adj bow.left1 bow.right2 ∨
     G.Adj bow.left2 bow.right1 ∨ G.Adj bow.left2 bow.right2) := by
  sorry

/-- For bowtie: the two edges incident to center block all max packings -/
lemma bowtie_center_edges_block (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (bow : Bowtie G) :
    let e1 := s(bow.center, bow.left1)
    let e2 := s(bow.center, bow.right1)
    BlocksAllMaxPackings G {e1, e2} := by
  sorry

/-! ## Main Theorem: Blocking Number ≤ 2 for ν=2 -/

/-- THE KEY STRUCTURAL THEOREM:
    When ν(G) = 2, there always exist 2 edges that hit every maximum packing -/
theorem blocking_number_le_2_when_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    blockingNumber G ≤ 2 := by
  -- Case split on whether the two packing triangles share a vertex
  obtain ⟨t1, t2, ht1, ht2, hne, h_edge_disj⟩ := packing_two_triangles G h
  by_cases h_vertex_disj : Disjoint t1 t2
  · -- Case 1: Vertex-disjoint → unique packing → trivial
    sorry
  · -- Case 2: Share vertex(es) → bowtie structure → center edges work
    sorry

/-! ## Corollary: The Reduction Lemma for ν=2 -/

/-- Blocking all max packings with 2 edges implies ν decreases -/
lemma blocking_implies_nu_decrease (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (h_blocks : BlocksAllMaxPackings G S) :
    trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  sorry

/-- THE REDUCTION LEMMA FOR ν=2:
    When ν(G) = 2, there exist ≤2 edges whose removal reduces ν -/
theorem exists_two_edge_reduction_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < 2 := by
  have h_block := blocking_number_le_2_when_nu_2 G h
  -- Extract the blocking set from the definition
  sorry

end
