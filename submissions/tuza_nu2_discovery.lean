/-
TUZA'S CONJECTURE ν=2: DISCOVERY MODE

=== PROVEN BUILDING BLOCKS (use freely) ===
1. tuza_case_nu_1: ν(G)=1 → τ(G)≤2 [PROVEN]
2. tuza_base_case: ν(G)=0 → τ(G)=0 [PROVEN]
3. packing_two_triangles: ν=2 → ∃ t1,t2 edge-disjoint triangles [PROVEN]
4. blocking_number_le_2: ν=2 → ≤2 edges hit all max packings [PROVEN]
5. triangleCoveringNumber_le_card_add_deleteEdges: τ(G) ≤ |S| + τ(G\S) [PROVEN]
6. packing_one_implies_intersect: ν=1 → any two triangles share edge [PROVEN]

=== THE GAP ===
We need: τ(G) ≤ 4 when ν(G) = 2

One approach (STUCK): exists_reducing_edges
  ∃ S, |S| ≤ 2 ∧ ν(G\S) ≤ 1
This + deletion lemma + ν≤1 case would give τ ≤ 2 + 2 = 4.

=== YOUR MISSION: EXPLORE FREELY ===
You have complete freedom. Possibilities:

1. PROVE exists_reducing_edges if you can find the right approach
2. Find a COUNTEREXAMPLE to exists_reducing_edges (graph where no 2 edges reduce ν)
3. Find an ALTERNATIVE path to τ≤4 that bypasses exists_reducing_edges entirely
4. Discover STRUCTURAL PROPERTIES of ν=2 graphs we haven't noticed
5. Find MATHLIB CONNECTIONS - edge covers, fractional covers, LP duality?
6. Prove a WEAKER result: τ ≤ 5? τ ≤ 6? Any bound?
7. Characterize the EXTREMAL case: when is τ = 4 achieved? (K₅ has ν=2, τ=4)

=== KEY INSIGHT FROM PRIOR WORK ===
vertex_disjoint_unique_packing was NEGATED - counterexample exists!
Graph on 7 vertices where vertex-disjoint t1={0,1,2}, t2={3,4,5} are NOT the unique max packing.
This killed our "unique packing" approach.

=== QUESTIONS TO EXPLORE ===
- What makes K₅ extremal? (ν=2, τ=4, and τ=4 is tight)
- If t1, t2 are edge-disjoint, what constrains t3, t4, ...?
- Can fractional relaxation help? (Tuza proved τ ≤ 2ν for fractional)
- Is there a vertex-degree argument?

Output whatever you discover. Partial progress is valuable.
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

/-! ## Proven Building Blocks (from prior submissions) -/

lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  sorry -- PROVEN in prior submission, included as foundation

lemma packing_one_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  sorry -- PROVEN

lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry -- PROVEN

lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  sorry -- PROVEN

lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  sorry -- PROVEN

lemma packing_mono_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) :
    trianglePackingNumber (G.deleteEdges S) ≤ trianglePackingNumber G := by
  sorry -- PROVEN

/-! ## DISCOVERY ZONE - Explore freely below -/

-- Approach 1: The stuck lemma - can you prove it?
lemma exists_reducing_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) ≤ 1 := by
  sorry

-- Approach 2: Alternative - maybe direct construction works?
lemma tuza_nu2_direct (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

-- Approach 3: Weaker bound - can we at least get τ ≤ 5 or τ ≤ 6?
lemma tuza_nu2_weak (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 6 := by
  sorry

-- Approach 4: Structure theorem - what DO we know about ν=2 graphs?
-- Maybe characterizing them helps

-- Explore: What's special about the two edge-disjoint triangles?
lemma nu2_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hdisj : Disjoint (triangleEdges t1) (triangleEdges t2)) :
    -- What can we say about other triangles t3?
    ∀ t3 ∈ G.cliqueFinset 3,
      ¬Disjoint (triangleEdges t3) (triangleEdges t1) ∨
      ¬Disjoint (triangleEdges t3) (triangleEdges t2) := by
  sorry

-- Explore: K₅ extremal case
-- K₅ has exactly 10 triangles, ν=2, τ=4
-- Can we prove this specific case?

-- Explore: Vertex overlap patterns
-- If t1 ∩ t2 = ∅ (vertex disjoint), what happens?
-- If |t1 ∩ t2| = 1 (share one vertex), what happens?
-- If |t1 ∩ t2| = 2 (share an edge), IMPOSSIBLE since edge-disjoint

-- YOUR DISCOVERIES GO HERE
-- Add any lemmas, counterexamples, or observations you find

end
