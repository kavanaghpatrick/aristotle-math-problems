/-
  slot481_counterexample_test.lean

  TEST: Does the 2-edges-per-M construction always work?

  POTENTIAL COUNTEREXAMPLE CONSTRUCTION:
  Consider vertices {1, 2, 3, 4, 5, 6, 7} with:
  - m1 = {1, 2, 4}
  - m2 = {1, 3, 5}
  - m3 = {2, 3, 6}
  - m4 = {4, 5, 7}
  - t = {1, 2, 3} (the "bridge" triangle)

  t shares:
  - {1, 2} with m1
  - {1, 3} with m2
  - {2, 3} with m3

  If {1,2}-externals is empty for m1, then m1 picks {1,4}, {2,4}.
  If {1,3}-externals is empty for m2, then m2 picks {1,5}, {3,5}.
  If {2,3}-externals is empty for m3, then m3 picks {2,6}, {3,6}.

  None of these edges are edges of t!

  Question: Can all three external sets be empty simultaneously?
  Answer: YES, if the only triangles in the graph are exactly:
    m1, m2, m3, m4, t, and {1,4,5}

  But τ for this graph is actually 4 (pick edges of t plus {4,5}).
  So τ ≤ 8 is still satisfied, just not via the 2-per-M construction.

  CONCLUSION: The 2-edges-per-M construction with 6-packing selection
  is NOT guaranteed to give a valid cover. Need different approach.

  CORRECT APPROACH: The edge selection must be ADAPTIVE based on
  triangle structure, not just based on externals.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- THE CORRECT τ ≤ 8 PROOF FOR ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
CORRECT APPROACH: Use ALL edges from M, then prove |M_edges| ≤ 8 via structure.

Wait, that gives 12 edges (4 triangles × 3 edges), not 8.

ALTERNATIVE: For each triangle t in graph:
- t shares ≥2 with some m ∈ M (maximality)
- So t shares at least 1 edge with m
- That edge of m is in our cover

The cover is: union of all edges from all M-elements that are shared with
some non-M triangle.

Hmm, but this could still be up to 12 edges.

ACTUAL CORRECT PROOF (literature):
For ν ≤ 4, use the fact that the "intersection graph" of triangles has
special structure. The Haxell-Kohayakawa-Łuczak proof uses LP relaxation
and probabilistic methods.

For a cleaner proof, observe:
- M has 4 elements, each contributing ≤3 edges to the cover.
- But edges are shared among M-elements via bridges.
- With careful accounting, total is ≤ 8.

Actually, the cleanest proof:
1. Pick 2 edges from each M-element (any choice).
2. For triangles not covered, they must be bridges.
3. Bridges share vertex with ≥2 M-elements.
4. There can be at most "a few" bridges, and they can be covered
   by adjusting edge choices.

The key insight: bridges are "rare" in some sense.

Let me formalize the "bridge bound" approach.
-/

-- Count how many distinct M-elements a triangle shares ≥2 with
def bridgeCount (t : Finset V) (M : Finset (Finset V)) : ℕ :=
  (M.filter (fun m => (t ∩ m).card ≥ 2)).card

-- A triangle is a "bridge" if it shares ≥2 with multiple M-elements
def isBridge (t : Finset V) (M : Finset (Finset V)) : Prop :=
  bridgeCount t M ≥ 2

/--
KEY LEMMA: If M is a 4-packing and t is a bridge (shares ≥2 with ≥2 M-elements),
then t shares a common vertex with all M-elements it bridges.

PROOF SKETCH:
Suppose t shares ≥2 with m1 and m2.
t ∩ m1 has ≥2 elements, t ∩ m2 has ≥2 elements.
t has only 3 vertices.
By pigeonhole, (t ∩ m1) ∩ (t ∩ m2) is non-empty.
Let v ∈ (t ∩ m1) ∩ (t ∩ m2).
Then v ∈ m1 ∩ m2.
Since M is a packing, |m1 ∩ m2| ≤ 1, so m1 ∩ m2 = {v}.

So all M-elements that t bridges share the same vertex v.
-/
lemma bridge_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M) (hne : m1 ≠ m2)
    (h1 : (t ∩ m1).card ≥ 2) (h2 : (t ∩ m2).card ≥ 2) :
    ∃ v, v ∈ t ∧ v ∈ m1 ∧ v ∈ m2 ∧ m1 ∩ m2 = {v} := by
  -- By pigeonhole on t's 3 vertices
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have h_overlap : ((t ∩ m1) ∩ (t ∩ m2)).Nonempty := by
    -- (t ∩ m1) ∪ (t ∩ m2) ⊆ t
    have h_sub : (t ∩ m1) ∪ (t ∩ m2) ⊆ t := by
      intro x hx
      simp only [mem_union, mem_inter] at hx
      rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
    have h_card_bound : ((t ∩ m1) ∪ (t ∩ m2)).card ≤ t.card := card_le_card h_sub
    -- By inclusion-exclusion
    have h_ie : (t ∩ m1).card + (t ∩ m2).card =
        ((t ∩ m1) ∪ (t ∩ m2)).card + ((t ∩ m1) ∩ (t ∩ m2)).card := by
      exact (card_union_add_card_inter (t ∩ m1) (t ∩ m2)).symm
    -- 2 + 2 ≤ 3 + inter_card → inter_card ≥ 1
    have h_inter_pos : ((t ∩ m1) ∩ (t ∩ m2)).card ≥ 1 := by
      omega
    exact card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := h_overlap
  simp only [mem_inter] at hv
  use v
  refine ⟨hv.1.1, hv.1.2, hv.2.2, ?_⟩
  -- m1 ∩ m2 = {v} by packing condition
  have h_packing := hM.2 hm1 hm2 hne
  have hv_in : v ∈ m1 ∩ m2 := mem_inter.mpr ⟨hv.1.2, hv.2.2⟩
  -- |m1 ∩ m2| ≤ 1 and v ∈ m1 ∩ m2 → m1 ∩ m2 = {v}
  have h_card_one : (m1 ∩ m2).card ≤ 1 := h_packing
  have h_card_ge : (m1 ∩ m2).card ≥ 1 := card_pos.mpr ⟨v, hv_in⟩
  have h_card_eq : (m1 ∩ m2).card = 1 := by omega
  exact card_eq_one.mp h_card_eq

/--
BRIDGE STRUCTURE THEOREM:
If t is a bridge (shares ≥2 with m1 and m2), then:
- m1 ∩ m2 = {v} for some vertex v
- v ∈ t
- t = {v, a, b} where a, b ∉ m1 ∩ m2
- t ∩ m1 = {v, a} or {v, b} or {v, a, b}
- t ∩ m2 = {v, c} or similar

The edges of t are {v, a}, {v, b}, {a, b}.
The shared edges are:
- With m1: {v, a} (assuming a ∈ m1)
- With m2: {v, b} (assuming b ∈ m2)

Key insight: Both shared edges go through v!

So if we include ANY edge through v from m1's edge set AND any edge through v
from m2's edge set, we might cover t.

Actually, both {v, a} and {v, b} are "spoke" edges through v.
If our cover includes {v, a} (from m1) or {v, b} (from m2), t is covered.

The 6-packing constraint might not pick these spokes if their externals are empty.
But we can MODIFY the selection to prioritize spoke edges for bridges.
-/

-- The correct proof needs a more sophisticated edge selection strategy.
-- For now, let's verify the bridge structure theorem.

theorem tau_le_8_corrected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  -- Strategy: partition triangles into:
  -- 1. "Internal" triangles (in some S_e) - covered by 6-packing edge selection
  -- 2. "Bridge" triangles - need special handling

  -- For bridges: use the fact that they share spoke vertex v with multiple M-elements.
  -- The spoke edges through v are in the union of M's edges.
  -- We need to ensure at least one such spoke is selected.

  -- Observation: If t bridges m1 and m2 via vertex v, then:
  -- - t has edge {v, a} in m1 (where a ∈ m1 \ {v})
  -- - t has edge {v, b} in m2 (where b ∈ m2 \ {v})
  -- - At least one of these is in our cover

  -- The key: ensure spoke edges are selected for vertices that are "busy"
  -- (shared by multiple M-elements).

  sorry

end
