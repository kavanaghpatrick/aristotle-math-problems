/-
  slot313: τ ≤ 8 for PATH_4 - NEW PROOF STRATEGY

  PREVIOUS STRATEGY (FAILED):
  "2 edges from each element's apex covers everything"
  - FAILS for bridges when apex is forced away from shared vertices

  KEY INSIGHT (from Grok verification):
  The 8-edge cover doesn't need to come from packing element edges only!
  In the counterexample, Grok's 5-edge cover included {v1, x} where x is an EXTERNAL vertex.

  NEW STRATEGY:
  Instead of showing a SPECIFIC 8-edge construction, show that some 8-edge cover EXISTS.

  APPROACH 1: Greedy Cover
  Every triangle T in G is covered by SOME edge. The question is: what's the minimum?
  For ν = 4, we have at most 4 packing elements, each with 3 edges = 12 edges.
  But these may not be enough (some triangles use edges outside M).

  APPROACH 2: Adaptive Cover
  Partition triangles into:
  1. M-elements: 4 triangles, each has 3 edges
  2. X-externals: For each X ∈ M, 2 edges from common vertex cover X + all X-externals
  3. Bridges: Triangles sharing edges with multiple M-elements

  For bridges at shared vertex s (e.g., v2 between B and C):
  - Bridge T contains s (proven in slot309)
  - T has edges {s, b'} and {s, c'} where b' ∈ B, c' ∈ C
  - If we include {s, b'} in cover, T is covered!

  KEY LEMMA: If bridge T exists at shared vertex s between X and Y,
  we can include {s, x'} for some x' ∈ X \ {s} in the cover,
  and this edge covers T.

  REFINED STRATEGY:
  For each X ∈ M, choose 2 cover edges as follows:
  - If X has a shared vertex s with some Y, and bridges exist at s:
    Include edges {s, x1} and {s, x2} where x1, x2 are the other X-vertices
  - Else: Use apex-based edges (2 edges from common vertex of X-externals)

  This ensures bridges at s are covered by at least one adjacent element.

  PROOF SKETCH:
  1. Every triangle is in M, external to some X, or a bridge
  2. M-elements are covered by their own edges
  3. Externals are covered by two_edges_cover_all_externals
  4. Bridges at s are covered by {s, ?} edges from adjacent elements
  5. Total edges ≤ 8 (2 per element)

  ISSUE: What if an element X needs apex-based edges for externals AND
  shared-vertex edges for bridges, and these conflict?

  RESOLUTION: The common vertex from all_externals_share_common_vertex
  could BE the shared vertex s. In that case, apex edges = shared-vertex edges.

  The only conflict is when:
  - X's common vertex c_X ≠ s (external structure forces apex away from s)
  - Bridges exist at s (requiring {s, ?} edges)

  In this case, X's 2 edges go to c_X, not s.
  But the bridge at s is still covered by Y's edges (if Y's common is s).

  REMAINING GAP: What if BOTH adjacent elements have apex ≠ s?
  E.g., B's apex = v1, C's apex = v3, bridge at v2.

  Grok's solution: Use an edge {v2, b} which IS an edge of B!
  Even though B's apex is v1, we can CHOOSE to include {v2, b} instead of {v1, b}.

  NEW KEY LEMMA: For any triangle T sharing edge with X, we can include that
  shared edge in the cover. The shared edge IS a graph edge.

  So the cover for X can be ANY 2 edges that cover X + X-externals, not just apex edges.

  FINAL STRATEGY:
  For each X ∈ M with shared vertex s:
  - Include edge {s, x'} for some x' ∈ X (covers bridges at s)
  - Include one more edge to complete coverage of X and X-externals

  This requires proving: 2 edges suffice to cover X + X-externals + bridges at s.
-/

import Mathlib

set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW APPROACH: Edge-based cover construction
-- ══════════════════════════════════════════════════════════════════════════════

/-
KEY LEMMA: For any X ∈ M with |X| = 3 and X = {a, b, c}, any triangle T
containing vertex a and sharing edge with X is covered by edges {a, b} or {a, c}.

PROOF: If T contains a and shares edge {x, y} with X, then {x, y} ⊆ T ∩ X.
Since a ∈ T ∩ X, we have a ∈ {x, y} or a is the third vertex of T.
If a ∈ {x, y}, say a = x, then {a, y} is the shared edge, so y ∈ {b, c}.
Thus T contains edge {a, b} or {a, c}.
-/
lemma triangle_through_vertex_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX : X ∈ G.cliqueFinset 3) (hX_card : X.card = 3)
    (a b c : V) (hX_eq : X = {a, b, c}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (ha_in_T : a ∈ T) (h_share : sharesEdgeWith T X) :
    s(a, b) ∈ T.sym2 ∨ s(a, c) ∈ T.sym2 := by
  -- T shares edge with X, so T ∩ X has ≥ 2 elements
  -- a ∈ T ∩ X, so there's another element in T ∩ X
  -- That element is b or c
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := h_share
  have ha_X : a ∈ X := by simp [hX_eq]
  have h_inter : (T ∩ X).card ≥ 2 := by
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu_T, hu_X⟩,
                                   v, Finset.mem_inter.mpr ⟨hv_T, hv_X⟩, huv⟩
  have ha_inter : a ∈ T ∩ X := Finset.mem_inter.mpr ⟨ha_in_T, ha_X⟩
  -- Get another element in T ∩ X
  obtain ⟨w, hw_inter, hw_ne_a⟩ : ∃ w ∈ T ∩ X, w ≠ a := by
    have : 1 < (T ∩ X).card := by linarith
    exact Finset.exists_ne_of_one_lt_card this a ha_inter
  have hw_T : w ∈ T := (Finset.mem_inter.mp hw_inter).1
  have hw_X : w ∈ X := (Finset.mem_inter.mp hw_inter).2
  -- w ∈ X = {a, b, c} and w ≠ a, so w = b or w = c
  rw [hX_eq] at hw_X
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw_X
  rcases hw_X with rfl | rfl | rfl
  · exact absurd rfl hw_ne_a
  · left; simp only [Finset.mem_sym2_iff]; exact ⟨ha_in_T, hw_T⟩
  · right; simp only [Finset.mem_sym2_iff]; exact ⟨ha_in_T, hw_T⟩

/-
COROLLARY: For X = {a, b, c} with shared vertex a (with some Y ∈ M),
the edges {a, b} and {a, c} cover:
1. X itself
2. All triangles sharing edge with X that contain a
3. All bridges at a (they contain a by bridge_triangle_contains_shared_vertex)
-/

/-
MAIN THEOREM: τ ≤ 8 for PATH_4

NEW PROOF STRATEGY:
For each X ∈ M, choose 2 edges passing through a "hub" vertex h_X:
- If X has shared vertices with adjacent elements, use one of them as hub
- The 2 edges {h_X, x1}, {h_X, x2} cover X + all triangles through h_X

For PATH_4: M = {A, B, C, D}
- A = {v1, a1, a2}: hub = v1, edges {v1, a1}, {v1, a2}
- B = {v1, v2, b}: hub = v2, edges {v1, v2}, {v2, b}
- C = {v2, v3, c}: hub = v2, edges {v2, v3}, {v2, c}
- D = {v3, d1, d2}: hub = v3, edges {v3, d1}, {v3, d2}

Total: 8 edges

Coverage:
- A: {v1, a1} ✓
- B: {v1, v2} ✓
- C: {v2, v3} ✓
- D: {v3, d1} ✓
- A-externals: All share edge with A, which has edges {v1, a1}, {v1, a2}, {a1, a2}.
  If external contains v1, covered by {v1, a1} or {v1, a2}.
  If external contains {a1, a2} only... ISSUE: not covered by our edges!

PROBLEM: A-externals sharing edge {a1, a2} are not covered.

RESOLUTION: A-externals sharing {a1, a2} don't contain v1.
But all A-externals share a common vertex (by all_externals_share_common_vertex).
If that common vertex is a1 or a2 (not v1), our hub-based cover fails.

SO: We must use the COMMON VERTEX as the hub, not an arbitrary shared vertex.

REVISED STRATEGY:
For each X ∈ M:
1. Compute common vertex c_X of X-externals (by all_externals_share_common_vertex)
2. Use {c_X, x1}, {c_X, x2} as cover edges

This covers X + X-externals by two_edges_cover_all_externals.

FOR BRIDGES: If bridge at shared vertex s between X and Y:
- If c_X = s: bridge covered by X's edges
- If c_Y = s: bridge covered by Y's edges
- If neither: ??? GAP

ADDITIONAL INSIGHT: If both c_X ≠ s and c_Y ≠ s, maybe the bridge doesn't exist?

Actually, Grok's solution used an edge {v1, x} to an EXTERNAL vertex x.
This suggests: When the standard construction fails, we can use external edges.

ULTIMATE APPROACH: Show τ ≤ 8 by a counting/existence argument, not construction.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅)
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧
      E ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by
  /-
  NEW PROOF SKETCH:

  1. Classify all triangles: M-elements, X-externals, bridges
  2. For X-externals: Use two_edges_cover_all_externals (proven in slot306)
  3. For bridges at shared vertex s:
     - Bridge contains s (proven in slot309)
     - Edge {s, ?} from adjacent element covers bridge
  4. Construct cover adaptively:
     - If X has externals with common vertex c: use edges from c
     - If bridge at s needs coverage: ensure some adjacent element uses s

  The key is showing we can always satisfy both external and bridge requirements
  with ≤ 2 edges per element.

  When external apex ≠ shared vertex:
  - Use Grok's insight: May need edges to EXTERNAL vertices
  - Or: Prove this configuration allows bridge coverage anyway
  -/
  sorry

end
