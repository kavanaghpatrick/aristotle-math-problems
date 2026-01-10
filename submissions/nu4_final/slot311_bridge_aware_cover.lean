/-
  slot311: τ ≤ 8 for ν = 4 - BRIDGE-AWARE COVER STRATEGY

  CRITICAL GAP IDENTIFIED (Gemini + Analysis):
  The bridge triangle T = {v2, b, c} may not be covered when:
  - B's apex is forced to v1 (away from v2) by B-externals
  - C's apex is forced to v3 (away from v2) by C-externals
  - Edge {b, c} exists, creating bridge T

  NEW APPROACH: Instead of 2 edges per element, use an ADAPTIVE strategy
  that considers bridges explicitly.

  KEY LEMMA TO PROVE:
  If bridge T = {v2, b, c} exists (sharing edges with B and C),
  then EITHER:
  1. Some B-external or C-external contains v2 (covered by fan cover), OR
  2. T is the ONLY non-packing, non-external triangle at v2

  PROOF SKETCH:
  If T = {v2, b, c} exists with {b, c} ∈ G:
  - T shares edge {v2, b} with B
  - T shares edge {v2, c} with C
  - T is NOT external (shares edges with TWO packing elements)

  Consider any other triangle containing v2:
  - If it's B or C, it's in M ✓
  - If it contains edge {v2, b}, it's either B or shares edge with B
  - If it contains edge {v2, c}, it's either C or shares edge with C

  The key is: we can add edge {v2, b} or {v2, c} to cover T
  while still staying within 8 edges total.

  REVISED STRATEGY:
  For each shared vertex c between X and Y:
  - Include edge from X to c AND edge from Y to c
  - This covers: X, Y, all bridges at c
  - The remaining 2 edges per element cover externals

  Wait - that exceeds 8 edges. Let me think more carefully...

  CORRECT APPROACH:
  The 8-edge cover is:
  - For endpoints A, D: 2 edges each (fan from apex) = 4 edges
  - For middle elements B, C: 2 edges each = 4 edges

  For B = {v1, v2, b}: Include {v1, v2} and {v2, b}
  For C = {v2, v3, c}: Include {v2, v3} and {v2, c}

  This ensures:
  - Edge {v2, b} covers any triangle containing {v2, b}
  - Edge {v2, c} covers any triangle containing {v2, c}
  - Bridge T = {v2, b, c} has edge {v2, b} or {v2, c} covered!

  KEY INSIGHT: Use SHARED VERTICES as hubs, not arbitrary fan apexes.

  For PATH_4: M = {A, B, C, D} with chain A-B-C-D
  - A = {v1, a1, a2}, shared vertex v1
  - B = {v1, v2, b}, shared vertices v1, v2
  - C = {v2, v3, c}, shared vertices v2, v3
  - D = {v3, d1, d2}, shared vertex v3

  SPINE-BASED COVER:
  - From v1: edges {v1, a1}, {v1, a2} cover A and A-externals
            edge {v1, v2} covers B-triangles through v1
            edge {v1, b} covers B-externals through v1
  - From v2: edges {v2, b}, {v2, c} cover bridges at v2
  - From v3: similar to v1

  Hmm, this is getting complex. Let me try a cleaner approach.

  SIMPLIFIED 8-EDGE COVER FOR PATH_4:
  E = {v1-a1, v1-a2, v1-v2, v2-b, v2-c, v2-v3, v3-d1, v3-d2}

  Check coverage:
  1. A = {v1, a1, a2}: Covered by {v1-a1} ✓
  2. B = {v1, v2, b}: Covered by {v1-v2} ✓
  3. C = {v2, v3, c}: Covered by {v2-v3} ✓
  4. D = {v3, d1, d2}: Covered by {v3-d1} ✓
  5. A-externals: All share edge with A, so contain 2 of {v1, a1, a2}.
                  If they contain v1, covered by {v1-a1} or {v1-a2}.
                  If they contain {a1, a2}, covered by... hmm, need v1!
     Actually A-externals containing edge {a1, a2} might not be covered!

  This is the same problem - some externals might avoid the spine.

  FUNDAMENTAL INSIGHT:
  The proven lemma all_externals_share_common_vertex says there EXISTS a common vertex.
  If that vertex is ON the spine (v1, v2, v3), we're fine.
  If it's OFF the spine (a1, a2, b, c, d1, d2), we need edges there.

  FINAL APPROACH: Use the common vertex adaptively
  For each X ∈ M:
  1. Compute the common vertex c_X of X-externals
  2. Include 2 edges incident to c_X

  These 8 edges cover all externals by construction.
  We need to prove they also cover bridges.

  BRIDGE COVERAGE PROOF:
  Let T be a bridge sharing edges with X and Y.
  By bridge_triangle_contains_shared_vertex, T contains the shared vertex s of X ∩ Y.

  Case 1: c_X = s. Then T contains s = c_X, and some edge from c_X to another
          X-vertex is in T. This edge is in our cover.
  Case 2: c_Y = s. Similarly.
  Case 3: c_X ≠ s and c_Y ≠ s. This is the GAP CASE.

  In Case 3, we need to show either:
  - Such configurations don't exist, OR
  - The bridge is covered anyway

  CLAIM: In PATH_4, if c_X ≠ s and c_Y ≠ s, then there are NO X-externals
         and NO Y-externals sharing the non-s edges.

  If true, then c_X and c_Y can be CHOSEN to be s (since externals are
  actually at s), and Case 3 doesn't apply.

  This requires deeper analysis of external structure in PATH_4...
-/

import Mathlib

set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

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

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING (from proven lemmas)
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.2 ⟨u, by aesop, v, by aesop⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- From slot309: Bridge triangle contains shared vertex
lemma bridge_triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hX_card : X.card = 3) (hY_card : Y.card = 3)
    (h_inter : (X ∩ Y).card = 1)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_X : sharesEdgeWith T X) (hT_share_Y : sharesEdgeWith T Y) :
    ∃ c, c ∈ X ∧ c ∈ Y ∧ c ∈ T := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h_inter
  use c
  constructor
  · exact Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.1
  constructor
  · exact Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.2
  · by_contra hc_notin_T
    have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp hT_share_X
    have h_TY : (T ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T Y |>.mp hT_share_Y
    have hT_card : T.card = 3 := by
      simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT_tri
      exact hT_tri.2.2
    have h1 : T ∩ X ⊆ X \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hv.2, fun hvc => hc_notin_T (hvc ▸ hv.1)⟩
    have h2 : T ∩ Y ⊆ Y \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hv.2, fun hvc => hc_notin_T (hvc ▸ hv.1)⟩
    have h3 : (X \ {c}) ∩ (Y \ {c}) = ∅ := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton, Finset.not_mem_empty,
                 iff_false, not_and, not_not]
      intro ⟨hvX, hvc⟩ ⟨hvY, _⟩
      have : v ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hvX, hvY⟩
      rw [hc] at this
      exact hvc (Finset.mem_singleton.mp this)
    have h4 : Disjoint (T ∩ X) (T ∩ Y) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      have : (T ∩ X) ∩ (T ∩ Y) ⊆ (X \ {c}) ∩ (Y \ {c}) := by
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨h1 (Finset.mem_inter.mpr ⟨hv.1.1, hv.1.2⟩),
               h2 (Finset.mem_inter.mpr ⟨hv.2.1, hv.2.2⟩)⟩
      exact Finset.eq_empty_of_subset_empty (h3 ▸ this)
    have h5 : (T ∩ X).card + (T ∩ Y).card ≤ T.card := by
      have : (T ∩ X) ∪ (T ∩ Y) ⊆ T := by
        intro v hv
        cases Finset.mem_union.mp hv with
        | inl h => exact Finset.mem_inter.mp h |>.1
        | inr h => exact Finset.mem_inter.mp h |>.1
      calc (T ∩ X).card + (T ∩ Y).card
          = ((T ∩ X) ∪ (T ∩ Y)).card := by rw [Finset.card_union_eq_card_add_card h4]
        _ ≤ T.card := Finset.card_le_card this
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW LEMMA: Spine-based cover for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
For PATH_4, we construct a specific 8-edge cover based on the spine {v1, v2, v3}.

COVER CONSTRUCTION:
E = { v1-a1, v1-a2,    -- Cover A and A-externals
      v1-v2, v2-b,      -- Cover B and its triangles through v1, v2
      v2-v3, v2-c,      -- Cover C and its triangles through v2
      v3-d1, v3-d2 }    -- Cover D and D-externals

This ensures EVERY triangle containing a spine vertex is covered.
Bridge triangles must contain a spine vertex (by bridge_triangle_contains_shared_vertex).
-/

theorem tau_le_8_path4_spine (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  /-
  PROOF SKETCH:

  Define E = {v1-a1, v1-a2, v1-v2, v2-b, v2-v3, v2-c, v3-d1, v3-d2}

  1. E ⊆ G.edgeFinset: All edges are from cliques A, B, C, D
  2. E.card ≤ 8: Obvious from construction
  3. Every triangle T is covered:

  Case T ∈ M: Each of A, B, C, D contains one of our edges:
    - A has v1-a1
    - B has v1-v2
    - C has v2-v3
    - D has v3-d1

  Case T ∉ M: T shares edge with some X ∈ M (maximality).

  Subcase T is X-external (shares with exactly one X):
    - If X = A: T shares edge with A = {v1, a1, a2}
      * Edge {v1, a1}: covered by v1-a1 ✓
      * Edge {v1, a2}: covered by v1-a2 ✓
      * Edge {a1, a2}: T = {a1, a2, w}. Since T ∉ A, w ∉ {v1}.
        But T is A-external, so T doesn't share edge with B, C, D.
        T doesn't share {a1, a2} with B/C/D (disjoint).
        T doesn't share {a1, w} or {a2, w} with B/C/D.
        For T ∉ B, need no edge of T in B = {v1, v2, b}.
        Since a1, a2 ∉ B, and w ∉ B (else T shares with B), OK.
        So {a1, a2, w} can exist as A-external.
        BUT: Is it covered? Our E doesn't have a1-a2 or edges to w!

        THIS IS THE GAP - A-externals sharing edge {a1, a2} are NOT covered!

  REVISED APPROACH:

  By all_externals_share_common_vertex, all A-externals share a common vertex.

  Case 1: Common vertex is v1. Then A-externals all contain v1.
          Any triangle containing v1 is covered by v1-a1 or v1-a2 or v1-v2.
          (Since T is A-external, T ∩ A has 2 elements, one of which could be v1.)
          If T = {v1, x, y} with {v1, x} or {v1, y} = {v1, a1} or {v1, a2}, covered.

  Case 2: Common vertex is a1 or a2. Then NOT all triangles containing v1 are covered.
          But all A-externals contain a1 (say).
          We need edge from a1 in our cover.

  This suggests the cover should be ADAPTIVE to the common vertex.

  PROBLEM: The 8-edge construction must handle ALL possible common vertex choices.

  SOLUTION: Prove that for PATH_4 endpoints (A and D), the common vertex
            must be the SPINE vertex (v1 for A, v3 for D).

  CLAIM: For A = {v1, a1, a2} with v1 ∈ A ∩ B, all A-externals share vertex v1.

  PROOF OF CLAIM:
  Suppose A-external T shares edge {a1, a2} (not involving v1).
  Then T = {a1, a2, w} for some w.
  T must not share edge with B = {v1, v2, b}.
  Since a1, a2 ∉ B, the only way T shares edge with B is if w ∈ {v1, v2, b}
  and one of a1, a2 ∈ B. But a1, a2 ∉ B. So T doesn't share edge with B. ✓

  So T = {a1, a2, w} can exist as A-external. But then the common vertex
  of A-externals would need to be in T ∩ {a1, a2, ...other externals}.

  If another A-external T' shares edge {v1, a1}, then T' = {v1, a1, w'}.
  T ∩ T' = {a1} ∪ (possibly more).
  If both T and T' exist, common vertex ∈ T ∩ T' = {a1} (at least).

  So common vertex is a1 in this case, not v1!

  THIS DISPROVES THE CLAIM. The spine-based cover doesn't work directly.

  ULTIMATE FIX:
  The 8-edge cover must include:
  - 2 edges from each element's common vertex (which may vary)

  This is what the original approach tried, but failed for bridges.

  FINAL APPROACH - Count triangles more carefully:
  Every non-M triangle T shares edge with some X ∈ M.
  Either T is X-external (covered by 2 edges from X's common vertex),
  or T is a bridge (shares edges with X and Y).

  For bridges at shared vertex s:
  - B-C bridges must contain v2 (the shared vertex)
  - If B's common vertex is v2 OR C's common vertex is v2, bridge is covered
  - Otherwise, B's common is v1/b and C's common is v3/c

  KEY INSIGHT: If B's common vertex is v1 (not v2), then ALL B-externals
  share edge involving v1. But the B-C bridge T = {v2, b, c} doesn't involve v1!
  So T is NOT a B-external. Similarly for C.

  So T is ONLY a bridge, not counted as external to either B or C.

  The question is: Can the 8 edges cover all bridges in addition to externals?

  COUNTING ARGUMENT:
  - A contributes 2 edges (covers A + A-externals)
  - D contributes 2 edges (covers D + D-externals)
  - B contributes 2 edges (covers B + B-externals)
  - C contributes 2 edges (covers C + C-externals)
  Total: 8 edges

  Bridges: T sharing edges with two elements.
  - A-B bridges contain v1, covered by one of A's or B's edges through v1
  - B-C bridges contain v2
  - C-D bridges contain v3

  For B-C bridge T containing v2:
  If B's common vertex is v2: T contains v2 and another B-vertex, covered by B's edges
  If C's common vertex is v2: Similarly covered by C's edges

  REMAINING GAP: What if NEITHER B nor C has v2 as common vertex?

  Then all B-externals avoid v2 (share edges not through v2),
  and all C-externals avoid v2.

  In this case, are there any bridges at v2?

  For a B-C bridge T to exist at v2:
  - T = {v2, x, y} with {v2, x} ∈ B and {v2, y} ∈ C
  - Since B = {v1, v2, b}, edges through v2 are {v1, v2} and {v2, b}
  - Since C = {v2, v3, c}, edges through v2 are {v2, v3} and {v2, c}
  - So x ∈ {v1, b} and y ∈ {v3, c}
  - T = {v2, v1, v3}, {v2, v1, c}, {v2, b, v3}, or {v2, b, c}

  T = {v2, v1, v3}:
    - Contains edge {v1, v2} of B ✓
    - Contains edge {v2, v3} of C ✓
    - But also: {v1, v3} - if this is an edge, T is a triangle
    - T shares {v1, v2} with B, {v2, v3} with C
    - Does T share edge with A? A's edges: {v1, a1}, {v1, a2}, {a1, a2}
      T's edges: {v1, v2}, {v2, v3}, {v1, v3}. No overlap.
    - Does T share edge with D? D's edges: {v3, d1}, {v3, d2}, {d1, d2}
      T's edges don't include these. No overlap.
    - So T = {v2, v1, v3} is a pure B-C bridge.

  If T = {v1, v2, v3} exists:
    - Our cover includes v1-v2 (from B) or v2-v3 (from C)
    - So T IS COVERED! ✓

  T = {v2, b, c}:
    - Contains edge {v2, b} of B ✓
    - Contains edge {v2, c} of C ✓
    - {b, c} must be in G for T to be a triangle
    - T shares edges with B and C but not A or D

  If T = {v2, b, c} exists:
    - Our cover doesn't necessarily include v2-b or v2-c!
    - If B's common is v1: cover has v1-v2, v1-b (not v2-b)
    - If C's common is v3: cover has v2-v3, v3-c (not v2-c)
    - T's edges: {v2, b}, {v2, c}, {b, c}
    - NONE of these are in our cover!

  THIS IS THE EXACT GAP identified by Gemini.

  RESOLUTION:
  Prove that if T = {v2, b, c} exists (requiring edge {b, c}),
  then one of the following holds:
  1. B has an external containing v2 (so B's common is v2)
  2. C has an external containing v2 (so C's common is v2)
  3. The graph G has additional structure forcing coverage

  Let me try a different approach: if {b, c} is an edge, what does it imply?

  If {b, c} ∈ G, consider triangle {b, c, ?}:
  - {b, c, v2} exists (bridge at v2)
  - Could there be {b, c, w} for other w?

  For maximality: every triangle shares edge with M.
  {b, c, w} must share edge with A, B, C, or D.
  - Shares with B iff w ∈ B or {b, w} ∈ B or {c, w} ∈ B
    B = {v1, v2, b}, so w ∈ {v1, v2} or c ∈ B (false) or {b, w} edge of B means w = v1 or v2
  - Similarly for others

  So {b, c, v2} might be the ONLY triangle containing {b, c}.

  The issue is: can the 8 edges cover {b, c, v2} without dedicated edges to b or c?

  FINAL RESOLUTION:
  Include {v2, b} and {v2, c} explicitly in the cover:

  E = {v1-a1, v1-a2, v2-b, v2-c, v2-v3, v3-c, v3-d1, v3-d2}
  Wait, that's 8 but we need to check it covers everything.

  Actually: Let me try
  E = {v1-a1, v1-a2, v1-v2, v2-b, v2-c, v2-v3, v3-d1, v3-d2}

  Hmm, we lost the edge from v3 to c. Let me reconsider.

  The CORRECT 8-edge cover should be:
  - v1-a1, v1-a2 (for A)
  - v2-b, v2-c (for bridges at v2 and to cover externals)
  - v2-v3 (for B-C overlap)
  - v3-d1, v3-d2 (for D)
  - v1-v2 (for A-B overlap)

  That's 8 edges. Let me verify coverage:
  - A = {v1, a1, a2}: v1-a1 ∈ E ✓
  - B = {v1, v2, b}: v1-v2 ∈ E ✓
  - C = {v2, v3, c}: v2-v3 ∈ E ✓
  - D = {v3, d1, d2}: v3-d1 ∈ E ✓
  - A-externals: Share edge with A, contain 2 of {v1, a1, a2}
    If contain v1: v1-a1 or v1-a2 covers
    If contain {a1, a2}: These triangles {a1, a2, w} need w ∉ A...
    Hmm, still might not be covered!

  CRITICAL: A-externals sharing {a1, a2} are NOT covered by v1-a1, v1-a2.

  This means we need at least one edge from {a1, a2}.

  BUT: all_externals_share_common_vertex says there's a common vertex for A-externals.
  If it's v1, then all A-externals contain v1, so edges {v1, ?} cover them.
  If it's a1 or a2, we need edges from there.

  Since the common vertex is FIXED by the external structure, we cannot
  guarantee it's v1. So the fixed spine-based cover fails.

  ADAPTIVE COVER (the original approach):
  - For A: use edges from common vertex (2 edges)
  - For B: use edges from common vertex (2 edges)
  - For C: use edges from common vertex (2 edges)
  - For D: use edges from common vertex (2 edges)
  Total: 8 edges

  This covers all externals. The question is bridges.

  BRIDGE AT v2 (B ∩ C):
  T = {v2, b, c} is a bridge.
  If B's common is v2: edges include v2-v1, v2-b. T has v2-b. Covered! ✓
  If B's common is v1: edges include v1-v2, v1-b. T doesn't have v1. NOT covered by B.
  If B's common is b: edges include v1-b, v2-b. T has v2-b. Covered! ✓

  So T is covered unless B's common is v1.

  Similarly, T is covered unless C's common is v3.

  If B's common is v1 AND C's common is v3:
  T = {v2, b, c} has edges {v2, b}, {v2, c}, {b, c}.
  B's cover: v1-v2, v1-b (neither in T)
  C's cover: v2-v3, v3-c (neither in T)

  THE GAP PERSISTS.

  POSSIBLE RESOLUTION:
  Prove that B's common = v1 implies B has no externals through v2,
  which implies T = {v2, b, c} is B-external (contradiction) or doesn't exist.

  Wait: if B's common = v1, then all B-externals contain v1.
  T = {v2, b, c} does NOT contain v1.
  So T is NOT a B-external.

  Similarly, if C's common = v3, T doesn't contain v3, so T is NOT a C-external.

  So T is NEITHER a B-external NOR a C-external.
  T is a bridge, only sharing edges with B and C.

  For maximality: T must share edge with some M-element.
  T shares edge {v2, b} with B and {v2, c} with C.

  But T is not external to B or C (it shares with both).
  T is a bridge.

  THE KEY QUESTION: Does the adaptive 8-edge cover always cover bridges?

  NO, as shown above. When B's common is v1 and C's common is v3,
  the bridge T = {v2, b, c} is not covered.

  ULTIMATE FIX NEEDED:
  Either prove such configurations don't exist, or find a different strategy.
  -/
  sorry

end
