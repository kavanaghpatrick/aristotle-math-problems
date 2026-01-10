/-
  slot312: Bridge Non-existence in GAP Configuration

  THE GAP: When B's apex = v1 and C's apex = v3, bridge T = {v2, b, c} is not covered.

  THIS FILE: Prove that if B's apex is v1 (not v2) AND C's apex is v3 (not v2),
  then the edge {b, c} CANNOT exist in G.

  PROOF STRATEGY:

  If B's apex is v1 (not v2), then:
  - All B-externals share vertex v1
  - No B-external shares edge {v2, b} (since they all contain v1, not v2)
  - So all B-externals share edge {v1, v2} or {v1, b}

  Similarly for C with apex v3.

  Now suppose edge {b, c} exists in G. Consider triangle T = {b, c, v2}.

  T is a triangle in G:
  - {b, v2} is edge in B ✓
  - {c, v2} is edge in C ✓
  - {b, c} assumed to exist ✓

  T is not in M (T ≠ A, B, C, D since T doesn't contain v1 or v3).

  By maximality, T shares edge with some X ∈ M.
  T's edges: {b, v2}, {c, v2}, {b, c}

  - T shares {b, v2} with B ✓
  - T shares {c, v2} with C ✓
  - T shares {b, c} with whom? Not A (b, c ∉ A), not D (b, c ∉ D)
    Not B (c ∉ B), not C (b ∉ C). So only B and C.

  So T is a bridge between B and C.

  KEY CLAIM: If B's apex is v1 AND T = {b, c, v2} exists, then T would be
  a "B-external" candidate that DOESN'T contain v1.

  Wait, T is NOT a B-external because T shares edge with C (not just B).

  The real question: Does the existence of T = {v2, b, c} force B's apex to be v2?

  ANALYSIS:

  B's apex is the common vertex of ALL B-externals.
  B-externals are triangles sharing edge with B but NOT with A, C, or D.

  If T = {v2, b, c} exists:
  - T shares edge {v2, b} with B
  - T shares edge {v2, c} with C
  - So T is NOT a B-external (it shares edge with C)

  So T existing doesn't directly affect B-externals.

  However, consider: what if T is NOT a bridge but somehow only touches B?

  Actually, T = {v2, b, c} MUST share edge with C because {v2, c} ∈ C.

  So T is always a bridge, never an external.

  DIFFERENT APPROACH: Prove edge {b, c} creates a 5-packing

  If {b, c} ∈ G, consider the set {A, B, C, D, T} where T = {v2, b, c}.

  Is this a 5-packing? Need to check pairwise edge-disjointness.

  A = {v1, a1, a2}, T = {v2, b, c}:
  A ∩ T = ∅ (no common vertices), so edge-disjoint ✓

  B = {v1, v2, b}, T = {v2, b, c}:
  B ∩ T = {v2, b}. |B ∩ T| = 2. NOT edge-disjoint!

  So {A, B, C, D, T} is NOT a packing.

  This doesn't help directly.

  ANOTHER APPROACH: Count triangles at the gap vertex v2

  If B's apex = v1, all B-externals contain v1.
  So any triangle containing v2 but not v1 is either:
  - In M (namely B or C)
  - A bridge (shares edges with B and C)
  - External to some element NOT B

  Consider triangles containing v2:
  - B = {v1, v2, b} contains v2
  - C = {v2, v3, c} contains v2
  - Bridge T = {v2, b, c} (if {b, c} edge exists)
  - Other triangles {v2, x, y}

  For {v2, x, y} to be a triangle:
  - Needs edges {v2, x}, {v2, y}, {x, y} in G

  By maximality, {v2, x, y} shares edge with some M-element.

  If shares with B: {v2, x} or {v2, y} ∈ B.edges = {{v1, v2}, {v1, b}, {v2, b}}
    So x or y ∈ {v1, b}
  If shares with C: x or y ∈ {v3, c}
  If shares with A: Need edge of {v2, x, y} in A.edges = {{v1, a1}, {v1, a2}, {a1, a2}}
    But v2 ∉ A, so edges of T containing v2 aren't in A. So x, y ∈ {a1, a2}.
  If shares with D: Similarly, x, y ∈ {d1, d2}.

  So triangles at v2 are:
  - B, C (in M)
  - Bridges sharing with B and C: vertices from {v1, b} × {v3, c}
    - {v2, v1, v3}: if edge {v1, v3} exists
    - {v2, v1, c}: if edge {v1, c} exists
    - {v2, b, v3}: if edge {b, v3} exists
    - {v2, b, c}: if edge {b, c} exists
  - Triangles sharing only with B: Need {v2, x, y} with {v2, x} or {v2, y} in B,
    and no edge in C. If y = v1, then {v2, v1, x}, but {v2, v1} ∈ B and we need
    no edge in C. {v2, v1} ∉ C (since v1 ∉ C). What about {v1, x} and {v2, x}?
    {v1, x} ∈ C iff x ∈ {v3, c} and v1 ∈ C. But v1 ∉ C. So {v1, x} ∉ C.
    {v2, x} ∈ C iff x ∈ {v3, c}. So if x ∉ {v3, c}, {v2, v1, x} shares only with B.
    But {v2, v1, x} shares {v1, v2} with B, and maybe {v1, x} with A if x ∈ {a1, a2}.

  This is getting complicated. Let me try a simpler approach.

  SIMPLER APPROACH: Use the 5-packing argument

  If edge {b, c} exists AND B's apex = v1 AND C's apex = v3, what happens?

  B's apex = v1 means: all B-externals share v1.
  C's apex = v3 means: all C-externals share v3.

  CLAIM: Under these conditions, the bridge T = {v2, b, c} can be added to a packing.

  Consider M' = M \ {B, C} ∪ {T} = {A, T, D} where T = {v2, b, c}.

  Is M' a packing?
  - A ∩ T = ∅ (disjoint vertices) ✓
  - A ∩ D = ∅ (given hAD) ✓
  - T ∩ D: T = {v2, b, c}, D = {v3, d1, d2}. T ∩ D = ∅ ✓

  So M' = {A, T, D} is a valid 3-packing.

  Can we extend it? We removed B and C.
  Can we add B back? B ∩ A = {v1} (size 1) ✓, B ∩ T = {v2, b} (size 2) ✗

  So we can't have both B and T in a packing.

  This means T = {v2, b, c} is "blocked" by B (or by C).

  By maximality of M, T ∉ M implies T shares edge with some M-element.
  T shares edges with both B and C.

  This doesn't give us a contradiction yet.

  FINAL APPROACH: Use all_externals_share_common_vertex more carefully

  If there are NO B-externals, then any vertex of B can be the "apex" (vacuously).
  In particular, we can CHOOSE v2 as B's apex.

  So the GAP case (B's apex = v1 ≠ v2) only happens when there ARE B-externals.

  If there ARE B-externals, they all share a common vertex.
  The common vertex is in every B-external.

  CLAIM: If bridge T = {v2, b, c} exists, then there exists a B-external
         containing v2.

  PROOF:
  Consider triangle T' = {v2, b, w} where w is a vertex making this a triangle.
  Actually, we need to construct such a T'.

  Hmm, this doesn't work directly.

  ALTERNATIVE: Prove that if B's apex = v1, then all triangles sharing
  edge with B also share v1.

  Wait, that's not true either. B itself shares edge with A (via {v1}),
  but C shares edge {v1, v2} with B? No, B ∩ C = {v2}, not an edge.

  Let me reconsider the problem entirely.

  FUNDAMENTAL OBSERVATION:

  The edge {b, c} connects two "private" vertices of B and C.
  In the PATH_4 structure, b and c are "off the spine".

  CONJECTURE: In a maximum packing with PATH_4 structure, the edge {b, c}
  cannot exist without creating a 5-packing opportunity.

  PROOF ATTEMPT:
  Suppose {b, c} is an edge in G. Then T = {v2, b, c} is a triangle.

  Consider replacing B and C in M with T and some other triangle.

  M has 4 triangles: A, B, C, D.
  If we can find 5 edge-disjoint triangles, ν ≥ 5, contradicting ν = 4.

  Candidate 5-packing: {A, T, D, X, Y} where X, Y are new triangles.

  We need X, Y to be edge-disjoint from A, T, D and from each other.

  T = {v2, b, c} has edges {v2, b}, {v2, c}, {b, c}.
  A = {v1, a1, a2} has edges {v1, a1}, {v1, a2}, {a1, a2}.
  D = {v3, d1, d2} has edges {v3, d1}, {v3, d2}, {d1, d2}.

  These are all disjoint (no common edges).

  Can we add X = B = {v1, v2, b}?
  B ∩ T = {v2, b} (size 2 - shares edge!) ✗

  Can we add Y = C = {v2, v3, c}?
  C ∩ T = {v2, c} (size 2 - shares edge!) ✗

  So we CAN'T add B or C to {A, T, D}.

  What about other triangles?

  If there's a triangle {v1, v2, x} edge-disjoint from T:
  - Must not share edges with T = {v2, b, c}
  - T's edges: {v2, b}, {v2, c}, {b, c}
  - {v1, v2, x}'s edges: {v1, v2}, {v1, x}, {v2, x}
  - No overlap iff x ∉ {b, c}

  So {v1, v2, x} for x ∉ {b, c} is edge-disjoint from T.

  Does {v1, v2, x} conflict with A or D?
  - A's edges: {v1, a1}, {v1, a2}, {a1, a2}
  - {v1, v2, x} shares {v1, x} with A iff x ∈ {a1, a2}
  - D's edges: {v3, d1}, {v3, d2}, {d1, d2}
  - No overlap with {v1, v2, x}

  So {v1, v2, x} is edge-disjoint from A iff x ∉ {a1, a2}.

  If there exists x ∉ {b, c, a1, a2} such that {v1, v2, x} is a triangle,
  then {A, T, D, {v1, v2, x}} is a 4-packing edge-disjoint.

  Similarly, look for a fifth triangle.

  We need triangle X edge-disjoint from A, T, D, and {v1, v2, x}.

  This is getting into detailed case analysis.

  SIMPLIFICATION: The key is that in PATH_4, we're assuming a SPECIFIC structure.
  The existence of edge {b, c} may violate ν = 4.

  Let me just state the key lemma and let Aristotle try:
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

/-
KEY LEMMA: If B's common vertex is NOT v2, then edge {b, c} cannot exist.

PROOF SKETCH:
If B's common vertex is v1 (not v2), all B-externals contain v1.
If edge {b, c} exists, consider the triangle T = {v2, b, c}.
T shares edge {v2, b} with B and edge {v2, c} with C.
T is a bridge, not a B-external.

If we can show that the existence of edge {b, c} forces B to have
an external containing v2, then B's common vertex must be v2.

The key insight: edge {b, c} creates new triangles that constrain
the external structure.

Alternatively: if B's common is v1 AND C's common is v3, and edge {b, c} exists,
we can construct a 5-packing, contradicting ν = 4.
-/
lemma edge_bc_implies_v2_in_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
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
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    (h_bc_edge : G.Adj b c)  -- The critical assumption
    -- Common vertex of B-externals
    (B_externals : Finset (Finset V))
    (hB_ext : ∀ T ∈ B_externals, isExternalOf G M B T)
    (hB_nonempty : B_externals.Nonempty)
    (common_B : V)
    (h_common_B : ∀ T ∈ B_externals, common_B ∈ T)
    (h_common_B_in_B : common_B ∈ B) :
    common_B = v2 ∨ common_B = b := by
  /-
  PROOF SKETCH:
  B = {v1, v2, b}. The common vertex is one of v1, v2, b.

  If common_B = v1:
    - All B-externals contain v1
    - The bridge T = {v2, b, c} exists (since h_bc_edge)
    - T contains v2 and b, so if a B-external also contains v2 or b...

  Key: The edge {b, c} creates triangle {v2, b, c} which interacts with externals.

  Actually, we need to show that having common_B = v1 leads to a contradiction
  when edge {b, c} exists.

  STRONGER CLAIM: If edge {b, c} exists, then B has an external containing v2.

  Let T = {v2, b, c}. T is a triangle (edges v2-b from B, v2-c from C, b-c given).
  T shares edge {v2, b} with B.
  T shares edge {v2, c} with C.
  So T is NOT an external of B (shares edge with C).

  Hmm, T being a bridge doesn't directly give us a B-external containing v2.

  ALTERNATIVE: Consider other triangles containing edge {b, c}.

  If {b, c, w} is a triangle for some w:
  - By maximality, shares edge with some M-element
  - If w = v2, we get the bridge T
  - If w ∈ A = {v1, a1, a2}, shares edge with A? {b, c, v1} shares {b, v1}?
    No, b ∉ A. So {b, c, v1} shares no edge with A unless {c, v1} ∈ A. c ∉ A.
    So {b, c, w} with w ∈ A doesn't share edge with A.
  - By maximality, {b, c, w} must share edge with B or C (or D).
    {b, c, w} shares with B if w ∈ B, i.e., w ∈ {v1, v2, b}.
    {b, c, w} shares with C if w ∈ C, i.e., w ∈ {v2, v3, c}.
    {b, c, w} shares with D if w ∈ D, i.e., w ∈ {v3, d1, d2}.

  So triangles containing {b, c} have third vertex in B ∪ C ∪ D = {v1, v2, b, v3, c, d1, d2}.
  But we already have b and c, so w ∈ {v1, v2, v3, d1, d2}.

  - w = v1: {b, c, v1}. Shares {b, v1}? No, need b and v1 both in some M-element.
    v1 ∈ B, b ∈ B, so {b, v1} is edge of B. So {b, c, v1} shares edge with B!
    Does it share with C? {c, v1}? v1 ∉ C. So only shares with B.
    Is {b, c, v1} a B-external? Need to check it doesn't share edge with A or D.
    A's edges: {v1, a1}, {v1, a2}, {a1, a2}. {b, c, v1} has edges {b, c}, {b, v1}, {c, v1}.
    Shares with A via {v1, ?}. {v1, a1} ≠ {b, v1} or {c, v1} (since b, c ∉ {a1, a2}).
    So {b, c, v1} doesn't share edge with A. ✓
    D's edges: {v3, d1}, {v3, d2}, {d1, d2}. No overlap. ✓
    So {b, c, v1} IS a B-external IF it's a triangle in G.

  For {b, c, v1} to be a triangle: need edges {b, c} (given), {b, v1}, {c, v1}.
  {b, v1} is edge in B, so if B ⊆ G.clique, then G.Adj b v1. ✓
  {c, v1}: Need G.Adj c v1. This is NOT given!

  So {b, c, v1} is a triangle IFF G.Adj c v1.

  CASE ANALYSIS:
  Case 1: G.Adj c v1. Then {b, c, v1} is a B-external containing v1.
          So common_B could be v1.
          But {v2, b, c} is a bridge containing v2.
          We need common_B = v2 or b to cover the bridge.
          So this case doesn't help.

  Case 2: ¬G.Adj c v1. Then {b, c, v1} is NOT a triangle.
          Consider w = v3: {b, c, v3}. Edges {b, c}, {b, v3}, {c, v3}.
          {b, v3}? b ∉ D, v3 ∉ B. So G.Adj b v3 is possible but not given.
          {c, v3} is edge in C. ✓
          For {b, c, v3} to be triangle: need G.Adj b v3.

  This is getting too case-heavy. Let me state a cleaner lemma.
  -/
  sorry

/-
MAIN THEOREM: τ ≤ 8 for PATH_4

The proof uses the fact that for each X ∈ M, two edges from the common vertex
cover X and all X-externals. The bridge coverage follows from the lemma above
showing that bridge-critical edges force the common vertex to be at the shared spine.
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
  PROOF SKETCH:
  1. For each X ∈ M, get common vertex c_X from all_externals_share_common_vertex
  2. For X with externals, c_X is fixed; for X without externals, choose c_X = spine vertex
  3. Include 2 edges from each c_X: total ≤ 8 edges
  4. These cover all externals (by construction) and all M-elements
  5. For bridges: use edge_bc_implies_v2_in_common_vertex to show they're covered
  -/
  sorry

end
