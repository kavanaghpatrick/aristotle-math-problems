/-
slot131: Packing Number at Shared Vertex is at Most 1

GOAL: Prove that at a shared vertex v in Cycle4, the packing number of
triangles sharing an M-edge at v (excluding M itself) is at most 1.

PROOF STRATEGY (from Gemini/AI consensus Dec 28, 2025):
By contradiction. Suppose 2 edge-disjoint triangles T1, T2 exist at v, both outside M.
- T1 = {v, m1, x1} shares M-edge {v, m1}
- T2 = {v, m2, x2} shares M-edge {v, m2}
- Since T1, T2 are edge-disjoint and both contain v, they share only v
- Therefore m1 ≠ m2 and x1 ≠ x2 and {m1,x1} ∩ {m2,x2} = ∅

Now construct new packing P' = {T1, T2, C, D}:
- T1, T2 are edge-disjoint (by assumption)
- T1, T2 are edge-disjoint from C, D because:
  - T1, T2 use edges at v (which is v_ab or v_bc etc)
  - C, D don't contain v (v is shared vertex of A-B, not C-D)
  - External vertices x1, x2 are not in M

|P'| = 4, but this contradicts maximality of M if we can show P' is valid.
Actually we need |P'| > |M| = 4, so we need to include more...

REFINED STRATEGY:
Show that if 2 edge-disjoint triangles T1, T2 at v exist outside M,
then {T1, T2, C, D} forms a packing of size 4, but we could also add
one of A, B (the ones containing v) to get size 5... No that's wrong.

CORRECT ARGUMENT:
At v = v_ab, M has triangles A, B containing v.
External triangles at v (sharing M-edge but not in M) form a family F.
Claim: Any two triangles in F share an edge (not just v).

Proof: If T1, T2 ∈ F are edge-disjoint:
- Both share an M-edge at v, say T1 uses {v, m1}, T2 uses {v, m2}
- If m1 = m2, they share edge {v, m1}, not edge-disjoint. Contradiction.
- If m1 ≠ m2, then T1 = {v, m1, x1}, T2 = {v, m2, x2}
- For edge-disjointness: {v,m1}, {v,x1}, {m1,x1} all different from {v,m2}, {v,x2}, {m2,x2}
- Since v is shared, we need: m1≠m2, x1≠x2, m1≠x2, m2≠x1, {m1,x1}≠{m2,x2}
- But wait, T1 and T2 both contain v, so they share vertex v. For edge-disjointness
  with sharing only v, we need the edge {v,*} to be different.
- T1 has edges {v,m1}, {v,x1}, {m1,x1}
- T2 has edges {v,m2}, {v,x2}, {m2,x2}
- Disjoint means: {v,m1}≠{v,m2} (so m1≠m2), {v,m1}≠{v,x2}, {v,m1}≠{m2,x2}, etc.

If T1, T2 are edge-disjoint, then {A, B, T1, T2} might form a packing...
But A and T1 share edge {v, m1} where m1 ∈ A (since T1 shares M-edge from A or B).

So T1 is NOT edge-disjoint from A or B! This is the key.

FINAL CORRECT ARGUMENT:
Every triangle in trianglesSharingMEdgeAt G M v shares an M-edge with A or B.
So every such triangle shares ≥2 vertices with A or B.
Therefore they cannot be edge-disjoint from A and B.
The packing number of trianglesSharingMEdgeAt (restricted to triangles outside M)
is bounded by how many can be mutually edge-disjoint AND edge-disjoint from A,B.

Since each external triangle shares an edge with A or B, any two external triangles
that are edge-disjoint must share edges with DIFFERENT elements (one with A, one with B).
But then they share at most the common vertex v of A and B.

Hmm, this is getting complicated. Let me try a simpler formulation.

SIMPLEST APPROACH:
Define: externalTrianglesAtV = trianglesSharingMEdgeAt G M v \ M

Claim: For any T1, T2 ∈ externalTrianglesAtV with T1 ≠ T2, (T1 ∩ T2).card ≥ 2.

This means they share an edge, so ν(externalTrianglesAtV) ≤ 1.

Proof of claim:
- T1 shares M-edge e1 at v, where e1 ∈ A.sym2 or e1 ∈ B.sym2
- T2 shares M-edge e2 at v, where e2 ∈ A.sym2 or e2 ∈ B.sym2
- Both T1, T2 contain v (since they share M-edges containing v)
- If T1, T2 share only v (i.e., |T1 ∩ T2| = 1):
  - Then T1, T2 have 6 distinct edges total (3 each, disjoint)
  - Consider {T1, T2, C, D} - this has 4 triangles
  - T1 shares edge with A or B, T2 shares edge with A or B
  - If both share with A: then both share e1, e2 ∈ A.sym2 with e1 ∩ e2 = {v}
    This means T1 ∩ A ⊇ e1 ≥ 2, T2 ∩ A ⊇ e2 ≥ 2
  - Actually T1 ∉ M and T1 shares edge with A means (T1 ∩ A).card = 2 (the M-edge)
  - Similarly for T2

  Key insight: T1, T2 both contain v, and v ∈ A ∩ B.
  If T1 shares M-edge {v, a} from A, then a ∈ A, so T1 ∩ A ⊇ {v, a}.
  If T2 shares M-edge {v, b} from B, then b ∈ B, so T2 ∩ B ⊇ {v, b}.

  Now consider: T1 ∩ T2 = {v} (by assumption for contradiction)
  T1 = {v, a, x1} where a ∈ A \ {v}, x1 ∉ A (else |T1 ∩ A| ≥ 3 = |A|, so T1 = A ∈ M)
  T2 = {v, b, x2} where b ∈ B \ {v}, x2 ∉ B

  For |T1 ∩ T2| = 1: need a ≠ b, a ≠ x2, x1 ≠ b, x1 ≠ x2

  Now: Is {T1, T2, C, D} a valid packing?
  - T1 ∩ T2 = {v}, so |T1 ∩ T2| = 1 ✓
  - T1 ∩ C: T1 = {v, a, x1}, C contains v_bc, v_cd, c_priv
    If v = v_ab, then v ∉ C (since v_ab ∈ A ∩ B, and A ∩ C = ∅ in cycle4)
    So T1 ∩ C ⊆ {a, x1} ∩ C
    a ∈ A and A ∩ C = ∅, so a ∉ C
    x1 might be in C... if x1 ∈ C, then |T1 ∩ C| = 1
    So |T1 ∩ C| ≤ 1 ✓
  - Similarly T1 ∩ D ≤ 1, T2 ∩ C ≤ 1, T2 ∩ D ≤ 1
  - C ∩ D = {v_cd}, |C ∩ D| = 1 ✓

  So {T1, T2, C, D} is a valid packing of size 4.

  But we also have {A, B, C, D} as a packing of size 4.

  The issue: can we get size 5?

  Consider {T1, T2, A, C, D}:
  - T1 ∩ A = {v, a}, |T1 ∩ A| = 2 ✗ NOT a valid packing!

  Consider {T1, T2, B, C, D}:
  - T2 ∩ B = {v, b}, |T2 ∩ B| = 2 ✗ NOT a valid packing!

  Hmm, so we can't directly get size 5.

  But wait - the claim is about MAXIMALITY.
  If {T1, T2, C, D} is a packing of size 4, and M = {A, B, C, D} is MAXIMAL,
  then we can't add any triangle to M.

  Can we add T1 to {T1, T2, C, D}? It's already there.
  Can we add A to {T1, T2, C, D}? No, |T1 ∩ A| = 2.

  So {T1, T2, C, D} is also a maximal packing of size 4. That's fine.

  The key is: we assumed M is THE maximal packing with the cycle4 structure.
  {T1, T2, C, D} might not have cycle4 structure!

  Actually, for nu=4, ANY maximal packing has size 4. The structure might differ.

  I think the argument needs refinement. Let me try:

  If T1, T2 are edge-disjoint external triangles at v = v_ab:
  - T1 uses M-edge from A or B
  - T2 uses M-edge from A or B

  Case 1: Both use M-edges from A.
  Then T1 ∩ A ⊇ {v, a1}, T2 ∩ A ⊇ {v, a2} for some a1, a2 ∈ A \ {v}.
  If a1 = a2, then T1 and T2 share edge {v, a1}, contradicting edge-disjointness.
  If a1 ≠ a2, then A = {v, a1, a2} (since |A| = 3).
  T1 = {v, a1, x1}, T2 = {v, a2, x2} for external x1, x2.
  T1 ∩ T2 = {v} (edge-disjoint means they share only the vertex v, not any edge).

  Now x1 ≠ x2 (else T1 ∩ T2 ⊇ {v, x1} has 2 elements).
  And x1, x2 ∉ {v, a1, a2} = A.

  Consider packing {T1, T2, C, D}:
  - Already shown this is valid packing of size 4.

  But I claim we can add B!
  T1 ∩ B: T1 = {v, a1, x1}, B = {v, v_bc, b_priv}
  v ∈ T1 ∩ B. Is a1 ∈ B? a1 ∈ A \ {v}, and A ∩ B = {v}, so a1 ∉ B.
  Is x1 ∈ B? x1 ∉ A, but could x1 ∈ B? If x1 ∈ B, then x1 ∈ B \ {v} = {v_bc, b_priv}.

  Hmm, x1 could potentially be v_bc or b_priv.

  If x1 = v_bc, then T1 = {v_ab, a1, v_bc}.
  This triangle contains v_ab and v_bc, both shared vertices.
  T1 ∩ A = {v_ab, a1} (since v_bc ∉ A because A ∩ B = {v_ab} and v_bc ∈ B)
  Wait, v_bc ∈ B ∩ C, not necessarily in A.
  A ∩ C could be empty (diagonal). So v_bc ∉ A is plausible.

  So T1 = {v_ab, a1, v_bc} has:
  - T1 ∩ A = {v_ab, a1}, |T1 ∩ A| = 2
  - T1 ∩ B = {v_ab, v_bc}, |T1 ∩ B| = 2

  This means T1 shares an edge with BOTH A and B!
  But the definition says T1 shares an M-edge at v.
  If T1 shares {v_ab, a1} from A AND {v_ab, v_bc} from B, that's two M-edges.

  For T1 to be in trianglesSharingMEdgeAt, it needs ∃ e ∈ M_edges_at, e ∈ T1.sym2.
  Both edges qualify, so T1 is definitely in the set.

  But now T1 ∩ B has 2 elements, so {T1, T2, B, C, D} is NOT a valid packing.

  What about T2? T2 = {v_ab, a2, x2}. If x2 ∈ B, similar issue.
  If x2 ∉ B, then T2 ∩ B = {v_ab}, so |T2 ∩ B| = 1 ✓.

  So if x1 ∉ B and x2 ∉ B, then {T1, T2, B, C, D} is a valid packing!
  And |{T1, T2, B, C, D}| = 5 > 4 = ν. Contradiction!

  So we must have x1 ∈ B or x2 ∈ B.

  If x1 ∈ B, then T1 ∩ T2: T1 = {v, a1, x1}, T2 = {v, a2, x2}.
  If x1 = x2, they share {v, x1}, not edge-disjoint.
  If x1 ≠ x2, they share only v.

  So let's say x1 ∈ B, x2 ∉ B. Then:
  - T1 ∩ B = {v, x1}, |T1 ∩ B| = 2
  - T2 ∩ B = {v}, |T2 ∩ B| = 1

  Can we form {T1, T2, A, C, D}?
  - T1 ∩ A = {v, a1}, |T1 ∩ A| = 2 ✗

  Can we form {T2, B, C, D, ?}?
  - We have T2 disjoint from B (intersect at 1 vertex)
  - T2 ∩ C: T2 = {v_ab, a2, x2}. v_ab ∉ C (diagonal), a2 ∈ A so a2 ∉ C. x2?
    If x2 ∉ C, |T2 ∩ C| = 0 ✓
  - T2 ∩ D: similarly can be 0 or 1

  So {T2, B, C, D} is a valid packing of size 4. But we need size 5 for contradiction.

  Can we add A or T1?
  - A ∩ B = {v_ab}, |A ∩ B| = 1 ✓
  - A ∩ T2 = {v_ab, a2}, |A ∩ T2| = 2 ✗

  So we can't add A. What about T1?
  - T1 ∩ T2 = {v} (assumed edge-disjoint), |T1 ∩ T2| = 1 ✓
  - T1 ∩ B = {v, x1}, |T1 ∩ B| = 2 ✗

  Hmm, stuck again.

  Let me reconsider. The key constraint is that x1 or x2 must be in B (or both).

  Case: x1 ∈ B, x2 ∈ B.
  Then x1, x2 ∈ B \ {v} = {v_bc, b_priv}.
  If x1 = x2, then T1 ∩ T2 ⊇ {v, x1}, not edge-disjoint.
  If x1 ≠ x2, then {x1, x2} = {v_bc, b_priv}.

  So T1 = {v_ab, a1, v_bc} or {v_ab, a1, b_priv}
  And T2 = {v_ab, a2, b_priv} or {v_ab, a2, v_bc}

  With x1 ≠ x2, say x1 = v_bc, x2 = b_priv.

  T1 = {v_ab, a1, v_bc}, T2 = {v_ab, a2, b_priv}

  T1 ∩ T2 = {v_ab} ✓ (edge-disjoint, share only one vertex)

  Now:
  - T1 ∩ A = {v_ab, a1}
  - T1 ∩ B = {v_ab, v_bc}
  - T2 ∩ A = {v_ab, a2}
  - T2 ∩ B = {v_ab, b_priv}

  Both T1 and T2 share an edge with both A and B!

  - T1 ∩ C = ? T1 = {v_ab, a1, v_bc}. v_bc ∈ C, so T1 ∩ C ⊇ {v_bc}. Is a1 ∈ C? a1 ∈ A, A ∩ C = ∅, so a1 ∉ C. Is v_ab ∈ C? v_ab ∈ A ∩ B, A ∩ C = ∅, so v_ab ∉ C.
    So T1 ∩ C = {v_bc}, |T1 ∩ C| = 1 ✓

  - T1 ∩ D = ? T1 = {v_ab, a1, v_bc}. v_ab ∉ D (v_ab ∈ A ∩ B, and B ∩ D = ∅). a1 ∉ D (a1 ∈ A, A ∩ D = {v_da}, but a1 ≠ v_da since a1 ∈ A \ {v_ab} and A \ {v_ab} = {v_da, a_priv}, so a1 could be v_da).
    If a1 = v_da, then T1 ∩ D ⊇ {v_da}. Also v_bc ∈ D? v_bc ∈ B ∩ C, and B ∩ D = ∅, C ∩ D = {v_cd}. So v_bc ∉ D unless v_bc = v_cd, but those are distinct by the cycle4 distinctness axioms.
    So T1 ∩ D ⊆ {v_da} if a1 = v_da, else T1 ∩ D = ∅.
    Either way |T1 ∩ D| ≤ 1 ✓

  - T2 ∩ C = ? T2 = {v_ab, a2, b_priv}. v_ab ∉ C, a2 ∈ A so a2 ∉ C, b_priv ∈ B so is b_priv ∈ C? B ∩ C = {v_bc}, so b_priv ∈ C iff b_priv = v_bc, but b_priv ≠ v_bc (they're different vertices of B).
    So T2 ∩ C = ∅, |T2 ∩ C| = 0 ✓

  - T2 ∩ D = ? Similar analysis, T2 ∩ D ⊆ {v_da} if a2 = v_da.
    |T2 ∩ D| ≤ 1 ✓

  So {T1, T2, C, D} is a valid packing! Size 4.

  Can we add A?
  - A ∩ T1 = {v_ab, a1}, |A ∩ T1| = 2 ✗

  Can we add B?
  - B ∩ T1 = {v_ab, v_bc}, |B ∩ T1| = 2 ✗

  So we're stuck at size 4 again.

  Hmm, it seems like the argument doesn't give us a packing of size 5.

  Let me think differently. The issue is that external triangles at v_ab that use M-edges from A or B will share edges with A or B respectively. So they can't coexist with A or B in a packing.

  But {T1, T2, C, D} is a different maximal packing than {A, B, C, D}!

  Wait, but nu = 4 means THE MAXIMUM packing size is 4. Both packings have size 4, so both are maximal. That's consistent.

  So the argument fails? Let me reconsider the original claim.

  CLAIM: ν(trianglesSharingMEdgeAt G M v) ≤ 1

  This is about the packing number OF THE SET trianglesSharingMEdgeAt, which INCLUDES A and B (the packing elements containing v).

  So we're asking: among all triangles that share an M-edge at v, how many can be mutually edge-disjoint?

  A and B are in this set. Are A and B edge-disjoint? A ∩ B = {v_ab}, so |A ∩ B| = 1.
  For edge-disjointness we need them to share at most 1 vertex. ✓

  So {A, B} is a packing within trianglesSharingMEdgeAt of size 2!

  Therefore ν(trianglesSharingMEdgeAt G M v) ≥ 2.

  So the claim ν ≤ 1 is FALSE as stated!

  Let me re-read what we actually need...

  The Local Tuza approach says:
  τ(trianglesSharingMEdgeAt G M v) ≤ 2 * ν(trianglesSharingMEdgeAt G M v)

  If ν ≥ 2, then τ ≤ 2 * ν could be ≥ 4, which doesn't help.

  Wait, but the partition is:
  All triangles ⊆ T_vab ∪ T_vbc ∪ T_vcd ∪ T_vda

  If each T_v has τ ≤ 4, total could be 16, not 8.

  Hmm, I think I misunderstood the approach.

  Let me go back to the original support_sunflower approach:
  We want to show τ(trianglesSharingMEdgeAt G M v) ≤ 2.

  This does NOT follow from ν ≤ 1 via Local Tuza if ν ≥ 2.

  But actually, the Codex counterexample showed that all external triangles share {v, x}!
  So they have ν = 1 (all share an edge).

  The key insight: External triangles (outside M) at v have ν ≤ 1 because they all share the external vertex x.

  Triangles IN M at v (A and B) have τ contribution from their edges, but those edges are already counted as M-edges.

  Actually, I think the partition is wrong. Let me reconsider.

  The goal is to cover ALL triangles in G with ≤ 8 edges.

  The partition by trianglesSharingMEdgeAt:
  - T_vab = triangles sharing an M-edge at v_ab
  - etc.

  But triangles in M are also in these sets! A, B ∈ T_vab.

  When we cover T_vab, we cover A and B as well.

  The bound we want: τ(T_vab) ≤ 2.

  Can we cover all of {A, B, external triangles at v_ab} with 2 edges?

  - A = {v_ab, v_da, a_priv} has edges {v_ab, v_da}, {v_ab, a_priv}, {v_da, a_priv}
  - B = {v_ab, v_bc, b_priv} has edges {v_ab, v_bc}, {v_ab, b_priv}, {v_bc, b_priv}
  - External T1 = {v_ab, ?, x} has edges involving v_ab and x

  If all external triangles share {v_ab, x}, then {v_ab, v_da}, {v_ab, x} covers... wait:
  - {v_ab, v_da} covers A (yes, it's an edge of A)
  - {v_ab, x} covers all external triangles (yes, they all contain this edge)
  - Does {v_ab, v_da} or {v_ab, x} cover B? B's edges are {v_ab, v_bc}, {v_ab, b_priv}, {v_bc, b_priv}.
    {v_ab, v_da} is not an edge of B (v_da ∉ B).
    {v_ab, x} might be an edge of B if x ∈ B, i.e., x = v_bc or x = b_priv.

  So we need 3 edges to cover {A, B, externals}: one for A, one for B, one for externals (if externals exist and x ∉ B).

  But wait, one edge from A containing v_ab, and one edge from B containing v_ab, might suffice:
  - {v_ab, v_da} covers A and any external triangle containing v_da
  - {v_ab, v_bc} covers B and any external triangle containing v_bc

  External triangles have form {v_ab, m, x} where m ∈ A ∪ B \ {v_ab}, x external.
  If m = v_da, then {v_ab, v_da} covers this triangle.
  If m = a_priv, then need {v_ab, a_priv} or edge containing x.
  ...

  This is getting complicated. Let me just write a clean Lean file with the correct definitions and let Aristotle figure it out.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- M-edges incident to vertex v -/
def M_edges_at (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun X => X.sym2.filter (fun e => v ∈ e))

/-- Triangles that share an M-edge containing v -/
def trianglesSharingMEdgeAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e ∈ M_edges_at M v, e ∈ t.sym2)

/-- Packing number restricted to a subset of triangles -/
noncomputable def trianglePackingOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  triangles.powerset.filter (fun S =>
    Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1))
    |>.image Finset.card |>.max |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE WITH DISTINCTNESS
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  h_diag_AC : (A ∩ C).card ≤ 1
  h_diag_BD : (B ∩ D).card ≤ 1
  h_vab_ne_vbc : v_ab ≠ v_bc
  h_vbc_ne_vcd : v_bc ≠ v_cd
  h_vcd_ne_vda : v_cd ≠ v_da
  h_vda_ne_vab : v_da ≠ v_ab

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Triangle card = 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp ht).2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: External triangles at v share common structure
-- ══════════════════════════════════════════════════════════════════════════════

/--
External triangles at a shared vertex v (triangles in trianglesSharingMEdgeAt but not in M)
form a "near-sunflower": any two such triangles share at least an edge, not just v.

PROOF IDEA:
Let T1, T2 be external triangles at v = v_ab.
- T1 shares M-edge {v, m1} where m1 ∈ (A ∪ B) \ {v}
- T2 shares M-edge {v, m2} where m2 ∈ (A ∪ B) \ {v}
- T1 = {v, m1, x1}, T2 = {v, m2, x2} for external vertices x1, x2

If T1 ∩ T2 = {v} (share only one vertex):
- Build packing {T1, T2, C, D} which is valid (each pair shares ≤1 vertex)
- Try to add A or B to get size 5, contradiction with ν=4
- But T1 shares edge with A or B, so can't add both

The key insight from Codex counterexample: all external triangles share a common
external vertex x, making them share edge {v, x}. This is the "degenerate sunflower".
-/
lemma external_triangles_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da)
    (T1 T2 : Finset V)
    (hT1 : T1 ∈ trianglesSharingMEdgeAt G M v)
    (hT2 : T2 ∈ trianglesSharingMEdgeAt G M v)
    (hT1_ext : T1 ∉ M)
    (hT2_ext : T2 ∉ M)
    (hne : T1 ≠ T2) :
    (T1 ∩ T2).card ≥ 2 := by
  -- Proof by contradiction: assume they share only vertex v
  by_contra h_small
  push_neg at h_small
  -- T1 ∩ T2 has card ≤ 1

  -- Both T1, T2 contain v (since they share M-edge at v)
  have hv_T1 : v ∈ T1 := by
    simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at hT1
    obtain ⟨e, he_M, he_T1⟩ := hT1.2
    simp only [M_edges_at, Finset.mem_biUnion, Finset.mem_filter] at he_M
    obtain ⟨X, hX, he_X, hv_e⟩ := he_M
    simp only [Finset.mem_sym2_iff] at he_T1
    obtain ⟨a, b, hab, ha, hb, he_eq⟩ := he_T1
    simp only [he_eq, Sym2.mem_iff] at hv_e
    cases hv_e with
    | inl h => exact h ▸ ha
    | inr h => exact h ▸ hb

  have hv_T2 : v ∈ T2 := by
    simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at hT2
    obtain ⟨e, he_M, he_T2⟩ := hT2.2
    simp only [M_edges_at, Finset.mem_biUnion, Finset.mem_filter] at he_M
    obtain ⟨X, hX, he_X, hv_e⟩ := he_M
    simp only [Finset.mem_sym2_iff] at he_T2
    obtain ⟨a, b, hab, ha, hb, he_eq⟩ := he_T2
    simp only [he_eq, Sym2.mem_iff] at hv_e
    cases hv_e with
    | inl h => exact h ▸ ha
    | inr h => exact h ▸ hb

  -- So T1 ∩ T2 ⊇ {v}, meaning (T1 ∩ T2).card ≥ 1
  have h_inter_ge_1 : (T1 ∩ T2).card ≥ 1 := by
    apply Finset.one_le_card.mpr
    exact ⟨v, Finset.mem_inter.mpr ⟨hv_T1, hv_T2⟩⟩

  -- By h_small, (T1 ∩ T2).card ≤ 1, so (T1 ∩ T2).card = 1
  have h_inter_eq_1 : (T1 ∩ T2).card = 1 := by omega

  -- T1 ∩ T2 = {v}
  have h_inter_eq_v : T1 ∩ T2 = {v} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact Finset.mem_inter.mpr ⟨hv_T1, hv_T2⟩
    · intro x hx
      have h_card := Finset.card_eq_one.mp h_inter_eq_1
      obtain ⟨y, hy⟩ := h_card
      have := Finset.mem_singleton.mp (hy ▸ hx)
      have hv_mem := Finset.mem_singleton.mp (hy ▸ Finset.mem_inter.mpr ⟨hv_T1, hv_T2⟩)
      simp_all

  -- T1 and T2 are triangles
  have hT1_tri : T1 ∈ G.cliqueFinset 3 := by
    simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at hT1; exact hT1.1
  have hT2_tri : T2 ∈ G.cliqueFinset 3 := by
    simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at hT2; exact hT2.1

  have hT1_card : T1.card = 3 := triangle_card_eq_3 G T1 hT1_tri
  have hT2_card : T2.card = 3 := triangle_card_eq_3 G T2 hT2_tri

  -- Now we build a packing of size > 4 to contradict maximality
  -- The construction depends on which shared vertex v is

  -- Key observation: T1 shares M-edge with some X ∈ M containing v
  -- At v = v_ab, X ∈ {A, B}
  -- At v = v_bc, X ∈ {B, C}
  -- etc.

  -- For v = v_ab case:
  -- T1 shares edge with A or B (the M-elements containing v_ab)
  -- T2 shares edge with A or B
  -- C and D don't contain v_ab (since A ∩ C = ∅, B ∩ D = ∅ in cycle4)

  -- Consider packing {T1, T2, C, D}:
  -- - T1 ∩ T2 = {v}, card = 1 ✓
  -- - T1 ∩ C: T1 contains v = v_ab, C doesn't (diagonal disjoint), so v ∉ T1 ∩ C
  --   T1 shares M-edge at v, meaning T1 uses edge from A or B incident to v
  --   The other vertices of T1 could intersect C at most 1 vertex
  -- Similar analysis for other pairs

  -- This is complex to formalize directly. Let Aristotle work on it.
  sorry

/--
Corollary: The packing number of external triangles at v is at most 1.
Since any two external triangles share an edge, at most 1 can be in any packing.
-/
lemma external_packing_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    trianglePackingOn G (trianglesSharingMEdgeAt G M v \ M) ≤ 1 := by
  -- Any two triangles in this set share an edge (by external_triangles_share_edge)
  -- So at most 1 can be mutually edge-disjoint
  unfold trianglePackingOn
  -- If the set is empty, packing number is 0
  by_cases h_empty : trianglesSharingMEdgeAt G M v \ M = ∅
  · simp [h_empty]

  -- If non-empty, any packing has size ≤ 1
  push_neg at h_empty
  apply Nat.le_of_lt_succ
  simp only [Nat.lt_succ_iff]

  -- The maximum packing of a set where any two elements share ≥2 vertices is 1
  -- (since edge-disjoint means share ≤1 vertex)
  sorry

end
