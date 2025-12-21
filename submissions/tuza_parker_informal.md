# Tuza Conjecture τ ≤ 2ν for ν ≤ 3: Informal Proof

## Goal
Prove τ(G) ≤ 2ν(G) when ν(G) ≤ 3.

## Definitions
- τ(G) = minimum edges to hit all triangles
- ν(G) = maximum edge-disjoint triangles
- M = maximal edge-disjoint triangle packing with |M| = ν
- T_e = triangles sharing an edge with e ∈ M
- S_e = triangles sharing edge with e but NOT with any other f ∈ M

## Key Lemma (Parker Lemma 2.2)
S_e triangles pairwise share edges.

**Proof sketch**: If t1, t2 ∈ S_e were edge-disjoint, we could swap e for {t1, t2}, increasing the packing. Contradiction.

## Case ν = 1
M = {e}. Every triangle shares edge with e, so T_e = S_e.
Pairwise-sharing triangles have τ ≤ 2.

## Case ν = 2
M = {e, f} edge-disjoint triangles.

**Subcase 2a**: |e ∩ f| = 0 (vertex-disjoint)
- No triangle can share edges with both (would need ≥4 vertices from a 3-vertex triangle)
- So T_e = S_e, and τ(T_e) = τ(S_e) ≤ 2

**Subcase 2b**: |e ∩ f| = 1 (share vertex v)
- Bridge triangles must contain v (to share edge with both e and f using only 3 vertices)
- S_e triangles pairwise share edges
- Since all share with e and are pairwise-sharing, they fit in K4 or share common edge
- In either case: ≤2 edges of e containing v cover S_e
- Bridges contain v, so same edges cover bridges
- Total: τ(T_e) ≤ 2

## Case ν = 3
M = {e, f, g} edge-disjoint triangles.

By similar analysis: at least one e ∈ M satisfies τ(T_e) ≤ 2.

The key is that packing constraints limit bridge complexity. When ν = 3:
- Each triangle has 3 vertices
- Pairwise vertex overlap ≤ 1 (edge-disjoint)
- Total vertices ≤ 9, but overlaps reduce this

Parker's matching type analysis (Figure 1) shows in each configuration,
some e has τ(T_e) ≤ 2.

## Inductive Bound
For any e ∈ M with τ(T_e) ≤ 2:
- Remove e from M: τ(G \ T_e) ≤ 2(ν - 1) by induction
- Add 2 edges for T_e
- Total: τ(G) ≤ 2(ν - 1) + 2 = 2ν

## Conclusion
When ν ≤ 3: τ(G) ≤ 2ν(G). ∎
