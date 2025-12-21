# Tuza's Conjecture for Split Graphs

## Problem Statement

Prove that for any split graph G = (K ∪ I, E) where K is a clique and I is an independent set:

**τ(G) ≤ 2ν(G)**

where τ(G) is the minimum number of edges needed to hit all triangles, and ν(G) is the maximum number of edge-disjoint triangles.

## What's Known

- **Threshold graphs** (a subclass of split graphs with nested neighborhoods): PROVEN by Botler et al. 2021
- **General split graphs**: OPEN

## Key Structural Insight

In a split graph:
- K is a clique (all pairs in K are adjacent)
- I is an independent set (no pairs in I are adjacent)
- Every triangle must use ≥2 vertices from K

**Proof of key insight**: A triangle needs 3 mutually adjacent vertices. Since I is independent, at most 1 vertex can come from I. Therefore ≥2 must come from K.

## Proof Strategy

**Induction on |K|**:

**Base case**: |K| ≤ 3. Then G has at most 1 triangle (since triangles need ≥2 vertices from K, and K itself is the only triangle). So τ ≤ 1 ≤ 2ν.

**Inductive step**: Assume true for cliques of size < k. Consider |K| = k.

1. Pick a maximum triangle packing M with ν = |M|.

2. **Claim**: All triangles sharing a clique edge e = {u,v} ⊆ K pairwise share that edge.
   - Any triangle containing e has form {u, v, w} for some w ∈ K ∪ I
   - Two such triangles {u,v,w} and {u,v,w'} share edge {u,v}

3. By our proven lemma `structural_cover`: triangles that pairwise share edges can be covered by ≤2 edges.

4. For each packing element e ∈ M:
   - S_e (triangles sharing edge only with e) has τ(S_e) ≤ 2 by structural_cover
   - This gives τ(G) ≤ Σ_{e∈M} 2 = 2ν

**Alternative approach**:

Cover all triangles using only clique edges (edges within K):
- Every triangle has ≥2 clique vertices, so contains ≥1 clique edge
- K has (k choose 2) edges
- At most (k choose 2) edge-disjoint triangles can exist (each uses ≥1 clique edge)
- So ν ≤ (k choose 2)
- Can cover with appropriate selection of clique edges

## Connection to Our Proven Lemmas

- `structural_cover`: pairwise sharing triangles → τ ≤ 2 ✓
- `intersecting_triangles_structure`: pairwise sharing → star OR K4 ✓
- `tau_star`: star structure → τ ≤ 1 ✓
- `k4_cover`: triangles on ≤4 vertices → τ ≤ 2 ✓

## Expected Result

Prove: For any split graph G, τ(G) ≤ 2ν(G).
