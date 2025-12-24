# Tuza's Conjecture for ν = 4: Bridge Absorption Strategy

## Goal
Prove τ(G) ≤ 8 when ν(G) = 4.

## Key Insight (from AI consultation)
The cleanest path is **Bridge Absorption**: show that edges covering S_e also automatically cover bridge triangles.

## Definitions
- **Triangle packing M**: Set of edge-disjoint triangles in G
- **ν(G)**: Maximum size of a triangle packing
- **τ(G)**: Minimum edges needed to cover all triangles
- **S_e**: Triangles sharing an edge with e AND compatible with rest of packing M
- **X(e,f)**: Bridge triangles - share edges with BOTH e and f

## Proven Lemmas (Available as scaffolding)
1. **tau_S_le_2**: τ(S_e) ≤ 2 for any packing element e
2. **tau_X_le_2**: τ(X(e,f)) ≤ 2 for bridges between e and f
3. **lemma_2_2**: All triangles in S_e pairwise share edges
4. **k4_cover**: Triangles on ≤4 vertices have τ ≤ 2

## The Bridge Absorption Argument

### Key Observation
A bridge triangle t ∈ X(e,f) shares an edge with e (by definition). This means:
- t ∩ e has at least 2 vertices
- So t shares some edge {u,v} with e where u,v ∈ e

### Why Bridges Are Absorbed
Consider a minimal cover C for S_e with |C| ≤ 2.

**Claim**: C also covers every bridge t ∈ X(e,f).

**Proof sketch**:
1. The packing triangle e is in trianglesSharingEdge(G, e) trivially
2. If e ∈ S_e (e is compatible with itself), then C covers e
3. Any edge of e that C uses to cover triangles in S_e will also hit bridges sharing that edge
4. If e ∉ S_e, then e shares edge with another packing element - but this contradicts packing definition

### Alternative argument
- Every triangle in S_e shares an edge with e
- By lemma_2_2, triangles in S_e pairwise share edges
- This forces S_e triangles to cluster around edges of e
- The ≤2 edges covering S_e must include edges of e (or edges incident to e's vertices)
- Bridges also share edges with e, so they're hit by the same cover

## Main Theorem

**Theorem (tuza_nu4)**: If ν(G) = 4, then τ(G) ≤ 8.

**Proof using bridge absorption**:
1. Let M = {e, f, g, h} be a maximum packing with 4 triangles
2. Every triangle in G either:
   - Is in some S_x for x ∈ M, or
   - Is a bridge X(x,y) for some x,y ∈ M
3. Cover each S_x with ≤2 edges: total ≤ 8 edges
4. By bridge absorption, these same 8 edges also cover all bridges
5. Therefore τ(G) ≤ 8 ∎

## Key Lemma to Prove

**bridge_absorption**: For any cover C of S_e ∪ S_f, C also covers X(e,f).

This is the "tip of the spear" - the new result that unlocks τ ≤ 8.
