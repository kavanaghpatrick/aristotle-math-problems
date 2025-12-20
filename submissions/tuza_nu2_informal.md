# Prove Tuza's Conjecture for ν ≤ 3

## The Conjecture
For any graph G: τ(G) ≤ 2ν(G)
- τ(G) = minimum edges to hit all triangles
- ν(G) = maximum edge-disjoint triangles

## What's Already Proven (in attached context)
1. **tau_S_le_2**: τ(S_e) ≤ 2 for any packing element e
2. **lemma_2_2**: Triangles in S_e pairwise share edges
3. **lemma_2_3**: ν(G \ T_e) = ν - 1
4. **tuza_case_nu_0**: Base case ν = 0

## Proof Strategy for ν = 2

Let M = {e, f} be a maximum packing with |e ∩ f| = 1 (share vertex v).

Decompose all triangles into:
- S_e: share edge with e, not f
- S_f: share edge with f, not e
- X = T_e ∩ T_f: share edge with both
- Rest: share edge with neither (empty for ν = 2)

**Key observations:**
1. τ(S_e) ≤ 2 and τ(S_f) ≤ 2 (by tau_S_le_2)
2. X consists of triangles containing v (the shared vertex)
3. All triangles in X share vertex v, so τ(X) ≤ 2

**Bound:** τ(G) ≤ τ(S_e) + τ(S_f) + τ(X) ≤ 2 + 2 + 2 = 6

**Better bound:** When S_e is a star (τ = 1), we get τ ≤ 1 + 1 + 2 = 4 ✓

## Goal
Prove: trianglePackingNumber G = 2 → triangleCoveringNumber G ≤ 4
