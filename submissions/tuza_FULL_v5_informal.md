# Tuza's Conjecture: τ(G) ≤ 2ν(G)

## The Problem

For any graph G:
- **ν(G)** = maximum number of edge-disjoint triangles (triangle packing number)
- **τ(G)** = minimum number of edges to delete to make G triangle-free (triangle covering number)

**Tuza's Conjecture (1981)**: τ(G) ≤ 2ν(G) for all graphs G.

This conjecture is OPEN. Best known bound is τ(G) ≤ 2.87ν(G).

## Proof Strategy: Strong Induction

**Prove by strong induction on ν(G):**

**Base case (ν = 0):** If G has no triangles, τ(G) = 0. Done.

**Inductive step (ν > 0):**
1. Let P be a maximum edge-disjoint triangle packing with |P| = ν
2. Pick any triangle p ∈ P with vertices {a, b, c}
3. Let S = {edge(a,b), edge(a,c)} (two edges of p)
4. Claim: ν(G\S) < ν(G)
5. By IH: τ(G\S) ≤ 2·ν(G\S) ≤ 2·(ν-1)
6. By subadditivity: τ(G) ≤ |S| + τ(G\S) ≤ 2 + 2·(ν-1) = 2ν

## The Key Lemma to Prove

**exists_two_edge_reduction**: For any G with ν(G) > 0, there exist at most 2 edges whose removal strictly decreases ν.

### Why This Should Be True

Pick triangle p from max packing P. Remove 2 of p's 3 edges (call them e₁, e₂).

**Observation 1**: Triangle p is destroyed (a triangle needs all 3 edges).

**Observation 2**: Any triangle sharing e₁ or e₂ with p is also destroyed.

**Observation 3**: Every triangle in G shares at least one edge with some packing triangle (by maximality of P - otherwise we could add it to P).

**Key insight**: In G\{e₁,e₂}, the "contribution" of p to any packing is gone. Any max packing Q in G\{e₁,e₂} cannot use p or triangles that relied on e₁, e₂. So |Q| < |P|.

### More Detailed Argument

Let Q be a max packing in G\{e₁,e₂}.
- Q is also a valid packing in G (removing edges only removes triangles)
- So |Q| ≤ ν(G) = |P|
- But can |Q| = |P|?

If |Q| = |P|, then Q is also a max packing in G. By the "every triangle shares edge with max packing" lemma, every triangle in G shares an edge with some q ∈ Q.

But p ∈ G is a triangle, so p shares an edge with some q ∈ Q. Since p has only 3 edges and we removed 2, p shares its remaining edge e₃ with q.

This means q also uses edge e₃ = edge(b,c). But then q and p share edge e₃, contradicting that P was edge-disjoint (since p ∈ P and |Q| = |P| means Q could replace P as a max packing, but then q sharing edge with p contradicts edge-disjointness).

Therefore |Q| < |P|, i.e., ν(G\S) < ν(G).

## Proven Lemmas Available

These lemmas have been formally verified:

1. **tuza_base_case**: ν(G) = 0 implies τ(G) = 0
2. **triangleCoveringNumber_le_card_add_deleteEdges**: τ(G) ≤ |S| + τ(G\S)
3. **exists_max_packing**: Maximum packing exists
4. **triangle_shares_edge_with_max_packing**: Every triangle shares edge with some max packing triangle
5. **triangle_has_three_edges**: A triangle has exactly 3 edges
6. **triangle_destroyed_by_two_edges**: Removing 2 edges destroys a triangle

## What Remains

Prove: exists_two_edge_reduction

Once this is proven, the main theorem follows immediately by the induction structure above.
