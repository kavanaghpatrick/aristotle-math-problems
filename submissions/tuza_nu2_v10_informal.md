# Tuza's Conjecture: ν=2 Case

## Goal
Prove: If a graph G has triangle packing number ν(G) = 2, then the triangle covering number τ(G) ≤ 4.

## Proven Building Blocks

1. **exists_max_packing**: A maximum triangle packing always exists.

2. **triangle_shares_edge_with_packing**: When ν=2, every triangle in G shares at least one edge with some triangle in the maximum packing. (Otherwise we could extend the packing to size 3.)

3. **extensions_form_K4**: When ν=2 and τ>4, each packing triangle extends to a K₄. (Uses the key lemma extension_triangle_exists_nu2.)

4. **tau_gt_4_implies_two_K4_with_packing**: Extracts two K₄s s1, s2 containing the edge-disjoint packing triangles T1, T2.

## Three Gaps to Prove

### Gap 1: two_K4_almost_disjoint
**Claim**: |s1 ∩ s2| ≤ 1

**Proof sketch**: If |s1 ∩ s2| ≥ 2, then s1 and s2 share an edge e. But T1 ⊆ s1 and T2 ⊆ s2 are edge-disjoint packing triangles. In a K₄, every edge belongs to exactly 2 triangles. If e is shared by both K₄s, then some triangle containing e would appear in both K₄s, creating overlap with the packing structure. This contradicts edge-disjointness.

### Gap 2: exists_disjoint_in_K4 (Outlier Lemma)
**Claim**: If triangle T shares an edge with T_base ⊆ K₄ but T ⊄ K₄, then there exists triangle U ⊆ K₄ edge-disjoint from T.

**Proof sketch**: Let K₄ = {a,b,c,d} and T_base = {a,b,c}. If T shares edge {a,b} but has vertex x ∉ K₄, then T = {a,b,x}. The triangles in K₄ are: {a,b,c}, {a,b,d}, {a,c,d}, {b,c,d}. Triangle {c,d,a} has edges {{c,d}, {c,a}, {d,a}} which shares no edge with {{a,b}, {a,x}, {b,x}} since x ∉ K₄. Similarly for {c,d,b}. So we can always find an edge-disjoint triangle in K₄.

### Gap 3: two_K4_cover_le_4 (Main Covering Lemma)
**Claim**: There exists S with |S| ≤ 4 that covers all triangles.

**Proof sketch**:
1. Every triangle T shares edge with T1 or T2 (by triangle_shares_edge_with_packing).
2. If T shares edge with T1 but T ⊄ s1, apply exists_disjoint_in_K4 to get U ⊆ s1 edge-disjoint from T.
3. Then {T, U, T2} is an edge-disjoint packing of size 3, contradicting ν=2.
4. So every triangle is contained in s1 or s2.
5. In K₄, τ(K₄) = 2: two opposite edges (like {a,b} and {c,d}) cover all 4 triangles.
6. Take 2-edge cover S1 for s1 and 2-edge cover S2 for s2. Then S1 ∪ S2 covers all triangles with ≤ 4 edges.

## Main Theorem
Combining these: If ν=2 and τ>4, we derive two K₄s that cover all triangles with ≤ 4 edges, contradiction. So τ ≤ 4.
