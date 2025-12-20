# Tuza's Conjecture for ν ≤ 3: Final Assembly

## Goal
Prove: For any graph G with packingNumber(G) ≤ 3, we have coveringNumber(G) ≤ 2 * packingNumber(G).

## Already Proven (by Aristotle)

### Case ν = 0
If packingNumber(G) = 0, then G has no triangles, so coveringNumber(G) = 0.

### Case ν = 1 (UUID: 2b21c426)
If packingNumber(G) = 1, then any two triangles share an edge (otherwise we'd have a packing of size 2).
By the K4 covering lemma: if all triangles pairwise share edges, either:
1. They share a common edge → cover with 1 edge
2. Their union is on ≤4 vertices → cover with 2 edges

### Case ν = 2 (UUID: 0764be78)
If packingNumber(G) = 2 with max packing M = {e, f}:
- Every triangle shares an edge with e or f (by maximality)
- T_e = triangles sharing edge with e
- T_f = triangles sharing edge with f
- By covering lemma: τ(T_e) ≤ 2 and τ(T_f) ≤ 2
- Total: coveringNumber(G) ≤ 4 = 2 * 2

## What Remains: Case ν = 3

### Key Insight (Parker's Lemma 2.2)
For max packing M with element e:
- S_e = {t ∈ T_e : t doesn't share edge with other packing elements}
- All triangles in S_e pairwise share edges
- τ(S_e) ≤ 2

### The Challenge for ν = 3
We need to show: For some e ∈ M, T_e = S_e.

If e, f, g ∈ M are the three packing triangles:
- T_e \ S_e = triangles sharing edge with e AND with f or g
- If this set is nonempty for ALL choices of e, we get a contradiction

### Argument for ν = 3
Consider max packing M = {e, f, g} with |M| = 3.

**Claim**: There exists e ∈ M such that T_e ∩ T_f ∩ T_g = ∅.

**Proof**: Suppose every e ∈ M has some triangle t sharing edges with all three.
Such a triangle t would need |(t ∩ e)| ≥ 2, |(t ∩ f)| ≥ 2, |(t ∩ g)| ≥ 2.
But t has only 3 vertices, and e, f, g are edge-disjoint (packing!).
This is impossible - t can share 2+ vertices with at most one packing element.

So for this e: T_e = S_e, and τ(T_e) ≤ 2.

The remaining graph G' = G \ T_e has:
- packingNumber(G') ≤ 2 (packing M' = M \ {e})
- By induction: coveringNumber(G') ≤ 4

Total: coveringNumber(G) ≤ τ(T_e) + τ(G') ≤ 2 + 4 = 6 = 2 * 3

## Main Theorem

**Theorem (Tuza for ν ≤ 3)**: For any graph G with packingNumber(G) ≤ 3:
coveringNumber(G) ≤ 2 * packingNumber(G)

**Proof by cases**:
- ν = 0: τ = 0 ≤ 0
- ν = 1: τ ≤ 2 ≤ 2 (Proven: 2b21c426)
- ν = 2: τ ≤ 4 ≤ 4 (Proven: 0764be78)
- ν = 3: τ ≤ 6 ≤ 6 (Above argument) □
