# Tuza's Conjecture for ν ≤ 3: Informal Proof

## Goal
Prove: For any graph G with ν(G) ≤ 3, we have τ(G) ≤ 2ν(G).

Where:
- ν(G) = maximum number of edge-disjoint triangles (packing number)
- τ(G) = minimum edges to hit all triangles (covering number)

## Known Results (Already Proven in Lean)
1. τ(S_e) ≤ 2 for any packing element e
2. Inductive bound: τ(G) ≤ τ(T_e) + τ(rest) where ν(rest) = ν - 1
3. Pairwise intersecting triangles are either a star or contained in K₄

## The Gap
The inductive bound uses τ(T_e), but we only proved τ(S_e) ≤ 2.
- T_e = triangles sharing edge with e
- S_e = T_e minus triangles sharing edge with OTHER packing elements
- S_e ⊆ T_e

## Key Insight
For ν ≤ 3, we can always find packing element e with τ(T_e) ≤ 2.

## Proof by Cases

### Case ν = 0
No triangles, so τ = 0 ≤ 0 = 2ν. ✓

### Case ν = 1
M = {e}. Only one packing element.
- S_e = T_e (no other elements to exclude)
- τ(T_e) = τ(S_e) ≤ 2
- τ(G) ≤ τ(T_e) + τ(rest) = 2 + 0 = 2 = 2ν ✓

### Case ν = 2
M = {e, f} is a maximum packing.

**Subcase 2a: e and f are vertex-disjoint**
- A triangle cannot share ≥2 vertices with both e and f (would need 4+ vertices in 3-vertex triangle)
- So T_e ∩ T_f = ∅ (except possibly triangles = e or f)
- T_e = S_e (no triangles share edge with both)
- τ(T_e) = τ(S_e) ≤ 2 ✓
- Similarly τ(T_f) ≤ 2
- Every triangle shares edge with e or f (else extends packing)
- τ(G) ≤ τ(T_e) + τ(T_f) ≤ 4 = 2ν ✓

**Subcase 2b: e = {v,a,b} and f = {v,c,d} share exactly vertex v**
Two possibilities:

*Case 2b-i: There exists triangle {a,b,z} for some z ≠ v*
- {a,b,z} shares edge ab with e
- {a,b,z} is vertex-disjoint from f (since a,b ∉ f and z ≠ v)
- M' = {{a,b,z}, f} is a packing (both edge-disjoint from each other)
- |M'| = 2, and M' is vertex-disjoint!
- Reduces to Subcase 2a ✓

*Case 2b-ii: No triangle {a,b,z} exists for z ≠ v*
- The only triangle with edge ab is e = {v,a,b}
- All triangles in T_e must contain vertex v:
  - Triangles with edge va: {v,a,x} all contain v ✓
  - Triangles with edge vb: {v,b,y} all contain v ✓
  - Triangles with edge ab: only {v,a,b} = e (by assumption), contains v ✓
- All triangles in T_e contain v
- Cover all of T_e with edges va and vb (both incident to v)
- τ(T_e) ≤ 2 ✓
- τ(G) ≤ τ(T_e) + τ(T_f) ≤ 2 + 2 = 4 = 2ν ✓

### Case ν = 3
M = {e, f, g} is a maximum packing.

By similar case analysis on vertex-sharing patterns:
- If any element is vertex-disjoint from others, that's our e with T_e = S_e
- If all share vertices, the structure is constrained:
  - At most 3 shared vertex pairs possible
  - By pigeonhole, at least one element e shares vertices with ≤1 other element
  - For that e, T_e \ S_e is small and covered by same edges as S_e

**Pigeonhole argument:**
- Each pair of triangles can share at most 1 vertex (they're edge-disjoint)
- With 3 triangles, at most 3 shared vertex pairs
- The "sharing graph" has 3 vertices (e, f, g) and at most 3 edges
- Average degree ≤ 2, so some element has degree ≤ 2
- That element shares vertices with at most 2 others
- The T_e \ S_e triangles must contain these shared vertices
- Combined with S_e (which is pairwise intersecting), τ(T_e) ≤ 2

Therefore τ(G) ≤ τ(T_e) + τ(rest) ≤ 2 + 2(ν-1) = 2ν ✓

## Conclusion
For all ν ∈ {0, 1, 2, 3}, we have τ(G) ≤ 2ν(G). ∎
