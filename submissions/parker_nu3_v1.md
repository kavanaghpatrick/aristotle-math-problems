# Parker's Proof of Tuza for ν ≤ 3

## Goal
Prove: If trianglePackingNumber(G) ≤ 3, then triangleCoveringNumber(G) ≤ 6.

## Definitions

**Triangle packing number** ν(G): Maximum number of edge-disjoint triangles.

**Triangle covering number** τ(G): Minimum edges to hit all triangles.

**Tuza's conjecture**: τ(G) ≤ 2ν(G) for all graphs G.

## Parker's Method (arXiv:2406.06501)

Let M be a maximum edge-disjoint triangle packing with |M| = ν.

For each e ∈ M, define:
- **T_e** = triangles sharing an edge with e
- **S_e** = triangles sharing an edge with e but NOT with any other f ∈ M

### Lemma 2.2: ν(S_e) = 1
Any two triangles in S_e share an edge.

**Proof**: Suppose h₁, h₂ ∈ S_e don't share an edge.
- h₁ shares edge with e (by definition of S_e)
- h₂ shares edge with e (by definition of S_e)
- h₁ doesn't share edge with any f ∈ M \ {e} (by definition of S_e)
- h₂ doesn't share edge with any f ∈ M \ {e} (by definition of S_e)
- h₁ and h₂ don't share an edge (by assumption)

Then (M \ {e}) ∪ {h₁, h₂} is an edge-disjoint packing of size |M| + 1.
This contradicts maximality of M.

### Lemma 2.3: ν(G \ T_e) = ν - 1
After removing all triangles in T_e, the packing number drops by exactly 1.

**Proof**:
- M \ {e} is a packing in G \ T_e of size ν - 1.
- Suppose N is a packing in G \ T_e with |N| ≥ ν.
- Every triangle in N doesn't share an edge with e (since T_e removed).
- So N ∪ {e} is an edge-disjoint packing in G of size |N| + 1 ≥ ν + 1.
- Contradiction.

### Inductive Bound
τ(G) ≤ τ(T_e) + τ(G \ T_e)
     ≤ τ(T_e) + 2(ν - 1)    [by induction]

For Tuza (τ ≤ 2ν), we need τ(T_e) ≤ 2.

### Why τ(T_e) ≤ 2 for ν ≤ 3
The paper proves by case analysis that for small ν, we can always find e ∈ M with τ(T_e) ≤ 2.

## Theorem Statement

```lean
theorem tuza_case_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) : triangleCoveringNumber G ≤ 6
```
