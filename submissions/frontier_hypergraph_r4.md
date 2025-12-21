# Aharoni-Zerbib Conjecture for 4-Uniform Hypergraphs

## Problem Statement

**Aharoni-Zerbib Conjecture**: For an r-uniform hypergraph H:

**τ(H) ≤ ⌈(r+1)/2⌉ · ν(H)**

where:
- τ(H) = minimum number of (r-1)-edges needed to hit all r-edges
- ν(H) = maximum number of pairwise edge-disjoint r-edges

## Cases by r

| r | Bound | Status |
|---|-------|--------|
| 2 | τ ≤ 1.5ν | Known (edge covering) |
| 3 | τ ≤ 2ν | **Tuza's conjecture (OPEN)** |
| 4 | τ ≤ 2.5ν | **OPEN - our target** |
| 5 | τ ≤ 3ν | OPEN |

## Definitions for r=4

- **4-edge**: A set of 4 vertices that form a clique (all pairs adjacent)
- **3-face**: A set of 3 vertices (used for covering)
- **Edge-disjoint 4-edges**: Share at most 2 vertices
- **Cover**: A 3-face f covers a 4-edge e if f ⊆ e

## Generalization of Tuza Lemmas

Our r=3 (Tuza) lemmas generalize to r=4:

### Lemma: Pairwise face-sharing structure

**r=3 version**: If triangles pairwise share edges (≥2 common vertices), they form star or K4.

**r=4 version**: If 4-edges pairwise share faces (≥3 common vertices), either:
1. All share a common 3-face, OR
2. Their union has at most 5 vertices

**Proof sketch**:
- Let e₁, e₂ be two 4-edges with |e₁ ∩ e₂| ≥ 3
- They share a 3-face f = e₁ ∩ e₂
- If e₃ also shares 3 vertices with both, it must contain f (else union grows too large)
- Union of all such 4-edges has at most |f| + 2 = 5 vertices

### Lemma: Common face implies τ ≤ 1

If all 4-edges contain a common 3-face f, then f alone covers all of them.
So τ = 1 ≤ 2.5ν for any ν ≥ 1.

### Lemma: Bounded union implies τ ≤ 2

If 4-edges have union of size ≤ 5, there are at most (5 choose 4) = 5 such 4-edges.
Two carefully chosen 3-faces can cover all of them.

**Proof**: In 5 vertices {a,b,c,d,e}, the 5 possible 4-edges are:
- {a,b,c,d}, {a,b,c,e}, {a,b,d,e}, {a,c,d,e}, {b,c,d,e}

The 3-faces {a,b,c} and {d,e,?} for appropriate ? cover all.

### Main Structural Lemma

**Claim**: If 4-edges pairwise share 3-faces, they can be covered by ≤2 3-faces.

**Proof**: By the structure lemma, either common face (τ ≤ 1) or bounded union (τ ≤ 2).

## Proof Strategy for τ ≤ 2.5ν

**Induction on ν**:

**Base case**: ν ≤ 1. Then τ ≤ 1 ≤ 2.5.

**Inductive step**: Let M be a maximum packing with |M| = ν.

For each 4-edge e ∈ M:
- T_e = 4-edges sharing a 3-face with e
- S_e = 4-edges in T_e that don't share 3-face with any other f ∈ M

By generalized Lemma 2.2: S_e 4-edges pairwise share faces.
By structural lemma: τ(S_e) ≤ 2.

The tricky part is bounding τ(T_e \ S_e), the "bridges" that share faces with multiple packing elements.

**Key insight**: With r=4, the bridge structure is more constrained:
- A 4-edge sharing 3-face with two packing elements must share ≥6 vertices total
- But packing elements are edge-disjoint (share ≤2 vertices)
- This severely limits bridge configurations

## Expected Results

1. **Weak theorem**: τ ≤ 3ν for 4-uniform hypergraphs
2. **Strong theorem** (the conjecture): τ ≤ 2.5ν = 5ν/2 for 4-uniform hypergraphs

Even the weak theorem would be new and publishable.

## Connection to Ryser's Conjecture

Ryser's Conjecture: For r-partite r-uniform hypergraphs, τ ≤ (r-1)ν.

Aharoni-Zerbib is intermediate: ⌈(r+1)/2⌉ < r-1 for r ≥ 4.

So proving Aharoni-Zerbib would be progress toward Ryser.
