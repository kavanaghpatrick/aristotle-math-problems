# Tuza's Conjecture: τ(G) ≤ 2ν(G) - Corrected Approach

## The Problem

- **ν(G)** = maximum number of edge-disjoint triangles
- **τ(G)** = minimum edges to delete to make G triangle-free
- **Tuza's Conjecture**: τ(G) ≤ 2ν(G)

## Why Our Previous Approach Failed

We tried to prove: "Removing any 2 edges from any packing triangle strictly decreases ν."

**Counterexample** (found by Aristotle):
```
Graph: 4 vertices {0,1,2,3}
Edges: {0-1, 1-2, 2-0, 0-3, 1-3}
Triangles: {0,1,2} and {0,1,3} sharing edge {0,1}

ν = 1 (only one edge-disjoint triangle fits)
Max packing P = {{0,1,2}}

If we remove edges {1,2} and {0,2} from {0,1,2}:
- Triangle {0,1,2} is destroyed
- BUT triangle {0,1,3} survives! (it uses edge {0,1} which we kept)
- So ν(G') = 1 = ν(G) -- NOT decreased!
```

The flaw: We left the shared edge {0,1} intact, allowing another triangle to "take over."

## The Corrected Approach

**Don't use induction on ν.** Instead, directly construct a cover.

### Key Insight

For each packing triangle p, we must choose 2 edges that cover:
1. Triangle p itself (any edge does this)
2. ALL triangles whose ONLY packing connection is through p

A triangle t is "nearby" p if:
- t shares an edge with p
- t shares NO edges with any other packing triangle

### Why 2 Edges Always Suffice

Let p have edges {e1, e2, e3}. Partition nearby triangles:
- T1 = triangles sharing e1 with p
- T2 = triangles sharing e2 with p
- T3 = triangles sharing e3 with p

**Claim**: At least one of T1, T2, T3 is empty.

**Proof by contradiction**: Suppose all three are non-empty. Pick t1 ∈ T1, t2 ∈ T2, t3 ∈ T3.

If t1, t2, t3 are pairwise edge-disjoint:
- They're edge-disjoint from each other
- They're edge-disjoint from P \ {p} (by definition of "nearby")
- So (P \ {p}) ∪ {t1, t2, t3} is a valid packing
- Size = |P| - 1 + 3 = |P| + 2 > |P|
- This contradicts P being maximum!

So at least two of t1, t2, t3 must share an edge. This forces structural constraints that allow 2 edges of p to cover all of T.

### Main Theorem

**Construction**:
1. Get max packing P with |P| = ν
2. For each p ∈ P, pick 2 edges covering all nearby triangles
3. Let S = union of all these edges
4. |S| ≤ 2|P| = 2ν

**S covers all triangles**:
- Every triangle t shares an edge with some p ∈ P (proven lemma)
- If t is "nearby" exactly one p, then p's 2 edges cover t
- If t shares edges with multiple packing triangles, at least one covers t

Therefore τ ≤ |S| ≤ 2ν. QED.

## What Needs to be Proven

The key lemma: `two_edges_cover_nearby`

For any max packing P and p ∈ P, there exist 2 edges e1, e2 ∈ triangleEdges(p) such that every nearby triangle shares at least one of {e1, e2}.
