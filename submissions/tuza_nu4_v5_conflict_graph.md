# Tuza ν=4: Conflict Graph Analysis

## Goal
Analyze the conflict graph of triangles to find structural restrictions that force Tuza's bound.

## Definitions

**Conflict Graph C(G)**:
- Vertices: triangles of G
- Edges: connect two triangles if they share an edge

**Key Property**: If two triangles share an edge, one edge covers both.

## Structural Questions

1. If the conflict graph C(G) is triangle-free, does τ ≤ 2ν hold more easily?

2. For ν=4, the conflict graph has 4 vertices (the packing). What structure forces τ > 8?

3. The conflict graph encodes which triangles can be "efficiently" covered together.

## Parker's Obstruction in Conflict Terms

For e ∈ M (max packing), T_e = triangles sharing edge with e.
In conflict graph terms: T_e = neighborhood of e plus triangles sharing edges with e's edges.

Parker fails when: For ALL e ∈ M, the subgraph induced by T_e requires 3+ edges to cover.

## Approach

Prove: If conflict graph has specific structure (e.g., bounded degree, no dense subgraph), then τ ≤ 2ν.

For ν=4: Characterize which conflict graph structures allow τ > 8.

## Target Theorem

For graph G with ν(G) = 4:
- Let C be the conflict graph restricted to a max packing M
- If C has property P, then τ(G) ≤ 8

Find property P that covers all cases.
