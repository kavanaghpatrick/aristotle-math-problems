# Tuza's Conjecture: ν=2 Case

## Statement

For any graph G with triangle packing number ν(G) = 2, prove that the triangle covering number τ(G) ≤ 4.

## Definitions

- **Triangle packing number ν(G)**: Maximum number of edge-disjoint triangles
- **Triangle covering number τ(G)**: Minimum number of edges that hit all triangles

## Goal

```lean
theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4
```

## Context

Tuza's Conjecture (1981): τ(G) ≤ 2ν(G) for all graphs.
- Known: τ ≤ (66/23)ν ≈ 2.87ν (Haxell 1999)
- Proven here: ν=1 case (τ ≤ 2)
- Target: ν=2 case (τ ≤ 4)
