# Tuza ν=0: Trivial Case

## Theorem

```lean
lemma nu_eq_0_implies_tau_eq_0 (h : trianglePackingNumber G = 0) :
    triangleCoveringNumber G = 0
```

## Statement

If a graph has no triangles (ν = 0), then zero edges are needed to cover all triangles (τ = 0).

## Proof Idea

If ν(G) = 0, there are no edge-disjoint triangles. This means either:
1. G has no triangles at all, OR
2. G has triangles but they all share edges

In either case, if we can't form even a single triangle packing, we check that G.cliqueFinset 3 = ∅.
The empty edge set ∅ trivially covers all (zero) triangles.

## Verification

```bash
lake env lean proven/tuza/nu0/tuza_nu0_PROVEN.lean
```

## Aristotle Details

- **UUID**: 2b21c426-552d-4eb4-831e-b797545758e2
- **Date**: December 19, 2025
- **Lean version**: leanprover/lean4:v4.24.0
- **Mathlib**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
