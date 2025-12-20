# Tuza ν=2: Four Edges Suffice

## Theorem

```lean
theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4
```

## Statement

If a graph has packing number ν = 2 (maximum 2 edge-disjoint triangles), then at most 4 edges are needed to cover all triangles.

## Proof Strategy

Let M = {e, f} be a maximum packing of size 2.

**Key Insight**: Every triangle in G must share an edge with e or f (otherwise we could extend the packing).

Define:
- T_e = triangles sharing an edge with e
- T_f = triangles sharing an edge with f

By maximality: G.cliqueFinset 3 ⊆ T_e ∪ T_f

**Case Analysis**:

**Case 1**: e and f are vertex-disjoint
- T_e triangles pairwise share edges (by ν=2 maximality)
- By ν=1 argument: τ(T_e) ≤ 2
- Similarly: τ(T_f) ≤ 2
- Total: τ(G) ≤ 4

**Case 2**: e = {v,a,b} and f = {v,c,d} share vertex v
- If triangle {a,b,z} exists with z ∉ {v,c,d}:
  - Use M' = {{a,b,z}, f} as vertex-disjoint packing → Case 1
- Otherwise: ALL triangles in T_e contain v
  - Covered by 2 edges incident to v

## Key Lemmas

```lean
-- Every triangle shares edge with e or f
lemma nu2_all_triangles_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    ∀ t ∈ G.cliqueFinset 3, (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2

-- Disjoint triangles can't both share edge with t
lemma vertex_disjoint_share_exclusive (e f t : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint e f) :
    ¬((t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- Triangles through vertex v covered by 2 edges
lemma cover_through_vertex ...
```

## Verification

```bash
lake env lean proven/tuza/nu2/tuza_nu2_PROVEN.lean
```

## Aristotle Details

- **UUID**: 0764be78-b5d4-4f03-a32f-dc5efb92806d
- **Date**: December 19, 2025
- **Lean version**: leanprover/lean4:v4.24.0
- **Mathlib**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
