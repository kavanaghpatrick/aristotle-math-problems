# slot306: All X-Externals Share Common Vertex - FULLY PROVEN

**UUID**: `1658ed6d-db63-42b1-9118-2911c7a06975`
**Status**: PROVEN (0 sorry, 0 axiom)
**Date**: 2026-01-08

## Summary

Aristotle has fully proven that **all X-externals share a common vertex** - a critical lemma for the τ ≤ 8 proof. This resolves the Hajós counterexample concern through elegant case analysis.

## Proven Theorems

### 1. `two_externals_share_edge`
```lean
lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂
```
**Proof**: By contradiction - if T₁, T₂ don't share an edge, we can form a 5-packing by adding both to M \ {X}, contradicting ν = 4.

### 2. `all_externals_share_common_vertex` (MAIN RESULT)
```lean
theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T
```

**Proof by cases**:
- **Case A** (all externals have same outside vertex v): Since |T \ X| = 1 for each external, if all these singletons are equal, v is in all externals.
- **Case B** (some externals have different outside vertices): By `externals_disjoint_outside_implies_same_edge`, all externals share the same edge within X. Any vertex of this edge is in all externals.

### 3. `two_edges_cover_all_externals`
```lean
theorem two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)
```

**Proof**: Apply `all_externals_share_common_vertex` to find v. If v ∈ X, take two edges of X incident to v. If v ∉ X, take appropriate edges connecting v to X.

## Key Supporting Lemmas (All Proven)

| Lemma | Purpose |
|-------|---------|
| `external_inter_X_card` | External T has |T ∩ X| = 2 |
| `externals_disjoint_outside_implies_same_edge` | Different outside ⟹ same X-edge |
| `externals_all_same_edge_of_exists_diff` | Lifts pairwise to global |
| `cover_externals_case_inside` | Cover when v ∈ X |
| `cover_externals_case_outside` | Cover when v ∉ X |

## Impact on τ ≤ 8

This theorem is **the missing piece** for proving τ ≤ 8:

```
For each X ∈ M (4 elements):
  - Find common vertex v of X's externals (by this theorem)
  - Take 2 edges incident to v

Total: 4 × 2 = 8 edges
Coverage: Each triangle is either in M or external to exactly one M-element
```

## Resolves Hajós Counterexample Concern

Previous analysis suggested pairwise sharing doesn't imply common vertex (Hajós). This proof shows:

1. **Pairwise sharing + external structure** ⟹ common vertex
2. The key constraint: externals are triangles sharing an *edge* with X (not just a vertex)
3. This forces either common outside vertex OR common edge in X

## Next Steps

1. ✅ slot306 proven
2. Create τ ≤ 8 main theorem combining:
   - `two_edges_cover_all_externals` (slot306)
   - Subadditivity across 4 elements
   - Union bound: 4 × 2 = 8 edges total

## File Location

Proven code in: `/Users/patrickkavanagh/Downloads/1658ed6d-db63-42b1-9118-2911c7a06975-output.lean`

Copy to: `proven/tuza/nu4/slot306_common_vertex_exists.lean`
