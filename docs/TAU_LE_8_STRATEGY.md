# Strategy for τ ≤ 8: From Proven τ ≤ 12

## Status: τ ≤ 12 PROVEN (0 sorry)

Aristotle proved `tau_le_12_cycle4_conservative` with structure:
- E_AB = 4 spokes at v_ab + 2 bases = 6 edges
- E_CD = 4 spokes at v_cd + 2 bases = 6 edges
- Union bound: |E_AB ∪ E_CD| ≤ 12

## The Gap: Why Not 8?

**Critical Finding**: E_AB ∩ E_CD = ∅ (zero overlap!)

- Spokes at v_ab: `{s(v_ab, v_da), s(v_ab, a_priv), s(v_ab, v_bc), s(v_ab, b_priv)}`
- Spokes at v_cd: `{s(v_cd, v_bc), s(v_cd, c_priv), s(v_cd, v_da), s(v_cd, d_priv)}`
- Different hub vertices → different edges → no overlap

## Two Paths to τ ≤ 8

### Approach 1: Grok's "6+6-4" (Modified Cover)

**Idea**: Modify E_AB and E_CD to share 4 "cycle edges"

```
Cycle edges (connect adjacent shared vertices):
- s(v_ab, v_bc) - in both E_AB and E_CD
- s(v_bc, v_cd) - in both E_AB and E_CD
- s(v_cd, v_da) - in both E_AB and E_CD
- s(v_da, v_ab) - in both E_AB and E_CD
```

**Why these work**: Each cycle edge appears in TWO triangles (one from each adjacent pair).

**Calculation**: 6 + 6 - 4 = 8

### Approach 2: Codex's "2+2+2+2" (Direct Partition)

**Idea**: Partition ALL triangles by containing shared vertex

```
T_ab = triangles containing v_ab
T_bc = triangles containing v_bc (not v_ab)
T_cd = triangles containing v_cd (not v_ab, v_bc)
T_da = triangles containing v_da (not v_ab, v_bc, v_cd)
```

**Key claim**: Each partition needs ≤ 2 edges (link graph has matching ≤ 1)

**Calculation**: 2 + 2 + 2 + 2 = 8

## Key Lemmas Needed

### For Approach 1:
1. `cycleEdges_subset_edgeFinset`: The 4 cycle edges exist in G
2. `cycleEdges_cover_bridges`: These edges cover all bridges
3. `modified_covers_intersect`: Both E_AB and E_CD can include all 4

### For Approach 2:
1. `tau_at_shared_vertex_le_2`: 2 edges cover triangles at each shared vertex
2. `link_matching_at_shared_le_1`: Link graph matching bound (enables the 2-edge claim)

## Submission Files

| Slot | Approach | Key Lemma |
|------|----------|-----------|
| 113 | PROVEN | τ ≤ 12 (0 sorry) |
| 120 | B | Shared edges foundation |
| 121 | B | Spoke cover exists |
| 122 | B | Link graph cover |
| 123 | NEW | Overlap cover (both approaches) |

## Next Steps

1. Submit slot123 to Aristotle
2. If cycle edges approach works → done
3. If not, fall back to link graph matching bound
4. Either way, τ ≤ 8 should follow from one of these

## False Patterns to Avoid

- ❌ `local_cover_le_2`: Can need 4 edges at a vertex
- ❌ `bridge_absorption`: S_e cover doesn't auto-cover bridges
- ❌ `disjoint_sets_combinable_packings`: Disjoint triangle sets ≠ edge-disjoint
- ❌ "One edge at v covers all triangles at v": FALSE! s(v,w) only covers triangles with BOTH v and w
