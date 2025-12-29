# CRITICAL GAPS IN CYCLE_4 PROOF - December 26, 2025

## Executive Summary

**THE CURRENT PROOF STRATEGY IS FLAWED.** Three AIs (Grok, Gemini, Codex) have independently identified critical issues.

## Issue 1: Self-Loop Bug in slot73

**Location:** `proven/tuza/nu4/slot73_eb28d806/output.lean` line 327

```lean
have h2 := hM { Sym2.mk ( v, v ) } ; simp_all +decide ;
```

**Problem:** `Sym2.mk (v, v)` is a SELF-LOOP, not a valid edge in SimpleGraph.

**Database Entry:** #22 `local_cover_le_2_self_loop` - marked BOGUS

## Issue 2: Wrong Partition Strategy (GEMINI)

**Counter-Example:**
Consider triangle `t = {v_ab, v_cd, c_ext}` where `c_ext` is the external vertex of C.

- **Validity:** t exists if edges (v_ab, v_cd) and (v_ab, c_ext) exist
- **Maximality:** t shares edge (v_cd, c_ext) with packing element C ✓
- **THE FAILURE:**
  - t contains v_ab, so current strategy assigns it to `trianglesContainingVertex v_ab`
  - But t does NOT share any M-edge incident to v_ab
  - The only shared edge is in C (incident to v_cd)
  - `local_cover_le_2` for v_ab CANNOT cover t!

**Wrong Chain:**
```
t contains v_ab → t is covered by local edges at v_ab  ❌ FALSE
```

**Correct Chain:**
```
t shares M-edge at v_ab → t is covered by local edges at v_ab  ✓ TRUE
```

## Issue 3: "Support" Ambiguity (GROK)

The lemma `cycle4_triangle_at_vertex_supported` says:
> If t contains v and shares edge with A, then t has edge from M_edges_at(v)

But this only applies to triangles sharing edge with A (which contains v).

**Gap:** Triangles that:
1. Contain v_ab
2. Share edge with C or D (not A or B)

These triangles are NOT "supported" at v_ab!

## The Correct Fix

### OLD (WRONG) Strategy:
```
For each shared vertex v:
  Cover all triangles CONTAINING v with 2 edges
```

### NEW (CORRECT) Strategy:
```
For each shared vertex v:
  Cover all triangles SHARING M-EDGE AT v with 2 edges

Then prove: Every triangle shares M-edge at SOME shared vertex
```

### Key New Lemma Needed:
```lean
lemma every_triangle_shares_M_edge_at_shared :
  ∀ t ∈ G.cliqueFinset 3,
  ∃ v ∈ {v_ab, v_bc, v_cd, v_da},
  ∃ e ∈ M_edges_at G M v, e ∈ t.sym2
```

**Proof Sketch:**
1. By maximality, t shares edge with some X ∈ M
2. Let e be the shared edge (|t ∩ X| ≥ 2)
3. X is a triangle in cycle_4, so X contains exactly 2 shared vertices
4. Every edge in X contains at least one shared vertex of X
5. Therefore e contains a shared vertex v
6. Therefore e ∈ M_edges_at G M v and e ∈ t.sym2 ✓

## Action Items

1. **DO NOT USE slot73's local_cover_le_2 proof** - it has self-loop bug
2. **Rewrite partition strategy** - use M-edge sharing, not vertex containment
3. **Prove new covering lemma** - every_triangle_shares_M_edge_at_shared
4. **Update all submissions** to use correct partition

## Database Updates

```sql
-- Mark the gap
INSERT INTO failed_approaches (frontier_id, approach_name, why_failed, avoid_pattern)
VALUES ('nu_4', 'trianglesContainingVertex_partition',
'WRONG: Triangle at v_ab can share edge only with C/D, not covered by local edges at v_ab',
'Do NOT partition by vertex containment. Partition by M-edge sharing.');
```
