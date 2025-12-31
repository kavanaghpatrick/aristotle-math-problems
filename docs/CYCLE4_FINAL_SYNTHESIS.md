# CYCLE4 FINAL SYNTHESIS - AI Debate Results

**Date**: December 29, 2025
**Status**: CONSENSUS REACHED (with caveats)

## AI Models Consulted
- **Grok-4**: Suggested 8-spoke strategy (INCOMPLETE)
- **Gemini**: Identified gaps, proposed "Local Sunflower Covers" (CORRECT DIRECTION)

---

## PROVEN BOUNDS

### slot113_tau_le_12_conservative.lean
- **UUID**: 5d2756b0-17d7-4e88-98ed-55117529555c
- **Bound**: τ ≤ 12 for cycle_4
- **Method**: T_pair decomposition (6 + 6)
- **Status**: COMPLETE PROOF (0 sorry)

---

## 8-SPOKE STRATEGY ANALYSIS

### Grok's Proposed 8 Edges
```
{v_ab, a}, {v_ab, b}, {v_bc, b}, {v_bc, c}, {v_cd, c}, {v_cd, d}, {v_da, d}, {v_da, a}
```

### FAILURE CASE (Gemini's Counter-Example)
**Triangle T_inner = {v_ab, v_bc, v_da}**
- Edges: {v_ab, v_bc}, {v_bc, v_da}, {v_da, v_ab}
- These are CYCLE EDGES (packing edges between shared vertices)
- NONE of Grok's 8 spokes hit T_inner!

**Why T_inner can exist:**
- Uses only shared vertices (all in {v_ab, v_bc, v_cd, v_da})
- Satisfies cycle4_all_triangles_contain_shared ✓
- Intersects A (at v_ab, v_da), B (at v_ab, v_bc), D (at v_da) → can't extend packing
- ν stays 4, so T_inner is valid

### CORRECT STRUCTURE

The cycle_4 packing (from slot113):
```
A = {v_ab, v_da, p_A}    B = {v_ab, v_bc, p_B}
C = {v_bc, v_cd, p_C}    D = {v_cd, v_da, p_D}

Cycle edges: {v_ab, v_da}, {v_ab, v_bc}, {v_bc, v_cd}, {v_cd, v_da}
Spokes: {v_ab, p_A}, {v_da, p_A}, {v_ab, p_B}, {v_bc, p_B}, ...
```

The 8-spoke strategy uses only spoke edges, missing cycle edges entirely!

---

## CORRECT APPROACH: Local Sunflower Covers

### Gemini's Solution

**Key Insight**: Every triangle contains at least one shared vertex (cycle4_all_triangles_contain_shared).

**Strategy**:
1. At each shared vertex v, triangles form a "sunflower" with center v
2. Due to ν=4 constraint, at most 2 distinct "external directions" at each v
3. Select 2 edges from v that cover all triangles at v
4. Total: 4 vertices × 2 edges = 8 edges

**Critical Difference**: The 2 edges may be:
- Packing spoke edges (v to private vertex)
- Cycle edges (v to adjacent shared vertex)
- NON-PACKING edges (chords/diagonals that exist in G)

### Why This Works

The sunflower at v_ab contains:
- A = {v_ab, v_da, p_A} (uses edges {v_ab, v_da}, {v_ab, p_A})
- B = {v_ab, v_bc, p_B} (uses edges {v_ab, v_bc}, {v_ab, p_B})
- External triangles at v_ab

To cover ALL triangles at v_ab, we need edges that hit all "petal tips".
- If petals only go to {v_da, p_A, v_bc, p_B}, we need ≤ 2 edges
- This is because further external vertices would allow ν > 4

---

## ACTION ITEMS

### For Aristotle Submission

1. **Cannot use fixed 8-edge set** - the correct cover depends on graph structure
2. **Need to prove**: At each shared vertex v, ≤ 2 edges suffice (sunflower lemma)
3. **Key lemma to prove**:
```lean
lemma sunflower_at_shared_vertex :
  ∀ v ∈ {v_ab, v_bc, v_cd, v_da},
  ∃ E_v ⊆ G.edgeFinset, E_v.card ≤ 2 ∧
  (∀ e ∈ E_v, v ∈ e) ∧  -- edges incident to v
  ∀ t ∈ trianglesContaining G v, ∃ e ∈ E_v, e ∈ t.sym2
```

4. **Then combine**: τ ≤ 4 × 2 = 8 by union over all shared vertices

---

## FALSE LEMMAS TO AVOID

From docs/FALSE_LEMMAS.md:
- ❌ local_cover_le_2 (wrong: 4 M-edges may be needed)
- ❌ support_sunflower τ≤2 (wrong: includes M-elements)
- ❌ external_share_common_vertex (wrong: slot131_v2 counterexample)
- ❌ 8-spoke strategy (wrong: misses cycle/chord triangles)

---

## NEXT STEPS

1. Formalize sunflower_at_shared_vertex lemma
2. Prove the "≤ 2 external directions" constraint from ν=4
3. Submit to Aristotle with careful structure
4. If that fails, accept τ ≤ 12 as best current bound

---

## CONFIDENCE ASSESSMENT

- **τ ≤ 12**: HIGH (complete proof in slot113)
- **τ ≤ 8 via sunflower**: MEDIUM (conceptually sound, needs formalization)
- **8-spoke strategy**: LOW (known gaps, DO NOT USE)
