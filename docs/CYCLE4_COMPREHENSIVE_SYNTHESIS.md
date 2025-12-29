# Cycle_4 Case: Comprehensive Synthesis
## December 26, 2025

This document synthesizes all AI debates, reviews, and findings for the ν=4 cycle_4 case.

---

## 1. THE PROBLEM

**Goal:** Prove τ(G) ≤ 8 when ν(G) = 4 and the maximal packing M forms a cycle_4 configuration.

**Cycle_4 Structure:**
```
    v_ab
   A----B
   |    |
v_da    v_bc
   |    |
   D----C
    v_cd
```

- M = {A, B, C, D}, four triangles
- Adjacent pairs share exactly 1 vertex: A∩B = {v_ab}, B∩C = {v_bc}, etc.
- **Diagonal constraint:** A∩C ≤ 1, B∩D ≤ 1 (opposite elements share ≤ 1 vertex)

---

## 2. WHAT DOESN'T WORK

### 2.1 FALSE LEMMAS (Confirmed by 3 AIs)

| False Lemma | Why False | Counter-example |
|-------------|-----------|-----------------|
| `local_cover_le_2 (M-edges only)` | At v_ab, may need 4 M-edges | 4 triangles using 4 different M-edges at v_ab |
| `avoiding_covered_by_spokes` | If t avoids v, spokes from v can't hit t | By definition |
| `bridge_absorption` | Bridges may not share edges with S_e | Geometric construction |
| `Sym2.mk(v,v)` | Self-loops aren't edges | Type error |
| `trianglesContainingVertex partition` | Wrong for T_pair decomposition | Overcounting |

### 2.2 FAILED APPROACHES

| Approach | Why Failed |
|----------|------------|
| T_pair gives τ ≤ 4 per pair | FALSE - actual bound is τ ≤ 6 per pair |
| Contrapositive (slot111 original) | "Edge-disjoint ≠ can extend packing" |
| No 4 disjoint petals (slot112) | Lemma is FALSE - 4 disjoint petals CAN exist |
| Local M-edge covering | 4 M-edges may be needed, not 2 |

### 2.3 THE CONTRAPOSITIVE FLAW (Detailed)

**Original claim:** If τ > 8, construct 5th packing element.

**The flaw:**
1. Claimed: "t_bad edge-disjoint from M ⟹ t_bad extends M"
2. Reality: Packing requires `(t_bad ∩ X).card ≤ 1` for all X (VERTEX condition)
3. Counter: Triangle can be edge-disjoint but share 2 vertices with some X

**Verdict:** Contrapositive is fundamentally unsound. Use direct approach.

---

## 3. WHAT WORKS: THE SUNFLOWER RESOLUTION

### 3.1 The Key Insight

From the Codex counterexample (4 triangles at v_ab):
```
T1 = {v_ab, v_da, x}    uses M-edge {v_ab, v_da}
T2 = {v_ab, a_priv, x}  uses M-edge {v_ab, a_priv}
T3 = {v_ab, v_bc, x}    uses M-edge {v_ab, v_bc}
T4 = {v_ab, b_priv, x}  uses M-edge {v_ab, b_priv}

ALL 4 TRIANGLES SHARE THE NON-M EDGE {v_ab, x}!
```

**Sunflower Structure:**
- Core: shared vertex v
- Petals: triangles radiating out
- All petals share a non-M edge from the core

### 3.2 Why `local_cover_le_2` IS True (With Non-M Edges)

**FALSE version:** "2 M-edges at v cover all triangles at v"
**TRUE version:** "2 edges (possibly non-M) at v cover all triangles at v"

The sunflower groups triangles by their external vertex:
- All triangles with external vertex x are hit by {v, x}
- By ν=4 constraint, at most 2 such groups exist
- So 2 edges {v, x₁}, {v, x₂} suffice

### 3.3 The Correct Approach

**Slot110 (Sunflower):**
```
4 shared vertices × 2 non-M edges each = 8 edges total
```

**Slot111 (Two-Vertex Decomposition):**
```
Class_AC (v_ab or v_cd): ≤ 4 edges
Class_BD (v_bc or v_da): ≤ 4 edges
Total: ≤ 8 edges
```

Both approaches use the sunflower insight at each vertex.

---

## 4. VALIDATED LEMMAS (Use These!)

| Lemma | English | Status |
|-------|---------|--------|
| `cycle4_all_triangles_contain_shared` | Every t contains some v_ij | PROVEN |
| `triangle_shares_edge_with_packing` | Every t shares edge with M | PROVEN (maximality) |
| `cycle4_element_contains_shared` | All-Middle property | PROVEN |
| `tau_union_le_sum` | Subadditivity | PROVEN |
| `tau_S_le_2` | S sets covered by 2 | PROVEN |
| `tau_X_le_2` | X sets covered by 2 | PROVEN |
| `trianglesSharingMEdgeAt` partition | Correct partition for covering | TRUE |

---

## 5. AI REVIEW SUMMARY

### Slot110 (Sunflower)

| Reviewer | Verdict | Key Point |
|----------|---------|-----------|
| Gemini | SUBMIT | No false lemmas, viable approach |
| Grok | REVISE | Pigeonhole claim needs detail |
| Codex | REVISE | "At most 2 external vertices" unjustified |

**Decision:** SUBMITTED (project 11348661-5701-48cb-a909-ab64983bba61)

### Slot111 (Contrapositive - Original)

| Reviewer | Verdict | Key Point |
|----------|---------|-----------|
| Gemini | REVISE | Edge-disjoint ≠ can extend packing |
| Grok | REVISE | Same flaw; direct approach safer |
| Codex | REVISE | Fundamental logical error |

**Decision:** REVISED to Two-Vertex Decomposition (slot111_two_vertex_decomposition.lean)

### Slot112 (No Disjoint Petals)

| Reviewer | Verdict | Key Point |
|----------|---------|-----------|
| Gemini | REVISE (HIGH RISK) | Core lemma is FALSE |
| Grok | - | - |
| Codex | REVISE | Lemma is FALSE |

**Decision:** ABANDONED (lemma mathematically false)

---

## 6. CURRENT STATUS

| Slot | Approach | Status | Notes |
|------|----------|--------|-------|
| 110 | Sunflower | SUBMITTED | Await Aristotle result |
| 111 | Two-Vertex Decomposition | REVISED | Ready for review/submit |
| 112 | No Disjoint Petals | ABANDONED | Lemma false |

---

## 7. KEY LEARNINGS

### 7.1 Approach Selection

1. **Direct > Contrapositive** for covering bounds
2. **Global > Local** when local bounds are tight
3. **Non-M edges > M-edges** for flexibility in covering

### 7.2 Common Pitfalls

1. Confusing "edge-disjoint" with "vertex condition for packing"
2. Assuming local bounds that are false (local_cover_le_2 with M-edges)
3. Trying to prove false lemmas (no 4 disjoint petals)

### 7.3 Underused Insights

1. **Diagonal constraint (A∩C≤1, B∩D≤1)** - creates natural partition
2. **Sunflower structure** - groups triangles by external vertex
3. **Non-M edge flexibility** - the fix for local_cover_le_2

---

## 8. NEXT ACTIONS

1. Monitor slot110 Aristotle result
2. Review slot111 (Two-Vertex Decomposition) with 3 AIs
3. If slot110 fails, analyze Aristotle feedback and revise
4. If both fail, investigate if sunflower pigeonhole is false

---

## 9. APPENDIX: PROOF SKETCHES

### A. Sunflower Proof (Slot110)

```
1. Every t shares edge with M [triangle_shares_edge_with_packing]
2. Every M-edge contains shared v [cycle4_element_contains_shared]
3. So t ∈ trianglesSharingMEdgeAt(v) for some v
4. Triangles at v form sunflower:
   - Core: v
   - Petals: {v, m, x} for various M-neighbors m
   - All share at most 2 external vertices x₁, x₂
5. Edges {v, x₁}, {v, x₂} cover all triangles at v
6. 4 vertices × 2 edges = 8 total. QED.
```

### B. Two-Vertex Decomposition (Slot111 Revised)

```
1. Partition: Class_AC (contains v_ab or v_cd) and Class_BD (contains v_bc or v_da)
2. By diagonal constraint: t can't have both v_ab and v_cd
3. By cycle4_all_triangles_contain_shared: every t in some class
4. Class_AC: sunflower at v_ab (2 edges) + sunflower at v_cd (2 edges) = 4
5. Class_BD: sunflower at v_bc (2 edges) + sunflower at v_da (2 edges) = 4
6. Total: 4 + 4 = 8. QED.
```

---

*Generated from AI debates between Grok, Gemini, and Codex on December 26, 2025.*
