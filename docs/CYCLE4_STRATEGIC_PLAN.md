# Cycle_4 Strategic Plan: τ ≤ 8

**Created**: Dec 26, 2025
**Target**: Prove τ(G) ≤ 8 for cycle_4 configuration
**Current Best**: τ ≤ 12 (proven)
**Gap**: 4 edges to eliminate

---

## 1. PROBLEM DEFINITION

### 1.1 The Cycle_4 Configuration

Four packing triangles A, B, C, D arranged in a cycle:
```
        v_da -------- v_ab
         /\            /\
        /  \          /  \
       /  D \        / A  \
      /      \      /      \
     d        \    /        a
              v_cd -------- v_bc
               /\            /\
              /  \          /  \
             / C  \        / B  \
            /      \      /      \
           c        --------      b
```

**Shared vertices**: v_ab, v_bc, v_cd, v_da (each shared by exactly 2 adjacent packing elements)

**Diagonal disjointness**: A ∩ C = ∅, B ∩ D = ∅

**Private vertices**: a, b, c, d (each belongs to exactly one packing element)

### 1.2 Goal

Prove: For any graph G with triangle packing M where |M| = 4 in cycle_4 configuration:
```
τ(G) ≤ 2 × ν(G) = 2 × 4 = 8
```

---

## 2. PROVEN INFRASTRUCTURE

### 2.1 Core Theorems (in `/proven/tuza/nu4/`)

| File | Theorem | Statement |
|------|---------|-----------|
| `slot_local_tuza_via_link_graph.lean` | `local_tuza_via_link_graph` | τ(T_v) ≤ 2·ν(T_v) for any vertex v |
| `slot_local_tuza_via_link_graph.lean` | `partition_piece_tuza_bound` | τ(Ti) ≤ 2·ν(Ti) for Ti ⊆ T_v |
| `slot_disjoint_partition_proven.lean` | `cycle4_disjoint_partition` | T = T₁ ⊔ T₂ ⊔ T₃ ⊔ T₄ (by primary shared vertex) |
| `slot113_tau_le_12_conservative.lean` | `tau_le_12_cycle4` | τ ≤ 12 via T_pair decomposition |
| `slot60_cycle4_proven.lean` | `tau_containing_v_in_pair_le_4` | τ(containing v in T_pair) ≤ 4 |
| `slot60_cycle4_proven.lean` | `tau_avoiding_v_in_pair_le_2` | τ(avoiding v in T_pair) ≤ 2 |
| `slot60_cycle4_proven.lean` | `tau_tpair_le_6` | τ(T_pair(e,f)) ≤ 6 |

### 2.2 The Local Tuza Breakthrough

**Key insight**: Link graph reduction proves local Tuza bound.

```
τ(T_v) ≤ VC(LinkGraph(v))     [cover_at_v_le_vertex_cover]
       ≤ 2·Matching(LinkGraph) [vertex_cover_le_two_matching - König]
       = 2·ν(T_v)              [packing_at_v_eq_matching]
```

**Why this matters**:
- Every triangle in cycle_4 contains at least one shared vertex (slot73_all_middle)
- So the 4-partition by shared vertex covers ALL triangles
- If we could bound Σ ν(T_i) ≤ 4, we'd get τ ≤ 8

### 2.3 Supporting Lemmas

```sql
-- Query from database
SELECT name, english FROM literature_lemmas WHERE validated_true = 1 AND frontier_id = 'nu_4';
```

Key validated lemmas:
- `triangleEdgeEquiv`: Bijection between triangles at v and link graph edges
- `disjoint_triangles_iff_matching`: Edge-disjoint triangles ↔ matching in link graph
- `packing_at_v_eq_matching`: ν(T_v) = matching number of link graph
- `tau_union_le_sum`: τ(A ∪ B) ≤ τ(A) + τ(B)

---

## 3. KNOWN FALSE LEMMAS (DO NOT USE)

| Lemma | Why False | Counterexample |
|-------|-----------|----------------|
| `tau_at_shared_vertex_le_2` | Local ν can be ≥ 2 | Graph with 3 edge-disjoint triangles at v_ab |
| `tau_containing_vertex_le_2` | Same as above | {v,a,b}, {v,c,d}, {v,e,f} need 3 edges |
| `bridge_absorption` | Bridges may not be hit by S_e ∪ S_f covers | Aristotle counterexample |
| `avoiding_v_vertices` | Avoiding triangles can have vertices outside e ∪ f | Aristotle counterexample |

---

## 4. HISTORY OF ATTEMPTS

### 4.1 Phase 1: T_pair Decomposition (Successful → τ ≤ 12)

**Approach**: Decompose into 2 T_pairs, each bounded by 6.
```
T = T_pair(A,B) ∪ T_pair(C,D)
τ ≤ τ(T_pair(A,B)) + τ(T_pair(C,D)) ≤ 6 + 6 = 12
```

**Why it stopped at 12**: Each T_pair has τ ≤ 6 = 4 (containing) + 2 (avoiding), but we can't improve this decomposition.

### 4.2 Phase 2: All-Middle Theorem (Successful)

**Proved**: Every triangle in cycle_4 contains at least one shared vertex.
- File: `slot73_all_middle.lean`
- Enables 4-partition by primary shared vertex

### 4.3 Phase 3: Local τ ≤ 2 Attempt (Failed)

**Attempted**: τ(T_i) ≤ 2 for each partition piece
**Why failed**: Grok's counterexample showed ν(T_v_ab) ≥ 2, so τ(T_v_ab) can be ≥ 3

### 4.4 Phase 4: Diagonal Pairing (Unclear)

**Attempted**: τ(S_{v_ab ∪ v_cd}) ≤ 4
**Status**: No valid counterexample found, but also no proof
**Submitted**: slot126 to Aristotle (pending)

### 4.5 Phase 5: Local Tuza via Link Graph (BREAKTHROUGH)

**Proved**: τ(T_v) ≤ 2·ν(T_v) for any vertex v
**Implication**: If Σ ν(T_i) ≤ 4, then τ ≤ 8

---

## 5. CURRENT STRATEGIC OPTIONS

### Option A: Local Packing Sum Bound

**Lemma to prove**:
```lean
theorem local_packing_sum_le_global :
    trianglePackingOn G T_ab + trianglePackingOn G T_bc +
    trianglePackingOn G T_cd + trianglePackingOn G T_da ≤ 4
```

**If TRUE**:
```
τ = Σ τ(T_i) ≤ 2·Σ ν(T_i) ≤ 2·4 = 8 ✓
```

**Challenge identified by Gemini**:
Cross-partition triangles can share edges!
- t₁ = {v_ab, a, c} ∈ T_ab
- t₂ = {v_cd, a, c} ∈ T_cd
- Both share edge {a, c}

This means P_ab ∪ P_cd may NOT be a valid global packing.

**Possible fix**: The constraint that cross-partition triangles share edges may FORCE the sum to be bounded. Need to prove this structurally.

**Feasibility**: 60% - Promising but needs careful structural argument

---

### Option B: Link Graph Vertex Cover ≤ 2

**Lemma to prove**:
```lean
lemma cycle4_link_graph_vertex_cover_le_2 (v : sharedVertex cfg) :
    vertexCoverNumber (linkGraph G v) ≤ 2
```

**If TRUE**:
```
τ(T_i) ≤ VC(LinkGraph(v_i)) ≤ 2
τ = Σ τ(T_i) ≤ 4 × 2 = 8 ✓
```

**Reasoning**:
- Two packing elements A, B contain v
- Their "opposite edges" (edges not containing v) appear in link graph
- These 2 edges might be coverable by 2 vertices

**Challenge**:
Link graph can have more edges from non-packing triangles. If link graph is a 5-cycle, VC = 3.

**Feasibility**: 40% - Seems too optimistic, likely FALSE

---

### Option C: Overlap-Aware Cover Construction

**Approach**: Account for edges that cover triangles in multiple partitions.

**Key observation**:
- Edge {a, c} covers both t₁ = {v_ab, a, c} and t₂ = {v_cd, a, c}
- So we shouldn't count it twice in the cover

**Lemma to prove**:
```lean
theorem overlap_cover_le_8 :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E covers all triangles
```

**Construction sketch**:
1. For each shared vertex v_i, take 2 spokes (VC of link graph)
2. Total: 4 × 2 = 8 spokes
3. But some spokes may be counted twice (shared between adjacent vertices)
4. Net: ≤ 8 distinct edges

**Feasibility**: 50% - Requires careful case analysis

---

### Option D: Direct 8-Edge Construction

**Approach**: Explicitly construct 8 edges that cover all triangles.

**Proposed construction**:
```
Cover = {v_ab-a, v_ab-b, v_bc-b, v_bc-c, v_cd-c, v_cd-d, v_da-d, v_da-a}
```

This is "2 spokes per shared vertex, choosing the private vertex neighbors."

**Why it might work**:
- Every packing triangle is covered (each has 2 spokes from its shared vertices)
- Non-packing triangles must share edge with packing → likely hit by a spoke

**Challenge**:
Non-packing triangles might need spokes to non-private vertices.

**Feasibility**: 45% - Need to verify all cases

---

### Option E: Case Analysis on Diagonal Edges

**Approach**: Different bounds depending on whether diagonal edges v_ab-v_cd or v_bc-v_da exist.

**Cases**:
1. **No diagonal edges**: Local link graphs are smaller → easier VC bounds
2. **One diagonal edge**: Creates bridging triangles → handle separately
3. **Both diagonal edges**: Maximum complexity → may need full 8

**Feasibility**: 55% - Systematic but requires 3 separate proofs

---

### Option F: Hybrid T_pair + Local Tuza

**Approach**: Use T_pair for one decomposition, local Tuza for refinement.

**Idea**:
```
τ ≤ τ(T_pair(A,B)) + τ(T_pair(C,D))
```

But instead of using τ(T_pair) ≤ 6, refine using local Tuza:
- T_pair(A,B) contains triangles at v_ab, v_bc, v_da
- Apply local_tuza to get tighter bound

**Feasibility**: 35% - Complex decomposition

---

## 6. RISK ANALYSIS: Is τ ≤ 8 Actually TRUE?

### Evidence FOR τ ≤ 8:
1. Grok's counterexample (3 triangles at v_ab) still has global τ = 4 ≤ 8
2. No counterexample with τ > 8 has been found
3. Tuza's conjecture is believed true for all ν

### Evidence AGAINST (potential issues):
1. Local ν can be large → naive sum gives τ ≤ 16 or more
2. Cross-partition edge sharing complicates analysis
3. Link graph VC can exceed 2

### Assessment:
**75% confidence** that τ ≤ 8 is TRUE, but proof is non-trivial.

---

## 7. RECOMMENDED ACTION PLAN

### Phase 1: Validate Key Lemmas (1-2 days)

**Step 1.1**: Test Option A (Local Packing Sum) with concrete examples
- Construct worst-case cycle_4 graph
- Compute actual Σ ν(T_i)
- If ever > 4, Option A is FALSE

**Step 1.2**: Test Option B (VC ≤ 2) with concrete examples
- For each shared vertex, compute link graph
- Find minimum vertex cover
- If any VC > 2, Option B is FALSE

**Step 1.3**: Submit both to Aristotle in parallel
- `slot127_local_packing_sum.lean` - Option A
- `slot128_link_graph_vc.lean` - Option B

### Phase 2: Based on Results (2-3 days)

**If Option A TRUE**: Done! τ ≤ 8 follows immediately.

**If Option B TRUE**: Done! τ ≤ 8 follows immediately.

**If both FALSE**: Move to Phase 3.

### Phase 3: Fallback Strategies (3-5 days)

**Step 3.1**: Implement Option C (Overlap-Aware Cover)
- Carefully count shared edges between partitions
- Prove net cover size ≤ 8

**Step 3.2**: Implement Option E (Case Analysis)
- Split by diagonal edge existence
- Prove τ ≤ 8 for each case separately

**Step 3.3**: Direct Construction (Option D)
- Explicitly verify 8-spoke cover works
- May need Aristotle for full formalization

---

## 8. CONCRETE ARISTOTLE SUBMISSIONS

### Submission 1: Local Packing Sum (Option A)

```lean
/-
Problem: Prove that sum of local packing numbers ≤ global packing number
Key insight: Cross-partition triangles share edges, limiting total
-/

theorem local_packing_sum_le_global (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4Config G M) :
    trianglePackingOn G (trianglesAtVertex G cfg.v_ab) +
    trianglePackingOn G (trianglesAtVertex G cfg.v_bc) +
    trianglePackingOn G (trianglesAtVertex G cfg.v_cd) +
    trianglePackingOn G (trianglesAtVertex G cfg.v_da) ≤ 4 := by
  sorry

-- If true, immediate corollary:
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4Config G M) :
    triangleCoveringNumber G ≤ 8 := by
  calc triangleCoveringNumber G
      ≤ τ(T_ab) + τ(T_bc) + τ(T_cd) + τ(T_da) := tau_union_le_sum ...
    _ ≤ 2*ν(T_ab) + 2*ν(T_bc) + 2*ν(T_cd) + 2*ν(T_da) := by apply local_tuza...
    _ = 2 * (ν(T_ab) + ν(T_bc) + ν(T_cd) + ν(T_da)) := by ring
    _ ≤ 2 * 4 := by apply local_packing_sum_le_global...
    _ = 8 := by norm_num
```

### Submission 2: Link Graph VC Bound (Option B)

```lean
/-
Problem: Prove vertex cover of link graph at shared vertex ≤ 2
Approach: Use structure of cycle_4 - only 2 packing elements at each vertex
-/

lemma cycle4_link_graph_vc_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4Config G M)
    (v : V) (hv : v ∈ cfg.sharedVertices) :
    vertexCoverNumber (linkGraph G v) ≤ 2 := by
  sorry

-- Direct corollary via cover_at_v_le_vertex_cover
theorem tau_le_8_via_vc (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4Config G M) :
    triangleCoveringNumber G ≤ 8 := by
  have h1 : τ(T_ab) ≤ 2 := by apply cover_at_v_le_vertex_cover.trans; apply cycle4_link_graph_vc_le_2...
  -- similarly for other vertices
  calc τ ≤ τ(T_ab) + τ(T_bc) + τ(T_cd) + τ(T_da) := ...
       _ ≤ 2 + 2 + 2 + 2 := by linarith
       _ = 8 := by norm_num
```

---

## 9. SUCCESS CRITERIA

**Primary goal**: Prove `tau_le_8_cycle4` with 0 sorry

**Intermediate goals**:
- [ ] Validate one of Options A or B with examples
- [ ] Submit to Aristotle and get partial progress
- [ ] Identify exact structural lemma needed

**Fallback goal**: If τ ≤ 8 is FALSE, find explicit counterexample graph with τ = 9.

---

## 10. APPENDIX: Key Code References

### File Locations
```
proven/tuza/nu4/
├── slot_local_tuza_via_link_graph.lean  # NEW - Local Tuza bound
├── slot_disjoint_partition_proven.lean   # 4-partition
├── slot113_tau_le_12_conservative.lean   # Current best τ ≤ 12
├── slot60_cycle4_proven.lean             # Core cycle_4 lemmas
└── slot73_all_middle.lean                # All triangles contain shared vertex
```

### Database Queries
```sql
-- Get all proven nu4 lemmas
SELECT name, english FROM literature_lemmas
WHERE validated_true = 1 AND frontier_id = 'nu_4';

-- Get failed approaches to avoid
SELECT approach_name, why_failed FROM failed_approaches
WHERE frontier_id = 'nu_4';

-- Get current case status
SELECT * FROM nu4_cases WHERE case_name = 'cycle_4';
```

---

## 11. DECISION POINT

**Recommended next action**: Submit Options A and B to Aristotle in parallel.

- If either succeeds → τ ≤ 8 is PROVEN
- If both fail with counterexamples → Pivot to Option C or E
- If both timeout → Need manual proof development

**Estimated time to resolution**: 3-7 days depending on Aristotle results.
