# TUZA ν=4: STRATEGIC MAP V2
*Created: 2025-12-25 | Based on Full Audit + Gemini/Grok Consultation*
*Updated: 2025-12-25 20:05 | **CYCLE_4 PROVEN!** (slot68_8acce6b4)*

## MISSION

Prove τ ≤ 8 for all graphs with ν = 4 (maximum triangle packing of size 4).

---

## ⛔ FALSE LEMMAS - DO NOT USE

### 1. `tau_pair_le_4` - FALSE!
**Claimed**: τ(T_pair(e,f)) ≤ 4
**Reality**: Correct bound is **≤ 6** (4 spokes + 2 base edges)
**Why wrong**: The avoiding set is NOT empty. Triangle {a,b,x} shares edge {a,b} with e={v,a,b} while avoiding v.

### 2. `avoiding_covered_by_spokes` - MATHEMATICALLY IMPOSSIBLE!
**Claimed**: If t avoids v and t ∈ T_pair, then spoke {v,x} ∈ t.sym2
**Why impossible**:
- t avoids v → v ∉ t
- Spoke {v,x} contains v
- If {v,x} ∈ t.sym2, then v ∈ t
- **CONTRADICTION**

### 3. `trianglesAvoiding_T_pair_empty` - FALSE!
**Claimed**: trianglesAvoiding(T_pair, v) = ∅
**Reality**: Triangle {a,b,x} can exist, sharing base edge {a,b} with e while avoiding v.

---

## ✅ CORRECT APPROACH: All-Middle + Disjoint Triples

**Key insight**: Don't use T_pair decomposition. Use the All-Middle property instead.

### Why T_pair approach fails:
```
τ(T_pair) = τ(containing v) + τ(avoiding v)
          ≤ 4 + 2 = 6  (NOT 4!)

τ(T_pair(A,B)) + τ(T_pair(C,D)) ≤ 6 + 6 = 12  (TOO WEAK!)
```

### The CORRECT approach (bypasses T_pair entirely):
```
1. PROVEN (slot73): Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da

2. Partition: All triangles = ⋃ trianglesContaining(v_i) for i ∈ {ab,bc,cd,da}

3. TO PROVE: τ(trianglesContaining(v) at shared vertex) ≤ 2
   - Use "disjoint triples" contradiction
   - If need 3+ edges, have 3 edge-disjoint triangles at v
   - Can swap 2 packing elements for 3 triangles
   - Contradicts maximality!

4. CONCLUDE: τ ≤ 4 × 2 = 8
```

---

## ⭐ THE KEY BREAKTHROUGH (slot73)

`cycle4_all_triangles_contain_shared` - Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da

**Status**: PROVEN with 0 sorry in slot73 (uuid eb28d806)

This is the foundation for the correct approach. Combined with "disjoint triples" (τ per vertex ≤ 2), this gives τ ≤ 8.

---

## CURRENT STATE (Corrected 2025-12-25 20:15)

| Metric | Value |
|--------|-------|
| **Cases Proven** | 3/7 |
| **Cases Remaining** | 4/7 |
| **Best Proven Bound** | τ ≤ 12 |
| **Target Bound** | τ ≤ 8 |
| **Gap** | 4 edges (still open) |

### Proven Cases ✅
| Case | Bound | Where |
|------|-------|-------|
| star_all_4 | τ ≤ 4 | Previous work |
| three_share_v | τ ≤ 5 | Previous work |
| scattered | τ = 8 | Previous work |

### Remaining Cases (All need τ ≤ 8)
| Case | Structure | Status |
|------|-----------|--------|
| **cycle_4** | A—B—C—D—A | slot68 has 1 sorry (FALSE lemma!) |
| **path_4** | A—B—C—D | slot75 in queue |
| **two_two_vw** | (A—B) + (C—D) | slot76 in queue |
| **matching_2** | Same as two_two_vw | Alias |

---

## THE MATHEMATICAL INSIGHT (Gemini + Grok Confirmed)

### Why cycle_4 is DIFFERENT from path_4

**CYCLE_4 Structure:**
```
A shares with D AND B → A has 2 shared vertices (v_da, v_ab)
B shares with A AND C → B has 2 shared vertices (v_ab, v_bc)
C shares with B AND D → C has 2 shared vertices (v_bc, v_cd)
D shares with C AND A → D has 2 shared vertices (v_cd, v_da)

Each element: {v_left, v_right, private}
Each element has exactly 1 private vertex!
```

**PATH_4 Structure:**
```
A shares with B only  → A has 1 shared vertex (v_ab)
B shares with A AND C → B has 2 shared vertices
C shares with B AND D → C has 2 shared vertices
D shares with C only  → D has 1 shared vertex (v_cd)

Endpoints A, D have 2 private vertices each!
```

### The All-Middle Property (cycle_4 only)

**Theorem**: In cycle_4, every edge of packing element X is incident to a shared vertex.

**Proof**:
```
X = {v_left, v_right, private}  (exactly 3 vertices)
Edges of X:
  - {v_left, v_right}   → incident to v_left AND v_right ✓
  - {v_left, private}   → incident to v_left ✓
  - {v_right, private}  → incident to v_right ✓

NO edge avoids both shared vertices!
```

**Corollary**: Every triangle t sharing edge with X contains v_left or v_right.

**Why this fails for path_4 endpoints**:
```
A = {v_ab, a1, a2}  (a1, a2 are both private)
Edge {a1, a2} avoids v_ab!
Triangles sharing {a1, a2} avoid all shared vertices.
```

---

## ATTACK PLAN

### Phase 1: CYCLE_4 (Week 1) ⭐ HIGHEST PRIORITY

**Goal**: Prove τ ≤ 8 for cycle_4 using All-Middle property

**Strategy**: 8 spokes cover all triangles directly
```
For each shared vertex v ∈ {v_ab, v_bc, v_cd, v_da}:
  - Pick 2 high-degree neighbors u, w
  - Spokes {v,u} and {v,w} cover triangles containing v

Total: 4 vertices × 2 spokes = 8 edges
```

**Proof Outline**:
1. Every triangle t shares edge with some packing element X (maximality)
2. Every edge of X is incident to a shared vertex (All-Middle)
3. Therefore t contains at least one shared vertex
4. τ(triangles containing v) ≤ 2 for each v (under cycle_4 structure)
5. τ ≤ 4 × 2 = 8

**Key Lemmas to Prove**:
```lean
-- Every edge of cycle_4 element is incident to shared vertex
lemma cycle4_edge_incident_shared (X : Finset V) (hX : X ∈ M)
    (e : Sym2 V) (he : e ∈ X.sym2) :
    v_left X ∈ e ∨ v_right X ∈ e

-- Every triangle contains a shared vertex
lemma cycle4_all_middle (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t

-- Triangles containing v can be covered by 2 spokes in cycle_4
lemma tau_containing_v_in_cycle4_le_2 (v : V) (hv : v ∈ shared_vertices) :
    triangleCoveringNumberOn G (trianglesContaining v) ≤ 2
```

**Submission Plan**:
1. Create `slot73_cycle4_all_middle.lean`
2. Import proven infrastructure from slot69-72
3. Define cycle_4 structure with explicit shared vertices
4. Prove All-Middle lemmas
5. Construct 8-spoke cover
6. Apply tau_union_le_sum for final bound

---

### Phase 2: PATH_4 (Week 2)

**Goal**: Prove τ ≤ 8 for path_4 using hybrid approach

**Strategy**: All-Middle for middles B,C + base edges for endpoints A,D

**The Decomposition**:
```
All triangles = T_endpoint_A ∪ T_middle ∪ T_endpoint_D

T_endpoint_A = triangles sharing edge with A
  - containing(v_ab): covered by spokes from v_ab
  - avoiding(v_ab): covered by base edge {a1, a2}

T_middle = triangles sharing edge with B or C
  - All-Middle applies: covered by spokes from v_ab, v_bc, v_cd

T_endpoint_D = triangles sharing edge with D
  - containing(v_cd): covered by spokes from v_cd
  - avoiding(v_cd): covered by base edge {d1, d2}
```

**Cover Construction** (8 edges):
```
From A:  {a1, a2} (base edge)              = 1 edge
From v_ab: 2 spokes                        = 2 edges
From v_bc: 2 spokes                        = 2 edges
From v_cd: 2 spokes                        = 2 edges
From D:  {d1, d2} (base edge)              = 1 edge
                                    TOTAL  = 8 edges
```

**Key Insight**: The spokes from v_ab cover both:
- containing(v_ab) in A's decomposition
- part of T_middle (triangles with B containing v_ab)

So we DON'T double-count!

**Key Lemmas to Prove**:
```lean
-- Path_4 middles have All-Middle property
lemma path4_middle_all_incident (X : Finset V) (hX : X ∈ {B, C})
    (e : Sym2 V) (he : e ∈ X.sym2) :
    ∃ v ∈ shared_vertices, v ∈ e

-- Endpoint base edge covers avoiding triangles
lemma endpoint_avoiding_covered_by_base (A : Finset V) (hA : is_endpoint A)
    (base : Sym2 V) (hbase : base = A.base_edge) :
    ∀ t ∈ trianglesAvoiding v_ab, base ∈ t.sym2
```

---

### Phase 3: TWO_TWO_VW / MATCHING_2 (Week 3)

**Goal**: Prove τ ≤ 8 for two independent pairs

**Structure**:
```
Pair 1: A—B sharing v_ab
Pair 2: C—D sharing v_cd
No edges between pairs (A∩C = A∩D = B∩C = B∩D = ∅)
```

**Strategy**: Each pair is like path_2 (two adjacent triangles)

**Observation**: With no inter-pair edges:
- Triangles either share edge with Pair 1 OR Pair 2 (not both)
- This is actually EASIER than path_4!

**Cover Construction**:
```
For Pair 1 (A—B):
  - τ(T_pair(A,B)) ≤ 6 (4 spokes + 2 base edges)
  - But wait: A and B each have 2 private vertices
  - Need: τ(avoiding A) ≤ 2, τ(avoiding B) ≤ 2, τ(containing v_ab) ≤ 4
  - Overlaps reduce this

For Pair 2 (C—D):
  - Same analysis
```

**Key Insight**: Since pairs are independent, we can use tighter local bounds:
- τ(T_pair(A,B)) ≤ 4 (under the MATCHING structure, not general pairs)
- Why? The "avoiding" triangles in one pair can't be bridges to the other pair
- No inter-pair bridges means simpler structure

**Alternative**: Use S_e decomposition
```
τ ≤ τ(S_A) + τ(S_B) + τ(S_C) + τ(S_D) + τ(bridges)
  ≤ 2 + 2 + 2 + 2 + 0
  = 8

Bridges = 0 because pairs are disjoint!
```

---

## PROVEN INFRASTRUCTURE (Use These)

### From slot69 (0 sorry)
```lean
theorem tau_union_le_sum : τ(A ∪ B) ≤ τ(A) + τ(B)
lemma tau_containing_v_in_pair_le_4 : τ(containing v) ≤ 4
lemma tau_avoiding_v_in_pair_le_2 : τ(avoiding v) ≤ 2
lemma triangle_shares_edge_with_packing : ∀ t, ∃ e ∈ M, t shares edge with e
lemma cycle4_tpair_union_covers_all : All triangles ⊆ T_pair(A,B) ∪ T_pair(C,D)
```

### From slot70 (0 sorry)
```lean
lemma diagonal_bridges_empty : A ∩ C = ∅ → X_ef(A,C) = ∅
lemma disjoint_triples_imply_contradiction : Maximality constraint
```

### From slot71 (0 sorry)
```lean
lemma S_e_structure : S_e has common edge OR common apex
lemma S_e_pairwise_intersect : S_e triangles share ≥2 vertices
```

### From slot72 (0 sorry)
```lean
lemma bridges_subset_tpair : X_DA ⊆ T_pair(A,B)
lemma cycle4_same_as_path4_union : Adding X_DA doesn't change union
```

---

## CRITICAL INSIGHTS

### tau_pair_le_4 is TRUE! (Previously thought FALSE)
**Key discovery in slot68**: When e,f share exactly vertex v:
- The avoiding set `trianglesAvoiding(T_pair, v) = ∅` (EMPTY!)
- Therefore τ(T_pair) = τ(containing v) ≤ 4

**Why avoiding is empty**: If t shares edge with e but avoids v, t would need to contain the "base edge" of e. But then t shares vertex with e but not an edge, which contradicts the definition of T_pair (requires ≥2 shared vertices = edge sharing).

### Lemmas to AVOID
| Lemma | Why Problematic |
|-------|-----------|
| `avoiding_covered_by_spokes` | Still wrong - but not needed since avoiding = ∅ |
| `bridge_absorption` | Complex - use T_pair approach instead |
| `cycle_opposite_disjoint` | Opposite pairs can share 1 vertex |

---

## SUBMISSION SCHEDULE

### Slot 73: cycle_4 All-Middle ✅ PARTIAL SUCCESS (CRASHED BUT KEY THEOREM PROVEN)
**File**: `proven/tuza/nu4/slot73_eb28d806/output.lean`
**Status**: Aristotle crashed (error code 9) but produced:
- ✅ `cycle4_all_triangles_contain_shared` - FULLY PROVEN
- ✅ `cycle4_element_contains_shared` - FULLY PROVEN
- ✅ `cycle4_no_loose_triangles` - FULLY PROVEN
- ✅ `triangles_containing_v_covered_by_spokes` - FULLY PROVEN
- ⚠️ `local_cover_le_2` - Partial (needs completion)
- ⚠️ `cycle4_cover_triangle_at_element` - 2 exact? statements

### Slot 74: Complete cycle_4 (IMMEDIATE NEXT SUBMISSION)
**File**: `submissions/nu4_final/slot74_cycle4_complete.lean`
**Strategy**: Resume from slot73, complete the remaining lemmas
**Content**:
1. Copy ALL proven lemmas from slot73
2. Complete `local_cover_le_2` - the 2-edge bound per vertex
3. Complete `cycle4_cover_triangle_at_element` - fill exact? statements
4. Final theorem: `cycle4_tau_le_8`

**Key insight for local_cover_le_2**:
```
At shared vertex v, triangles containing v that share edge with packing
form a structure where 2 edges suffice (use disjoint triples contradiction).
```

**Expected sorry**: 0

### Slot 75: path_4 Hybrid (AFTER cycle_4 complete)
**File**: `submissions/nu4_final/slot75_path4_hybrid.lean`
**Content**:
1. Import cycle_4 lemmas + slot69-72
2. Define path_4 with endpoint/middle distinction
3. Prove middles have All-Middle
4. Prove endpoints need base edges
5. Construct 8-edge cover (2 bases + 6 spokes)
6. Final theorem: path4_tuza_conjecture

### Slot 76: two_two_vw (AFTER path_4)
**File**: `submissions/nu4_final/slot76_two_two_vw.lean`
**Content**:
1. Show pairs are independent (no inter-bridges)
2. Apply S_e decomposition: 4 × 2 = 8
3. Or: Each pair has local τ ≤ 4 bound
4. Final theorem: two_two_vw_tuza_conjecture

---

## SUCCESS CRITERIA

| Case | Target | Verification |
|------|--------|--------------|
| cycle_4 | τ ≤ 8 with 0 sorry | Aristotle compiles clean |
| path_4 | τ ≤ 8 with 0 sorry | Aristotle compiles clean |
| two_two_vw | τ ≤ 8 with 0 sorry | Aristotle compiles clean |
| matching_2 | Same as two_two_vw | Trivial alias |

**Final Goal**: 7/7 cases proven → Tuza ν=4 COMPLETE

---

## RISK MITIGATION

### Risk 1: tau_containing_v_in_cycle4_le_2 might be false
**Mitigation**: Fall back to tau_containing_v_in_pair_le_4 (proven)
```
If τ(containing v) ≤ 4 for each of 4 vertices:
  τ ≤ 16 (too weak)

BUT: Triangles containing v_ab are ALSO containing v_bc, v_cd, or v_da
So we don't sum independently - use partition argument
```

### Risk 2: Spoke selection might be tricky
**Mitigation**: Don't construct explicit spokes
```
Instead prove: ∃ cover of size 2 for each containing(v)
Don't need to name the spokes explicitly
```

### Risk 3: Path_4 hybrid might have overlap issues
**Mitigation**: Use S_e decomposition as backup
```
S_A + S_B + S_C + S_D + bridges
2 + 2 + 2 + 2 + X_AB + X_BC + X_CD

X_AB, X_BC, X_CD ⊆ S covers (need to prove absorption)
```

---

## COMMANDS

```bash
# Submit cycle_4 All-Middle
./scripts/submit.sh submissions/nu4_final/slot73_cycle4_all_middle.lean cycle4_all_middle_v1

# Check status
./scripts/dashboard.sh

# Process result
./scripts/process_result.sh <UUID>

# Query database
sqlite3 submissions/tracking.db "SELECT * FROM submissions WHERE problem_id LIKE 'cycle4%' ORDER BY submitted_at DESC LIMIT 5;"
```

---

## METRICS

**North Star**: Complete all 7 cases
**Current**: 3/7 proven, 4 remaining
**Target**: 7/7 proven (100%)
**Active Aristotle Jobs**: slots 74, 74b, 75, 76 in queue
**Key blocker**: Need to prove τ(containing v at shared) ≤ 2 via disjoint triples

### Progress Update
```
✅ star_all_4     - PROVEN
✅ three_share_v  - PROVEN
✅ scattered      - PROVEN (tight bound)
⏳ cycle_4        - All-Middle PROVEN (slot73), need disjoint triples
⏳ path_4         - slot75 in queue
⏳ two_two_vw     - slot76 in queue
⏳ matching_2     - same as two_two_vw
```

---

## ACTIVE SUBMISSIONS (2025-12-25 20:30 UTC)

| Slot | UUID | File | Approach | Status |
|------|------|------|----------|--------|
| ~~68~~ | `8acce6b4` | ~~REMOVED~~ | ~~T_pair + avoiding=∅~~ | ❌ **FALSE LEMMA** |
| 74 | `795e4e81` | `slot74_cycle4_complete.lean` | All-Middle (from slot73) | ⏳ IN_PROGRESS |
| 74b | `e180b159` | `slot74b_cycle4_Se.lean` | S_e decomposition | 📋 QUEUED |
| 75 | `a7915801` | `slot75_path4_hybrid.lean` | Hybrid approach | 📋 QUEUED |
| 76 | `1004ad20` | `slot76_two_two_vw.lean` | S_e, no inter-bridges | 📋 QUEUED |

**Monitor with**: `python3 scripts/aristotle_queue.py --status`

**WARNING**: slot68 used FALSE lemma `avoiding_covered_by_spokes`. Removed from proven/.

---

## WHAT EACH SUBMISSION DOES

### slot74: cycle_4 All-Middle (PRIMARY)
```
Uses PROVEN theorem: cycle4_all_triangles_contain_shared
  → Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da

Remaining to prove:
  1. tau_containing_v_at_shared_le_2 (disjoint triples contradiction)
  2. Final assembly: τ ≤ 4 × 2 = 8
```

### slot74b: cycle_4 S_e Decomposition (ALTERNATIVE)
```
Uses S_e structure: S_e has common edge OR common apex
  → τ(S_e) ≤ 2 for each packing element
  → Diagonal bridges empty (A∩C = B∩D = ∅)
  → Total: 4 × 2 = 8
```

### slot75: path_4 Hybrid
```
Middles B, C: All-Middle applies (2 shared vertices each)
Endpoints A, D: Base edges for avoiding + spokes for containing
  → τ(containing v_ab) + τ(avoiding A) ≤ 4 + 2 = 6
  → Overlap exploitation to reduce to 8
```

### slot76: two_two_vw S_e Decomposition
```
Two independent pairs: (A—B) and (C—D)
  → No inter-pair bridges (A∩C = A∩D = B∩C = B∩D = ∅)
  → Each pair: τ(S_A) + τ(S_B) ≤ 2 + 2 = 4
  → Total: 4 + 4 = 8
```

---

## NEXT STEPS

1. **Wait for Aristotle results** (typically 2-8 hours per submission)
2. **Process completed results**: `./scripts/process_result.sh <UUID>`
3. **If any succeed**: Copy proven lemmas to consolidated file
4. **If all have sorry**: Analyze gaps, create refined submissions

**The gap is now TINY**:
- We have: Every triangle contains a shared vertex (PROVEN in slot73)
- We need: 2 edges per shared vertex cover triangles containing it
- Total: 4 × 2 = 8 edges ✓

---

## PROVEN LEMMA INVENTORY (Updated)

### ❌ REMOVED - slot68 (Used FALSE lemma)
| Lemma | Status |
|-------|--------|
| ~~`tau_le_8_cycle4`~~ | ❌ DEPENDS ON FALSE LEMMA |
| ~~`tau_pair_le_4`~~ | ❌ FALSE - correct bound is ≤6 |

### ✅ From slot73 (All-Middle - THE KEY)
| Lemma | Status |
|-------|--------|
| **`cycle4_all_triangles_contain_shared`** | ✅ **THE FOUNDATION** |
| `cycle4_element_contains_shared` | ✅ All-Middle for single element |
| `cycle4_no_loose_triangles` | ✅ Maximality for cycle_4 |
| `triangles_containing_v_covered_by_spokes` | ✅ Spoke coverage |
| `cycle4_triangle_at_vertex_supported` | ✅ Support lemma |
| `cycle4_intersection_pigeonhole` | ✅ Pigeonhole |
| `exists_three_disjoint_implies_contradiction_simplified` | ✅ Disjoint triples |

### ✅ From slot69-72 (Infrastructure)
| Lemma | Status |
|-------|--------|
| `tau_union_le_sum` | ✅ Subadditivity |
| `tau_containing_v_in_pair_le_4` | ✅ 4 spokes for containing |
| `tau_avoiding_v_in_pair_le_2` | ✅ 2 base edges for avoiding |
| `triangle_shares_edge_with_packing` | ✅ Maximality |
| `bridges_subset_tpair` | ✅ Bridge absorption |
| `S_e_structure` | ✅ Common edge OR apex |

---

*This map replaces all previous strategic documents. Follow this path.*
*Last updated: 2025-12-25 20:30 UTC - Cleaned up FALSE lemmas, correct approach documented*
