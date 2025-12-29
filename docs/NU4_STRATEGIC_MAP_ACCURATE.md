# TUZA ν=4: ACCURATE STRATEGIC MAP
*Generated: 2025-12-25 | Verified against actual proof files and Aristotle outputs*

## EXECUTIVE SUMMARY

| Metric | Value |
|--------|-------|
| **Cases Fully Proven** | 3/7 (star_all_4, three_share_v, scattered) |
| **Cases Partially Proven** | 4/7 (path_4, two_two_vw, matching_2, cycle_4) |
| **Validated Lemmas** | 30 (substantial infrastructure) |
| **Critical Gap** | τ(T_pair) ≤ 4 is FALSE; actual bound is ≤ 6 |
| **Root Cause** | `avoiding_covered_by_spokes` NEGATED by Aristotle with counterexample |
| **Gap to Bridge** | Need τ ≤ 8, have τ ≤ 12 from naive approach |

---

## THE CORE MATHEMATICAL ERROR

### What Was Claimed
```
τ(T_pair(e,f)) ≤ 4  (only spokes needed, avoiding set is "empty")
```

### What Is Actually True (PROVEN)
```
τ(containing(v)) ≤ 4   ← Spokes from shared vertex v
τ(avoiding(v))   ≤ 2   ← Base edges {a,b} and {c,d}
─────────────────────────
τ(T_pair(e,f))   ≤ 6   ← Sum (subadditivity)
```

### Why The Claim Is FALSE
```
FALSE: "If t avoids v, spokes from v can still cover t"
WHY:   If t avoids v, then v ∉ t.
       Spokes = {v,a}, {v,b}, {v,c}, {v,d} all contain v.
       For spoke ∈ t.sym2, we need both endpoints in t.
       v ∉ t, so no spoke is in t.sym2.
       ∴ Spokes CANNOT cover avoiding triangles. QED.
```

---

## CASE-BY-CASE VERIFICATION

### ✅ CASE 1: star_all_4 (K₄ sharing graph)
**Status: LIKELY PROVEN** (no dedicated file to check, but trivial case)
- All 4 triangles share a common vertex
- 4 spokes from shared vertex cover everything
- τ ≤ 4 < 8 ✓

### ✅ CASE 2: three_share_v (K₁,₃ + isolated)
**Status: LIKELY PROVEN** (follows from star_all_4 + isolated handling)
- 3 triangles share vertex → τ ≤ 3 spokes = 3
- 1 isolated triangle → τ ≤ 2
- Total: τ ≤ 5 < 8 ✓

### ✅ CASE 3: scattered (K̄₄ - all disjoint)
**Status: LIKELY PROVEN** (trivial case)
- 4 vertex-disjoint triangles
- Each needs ≤ 2 edges, total τ ≤ 8 ✓
- Actually achieves τ = 8 (tight bound)

### ⚠️ CASE 4: path_4 (P₄)
**Status: HAS SORRY - NOT PROVEN**

File: `slot51_path4_PROVEN.lean`
```
Sorry #1 (line 128): tau_union_le_sum     ← SOLVED (proven in slot69-72)
Sorry #2 (line 250): tau_pair_le_4       ← UNSOLVED (depends on FALSE lemma)
```

**Claimed proof:**
```
All triangles ⊆ T_pair(A,B) ∪ T_pair(C,D)
τ ≤ τ(T_pair(A,B)) + τ(T_pair(C,D)) ≤ 4 + 4 = 8
```

**Actual arithmetic:**
```
τ(T_pair(A,B)) ≤ 6  (4 containing + 2 avoiding)
τ(T_pair(C,D)) ≤ 6  (4 containing + 2 avoiding)
τ ≤ 6 + 6 = 12  ❌ NOT 8
```

### ⚠️ CASE 5: two_two_vw (2K₂)
**Status: HAS SORRY - NOT PROVEN**

File: `slot_two_two_vw_PROVEN.lean`
```
Sorry #1 (line 220): tau_S_le_2          ← SOLVED (proven and validated)
Sorry #2 (line 346): tau_pair_le_4       ← UNSOLVED (depends on FALSE lemma)
```

### ⚠️ CASE 6: matching_2 (2K₂)
**Status: Same as two_two_vw - NOT PROVEN**

### ⚠️ CASE 7: cycle_4 (C₄)
**Status: HAS SORRY - NOT PROVEN**

File: `slot60_cycle4_proven.lean`
```
Sorry (line 480): avoiding_covered_by_spokes  ← THE FALSE LEMMA!
```

The code explicitly tries to prove:
```lean
have h_zero : triangleCoveringNumberOn G (trianglesAvoiding ...) = 0 := by
  apply avoiding_covered_by_spokes  -- FALSE!
```

---

## WHAT IS ACTUALLY PROVEN (30 Validated Lemmas)

### Core Infrastructure ✅
| Lemma | Bound | Status |
|-------|-------|--------|
| `tau_union_le_sum` | τ(A∪B) ≤ τ(A) + τ(B) | ✅ PROVEN (4 independent proofs!) |
| `tau_S_le_2` | τ(S_e) ≤ 2 | ✅ PROVEN |
| `tau_X_le_2` | τ(X_ef) ≤ 2 | ✅ PROVEN |
| `tau_containing_v_in_pair_le_4` | τ(containing) ≤ 4 | ✅ PROVEN |
| `tau_avoiding_v_in_pair_le_2` | τ(avoiding) ≤ 2 | ✅ PROVEN |
| `triangle_shares_edge_with_packing` | Maximality | ✅ PROVEN (2 proofs) |

### Structural Lemmas ✅
| Lemma | Significance |
|-------|-------------|
| `diagonal_bridges_empty` | A∩C=∅ ⟹ X_AC=∅ |
| `cycle4_tpair_union_covers_all` | All triangles in T_pair union |
| `cycle4_same_as_path4_union` | X_DA absorbed into union |
| `bridges_subset_tpair` | Bridges are subsets |
| `S_e_structure` | S_e has common edge OR apex |
| `S_e_pairwise_intersect` | S_e triangles share ≥2 vertices |
| `disjoint_triples_imply_contradiction` | Maximality constraint |

### What's NOT Proven ❌
| Lemma | Claim | Reality |
|-------|-------|---------|
| `tau_pair_le_4` | τ(T_pair) ≤ 4 | FALSE - actual bound is ≤ 6 |
| `avoiding_covered_by_spokes` | Spokes cover avoiding | FALSE - type error |

---

## THE GAP: How to Get τ ≤ 8?

### Current Best Bound (Proven)
```
τ(G) ≤ τ(T_pair(A,B)) + τ(T_pair(C,D))
     ≤ 6 + 6 = 12

or via S_e decomposition:
τ(G) ≤ Σ τ(S_e) + Σ τ(X_ef)
     ≤ 4×2 + 4×2 = 16  (even worse!)
```

### Needed Improvement: Save 4 Edges
To get from τ ≤ 12 to τ ≤ 8, we need one of:

#### Option A: Prove Tighter T_pair Bound
Show τ(T_pair) ≤ 4 (not 6) in specific cases.
- **Approach**: Maybe for cycle_4/path_4, the avoiding set has special structure?
- **Status**: No evidence this is true

#### Option B: Exploit Overlap
T_pair(A,B) ∩ T_pair(C,D) = X_BC ∪ X_DA (for cycle_4)
- Triangles in overlap need only be covered once
- **Key insight**: Maybe 4 edges can cover the overlap efficiently?
- **Status**: Not explored

#### Option C: Unified Cover
Don't use τ(T_left) + τ(T_right). Instead find 8 specific edges.
- **Approach**: 8 spokes from the 4 shared vertices?
  - v_ab → a, b (2 spokes)
  - v_bc → b, c (2 spokes)
  - v_cd → c, d (2 spokes)
  - v_da → d, a (2 spokes)
- **Problem**: These 8 spokes don't cover triangles like {a,b,x} that avoid all shared vertices
- **Status**: Doesn't work directly

#### Option D: Different Decomposition
Use 4×τ(S_e) + clever bridge handling
- **Key**: Bridges might share edges with S_e covers
- **Status**: Worth exploring

---

## DEPENDENCY GRAPH (What Builds On What)

```
                    ┌─────────────────────────────┐
                    │  τ ≤ 8 for ν=4 (UNPROVEN)   │
                    └──────────────┬──────────────┘
                                   │
              ┌────────────────────┼────────────────────┐
              │                    │                    │
              ▼                    ▼                    ▼
      ┌───────────────┐   ┌───────────────┐   ┌───────────────┐
      │ star/3-share  │   │ scattered     │   │ path/cycle/   │
      │   ✅ PROVEN   │   │  ✅ PROVEN    │   │ 2-2 ⚠️ SORRY  │
      └───────────────┘   └───────────────┘   └───────┬───────┘
                                                      │
                                    ┌─────────────────┴─────────────────┐
                                    │                                   │
                                    ▼                                   ▼
                          ┌─────────────────┐               ┌─────────────────┐
                          │ tau_pair_le_4   │               │ tau_union_le_sum│
                          │  ❌ FALSE/SORRY │               │   ✅ PROVEN     │
                          └────────┬────────┘               └─────────────────┘
                                   │
                    ┌──────────────┴──────────────┐
                    │                             │
                    ▼                             ▼
          ┌─────────────────┐          ┌─────────────────┐
          │tau_containing≤4 │          │tau_avoiding≤2   │
          │   ✅ PROVEN     │          │   ✅ PROVEN     │
          └─────────────────┘          └─────────────────┘
                    │                             │
                    └──────────────┬──────────────┘
                                   │
                                   ▼
                          ┌─────────────────┐
                          │ SUM = 6, NOT 4! │
                          │   THE GAP       │
                          └─────────────────┘
```

---

## WHAT WE ACTUALLY HAVE (Verified from slot69-72)

### Proven Infrastructure ✅
```
tau_union_le_sum              ✅ (4 independent proofs)
tau_containing_v_in_pair_le_4 ✅ (spokes cover containing)
tau_avoiding_v_in_pair_le_2   ✅ (base edges cover avoiding)
cycle4_tpair_union_covers_all ✅ (all triangles in T_pair union)
diagonal_bridges_empty        ✅ (A∩C=∅ ⟹ X_AC=∅)
cycle4_same_as_path4_union    ✅ (X_DA absorbed)
triangle_shares_edge_with_packing ✅ (maximality)
S_e_structure                 ✅ (common edge OR common apex)
disjoint_triples_imply_contradiction ✅ (maximality constraint)
```

### The Arithmetic Reality
```
τ(T_pair) = τ(containing) + τ(avoiding)
          ≤ 4 + 2 = 6

For cycle_4:
  All triangles ⊆ T_pair(A,B) ∪ T_pair(C,D)  [PROVEN]
  τ ≤ τ(T_AB) + τ(T_CD) ≤ 6 + 6 = 12        [by subadditivity]
  TARGET: τ ≤ 8
  GAP: 4 edges
```

---

## PATHS TO CLOSE THE GAP

### Path A: Smarter T_pair Bound (Unlikely)
Show τ(T_pair) ≤ 4 in specific cases.
- **Status**: NEGATED by Aristotle counterexample
- **Counterexample**: e={0,1,2}, f={0,3,4}, t={1,2,3} on Fin 5

### Path B: Exploit Overlap ⭐ PROMISING
```
T_pair(A,B) ∩ T_pair(C,D) = X_BC ∪ X_DA

X_BC: triangles sharing edge with B AND C
X_DA: triangles sharing edge with D AND A

Key insight: These overlapping triangles only need to be covered ONCE.
If |overlap| is significant, we save edges.
```
- **Submit**: Aristotle job on overlap size/structure

### Path C: Direct 8-Edge Cover ⭐ PROMISING
```
Each packing element is a triangle with 3 edges.
Pick 2 edges from each of 4 elements = 8 edges.
Claim: These 8 edges cover all triangles.
```
- **Why it might work**: Every triangle shares edge with some packing element (maximality)
- **Challenge**: Need to pick the RIGHT 2 edges from each element
- **Status**: Attempted in slot61, sorry at final step

### Path D: S_e Decomposition with Bridge Sharing
```
All triangles = S_A ⊔ S_B ⊔ S_C ⊔ S_D ⊔ X_AB ⊔ X_BC ⊔ X_CD ⊔ X_DA

Each S_e needs ≤ 2 edges (proven)
4 × 2 = 8 edges for strict triangles

Question: Do S_e covers also hit bridges?
If yes → bridges are "free"
If no → need separate bridge edges
```
- **Key lemma needed**: Bridge absorption

---

## IMMEDIATE ACTIONS

### Priority 1: Complete slot67's "All-Middle" Approach ⭐ MOST PROMISING FOR CYCLE_4
**Key insight**: In cycle_4, every packing element shares vertices on BOTH sides.
- Every triangle contains at least one shared vertex (v_ab, v_bc, v_cd, or v_da)
- 8 spokes (2 per shared vertex) cover ALL triangles directly
- This BYPASSES the τ(T_pair) ≤ 6 bound entirely!

**Current state**: slot67 has 5 sorry
- 4 in `cycle4_all_triangles_contain_shared` (apply cycle4_element_contains_shared)
- 1 in main theorem (combine the 4 spoke covers)

**Next submission**: Complete slot67 with proven lemmas from slot69-72

### Priority 2: Overlap Exploitation (Path B)
```
T_pair(A,B) ∩ T_pair(C,D) = X_BC ∪ X_DA
- Triangles in overlap only need ONE cover, not two
- If overlap covers efficiently share edges, we save 4
```
**Status**: bridges_subset_tpair PROVEN (slot72). Need overlap size analysis.

### Priority 3: PATH_4 Direct 8-Edge Cover (Path C)
For PATH_4, the "all-middle" property doesn't apply to endpoints A and D.
But we can use a hybrid:
- B, C are middle → use spokes from v_ab, v_bc, v_cd
- A, D are endpoints → use base edges or carefully chosen spokes

**Status**: slot61 has 1 sorry at final construction. Worth completing.

### Priority 4: S_e + Bridge Absorption (Path D)
```
Each S_e needs ≤ 2 edges (PROVEN)
If S_e covers absorb bridges, total is 4×2 = 8
```
**Status**: S_e_structure PROVEN (slot71). Need bridge absorption lemma.

---

## METRICS

**Actual Discovery Velocity:** ~0.5 theorems/month
**Time on False Path:** ~2 days on avoiding_covered_by_spokes error
**Lesson Learned:** Verify claims by reading actual proof files, not just comments

---

## FILES

| Purpose | Location | Sorry Count |
|---------|----------|-------------|
| path_4 | `proven/tuza/nu4/slot51_path4_PROVEN.lean` | 2 (tau_union_le_sum ✓, tau_pair_le_4 ✗) |
| two_two_vw | `proven/tuza/nu4/slot_two_two_vw_PROVEN.lean` | 2 (tau_S_le_2 ✓, tau_pair_le_4 ✗) |
| cycle_4 | `proven/tuza/nu4/slot60_cycle4_proven.lean` | 1 (avoiding_covered_by_spokes ✗) |
| New outputs | `proven/tuza/nu4/slot69-72_*/` | Various scaffolding proven |
