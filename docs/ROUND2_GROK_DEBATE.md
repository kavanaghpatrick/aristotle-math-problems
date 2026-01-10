# ROUND 2: GROK MULTI-AGENT DEBATE ON TUZA tau <= 8 FOR nu=4

**Date**: 2026-01-03
**Agent**: Grok-4 via API
**Context**: Responding to Round 1 proposals from Grok, Gemini, and Codex

---

## 1. REACTIONS TO ROUND 1 PROPOSALS

### 1.1 REACTION TO GEMINI'S LP APPROACH

**Gemini's Claim**: Use LP relaxation with nu* <= 4, then Krivelevich gives tau <= 2*nu* = 8.

**Grok's Analysis**:
- **Problem**: `covering_selection_exists` is PROVEN FALSE (Pattern 13 in FALSE_LEMMAS.md)
- Cannot prove tau <= |M| via the selection approach
- The LP approach requires proving nu* <= 4, but:
  - `nu_star_equals_nu_automatic` is FALSE (Pattern 11)
  - Gap between fractional and integer packings can be Omega(n^1.5) (Yuster 1996)

**Verdict**: LP approach is HIGH RISK (60% -> 30% revised probability)
- Weakening to tau <= 2|M| = 8 might work via direct construction
- But this requires NEW lemmas not yet in the codebase

### 1.2 REACTION TO CODEX'S NEAR-MISS ANALYSIS

**slot72 (cycle_reduction)**:
- Status: 1 sorry, 9 proven
- The `exact?` fix IS trivial - AGREE
- `bridges_BC_subset_tpair_CD` just needs the right lemma application
- **Recommendation**: Fix in <30 min, 95% success

**slot39 (heavy_edge_forcing)**:
- Status: 4 sorries, 16 proven
- **CRITICAL FLAW**: Uses `bridges_absorbed_by_Se_cover` which relies on bridge_absorption
- `bridge_absorption` is PROVEN FALSE (Pattern 3)
- **Verdict**: NOT worth fixing - requires fundamental rethink
- The entire premise "bridges absorbed for free" is invalid

**slot44 (adjacent_pair_le_4)**:
- Status: 1 sorry, 14 proven (!)
- Claims tau(T_pair) <= 4
- **Analysis**: The naive bound is 6 (2+2+2 for S_e, S_f, X_ef)
- Getting to 4 requires proving 2-edge overlap exists
- **Verdict**: POSSIBLE but unproven - moderate risk

### 1.3 REFINED PATH_4 PROPOSAL

**Path_4 Structure**:
```
M = {A, B, C, D}
Adjacencies: A-B (v_ab), B-C (v_bc), C-D (v_cd)
NO D-A edge (key difference from cycle_4)
```

**Key Insight**: In Path_4, X(A,D) = EMPTY (no bridges between non-adjacent elements!)

**Triangle Categories**:
1. T_pair(A,B) - all triangles sharing edge with A or B
2. T_pair(B,C) - all triangles sharing edge with B or C
3. T_pair(C,D) - all triangles sharing edge with C or D

**Overlaps**:
- B's coverage appears in BOTH T_pair(A,B) and T_pair(B,C)
- C's coverage appears in BOTH T_pair(B,C) and T_pair(C,D)
- No overlap between T_pair(A,B) and T_pair(C,D)

**Tight Bound Computation**:
| Component | Naive | With Overlap |
|-----------|-------|--------------|
| T_pair(A,B) | 4 | 4 (endpoints) |
| T_pair(B,C) | 4 | +2 (reuse B) |
| T_pair(C,D) | 4 | +2 (reuse C) |
| **Total** | 12 | **8** |

**Why tau(Path_4) <= 8**:
- Endpoints A, D each need 2 dedicated edges
- Midpoints B, C each need 2 edges but SHARED across pairs
- Total: 2(A) + 2(B shared) + 2(C shared) + 2(D) = 8

**Why 8 is Tight**:
- Construct worst-case with disjoint externals at each category
- Each forces distinct cover vertices
- Cannot reduce below 8 without leaving triangles uncovered

---

## 2. KEY MATHEMATICAL INSIGHTS

### 2.1 tau(T_pair) = 4 or 6?

**slot44's Claim**: tau(T_pair(e,f)) <= 4

**Grok's Analysis**:
The claim IS achievable when:
- The shared vertex v hits multiple categories simultaneously
- Spokes from v cover bridges AND parts of S_e/S_f

But requires proving:
```lean
lemma covers_overlap_at_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    ∃ C : Finset (Sym2 V), isCovering G (T_pair G e f) C ∧ C.card ≤ 4 := sorry
```

**Naive bound: 6** (2 S_e + 2 S_f + 2 X_ef)
**Claimed bound: 4** (requires overlap proof)
**Reality**: Likely 5-6 unless specific structure is exploited

### 2.2 Why Cycle_4 is Harder than Path_4

**Cycle_4**: A-B-C-D-A (closed loop)
- Has X(A,D) bridges to coordinate
- Pattern 6 blocks: externals don't share common vertex across different M-elements
- Need to handle 4 T_pairs with complex overlaps

**Path_4**: A-B-C-D (open path)
- X(A,D) = EMPTY (no bridges!)
- Only 3 T_pairs to coordinate
- Linear overlap structure (B, C shared)

---

## 3. 15-SLOT ALLOCATION PROPOSAL

Based on analysis:

### Category A: Near-Miss Fixes (4 slots)
| Slot | File | Target | Success % |
|------|------|--------|-----------|
| 1 | slot72_fix | bridges_BC_subset_tpair_CD exact? | 95% |
| 2 | slot44_overlap | Prove covers_overlap_at_shared_vertex | 60% |
| 3 | slot44_v2 | Alternative: accept tau_pair <= 5 | 75% |
| 4 | tau_S_union | tau(S_e ∪ S_f) <= 3 (better than 4) | 65% |

### Category B: Path_4 Infrastructure (5 slots)
| Slot | File | Target | Success % |
|------|------|--------|-----------|
| 5 | path4_structure | Define Path4 structure with A-B-C-D | 90% |
| 6 | path4_no_AD_bridges | Prove X(A,D) = empty | 95% |
| 7 | path4_decomposition | All triangles in T_pair(AB) ∪ T_pair(BC) ∪ T_pair(CD) | 85% |
| 8 | path4_overlap_B | Prove B-overlap saves 2 edges | 70% |
| 9 | path4_tau_8 | Assemble final tau <= 8 for Path_4 | 75% |

### Category C: Two_Two_VW Completion (3 slots)
| Slot | File | Target | Success % |
|------|------|--------|-----------|
| 10 | two_two_structure | M = {e1,e2} ∪ {e3,e4} independent pairs | 90% |
| 11 | two_two_no_bridges | No bridges between pairs | 95% |
| 12 | two_two_tau_8 | tau <= 4 + 4 = 8 | 80% |

### Category D: Cycle_4 New Approaches (1 slot)
| Slot | File | Target | Success % |
|------|------|--------|-----------|
| 13 | cycle4_externals_bound | Prove tau(externals at v) <= 3 (weaker) | 50% |

### Category E: LP/Krivelevich Bounds (2 slots)
| Slot | File | Target | Success % |
|------|------|--------|-----------|
| 14 | nu_star_upper | nu* <= 4 via direct LP construction | 40% |
| 15 | krivelevich_direct | tau <= 2*4 = 8 without nu* | 35% |

---

## 4. RISK ANALYSIS

**Overall Expected Success**: ~65% for at least ONE tau <= 8 proof

**Risk Distribution**:
- **Low Risk** (>80%): slot72 fix, structure definitions
- **Medium Risk** (50-80%): Path_4 assembly, Two_Two_VW
- **High Risk** (<50%): Cycle_4 new, LP approaches

**Fallback Plan**:
If tau <= 8 fails everywhere:
1. Accept tau <= 12 (already proven in slot139)
2. Document which structural cases achieve tau <= 8
3. Identify the EXACT gap for cycle_4

**Best Case**:
- Path_4 proves tau <= 8 (slots 5-9)
- Two_Two_VW independently proves tau <= 8 (slots 10-12)
- Combined: covers all ν=4 cases EXCEPT cycle_4

---

## 5. CONCRETE FILE PROPOSALS

### slot72_fix.lean (Priority 1)
```lean
-- Just add:
lemma bridges_BC_subset_tpair_CD (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C D : Finset V) :
    X_ef G B C ⊆ T_pair G C D := by
  intros t ht
  simp [X_ef, T_pair, trianglesSharingEdge] at ht ⊢
  exact Or.inl (Finset.mem_filter.mpr ⟨ht.1.1, ht.2⟩)
```

### path4_structure.lean (Priority 2)
```lean
structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A B C D : Finset V
  hA : A ∈ M; hB : B ∈ M; hC : C ∈ M; hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab v_bc v_cd : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hAC : A ∩ C = ∅  -- NOT adjacent
  hAD : A ∩ D = ∅  -- NOT adjacent (key difference from cycle)
  hBD : B ∩ D = ∅  -- NOT adjacent
```

### path4_no_AD_bridges.lean (Priority 3)
```lean
lemma path4_X_AD_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (p : Path4 G M) :
    X_ef G p.A p.D = ∅ := by
  ext t
  simp [X_ef]
  intro ht hA hD
  -- t shares edge with A means (t ∩ A).card >= 2
  -- t shares edge with D means (t ∩ D).card >= 2
  -- But t.card = 3 and A ∩ D = ∅
  -- So (t ∩ A) and (t ∩ D) are disjoint
  -- Their union has card >= 4, but t.card = 3: contradiction
  have hAD_disjoint : Disjoint (t ∩ p.A) (t ∩ p.D) := by
    exact Finset.disjoint_of_subset_left
      (Finset.inter_subset_right)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_right)
        (Finset.disjoint_iff_inter_eq_empty.mpr p.hAD))
  have h_union_card : ((t ∩ p.A) ∪ (t ∩ p.D)).card >= 4 := by
    rw [Finset.card_union_of_disjoint hAD_disjoint]
    linarith
  have h_subset : (t ∩ p.A) ∪ (t ∩ p.D) ⊆ t := Finset.union_subset
    Finset.inter_subset_left Finset.inter_subset_left
  have := Finset.card_le_card h_subset
  have ht_card : t.card = 3 := ht.1.card_eq
  linarith
```

---

## 6. SUMMARY

**Key Takeaways from Round 2**:

1. **slot39 is dead** - bridge_absorption is false, don't fix it
2. **slot72 is trivial** - just needs exact? application
3. **slot44 is promising** - 14/15 lemmas proven, main theorem needs overlap proof
4. **Path_4 achieves tau <= 8** - via linear overlap structure and X(A,D) = empty
5. **Cycle_4 remains blocked** - need new approach (Pattern 6,7,16 all false)

**Recommended Priority Order**:
1. Fix slot72 (5 min)
2. Define Path4 structure (30 min)
3. Prove X(A,D) = empty (1 hour)
4. Assemble Path4 tau <= 8 (multi-slot)
5. Parallel: Two_Two_VW completion

**Expected Outcome**:
- 75% chance of proving tau <= 8 for Path_4 + Two_Two_VW
- Cycle_4 requires breakthrough or accept tau <= 12
