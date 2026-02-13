# Tuza ν=4: Complete Context for Next Debate
## February 4, 2026 (End of Day Summary)

---

## EXECUTIVE SUMMARY

Today was a **major breakthrough day**:

1. **Propeller Counterexample INVALIDATED** - The claimed counterexample to `tau_le_8_scattered` was based on wrong ν calculation
2. **scattered GENERAL THEOREM PROVEN** - `tau_le_8` now proven for ANY scattered graph with ν=4
3. **4 new submissions, all 0 sorry** - slots 54, 55, 56, 57 all proven

---

## CURRENT CASE STATUS

| Case | Phase 1 | Phase 2 | General | Status |
|------|---------|---------|---------|--------|
| star_all_4 | ✅ τ=4 | ✅ | ✅ | **COMPLETE** |
| three_share_v | ✅ τ≤4 | ✅ | ✅ | **COMPLETE** |
| path_4 | ✅ τ≤4 | ✅ | ✅ (107 thms) | **COMPLETE** |
| **scattered** | ✅ τ≤4 | ✅ τ≤4 | ✅ **τ≤8** | **COMPLETE** (today!) |
| two_two_vw | ✅ τ≤4 | ✅ τ≤8 | ❓ | Specific construction only |
| matching_2 | ✅ τ≤4 | ❓ | ❓ | Same as two_two_vw |
| cycle_4 | ✅ τ≤4 | 🔴 | 🔴 | **BLOCKED** - 4 false lemmas |

**Progress: 4/7 COMPLETE, 2 partial, 1 blocked**

---

## TODAY'S ACHIEVEMENTS

### 1. Propeller Discovery (CRITICAL)

The documentation claimed a "Propeller counterexample" disproved `tau_le_8_scattered`:

```
CLAIMED (WRONG):
- 4 Propellers with ν = 4 (centrals)
- τ = 12
- τ > 2ν = 8, violates Tuza

ACTUAL (PROVEN in slot57):
- Single Propeller has ν = 3 (petals are edge-disjoint!)
- 4 Propellers have ν = 12
- τ = 12 ≤ 2×12 = 24 ✓ Tuza SATISFIED
```

**Key theorem**: `nu_propeller_eq_3` - petals form maximum packing

### 2. Scattered General Theorem (slot56)

```lean
theorem scattered_tau_le_8 :
    ∀ G M, isMaxPacking G M → M.card = 4 → isScattered M →
    ∃ E, E.card ≤ 8 ∧ covers_all_triangles E
```

**Proof strategy**:
- Each M-element A has triangles T_A (sharing edge with A)
- Since M-elements vertex-disjoint, T_A sets are disjoint
- τ(T_A) ≤ 2 for each (by maximality argument)
- Total: τ ≤ 4 × 2 = 8

### 3. Specific Construction Proofs

| Slot | Case | Vertices | Triangles | τ |
|------|------|----------|-----------|---|
| 54 | scattered | Fin 15 | 7 (4M + 3 ext) | ≤ 4 |
| 55 | two_two_vw | Fin 14 | 8 (4M + 4 ext) | ≤ 8 |

---

## REMAINING WORK

### Priority 1: two_two_vw General Theorem

**Current status**: Specific construction proven (slot55), need general theorem

**Strategy**: Similar to scattered
- Two pairs {A,B} and {C,D} are vertex-disjoint
- No inter-pair bridges possible
- τ_pair(A,B) ≤ 4, τ_pair(C,D) ≤ 4
- Total: τ ≤ 8

**Blocker**: Need to prove `no_inter_pair_bridges` generally

### Priority 2: matching_2

**Current status**: Partial, assumed same as two_two_vw

**Open question**: Is matching_2 formally isomorphic to two_two_vw?
- Both have two vertex-disjoint pairs
- Should follow identical proof

### Priority 3: cycle_4 (BLOCKED)

**Status**: 4 false lemmas, 10 failed approaches

**False lemmas blocking cycle_4**:
| Lemma | Why False |
|-------|-----------|
| `link_graph_bipartite` | M-neighbors form odd cycles |
| `external_share_common_vertex` | Externals don't share apex |
| `support_sunflower_tau_2` | 2 edges at shared vertex insufficient |
| `krivelevich_bound_forall_w` | LP uses supremum, not any w |

**Failed approaches**:
1. cycle_opposite_disjoint - Opposite pairs share vertices
2. König theorem - Link graphs not bipartite
3. LP relaxation - Machinery too complex
4. Constructive cover - Blocked by bipartiteness
5. (6 more documented in database)

**Possible new approaches**:
- Finite model verification on Fin 10-12
- Decomposition into two path_4 subproblems
- Direct enumeration with symmetry

---

## DATABASE STATISTICS

### Submissions
| Status | Count |
|--------|-------|
| completed | 251 |
| proven | 109 |
| near_miss | 62 |
| failed | 37 |
| pending | 5 |

### False Lemmas (39 total)
| Evidence Level | Count |
|----------------|-------|
| aristotle_verified | 23 |
| ai_verified | 11 |
| reasoning_based | 3 |
| trivially_false | 2 |

### Validated True Lemmas (Key ones)
| Lemma | Statement |
|-------|-----------|
| `tau_S_le_2` | τ(S_e) ≤ 2 for exclusive externals |
| `tau_X_le_2` | τ(X_{e,f}) ≤ 2 for bridges |
| `avoiding_contains_base_edge` | Avoiding triangles share base edge |
| `Se_disjoint` | S_e sets are pairwise disjoint |
| `bridges_subset_tpair` | Bridges absorbed by T_pair |

---

## KEY FILES

### Proven Today
| File | Status | Key Theorem |
|------|--------|-------------|
| `slot54_scattered_phase2_aristotle.lean` | 0 sorry | `scattered_phase2_tau_le_4` |
| `slot55_two_two_vw_phase2_aristotle.lean` | 0 sorry | `two_two_vw_phase2_tau_le_8` |
| `slot56_scattered_general_aristotle.lean` | 0 sorry | `scattered_tau_le_8` (GENERAL!) |
| `slot57_propeller_nu_verify_aristotle.lean` | 0 sorry | `nu_propeller_eq_3` |

### Reference Files
| Purpose | File |
|---------|------|
| star_all_4 proof | `slot49_star_all_4_clean_aristotle.lean` |
| three_share_v proof | `slot50_three_share_v_clean_aristotle.lean` |
| path_4 assembly | `slot451-453*.lean` |
| Tracking database | `submissions/tracking.db` |

---

## QUESTIONS FOR NEXT DEBATE

### Strategic
1. Should we attempt two_two_vw general theorem next?
2. Is matching_2 worth separate treatment or just alias two_two_vw?
3. Should we abandon cycle_4 and accept 6/7 cases?

### Technical
4. Can the scattered general proof strategy apply to two_two_vw?
5. Are there any other "counterexamples" in the docs that need verification?
6. What's the minimum Fin n for cycle_4 finite verification?

### Meta
7. Should we publish partial results (6/7 cases)?
8. What's blocking the final assembly theorem?

---

## DEBATE PARTICIPANTS CONTEXT

### What Grok Should Focus On
- Code correctness, Lean syntax issues
- Concrete next file to create
- Specific theorem statements

### What Gemini Should Focus On
- Literature connections
- Proof strategy validation
- Counterexample hunting

### What Contrarian Should Challenge
- Are general theorems truly general?
- Hidden assumptions in proofs
- Edge cases not considered

---

## SUCCESS METRICS

**ν=4 is DONE when**:
1. All 7 cases have τ ≤ 8 proven (currently 4/7)
2. General theorem: `∀ G, ν(G) = 4 → τ(G) ≤ 8`
3. No regressions in proven cases
4. Assembly theorem compiles with 0 sorry

**Current blockers**:
- two_two_vw: Need general theorem (not just Fin 14)
- matching_2: Need to formalize equivalence
- cycle_4: 4 false lemmas, need new approach

---

*Document prepared February 4, 2026 after multi-agent debate and 4 successful Aristotle submissions*
