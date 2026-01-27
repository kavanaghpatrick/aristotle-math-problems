# Tuza ν=4 Multi-Agent Debate - Complete Synthesis

**Date**: January 27, 2026
**Participants**: Grok-4 (multiple perspectives), Claude (moderator)
**Rounds**: 4
**Outcome**: Consensus proof plan with concrete next steps

---

## Executive Summary

After 4 rounds of debate, we achieved consensus on a proof strategy for Tuza's conjecture (ν=4 → τ≤8):

**WINNING APPROACH**: Hybrid of B (5-packing bounds) + C (case analysis)

**KEY INSIGHT**: The PATH_4 gap (30 lemmas but main theorem sorry) is a "propagation" failure -
we proved endpoint coverage but not middle coverage.

**CONCRETE PLAN**: 5-step proof requiring ~5-7 core lemmas, completable in 1-2 weeks.

---

## Round-by-Round Summary

### Round 1: Initial Positions

| Agent | Approach | Key Argument |
|-------|----------|--------------|
| Grok (A) | B: 5-packing bounds | `three_bridges_imply_five_packing` lemma bounds bridges per element |
| Grok (B) | C: Pattern analysis | Leverages Aristotle's native_decide strength, proven for 6 patterns |

**Moderator synthesis**: Database shows slot452 (44 theorems) and slot453 (24 theorems) validate case analysis approach.

---

### Round 2: Case Enumeration

After eliminating impossible configurations (bridge + 2 externals → ν≥5), Grok enumerated 6 remaining cases:

| Case | Configuration | τ Bound | Status |
|------|---------------|---------|--------|
| 1 | Two disjoint bridges | ≤8 | slot452 covers |
| 2 | Two connected bridges (path of 3) | ≤6 | Needs proof |
| 3 | Three bridges in path (PATH_4) | ≤7 | **GAP** (slot262) |
| 4 | Three bridges in star | ≤6 | slot451 helps |
| 5 | Three bridges in triangle | ≤5 | Easy |
| 6 | Four bridges in cycle | ≤6 | slot450 covers |

**Critical finding**: `tau_S_union_X_le_2` is FALSE - tight bound is 3, not 2. But overlaps save edges globally.

---

### Round 3: PATH_4 Gap Analysis

**Why slot262 fails** (30 lemmas but main theorem sorry):
- Proves endpoint coverage (T_A ∪ T_D with ≤8 edges)
- Missing "propagation" to middle (S_B ∪ X_BC ∪ S_C)
- Individual bounds proven but composition not closed

**Proposed gap-closing lemma**:
```lean
lemma path4_middle_coverage (E' : set (edge G))
  (hE' : E'.finite ∧ E'.card ≤ 8 ∧ transversal E' (T_A ∪ T_D)) :
  (∃ E'' ⊆ E', transversal E'' (S_B ∪ X_BC ∪ S_C)) ∨
  (∃ packing5, packing5.card = 5 ∧ edge_disjoint packing5)
```

**Key insight**: Use slot451 (5-packing) for contradiction - if middle uncovered, extract bridge + 2 externals.

---

### Round 4: Final Recommendations

#### Q1: Is the lemma provable by Aristotle?

**YES**, with tactics:
- `induction` on PATH_4 structure
- `cases` on bridge intersections
- `by_contra` + `existsi` for 5-packing construction
- `native_decide` for finite instances

#### Q2: Should we use native_decide on Fin 10 first?

**ABSOLUTELY YES** - smoke test before generalizing:
```lean
def G : simple_graph (fin 10) := ... -- PATH_4
example : ∀ E', E'.card ≤ 8 → transversal E' (T_A ∪ T_D) → ... := by native_decide
```

#### Q3: Minimum lemma set for complete proof?

5-7 core lemmas:
1. **Base Case**: ν≤3 → τ≤6
2. **Path Propagation**: PATH_4 endpoint → middle coverage
3. **Cycle Closure**: CYCLE_4 opposite triangles → full coverage
4. **Star Lemma**: STAR_4 leaves → center coverage
5. **Maximality**: Every ν=4 packing is PATH/CYCLE/STAR/disjoint
6. **Reduction**: Minimal counterexample classification
7. (Optional) **5-packing extraction** from slot451

---

## Final 5-Step Proof Plan

### Step 1: Setup and Base Cases (1-2 days)
- Define types: `triangle`, `transversal`, `packing`
- Prove ν≤3 → τ≤6
- Verify ν=1 → τ=1 via `native_decide` on Fin 3
- **Milestone**: Base lemmas compile

### Step 2: Validate PATH_4 Computationally (2-3 days)
- Implement Fin 10 PATH_4 instance
- Use `native_decide` on proposed lemma
- If holds, generalize via induction on path length
- **Milestone**: `path4_middle_coverage` proven

### Step 3: Extend to Other Configurations (3-4 days)
- CYCLE_4 lemma (diagonal extraction)
- STAR_4 lemma (slot451 reuse)
- Test on Fin 12-15 instances
- **Milestone**: All config lemmas done

### Step 4: Maximality and Reduction (2 days)
- Prove every ν=4 packing classifies into PATH/CYCLE/STAR
- Assume minimal counterexample with τ>8
- Apply config lemmas → contradiction (5-packing exists)
- **Milestone**: Full proof skeleton compiles

### Step 5: Polish and Verify (1-2 days)
- Remove all `sorry`
- Run `lean --run` for verification
- Document with comments
- **Milestone**: Complete theorem `tuza_nu4 : ν G = 4 → τ G ≤ 8`

---

## Database Evidence Supporting Plan

| Slot | Proven | Relevance |
|------|--------|-----------|
| 451 | 39 | 5-packing contradiction (bridge + 2 externals) |
| 452 | 44 | Case 2a (bridge with ≤1 external) |
| 453 | 24 | Case 1 (no bridges) |
| 450 | 18 | τ≤8 for minimal PATH_4 on Fin 9 |
| 262 | 30 | PATH_4 lemmas (gap: middle coverage) |
| 370 | 13 | Triangle Helly for common vertex |

---

## Key False Lemmas to Avoid

| Lemma | Why False | Lesson |
|-------|-----------|--------|
| `at_most_two_edge_types` | Bridges use any edge-type | Don't assume min-index partition uses ≤2 types |
| `tau_S_union_X_le_2` | Base + bridges can be edge-disjoint | Tight bound is 3, not 2 |
| `Se_fan_apex` | Externals don't share common apex | Don't assume fan structure |
| `bridge_auto_covered_by_pigeonhole` | Covering vertex ≠ covering triangles | Need explicit bridge coordination |

---

## Recommended Aristotle Submissions

Based on debate consensus, submit these files to Aristotle:

### Priority 1: Close PATH_4 Gap
```
slot521_path4_middle_coverage.lean
- Target: path4_middle_coverage lemma
- Scaffolding: Import slot262 (30 lemmas) + slot451 (5-packing)
- Tactics: native_decide on Fin 10, then generalize
```

### Priority 2: Validate Cycle/Star Cases
```
slot522_cycle4_closure.lean
slot523_star4_coverage.lean
- Target: Cycle and star configuration lemmas
- Scaffolding: Import slot451 for 5-packing extraction
```

### Priority 3: Assembly Theorem
```
slot524_tuza_nu4_final.lean
- Target: Main theorem τ ≤ 8 when ν = 4
- Scaffolding: Import all config lemmas + maximality
```

---

## Conclusion

The 4-round debate achieved consensus on a **hybrid approach**:

1. **Use slot451** (5-packing) to eliminate impossible configurations
2. **Case analysis** on remaining 6 configurations (validated by slot452/453 success)
3. **Close PATH_4 gap** with propagation lemma + native_decide validation
4. **Assemble** via maximality argument

**Estimated completion**: 1-2 weeks with focused Aristotle submissions.

**Next action**: Submit `slot521_path4_middle_coverage.lean` targeting the propagation lemma.

---

*Debate synthesis generated January 27, 2026*
*Participants: Grok-4, Claude (moderator)*
