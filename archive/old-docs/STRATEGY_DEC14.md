# Math Project Strategy - December 14, 2025

## Executive Summary

Based on analysis of all outputs, we have **3 iterations queued** and **5 additional near-wins** ready for iteration.

---

## TIER 1: Currently Queued (Waiting for Results)

| Problem | Project ID | Holes Fixed | Expected Success |
|---------|------------|-------------|------------------|
| **#593** | 9e9244e6 | 1 → `IncidenceGraph_Bipartite H` | 85% |
| **Tuza** | 7e0ed119 | 2 → `k4_is_maximal_if_nu_1`, `packing_one_implies_intersect` | 80% |
| **#152** | 65238707 | 2 → `sum_gaps_eq_max_sub_min`, Cauchy-Schwarz | 75% |

---

## TIER 2: High Priority Near-Wins (1-2 holes)

### 1. Erdős #153 v4 - Sidon Set Squared Gaps
**Status**: 1 exact? hole
**File**: `submissions/erdos153_v4_OUTPUT.lean`
**Strategy**: Single hole fill - likely `card_sumset_sidon` or related lemma
**Expected Success**: 90%
**Priority**: HIGHEST - closest to completion

### 2. Erdős #23 Combined
**Status**: 2 exact? holes
**File**: `submissions/erdos23_combined_v2_OUTPUT.lean`
**Holes at**: Andrasfai-Kruskal-Szemerédi theorem, C5Colorable_bound
**Strategy**: Fill `exact?` with structural lemmas already in file
**Expected Success**: 70%

---

## TIER 3: Medium Priority (3-4 holes)

### 3. Erdős #23 Option C
**Status**: 4 exact? holes
**File**: `submissions/erdos23_optionC_v2_OUTPUT.lean`
**Strategy**: Structural approach - more holes but cleaner architecture
**Expected Success**: 60%
**Note**: Combined approach (2 holes) is closer

---

## TIER 4: Needs Different Approach

### 4. Erdős #149 - Strong Chromatic Index
**Status**: 6 exact? holes
**File**: `submissions/erdos149_v2_OUTPUT.lean`
**Analysis**: Good progress on Δ≤2 case, but too many holes
**Strategy Options**:
  - A) Fill all 6 holes individually (tedious)
  - B) Pivot to weaker statement (Δ≤1 case only)
  - C) Provide more lemmas upfront
**Expected Success**: 40% with current approach

### 5. Erdős #190 v2 - Van der Waerden
**Status**: 0 holes but INCOMPLETE
**File**: `submissions/erdos190_v2_OUTPUT.lean`
**Analysis**: Proved 8 useful lemmas but didn't prove main theorem H(k) ≥ ...
**Building blocks proven**:
  - `validN_subset_validW` (H(k) → W(k-1,k))
  - `countAPs_le`
  - `card_BadColorings_le`
  - `bad_card_bound`
  - `not_validW_of_lt_bound`
**Strategy**: Resubmit with explicit connection: these lemmas → main bound
**Expected Success**: 50%

### 6. Erdős #153 UNIVERSAL
**Status**: 0 holes but EXPLORATION DRIFT
**File**: `submissions/erdos153_UNIVERSAL_OUTPUT.lean`
**Analysis**: Built Singer set infrastructure, proved `constr_is_sidon_proven`, but never proved the universal statement
**Strategy**: Phase 5.3 - stricter lock, demand proof of `erdos_153_universal_statement`
**Expected Success**: 30% (hard problem)

---

## Priority Order for Next Actions

```
1. WAIT for queued results (#593, Tuza, #152)
2. IF any fail → iterate on them first
3. THEN attack Erdős #153 v4 (only 1 hole!)
4. THEN attack Erdős #23 Combined (2 holes)
5. THEN consider #190 with lemma connection
6. LAST: #149 (needs rethink) and #153 UNIVERSAL (needs strict lock)
```

---

## Pattern Recognition from December Attempts

### What Works
1. **Building block approach**: Proving helper lemmas first, then main theorem
2. **Explicit hole locations**: Telling Aristotle exactly where to fill
3. **Grok review before submit**: Catches wrong lemma applications
4. **1-3 holes max**: More than 3 holes usually means wrong approach

### What Doesn't Work
1. **Exploration**: Aristotle builds infrastructure but forgets main goal
2. **Universal statements**: AI tends to prove existential instead
3. **Too many tactics**: `grind`, `aesop`, `nlinarith` work; complex combos fail
4. **Asymptotic problems**: "for large enough n" is hard to formalize

### Red Flags in Outputs
- "Unable to complete in time" + 0 holes = exploration drift
- Proved `∃` when asked for `∀` = quantifier flip
- Added hypotheses not in original = hypothesis restriction
- Many `#check` and `#eval` = computational exploration, not proof

---

## Recommended Iteration Template

```
Complete this proof. Fill the hole(s) at line(s) [X, Y].

The answer is likely one of these lemmas already defined:
- [lemma_name_1]
- [lemma_name_2]

Constraints:
- Do NOT modify theorem statements
- Do NOT add new hypotheses
- Do NOT explore - just fill holes
- Use: simp, rw, exact, linarith, aesop

[PASTE FULL OUTPUT]
```

---

## Success Metrics

| Metric | Target | Current |
|--------|--------|---------|
| Problems with 0 holes | 3+ | 0 (waiting on 3) |
| Hole reduction rate | 50%/iter | TBD |
| Iterations to success | ≤3 | TBD |

---

## Files Reference

```
submissions/erdos153_v4_OUTPUT.lean     # 1 hole - HIGHEST PRIORITY
submissions/erdos23_combined_v2_OUTPUT.lean  # 2 holes
submissions/erdos23_optionC_v2_OUTPUT.lean   # 4 holes
submissions/erdos149_v2_OUTPUT.lean     # 6 holes
submissions/erdos190_v2_OUTPUT.lean     # 0 holes, incomplete
submissions/erdos153_UNIVERSAL_OUTPUT.lean   # exploration drift
```
