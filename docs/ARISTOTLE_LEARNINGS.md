# What We've Learned About Aristotle: 203 Submissions Analysis

**Date**: January 1, 2026
**Based on**: 203 Aristotle submissions over 19 days
**Note**: Aristotle is new technology - these learnings come from direct experience, not internet research.

---

## Key Insight: Scaffolding Is Everything

### The Data

| Scaffolding Level | Total Submissions | Zero-Sorry | Success Rate |
|-------------------|-------------------|------------|--------------|
| High (7+ proven) | 27 | 11 | **40.7%** |
| Medium (4-6 proven) | 39 | 14 | **35.9%** |
| Low (1-3 proven) | 30 | 4 | 13.3% |
| None (0 proven) | 5 | 0 | **0.0%** |

**Conclusion**: Never submit to Aristotle without at least 4 proven scaffolding lemmas. Ideal is 7+.

---

## What Works

### 1. Pattern: `safe_discard` - 6/6 Success Rate
Files with proven infrastructure that we're confident about. Example:
- `slot64a_ig_definitions_PROVEN.lean`
- `slot65_singleton_conflict_PROVEN.lean`

### 2. Files with 5-7 Proven Helper Lemmas
The "sweet spot" - enough scaffolding to guide Aristotle, not so much that it's just copying.

### 3. Breaking Big Goals into Small Pieces
- `tau_le_8` direct attempts: **0% success**
- `tau_le_12` (conservative): **100% success** (slot113, slot139)
- Infrastructure lemmas: **~30% success**

### 4. Proven Scaffolding from Previous Runs
Including FULL PROOF CODE (not sorry placeholders) from previous Aristotle outputs dramatically improves success.

---

## What Doesn't Work

### 1. Direct Main Theorem Attempts
Submissions targeting `tau_le_8` or `nu_star_eq_4` directly have **0% success rate**.

### 2. Zero Scaffolding
5 submissions with proven_count=0 had **0% success rate**.

### 3. Pattern: `boris_minimal`
Average 2.56 sorries per submission - too sparse for Aristotle to work with.

### 4. False Lemmas as Scaffolding
Including lemmas that are mathematically false wastes the entire submission.

---

## Aristotle-Specific Behaviors Observed

### 1. Aristotle Can Find Counterexamples
- `bridge_absorption` (Pattern 3): Aristotle found actual counterexample graph
- `krivelevich_bound_forall_w` (Pattern 10): Aristotle identified incorrect statement

**Implication**: If we're unsure about a lemma, submitting it might yield a counterexample.

### 2. Aristotle Respects Proof Structure
Files with clear `-- PROVEN SCAFFOLDING` sections do better than files where everything is mixed.

### 3. Aristotle Handles ~1 Non-Trivial Sorry Well
- 32 submissions with 1 sorry (near-misses)
- These often have high proven_count (avg 6.7)
- The sorry is usually on the KEY lemma we need

**Implication**: Design files with exactly 1 strategic sorry on the hard part.

### 4. Timeout/Budget Exhaustion
`slot_budget_exhausted_output.lean` proved 13 helper lemmas before running out of budget.
**Implication**: Aristotle has limited compute per submission. Front-load the hard stuff.

### 5. Processing Errors
Some submissions get "Aristotle encountered an error processing this file."
Often related to:
- Very large files
- Complex recursive definitions
- Certain Mathlib imports

---

## Optimal Submission Strategy (Based on Data)

### File Structure
```lean
/-
Clear description of EXACTLY what this file proves.
Target: ONE specific lemma with ONE sorry.
-/

import Mathlib

-- ═══════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (include FULL proofs, not sorry)
-- ═══════════════════════════════════════════════════════════════

-- Include 5-10 proven lemmas from previous successful submissions
-- Copy exact code from Aristotle outputs

-- ═══════════════════════════════════════════════════════════════
-- TARGET THEOREM (with 1 strategic sorry)
-- ═══════════════════════════════════════════════════════════════

theorem target_theorem : ... := by
  -- proof steps
  -- ONE sorry on the key insight needed
  sorry
```

### Pre-Submission Checklist
1. ✅ At least 5 proven scaffolding lemmas included
2. ✅ No known false lemmas (check against `false_lemmas` table)
3. ✅ Exactly 1 sorry on a well-defined gap
4. ✅ Clear structure with PROVEN vs TARGET sections
5. ✅ Not attempting main theorem directly

---

## Submission Pipeline Recommendations

### Pre-Validation (Before Aristotle)
1. **Syntax check**: Does it compile locally (ignore Mathlib version mismatches)?
2. **False lemma scan**: Grep for patterns from our 11 false lemmas
3. **Scaffolding count**: Require proven_count >= 5
4. **Sorry count**: Target exactly 1

### Parallel Slot Usage
- **Slots 1-5**: Near-misses (1-sorry files with high proven_count)
- **Slots 6-10**: Infrastructure lemmas (safe_discard pattern)
- **Slots 11-15**: Exploratory (new approaches with good scaffolding)

### Post-Aristotle Processing
1. **0 sorry**: Mark as PROVEN, add to scaffolding library
2. **1 sorry**: Analyze gap, queue variant or manual work
3. **2+ sorry**: Check for false lemmas, update failed_approaches

---

## Success Stories: What Actually Got Proven

| File | Proven Count | Key Achievement |
|------|--------------|-----------------|
| `slot_disjoint_partition` | 10 | cycle4_disjoint_partition PROVEN |
| `slot113_conservative_bound` | 7 | τ ≤ 12 PROVEN |
| `slot139_tau_le_12_fallback` | 7 | τ ≤ 12 alternative PROVEN |
| `slot70_d3159016` | 9 | Diagonal bridges infrastructure |
| `slot128_element_contains_shared` | 10 | Cycle4 pigeonhole |

**Pattern**: All successes have 7+ proven lemmas and target ONE specific result.

---

## Anti-Patterns to Avoid

### 1. The "Kitchen Sink" Submission
Including every lemma we think might help. Aristotle gets confused.

### 2. The "Wishful Thinking" Submission
Assuming a lemma is true without verification. Waste of a slot.

### 3. The "Copy-Paste Without Understanding"
Copying code without understanding it leads to inconsistent definitions.

### 4. The "One More Try" Loop
Resubmitting the same approach with minor changes. After 2 failures, the approach is probably wrong.

### 5. The "Main Theorem Direct" Attempt
Never works. Always decompose into infrastructure first.

---

## Recommendations for Agentic System

Based on these learnings, an autonomous system should:

1. **Enforce Scaffolding Minimum**: Reject files with < 5 proven lemmas
2. **Track Approach Hashes**: Prevent resubmitting failed approaches
3. **Prioritize Near-Misses**: 1-sorry files have highest marginal value
4. **Build Scaffolding Library**: Extract all proven theorems from successful runs
5. **Target One Sorry**: Each submission should have exactly 1 well-defined gap
6. **Avoid Main Theorem**: Never directly attempt τ ≤ 8; build up to it

---

## Metrics to Track

| Metric | Current | Target |
|--------|---------|--------|
| Success rate (0 sorry) | 29% | 50% |
| Near-miss rate (1 sorry) | 29% | 35% |
| Avg scaffolding in success | 7.1 | 7+ |
| Avg scaffolding in failure | 3.2 | N/A |
| False lemma submissions | 11+ | 0 |
| Slot utilization | 10/day | 15/day |
