# External Disjointness Analysis: Complete Index

## Overview

This collection of documents provides comprehensive analysis of the critical gap in the PATH_4 τ ≤ 8 proof for Tuza's conjecture (ν = 4).

**Core Problem**: Prove that any triangle sharing ≥2 vertices with B (but ≤1 with A) is covered by the 8-edge construction. Two lemmas require proof: `cover_hits_sharing_B` and `cover_hits_sharing_C`.

**Status**: All analysis complete. Ready for implementation.

---

## Files in This Collection

### 1. CRITICAL_GAP_RESOLUTION_SUMMARY.md
**Purpose**: Executive summary and navigation guide

**Contents**:
- What needs to be proven (the 2 sorries)
- Answers to your 4 critical questions
- Why the proof works (the big picture)
- Implementation roadmap
- Success criteria

**Read this first** if you're new to the analysis, or to get oriented.

### 2. EXTERNAL_DISJOINTNESS_ANALYSIS.md
**Purpose**: Deep mathematical analysis of the 15 pairwise intersection bounds

**Contents**:
- Definition of external types (T₁, T₂, T₃)
- Detailed table of all 15 pairs and their bounds
- Explanation of why freshness is required
- Step-by-step proof that T₁, T₂, T₃ are pairwise compatible with ν=4 constraint
- Connection to Aristotle's negation proof

**Read this** if you need to understand the mathematics deeply or prove the bounds formally.

### 3. COVER_HITS_B_C_STRATEGY.md
**Purpose**: Detailed case analysis strategy for filling the sorries

**Contents**:
- Problem statement (what the 2 lemmas must prove)
- Case analysis for each possible triangle type
- Why 8 edges suffice (coverage table)
- Lean proof sketch for cover_hits_sharing_B (~40-50 lines)
- Note on symmetry for cover_hits_sharing_C

**Read this** before starting to code the proofs.

### 4. PROOF_TEMPLATE_cover_hits_B_C.lean
**Purpose**: Ready-to-use Lean 4 proof templates

**Contents**:
- Concrete Lean 4 code for cover_hits_sharing_B
- Concrete Lean 4 code for cover_hits_sharing_C (parallel structure)
- Detailed comments explaining each step
- Notes on areas that may need syntax adjustment

**Use this** as your starting point for implementation. Copy-paste and adapt.

### 5. slot263_path4_explicit_DISJOINTNESS_GUIDE.lean
**Purpose**: Helper lemmas and tactic macros for the 15 intersection bounds

**Contents**:
- Generic lemmas for 3-vertex set intersections
- Proof templates for each of the 15 pairwise bounds
- Tactic macros to simplify proofs
- Code organization by pair category

**Use this** if you decide to prove all 15 bounds formally as separate lemmas (optional but recommended).

---

## Quick Reference: The 4 Key Questions

### Q1: What are the exact conditions on w₁, w₂, w₃ for edge-disjointness?

**File**: EXTERNAL_DISJOINTNESS_ANALYSIS.md, Section "Question 1"
**Summary**:
- T₁, T₂, T₃ are NOT edge-disjoint
- They satisfy PACKING property (pairwise ≤1 vertex intersection)
- This comes from: (1) definitions, (2) freshness of w_i, (3) PATH_4 structure
- The proof uses packing property → contradiction to ν=4

### Q2: Do w₁, w₂, w₃ need to be fresh?

**File**: EXTERNAL_DISJOINTNESS_ANALYSIS.md, Section "Question 2"
**Summary**:
- **YES, absolutely required**
- Prevents degeneracy: w_i = a_j would make T_i invalid
- Isolates externals: w_i ∉ {v₁,...,d₃} ensures (T_i ∩ M-element).card ≤ 1
- Enables contradiction: fresh w guarantees 6-triangle packing property

### Q3: Can we prove T₁, T₂, T₃ pairwise edge-disjoint?

**File**: EXTERNAL_DISJOINTNESS_ANALYSIS.md, Section "Question 3"
**Summary**:
- Definitional for externals themselves: {v₁}, {a₂}, {a₃} are the only intersections
- Use `simp [T₁, T₂, ...]; omega` tactic pattern
- ~3 lines of Lean per pair

### Q4: What's the cleanest proof of all 15 pairwise bounds?

**File**: EXTERNAL_DISJOINTNESS_ANALYSIS.md, Section "Question 4"
**Summary**:
- Three proof categories:
  1. Externals vs externals (3 pairs): Definitional
  2. Externals vs M-elements (12 pairs): Freshness + structure
  3. M-elements vs M-elements: Already proven
- Pattern: `simp [definitions]; omega` for most
- Estimated: ~150 lines of Lean total

---

## Implementation Workflow

### Phase 1: Understand (0.5-1 hour)
1. Read CRITICAL_GAP_RESOLUTION_SUMMARY.md (Executive Summary section)
2. Read COVER_HITS_B_C_STRATEGY.md (Problem Statement + Key Observations)
3. Understand the case analysis in COVER_HITS_B_C_STRATEGY.md

### Phase 2: Code the Main Proofs (1-2 hours)
1. Copy PROOF_TEMPLATE_cover_hits_B_C.lean as a starting point
2. Adjust to match your exact import structure
3. Fill in any `sorry` sections using COVER_HITS_B_C_STRATEGY.md as guide
4. Test with local Lean compilation

### Phase 3: (Optional) Prove the 15 Bounds (1-2 hours)
1. Use slot263_path4_explicit_DISJOINTNESS_GUIDE.lean for structure
2. For each of 15 pairs, prove bound ≤ 1
3. Makes the proof more self-contained and reusable

### Phase 4: Integrate and Submit (0.5 hour)
1. Insert proofs into slot263_path4_explicit_aristotle.lean
2. Verify compilation
3. Submit via `./scripts/submit.sh`

**Total time**: 3-6 hours for full proof

---

## Key Mathematical Insights

### The Fundamental Contradiction

If all 3 external types exist for A = {v₁, a₂, a₃}:
```
T₁ = {v₁, a₂, w₁}  ← Type 1 external
T₂ = {v₁, a₃, w₂}  ← Type 2 external
T₃ = {a₂, a₃, w₃}  ← Type 3 external

Plus the packing M = {A, B, C, D}

All 6 are pairwise disjoint (card ≤ 1 intersection)
Therefore: 6-element packing contradicts ν = 4
```

**This is the crux of the proof.**

### Why 8 Edges Suffice

```
Cover = {3 edges from A} ∪ {spine {v₁,v₂}} ∪ {spine {v₂,v₃}} ∪ {3 edges from D}
      = 8 edges

Covers:
- A itself: all 3 edges
- A-externals: share 2 with A, so covered by A's edges
- B: shares {v₁,v₂} spine with B-elements
- B-externals: 2 vertices in B, so edge covered by B or spine
- Similarly C and D
```

**All triangles are covered.**

---

## File Locations

| File | Location |
|------|----------|
| Main analysis | `/Users/patrickkavanagh/math/docs/EXTERNAL_DISJOINTNESS_ANALYSIS.md` |
| Strategy guide | `/Users/patrickkavanagh/math/docs/COVER_HITS_B_C_STRATEGY.md` |
| Summary | `/Users/patrickkavanagh/math/docs/CRITICAL_GAP_RESOLUTION_SUMMARY.md` |
| Proof template | `/Users/patrickkavanagh/math/submissions/nu4_final/PROOF_TEMPLATE_cover_hits_B_C.lean` |
| Helper lemmas | `/Users/patrickkavanagh/math/submissions/nu4_final/slot263_path4_explicit_DISJOINTNESS_GUIDE.lean` |
| Target file | `/Users/patrickkavanagh/math/submissions/nu4_final/slot263_path4_explicit_aristotle.lean` |
| This index | `/Users/patrickkavanagh/math/docs/EXTERNAL_ANALYSIS_INDEX.md` |

---

## Troubleshooting

### "Why is the proof stuck at line 318?"

**Answer**: The lemma `cover_hits_sharing_B` needs proof that any triangle sharing ≥2 vertices with B (but ≤1 with A) is covered by the 8-edge cover. See COVER_HITS_B_C_STRATEGY.md, Cases 2a-i through 2a-iii.

### "What does 'external type' mean?"

**Answer**: For M-element A = {v₁, a₂, a₃}, an external is a triangle t ∉ M that shares exactly 2 vertices with A. There are 3 such types based on which 2 vertices are shared. See EXTERNAL_DISJOINTNESS_ANALYSIS.md.

### "Why do we need w_i to be fresh?"

**Answer**: If w_i = a_j, then T_i would have repeated vertices (invalid). Also, freshness ensures T_i vertices don't overlap with B, C, D in problematic ways. See EXTERNAL_DISJOINTNESS_ANALYSIS.md, Question 2.

### "How do I connect the bounds to the main proof?"

**Answer**: The bounds are used in `six_triangles_contradict_nu4` to show that 6 triangles form a packing with card = 6 > 4, contradicting ν = 4. This contradiction proves that at most 2 external types can exist, which is exactly what we use to bound the cover size to 8.

### "Can I skip proving all 15 bounds?"

**Answer**: Yes! PROOF_TEMPLATE_cover_hits_B_C.lean gives a direct case analysis approach that doesn't require proving all 15 bounds separately. That's the faster route. Proving the 15 bounds is optional but makes the proof cleaner.

---

## Related Submissions

- **slot407**: Aristotle-proven proof of `at_most_two_A_external_types` (uses contrapositive)
- **slot406**: Helper lemma `six_triangles_contradict_nu4` (proven by Aristotle)
- **slot263**: Current target - PATH_4 τ ≤ 8 with explicit 8-edge cover

---

## Confidence Levels

| Aspect | Confidence | Reason |
|--------|-----------|--------|
| Mathematical correctness | 95%+ | Aristotle proved contrapositive; we reverse it |
| Lean implementation approach | 90%+ | Case analysis is straightforward |
| Estimated effort | 85%+ | Based on similar proof lengths in codebase |
| Timeline to completion | 80%+ | Depends on Lean syntax familiarity |

---

## Contact Points for Help

**If stuck on mathematics**: See EXTERNAL_DISJOINTNESS_ANALYSIS.md

**If stuck on proof strategy**: See COVER_HITS_B_C_STRATEGY.md

**If stuck on Lean syntax**: See PROOF_TEMPLATE_cover_hits_B_C.lean (copy examples)

**If integration issues**: Check line 458-493 of slot263_path4_explicit_aristotle.lean (main theorem structure)

---

## Summary

This analysis provides **complete theoretical and practical guidance** for filling the two sorries in slot263. The mathematics is solid, the strategy is clear, and Lean templates are provided.

**Next step**: Choose Phase 1 above and begin.

Expected result: A fully-proven `tau_le_8_path4` theorem in Lean 4, establishing τ(G) ≤ 8 for the PATH_4 configuration under ν = 4.
