# Lean 4 Tactic Guidance for 6-Packing Contradiction Proof

## Quick Start

You're implementing this theorem:

```lean
theorem not_all_three_types (G : SimpleGraph V) [DecidableRel G.Adj] ... :
    ¬(type1Exists G a b c ∧ type2Exists G a b c ∧ type3Exists G a b c)
```

**Goal**: Prove that for any maximum packing of size ≤ 4, all three external types of a triangle cannot coexist.

**Approach**: Extract witnesses T₁, T₂, T₃, construct a 6-element packing S = {T₁, T₂, T₃, B, C, D}, prove it's valid, then derive 6 ≤ 4 contradiction.

---

## Document Guide

### For Rapid Implementation
👉 **Start here**: `LEAN4_QUICK_REFERENCE.md` (8.4 KB)
- Copy-paste ready tactic sequences
- Compact code snippets for each step
- Error patterns table
- **Best for**: Getting tactic code working fast

### For Understanding the Full Proof
📖 **Read this**: `LEAN4_TACTIC_GUIDE_6PACKING.md` (15 KB)
- Complete 9-step proof outline
- Detailed explanation of each step
- All 15 pairwise intersection cases explained
- Cardinality calculation walkthrough
- **Best for**: Understanding the mathematical structure

### For Implementation in Lean
💻 **Use this**: `LEAN4_6PACKING_CODE_SKELETON.lean` (11 KB)
- Complete Lean 4 file structure
- Placeholder `sorry` statements
- Comments explaining each section
- Helper lemma templates
- **Best for**: Copy-paste into your editor and fill in gaps

### For Project-Specific Patterns
🔧 **Reference**: `LEAN4_PROJECT_IDIOMS.md` (8.9 KB)
- `simp +zetaDelta` and `simp +decide` patterns
- `aesop`, `grind`, `interval_cases` usage
- Finset manipulation idioms
- Project-specific style conventions
- **Best for**: Matching codebase style

### For Detailed Case Analysis
📋 **Details**: `LEAN4_15_PAIRWISE_CASES.md` (9.2 KB)
- All 15 pairwise intersection proofs
- Structured by category (internal, external, packing)
- Reasoning and mathematical intuition for each
- Compact form for copy-paste
- **Best for**: Implementing the intersection bounds

### For Navigation
🗺️ **Index**: `LEAN4_6PACKING_INDEX.md` (10 KB)
- Quick navigation to all sections
- Proof structure overview
- Key tactic patterns summary
- Critical definitions and hypotheses
- Implementation checklist
- FAQ and troubleshooting
- **Best for**: Finding specific information

### For Quick Reference
📄 **Summary**: `LEAN4_IMPLEMENTATION_SUMMARY.txt` (8.8 KB)
- All 9 proof steps in compact form
- Critical tactic patterns
- Common issues and solutions
- Document locations
- **Best for**: One-page quick reference

---

## Implementation Workflow

### Phase 1: Setup & Learning (15 min)
1. Read `LEAN4_QUICK_REFERENCE.md` patterns
2. Skim `LEAN4_PROJECT_IDIOMS.md` for style
3. Open `LEAN4_6PACKING_CODE_SKELETON.lean` in editor

### Phase 2: Main Proof (60-90 min)
1. Fill in Step 1: Witness extraction (2-3 min)
2. Fill in Step 2: Define S (1 min)
3. Fill in Steps 3-4: Prove 15 pairwise bounds (30-45 min)
   - Use `LEAN4_15_PAIRWISE_CASES.md` as reference
   - Cases 1-3: by_contra + omega
   - Cases 4-12: omega (may need debugging)
   - Cases 13-15: Extract from hM.2
4. Fill in Step 5: All are triangles (5 min)
5. Fill in Step 6: Construct packing proof (5-10 min)
6. Fill in Step 7: Prove all distinct (10 min)
7. Fill in Step 8: Calculate cardinality (5-10 min)
8. Fill in Step 9: Apply hNu4 and derive contradiction (2 min)

### Phase 3: Debugging (30-60 min)
- Use `LEAN4_QUICK_REFERENCE.md` error table
- Check `LEAN4_PROJECT_IDIOMS.md` for Lean 4 idioms
- Reference `path4_scaffolding_complete.lean` for similar patterns

### Phase 4: Testing & Submission
- Compile: `lake build` or Lean plugin
- Check for sorries: `grep sorry file.lean`
- Submit: `./scripts/submit.sh file.lean problem_id`

---

## Key Files by Size

| File | Size | Purpose | Read Time |
|------|------|---------|-----------|
| LEAN4_TACTIC_GUIDE_6PACKING.md | 15 KB | Complete guide | 20 min |
| LEAN4_6PACKING_CODE_SKELETON.lean | 11 KB | Ready-to-fill code | 15 min |
| LEAN4_6PACKING_INDEX.md | 10 KB | Navigation & checklist | 10 min |
| LEAN4_15_PAIRWISE_CASES.md | 9.2 KB | Detailed cases | 15 min |
| LEAN4_PROJECT_IDIOMS.md | 8.9 KB | Codebase patterns | 15 min |
| LEAN4_IMPLEMENTATION_SUMMARY.txt | 8.8 KB | One-page summary | 5 min |
| LEAN4_QUICK_REFERENCE.md | 8.4 KB | Copy-paste snippets | 10 min |

---

## Document Cross-References

```
LEAN4_QUICK_REFERENCE.md
├─ Links to: LEAN4_PROJECT_IDIOMS.md (for idiom explanations)
├─ Links to: LEAN4_15_PAIRWISE_CASES.md (for case details)
└─ Links to: LEAN4_TACTIC_GUIDE_6PACKING.md (for full guide)

LEAN4_TACTIC_GUIDE_6PACKING.md
├─ Part 1: Witness Extraction
├─ Part 2: Candidate Packing
├─ Part 3: Pairwise (→ see LEAN4_15_PAIRWISE_CASES.md)
├─ Part 4: Triangles
├─ Part 5: Packing Proof
├─ Part 6: Cardinality
├─ Part 7: Contradiction
└─ Summary table (→ see LEAN4_QUICK_REFERENCE.md)

LEAN4_6PACKING_CODE_SKELETON.lean
├─ Step 1: Assume → (see LEAN4_QUICK_REFERENCE.md)
├─ Step 2: Extract → (see LEAN4_QUICK_REFERENCE.md)
├─ Step 3: Define S → (direct)
├─ Step 4: Pairwise → (see LEAN4_15_PAIRWISE_CASES.md)
├─ Step 5-9: Follow structure
└─ Comments reference all guides

LEAN4_15_PAIRWISE_CASES.md
├─ Category A: Internal pairs (Cases 1-3)
├─ Category B: External vs packing (Cases 4-12)
├─ Category C: Packing pairs (Cases 13-15)
├─ All 15 compact form (→ copy to LEAN4_6PACKING_CODE_SKELETON.lean)
└─ Troubleshooting (→ see LEAN4_QUICK_REFERENCE.md)

LEAN4_PROJECT_IDIOMS.md
├─ Used in: LEAN4_QUICK_REFERENCE.md
├─ Used in: LEAN4_TACTIC_GUIDE_6PACKING.md
├─ Used in: LEAN4_6PACKING_CODE_SKELETON.lean
└─ Reference for: All Lean 4 code written
```

---

## Expected Tactic Success Rates

Based on `path4_scaffolding_complete.lean`:

| Component | Tactic | Success Rate | Notes |
|-----------|--------|--------------|-------|
| Witness extraction | obtain | 98% | Direct pattern matching |
| Internal bounds (3 cases) | by_contra + omega | 90% | Cardinality reasoning |
| Ext vs pack bounds (9 cases) | omega | 75% | May need case split |
| Pack vs pack bounds (3 cases) | hM.2 extraction | 95% | Already proven |
| Triangle verification | simp + rcases | 99% | Membership checks |
| Packing construction | simp + rcases | 85% | Case splitting on 6 elements |
| Distinctness proofs | intro + rw + omega | 95% | Direct contradictions |
| Cardinality calculation | simp + norm_num | 92% | Requires all distinctness |
| Final contradiction | omega | 100% | 6 ≤ 4 obviously false |
| **Overall** | **Mixed** | **40-60%** | **Needs debugging for bounds** |

---

## Typical Issues & Solutions

| Issue | Document | Solution |
|-------|----------|----------|
| "Definition doesn't unfold" | QUICK_REFERENCE.md | Use `simp only [defn]` |
| "simp doesn't simplify enough" | PROJECT_IDIOMS.md | Use `simp +zetaDelta` or `simp +decide` |
| Card calculation fails | QUICK_REFERENCE.md | Add distinctness hypotheses to simp |
| omega times out | TACTIC_GUIDE_6PACKING.md | Break into sub-cases first |
| Can't match on membership | QUICK_REFERENCE.md | `simp only [Finset.mem_insert]` first |
| Set.Pairwise syntax error | PROJECT_IDIOMS.md | Cast with `(M : Set (Finset V))` |
| Forgot a pairwise case | 15_PAIRWISE_CASES.md | Use table to find missing case |

---

## Proof Statistics

- **Total lines**: ~150 (with comments)
- **Steps**: 9
- **Pairwise cases**: 15
- **Distinctness proofs**: 12 (one-liner each)
- **Critical sections**: 5 (Steps 1, 3, 5, 6, 8)
- **Expected development time**: 2-4 hours
- **Expected debugging time**: 1-2 hours

---

## Files to Use Side-by-Side

**Recommended setup**:
1. **Left screen**: `LEAN4_6PACKING_CODE_SKELETON.lean` (editor)
2. **Right screen**: `LEAN4_QUICK_REFERENCE.md` (copy-paste) + `LEAN4_15_PAIRWISE_CASES.md` (case reference)
3. **Background**: `LEAN4_PROJECT_IDIOMS.md` (style reference)

**When debugging**:
- Check: QUICK_REFERENCE.md error table
- Inspect: LEAN4_PROJECT_IDIOMS.md for tactic patterns
- Consult: TACTIC_GUIDE_6PACKING.md for full context

---

## Reference Implementation

For comparison when stuck, see:
- `/Users/patrickkavanagh/math/proven/tuza/nu4/path4_scaffolding_complete.lean`
  - Look for `lemma larger_packing_of_disjoint_pair` (similar packing construction)
  - Look for `lemma tau_union_le_sum` (similar cardinality reasoning)
  - Look for `lemma path4_triangle_partition` (similar case splitting)

---

## After Implementation

1. **Compile**: `lake build` or your Lean 4 plugin
2. **Check sorries**: Ensure all are resolved
3. **Submit**: `./scripts/submit.sh file.lean tuza_nu4_6packing_contradiction`
4. **Process result**: `./scripts/process_result.sh <UUID>`
5. **Archive**: Move to `proven/` if successful
6. **Document**: Update `docs/current_status.md`

---

## Document Version Info

Created: 2026-01-14
Lean 4 Version: 4.24.0+
Mathlib Version: Latest from project
Based on: `path4_scaffolding_complete.lean` (proven reference)

---

## Questions?

- **Tactic syntax**: See LEAN4_QUICK_REFERENCE.md
- **Project style**: See LEAN4_PROJECT_IDIOMS.md
- **Proof structure**: See LEAN4_TACTIC_GUIDE_6PACKING.md
- **Specific cases**: See LEAN4_15_PAIRWISE_CASES.md
- **Navigation**: See LEAN4_6PACKING_INDEX.md
- **Implementation**: See LEAN4_6PACKING_CODE_SKELETON.lean
- **Quick lookup**: See LEAN4_IMPLEMENTATION_SUMMARY.txt

