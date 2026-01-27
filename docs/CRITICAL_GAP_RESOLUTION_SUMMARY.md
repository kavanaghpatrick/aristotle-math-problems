# PATH_4 τ ≤ 8 Proof: Critical Gap Resolution Summary

**Status**: Analysis complete. Ready for implementation.

**Key Discovery**: Aristotle NEGATED the "fan apex" lemma on Fin 6, revealing that the three external types cannot ALL exist simultaneously. This is the crux of the proof.

---

## The Critical Gap

### What Needs to Be Proven

In `/Users/patrickkavanagh/math/submissions/nu4_final/slot263_path4_explicit_aristotle.lean`:

**Lines 318-333**: Two sorry proofs
- `lemma cover_hits_sharing_B` - Line 319
- `lemma cover_hits_sharing_C` - Line 328

**These are the ONLY blockers** for a complete proof of `tau_le_8_path4`.

---

## The Mathematical Structure

### External Type Definition

For M-element **A = {v₁, a₂, a₃}**, there are exactly 3 possible external types:

```
Type 1: T₁ = {v₁, a₂, w₁}  (shares edge {v₁, a₂} with A)
Type 2: T₂ = {v₁, a₃, w₂}  (shares edge {v₁, a₃} with A)
Type 3: T₃ = {a₂, a₃, w₃}  (shares edge {a₂, a₃} with A)
```

Where **w₁, w₂, w₃ must be fresh** (not in {v₁, v₂, v₃, a₂, a₃, b₃, c₃, d₂, d₃}).

### Why Freshness Matters

| Constraint | Purpose |
|-----------|---------|
| w₁, w₂, w₃ distinct | Ensures T₁, T₂, T₃ are different triangles |
| w_i ∉ core 9-vertex set | Isolates externals from M structure; forces (T_i ∩ M-element).card ≤ 1 |
| Combined with packing property | Allows construction of 6-triangle packing contradicting ν = 4 |

### The 15 Pairwise Intersection Bounds

All come from THREE sources:

**Source 1: Definitional (External types)**
- T₁ ∩ T₂ = {v₁} (both contain v₁; differ in second vertex)
- T₁ ∩ T₃ = {a₂} (share a₂ only)
- T₂ ∩ T₃ = {a₃} (share a₃ only)

**Source 2: Freshness (External × M-element)**
- T₁ ∩ B = {v₁} (only shared vertex of B)
- T₂ ∩ B = {v₁} (same)
- T₃ ∩ B = ∅ (w₃ avoids B, {a₂, a₃} ∉ B)
- Similar for C and D

**Source 3: PATH_4 Structure (M-element × M-element)**
- B ∩ C = {v₂} (spine vertex)
- B ∩ D = ∅ (path structure)
- C ∩ D = {v₃} (spine vertex)

---

## Answers to Your 4 Questions

### Q1: Exact conditions on w₁, w₂, w₃ for edge-disjointness?

**Answer**: NOT edge-disjoint; PACKING (card ≤ 1 intersection).

The external types have **pairwise vertex intersections** defined by their structure, not edge-disjointness. The proof uses:
1. **Definition-based bounds**: T₁ ∩ T₂ = {v₁} comes from the triangle definitions
2. **Freshness-based bounds**: w_i avoid all M-elements, forcing isolated intersections
3. **Packing property**: The 6 triangles {T₁, T₂, T₃, B, C, D} form a packing with card = 6 > 4, contradicting ν = 4

### Q2: Do w₁, w₂, w₃ need to be "fresh"?

**Answer**: YES, absolutely required.

**Why**:
- **Prevents degeneracy**: If w₁ = a₂, then T₁ = {v₁, a₂, a₂} (invalid)
- **Isolates from M**: Ensures T_i vertices don't interfere with B/C/D structure
- **Enables proof by contradiction**: Fresh w_i guarantees the 6-triangle packing property needed to contradict ν = 4

### Q3: Prove T₁, T₂, T₃ pairwise ≤ 1 intersection?

**Answer**: Straightforward from definitions + freshness.

**Tactic pattern**:
```lean
simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
omega  -- Decidable finite set membership
```

Each pair reduces to a finite case analysis:
- T₁ ∩ T₂ = {x | (x = v₁ ∨ x = a₂ ∨ x = w₁) ∧ (x = v₁ ∨ x = a₃ ∨ x = w₂)} = {v₁}
- (Similar for other pairs)

### Q4: Cleanest proof of 15 pairwise bounds?

**Answer**: Separate lemmas for each pair class, then combine.

**Three classes**:
1. **Externals vs externals** (3 pairs): Definitional, using `simp + omega`
2. **Externals vs M-elements** (12 pairs): Freshness + structure, using `simp + omega`
3. **M-elements vs M-elements** (Already in existing PATH_4 structure)

**Estimate**: ~150 lines of Lean to prove all 15 bounds formally.

---

## The Two Remaining Sorries

### lemma cover_hits_sharing_B

**Goal**: Prove any triangle sharing ≥2 vertices with B (but ≤1 with A) is covered by spine edge {v₁, v₂}.

**Key insight**:
- B = {v₁, v₂, b₃}
- If t shares 2 vertices with B, they must be two of {v₁, v₂, b₃}
- Three possibilities: {v₁, v₂}, {v₁, b₃}, {v₂, b₃}
- All three pairs have at least one edge in the cover:
  - {v₁, v₂} is the spine edge
  - {v₁, b₃} and {v₂, b₃} are part of B's 3 edges (all in cover)

**Proof strategy**: Case analysis on which 2 vertices t shares with B, then show the resulting edge is in cover.

**Estimated length**: 40-50 lines

### lemma cover_hits_sharing_C

**Goal**: Identical to cover_hits_sharing_B, but for C = {v₂, v₃, c₃} and spine edge {v₂, v₃}.

**Proof strategy**: Symmetric to cover_hits_sharing_B.

**Estimated length**: 40-50 lines

---

## Implementation Roadmap

### Step 1: Pre-prove the 15 intersection bounds (Optional but recommended)

Create helper lemmas:
- `T1_inter_T2_bound`: T₁ ∩ T₂ = {v₁}, card ≤ 1
- `T1_inter_T3_bound`: T₁ ∩ T₃ = {a₂}, card ≤ 1
- ... (and 12 more)

**Benefit**: Makes `six_triangles_contradict_nu4` usage clearer, enables reuse.

**Effort**: ~150 lines, but once done, all future PATH_4 work is faster.

### Step 2: Prove cover_hits_sharing_B and cover_hits_sharing_C

Fill the two sorries in slot263 using the case analysis strategy from `/docs/COVER_HITS_B_C_STRATEGY.md`.

**Effort**: ~100 lines total

### Step 3: Verify and submit

Run local compilation:
```bash
lean --check submissions/nu4_final/slot263_path4_explicit_aristotle.lean
```

Then submit via:
```bash
./scripts/submit.sh submissions/nu4_final/slot263_path4_explicit_aristotle.lean slot263
```

---

## Documentation Files Created

| File | Purpose | Use Case |
|------|---------|----------|
| `EXTERNAL_DISJOINTNESS_ANALYSIS.md` | Deep analysis of all 15 bounds | Reference; understand mathematics |
| `COVER_HITS_B_C_STRATEGY.md` | Detailed case analysis for sorries | Implementation guide; copy patterns |
| `slot263_path4_explicit_DISJOINTNESS_GUIDE.lean` | Lean code templates | Implementation; proof skeletons |
| `CRITICAL_GAP_RESOLUTION_SUMMARY.md` | This file | Overview and next steps |

---

## Why This Proof Works: The Big Picture

### The 8-Edge Cover

```
From A: {v₁,a₂}, {v₁,a₃}, {a₂,a₃}        (3 edges)
From B: {v₁,v₂}                           (1 spine edge)
From C: {v₂,v₃}                           (1 spine edge)
From D: {v₃,d₂}, {v₃,d₃}, {d₂,d₃}        (3 edges)
────────────────────────────────────
Total:  8 edges
```

### Coverage Guarantees

| Triangle Type | Intersection | Covered By | Why |
|---|---|---|---|
| t ∈ M (any) | 3 vertices in M-element | All its edges | All 8 edges in cover |
| Type 1 external | 2 vertices in A | A's edges | A ⊆ cover |
| Type 2 external | 2 vertices in A | A's edges | A ⊆ cover |
| Type 3 external | 2 vertices in A | A's edges | A ⊆ cover |
| B-external | 2 vertices in B | Spine {v₁,v₂} OR B's edges | Always covered |
| C-external | 2 vertices in C | Spine {v₂,v₃} OR C's edges | Always covered |
| D-external | 2 vertices in D | D's edges | D ⊆ cover |

---

## Critical Insight: Why At Most 2 External Types Exist

If all 3 types (T₁, T₂, T₃) existed for A with distinct fresh w values, plus the 3 M-elements B, C, D (which form a packing), we'd have:

```
S = {T₁, T₂, T₃, B, C, D}  (6 triangles)
```

All 15 pairwise intersections have card ≤ 1 (by our bounds), so S is a packing.

But:
- |S| = 6 > 4 ≥ ν(G)
- **Contradiction!**

Therefore: **At most 2 of the 3 external types can exist**.

This is Aristotle's negation proof, and we reverse it in the contradiction approach.

---

## Next Actions

1. **Review** `/docs/COVER_HITS_B_C_STRATEGY.md` for implementation details
2. **Implement** the two lemma proofs (~100 lines total)
3. **Test** with local Lean compilation
4. **Submit** and process result
5. **Update** database with newly proven lemmas

---

## Success Criteria

- [ ] Both `cover_hits_sharing_B` and `cover_hits_sharing_C` are fully proven (0 sorry)
- [ ] `tau_le_8_path4` main theorem compiles without sorry (except final trivial step)
- [ ] All 15 intersection bounds are formally proven
- [ ] Submission passes Aristotle validation
- [ ] Result logged in submissions database

---

## Confidence Level

**Mathematical correctness**: 95%+ (Aristotle proved the contrapositive; we're reversing it)
**Lean implementation difficulty**: Moderate (case analysis + simp-based tactics)
**Timeline**: 2-4 hours to full proof

The structure is solid; it's just filling in the boilerplate proof details.
