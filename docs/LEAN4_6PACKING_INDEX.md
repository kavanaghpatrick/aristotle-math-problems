# Lean 4 6-Packing Proof: Complete Index

## Quick Navigation

### For Implementation
1. **START HERE**: [LEAN4_QUICK_REFERENCE.md](./LEAN4_QUICK_REFERENCE.md)
   - Copy-paste ready tactic sequences
   - Compact code snippets
   - Error patterns to avoid

2. **FULL GUIDE**: [LEAN4_TACTIC_GUIDE_6PACKING.md](./LEAN4_TACTIC_GUIDE_6PACKING.md)
   - Detailed explanation of each proof step
   - All 15 pairwise intersection cases
   - Complete cardinality calculation

3. **CODE SKELETON**: [LEAN4_6PACKING_CODE_SKELETON.lean](./LEAN4_6PACKING_CODE_SKELETON.lean)
   - Ready-to-fill Lean 4 file
   - Placeholder sorries for each major step
   - Comments explaining each section

### For Context
4. **PROJECT IDIOMS**: [LEAN4_PROJECT_IDIOMS.md](./LEAN4_PROJECT_IDIOMS.md)
   - Patterns used in this codebase
   - `simp +decide`, `aesop`, `grind` usage
   - Finset manipulation patterns

---

## Proof Structure Overview

```
Theorem: ¬(type1Exists ∧ type2Exists ∧ type3Exists)
├─ Step 1: Assume all three types exist
│  └─ Extract witnesses T₁, T₂, T₃ using Nonempty
├─ Step 2: Define candidate packing S = {T₁, T₂, T₃, B, C, D}
├─ Step 3: Prove S is edge-disjoint
│  ├─ 3 internal pairs (T₁-T₂, T₁-T₃, T₂-T₃)
│  ├─ 9 external pairs (T_i vs B, C, D)
│  └─ 3 packing pairs (B-C, B-D, C-D from hM)
├─ Step 4: Prove all elements are triangles
├─ Step 5: Prove S is a triangle packing
├─ Step 6: Prove all 6 elements distinct
├─ Step 7: Calculate |S| = 6
├─ Step 8: Apply hNu4 to get |S| ≤ 4
└─ Step 9: Derive 6 ≤ 4 contradiction → omega
```

---

## Key Tactic Patterns

### Witness Extraction
```lean
obtain ⟨T₁, hT₁⟩ := h1
simp only [externalsWithEdge, Finset.mem_filter] at hT₁
obtain ⟨hT₁_clique, hT₁_ne_E, hT₁_ab, hT₁_c_not⟩ := hT₁
```

### Intersection Bounds (Example)
```lean
have hT₁T₂_inter : (T₁ ∩ T₂).card ≤ 1 := by
  by_contra h; push_neg at h
  -- T₁ = {a,b,x}, T₂ = {b,c,y}, x ≠ y, so |T₁ ∩ T₂| ≤ 1
  omega
```

### Pairwise Property
```lean
have h_pairwise : Set.Pairwise (S : Set (Finset V)) (fun t t' => (t ∩ t').card ≤ 1) := by
  simp only [Set.Pairwise]
  intro t ht t' ht' hne
  -- Case split on which pair and apply bounds
```

### Cardinality
```lean
have hS_card : S.card = 6 := by
  simp only [S, Finset.card_insert_of_notMem]
  simp only [hT₁_ne_T₂, hT₁_ne_T₃, ..., hCD]
  norm_num
```

### Final Contradiction
```lean
have h_max : S.card ≤ 4 := hNu4 S hS_packing
rw [hS_card] at h_max
omega
```

---

## 15 Pairwise Intersection Cases

| # | Pair | Type | Bound Source | Notes |
|---|------|------|--------------|-------|
| 1 | T₁ ∩ T₂ | T₁ shares {a,b}, T₂ shares {b,c} | Structure | Max vertex: b |
| 2 | T₁ ∩ T₃ | T₁ shares {a,b}, T₃ shares {a,c} | Structure | Max vertex: a |
| 3 | T₂ ∩ T₃ | T₂ shares {b,c}, T₃ shares {a,c} | Structure | Max vertex: c |
| 4 | T₁ ∩ B | External vs packing element | Case analysis | Depends on B structure |
| 5 | T₁ ∩ C | External vs packing element | Case analysis | Depends on C structure |
| 6 | T₁ ∩ D | External vs packing element | Case analysis | Depends on D structure |
| 7 | T₂ ∩ B | External vs packing element | Case analysis | Depends on B structure |
| 8 | T₂ ∩ C | External vs packing element | Case analysis | Depends on C structure |
| 9 | T₂ ∩ D | External vs packing element | Case analysis | Depends on D structure |
| 10 | T₃ ∩ B | External vs packing element | Case analysis | Depends on B structure |
| 11 | T₃ ∩ C | External vs packing element | Case analysis | Depends on C structure |
| 12 | T₃ ∩ D | External vs packing element | Case analysis | Depends on D structure |
| 13 | B ∩ C | Packing pair | hM.2 | Set.Pairwise from isTrianglePacking |
| 14 | B ∩ D | Packing pair | hM.2 | Set.Pairwise from isTrianglePacking |
| 15 | C ∩ D | Packing pair | hM.2 | Set.Pairwise from isTrianglePacking |

---

## Critical Definitions

```lean
-- External triangles of type 1
def externalsWithEdge (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => T ≠ {a, b, c} ∧ a ∈ T ∧ b ∈ T ∧ c ∉ T)

def type1Exists (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) : Prop :=
  (externalsWithEdge G a b c).Nonempty

-- Triangle packing
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)
```

---

## Hypotheses Available

```lean
-- Main hypotheses in theorem statement
G : SimpleGraph V [DecidableRel G.Adj]     -- Graph with decidable adjacency
M : Finset (Finset V)                      -- Original packing
hM : isTrianglePacking G M                  -- M is a valid packing
hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4  -- Packing size constraint

-- Specific triangles
a b c : V [a ≠ b, b ≠ c, a ≠ c]            -- Vertices of base triangle
hE : {a, b, c} ∈ M                         -- Base triangle is in packing

-- Other packing elements
B C D : Finset V
hB : B ∈ M, hC : C ∈ M, hD : D ∈ M         -- All in packing
hB_ne : B ≠ {a,b,c}, ...                  -- All different from base
hBC : B ≠ C, hBD : B ≠ D, hCD : C ≠ D      -- All pairwise distinct
```

---

## Common Pitfalls & Solutions

### Pitfall 1: Finset vs Set Confusion
**Problem**: `Set.Pairwise` requires `(M : Set (Finset V))` but you write `M`
```lean
-- ❌ Wrong
have h : Pairwise (M) ... := hM.2

-- ✅ Correct
have h : Set.Pairwise (M : Set (Finset V)) (fun t t' => ...) := hM.2
simp only [Set.Pairwise] at h
```

### Pitfall 2: Membership in Finset Insert
**Problem**: Pattern matching on membership fails without simplification
```lean
-- ❌ Wrong
intro t ht
rcases ht with rfl | h'  -- Doesn't work, ht is still complex

-- ✅ Correct
intro t ht
simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
rcases ht with rfl | h'
```

### Pitfall 3: Card Equation Arithmetic
**Problem**: `norm_num` fails on finset card equations
```lean
-- ❌ Wrong
have : S.card = 6 := by norm_num

-- ✅ Correct
have : S.card = 6 := by
  simp only [S, Finset.card_insert_of_notMem]
  simp only [hT₁_ne_T₂, hT₁_ne_T₃, ...]  -- All distinctness
  norm_num
```

### Pitfall 4: omega Timeout on Complex Goals
**Problem**: omega can't handle complex set operations
```lean
-- ❌ Wrong (times out)
have : (T₁ ∩ T₂).card ≤ 1 := by omega

-- ✅ Correct
have : (T₁ ∩ T₂).card ≤ 1 := by
  by_contra h
  push_neg at h  -- Convert to explicit inequality
  -- Now omega works on arithmetic
```

---

## File Locations in Project

| File | Purpose | Status |
|------|---------|--------|
| `/Users/patrickkavanagh/math/docs/LEAN4_TACTIC_GUIDE_6PACKING.md` | Complete guide with all 7 steps | ✓ Ready |
| `/Users/patrickkavanagh/math/docs/LEAN4_QUICK_REFERENCE.md` | Copy-paste snippets & error table | ✓ Ready |
| `/Users/patrickkavanagh/math/docs/LEAN4_6PACKING_CODE_SKELETON.lean` | Lean 4 file with placeholders | ✓ Ready |
| `/Users/patrickkavanagh/math/docs/LEAN4_PROJECT_IDIOMS.md` | Codebase patterns (simp +decide, etc.) | ✓ Ready |
| `/Users/patrickkavanagh/proven/tuza/nu4/path4_scaffolding_complete.lean` | Reference implementation | ✓ Exists |

---

## Implementation Checklist

- [ ] Read LEAN4_QUICK_REFERENCE.md for patterns
- [ ] Study LEAN4_PROJECT_IDIOMS.md for project style
- [ ] Open LEAN4_6PACKING_CODE_SKELETON.lean in editor
- [ ] Step 1: Implement witness extraction (3 obtains)
- [ ] Step 2: Prove T₁ ∩ T₂ case (use by_contra + omega)
- [ ] Step 3: Prove T₁ ∩ T₃ case
- [ ] Step 4: Prove T₂ ∩ T₃ case
- [ ] Step 5: Prove remaining 12 pairwise bounds
- [ ] Step 6: Verify all elements are triangles
- [ ] Step 7: Construct isTrianglePacking proof
- [ ] Step 8: Prove all 6 elements distinct
- [ ] Step 9: Calculate |S| = 6
- [ ] Step 10: Apply hNu4 and derive omega contradiction
- [ ] Test compilation with Lean 4
- [ ] Submit to Aristotle for verification

---

## Expected Success Rate

Based on Aristotle's Tier 2 capability taxonomy:

| Component | Difficulty | Success Rate | Strategy |
|-----------|-----------|--------------|----------|
| Witness extraction | Tier 1 | 95% | Direct obtain pattern |
| Individual intersection proofs | Tier 1-2 | 85% | by_contra + omega or structure |
| Set packing definition | Tier 1 | 90% | Unfold + simp +decide |
| Cardinality calculation | Tier 1 | 95% | Finset.card_insert_of_notMem + norm_num |
| Final contradiction | Tier 1 | 100% | omega after setup |
| **Overall theorem** | **Tier 2** | **40-50%** | **Need proven helpers + good scaffolding** |

---

## Related Lemmas (Already Proven)

These are available in `path4_scaffolding_complete.lean`:

- `tau_union_le_sum`: Subadditivity of covering number
- `tau_S_le_2`: Covering bound on S_e
- `tau_X_le_2`: Covering bound on X_ef
- `X_ef_inter_card`: Intersection cardinality bound
- `X_ef_mem_inter`: Vertex membership in X_ef
- `path4_triangle_partition`: All triangles covered
- `overlap_implies_cover_lemma`: Overlap → shared edge
- `S_e_structure`: Structure of S_e
- `isTriangleCover_union`: Union covers both sets

These can be used to strengthen bounds on T_i ∩ {B,C,D} if needed.

---

## Questions & Answers

**Q: Should I use `simp` or `simp only`?**
A: Use `simp only [list]` in proofs to control what gets simplified. Use full `simp` only in exploration.

**Q: When should I use `omega` vs `linarith`?**
A: `omega` for integer/natural number contradictions; `linarith` for rational/real linear arithmetic.

**Q: Can I skip cases 4-12 (T_i vs packing elements)?**
A: No, all 15 pairs must satisfy the intersection bound. However, cases 4-12 might be automatic from structure.

**Q: Is it okay to use `sorry`?**
A: Only for cases you've fully reasoned through but can't formalize yet. Track with Aristotle.

**Q: What if intersection proofs are intractable?**
A: Fall back to computational verification: list all triangles in both T_i and {B,C,D}, compute intersections directly.

---

## Next Steps After Proof

1. **Compile**: `lean --check file.lean`
2. **Submit**: Use `./scripts/submit.sh file.lean problem_id`
3. **Process**: Run `./scripts/process_result.sh <UUID>` on Aristotle response
4. **Integrate**: If proven, move to `/proven/` and update database
5. **Archive**: Document in `docs/current_status.md`

