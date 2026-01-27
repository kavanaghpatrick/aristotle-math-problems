# Strategic Comparison: slot427 vs slot431

## The Fundamental Difference

### slot427: FIXED Cover + Case-by-Case Proof

```lean
-- Fixed 8-edge selection
let Cover := {s(a₁,v₁), s(a₂,v₁), s(v₁,v₂), s(v₁,b), s(v₂,v₃), s(v₂,c), s(v₃,d₁), s(v₃,d₂)}

-- Then prove each triangle is covered
∀ T, case_split_on_which_element_T_touches → prove_some_edge_hits_T
```

**Problem:** For bridge T = {v₂, b, x} between B and C:
- Our fixed cover for B is {s(v₁,v₂), s(v₁,b)}
- This bridge uses edge {v₂, b} which is NOT in our cover!
- We're stuck with many sorries trying to prove coverage

### slot431: ADAPTIVE Cover + Guaranteed Coverage

```lean
-- Adaptive selection based on which edge types are empty
by_cases h_spine : Type_spine.Nonempty
  -- Case 1: Spine nonempty, one leg must be empty → pick spine + non-empty leg
  -- Case 2: Spine empty → pick both legs
```

**Key Insight: Bridge-External Equivalence**

A bridge IS an external, just viewed from a different angle:

| Bridge | From B's perspective |
|--------|---------------------|
| A-B bridge using {v₁, v₂} | Spine-type external of B |
| A-B bridge using {v₁, b₃} | Left-type external of B |
| B-C bridge using {v₁, v₂} | Spine-type external of B |
| B-C bridge using {v₂, b₃} | Right-type external of B |

**Why this matters:**

The 6-packing constraint says: At most 2 of 3 edge types have externals.

If **spine type is EMPTY**:
- No externals use spine edge
- Therefore NO BRIDGES use spine edge!
- A-B bridges must use {v₁, b₃} → covered by left leg
- B-C bridges must use {v₂, b₃} → covered by right leg
- Pick both legs: {s(v₁,b₃), s(v₂,b₃)} ✓

If **spine type is NONEMPTY**, one leg must be empty:
- Say right leg empty → no B-C bridges use {v₂, b₃}
- Pick spine + left: {s(v₁,v₂), s(v₁,b₃)} ✓

---

## Assembly Strategy Comparison

### slot427 Assembly (Bottom-Up)

```
1. Fix 8 edges
2. For each triangle T:
   - Determine which packing element(s) T touches
   - Case split: packing / S_e external / bridge
   - For bridges: prove v_i ∈ T, then prove one of our edges hits T
   - PROBLEM: May not have the right edge in our fixed cover!
```

**Result:** Many sorries, complex case analysis

### slot431 Assembly (Top-Down)

```
1. For endpoint A:
   - Get S_e_edge types from slot423
   - Apply not_all_three constraint
   - 2 edges cover A + externals + bridges to B

2. For middle B:
   - Get S_e_edge types from slot423
   - Apply not_all_three constraint
   - Call adaptive_middle_covers_bridges
   - 2 edges GUARANTEED to cover B + externals + ALL bridges (A-B and B-C)

3. For middle C: Same as B

4. For endpoint D: Same as A

5. Union all 8 edges
   - Each triangle is external to some element OR is a packing element
   - Therefore covered by that element's 2 edges
```

**Result:** Clean integration, hypotheses already proven

---

## What slot431 Provides That slot427 Lacks

| Feature | slot427 | slot431 |
|---------|---------|---------|
| Bridge coverage proof | Case-by-case (sorries) | **PROVEN** in `adaptive_middle_covers_bridges` |
| 6-packing usage | Implicit | **EXPLICIT** hypothesis `h_not_all_three` |
| Adaptive selection | No (fixed cover) | **Yes** (case analysis on types) |
| Bridge-external equivalence | Not used | **Key insight** |

---

## Recommended Path Forward

**Use slot431's `adaptive_middle_covers_bridges` as the core.**

Assembly needs:
1. ✅ slot423: `not_all_three_edge_types` provides `h_not_all_three`
2. ✅ slot431: `adaptive_middle_covers_bridges` handles middles B, C
3. ❓ Need: `adaptive_endpoint_covers_bridges` for A, D (simpler - only one neighbor)

The endpoint case is simpler because:
- A only has bridges to B (one direction)
- D only has bridges to C (one direction)
- No "both sides" coordination needed

---

## Conclusion

**slot431 is the correct route.**

It solves the bridge coverage problem that slot427 was struggling with, using:
1. Bridge-External Equivalence (bridges ARE externals)
2. Adaptive selection (pick edges based on what's empty)
3. 6-packing constraint (at most 2 types nonempty)

The math is already done - we just need to wire up the assembly.
