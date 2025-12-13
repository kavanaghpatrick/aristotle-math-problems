# Jones Polynomial Success Patterns: Extracted for HOMFLY-PT

**Date**: 2025-12-12
**Source**: 25-crossing Jones polynomial breakthrough (Project ID: `4aef4bc7-ecf0-4e11-aab4-48da39ed3379`)
**Purpose**: Extract success patterns to apply to HOMFLY-PT polynomial verification

---

## 1. Problem Presentation Structure

### What Was Provided to Aristotle

**Inline data (complete, ready-to-use):**
- ✅ 20 knot definitions as braid words (complete test suite)
- ✅ Verification goal: Prove `jones_poly_norm(knot) ≠ [(0, 1)]` (NOT the unknot)
- ✅ Certificate-based approach: verify property, not compute full polynomial

**What Aristotle Figured Out:**
- ❌ No target Jones polynomial values provided (Aristotle computed, not verified against known)
- ✅ Aristotle chose Temperley-Lieb algebra representation
- ✅ Aristotle designed SparsePoly data structure
- ✅ Aristotle evolved algorithm through 4 versions (v4→v5→v6→v7)

### Key Insight: Certificate-Based Verification

**Pattern:** Don't ask Aristotle to compute the full polynomial and match known values.
**Instead:** Ask to verify a PROPERTY (Jones ≠ 1) which is decidable via `native_decide`.

**For HOMFLY-PT:**
- ❌ BAD: "Compute HOMFLY-PT and verify it matches P(a,z) = ..."
- ✅ GOOD: "Prove HOMFLY-PT ≠ 1" OR "Prove HOMFLY-PT has degree ≥ d" OR "Prove HOMFLY-PT coefficient at (a^i, z^j) ≠ 0"

---

## 2. Data Structure Choices

### SparsePoly (Sparse Laurent Polynomials)

```lean
abbrev SparsePoly := List (Int × Int)  -- (power, coefficient) pairs
```

**Why this worked:**
1. **Decidable equality** via normalization (sorting + merging duplicates)
2. **Supports negative powers** (essential for Jones polynomial A^(-1) terms)
3. **Efficient for sparse polynomials** (only non-zero terms stored)
4. **Simple operations** (add = concatenate + normalize, mul = nested map + fold)

**Operations implemented:**
- `add`, `add_norm` (v7: aggressive normalization)
- `mul`, `mul_norm` (v7: normalize after each multiply)
- `scale`, `mul_term`, `mul_loop_value`
- `div_monic` (v4-v5), `div_laurent` (v6: allows negative quotient powers)
- `power` (recursive: `p^(k+1) = p * p^k`)
- `normalize` (sort by exponent, merge duplicates, remove zeros)

### TL_elt (Temperley-Lieb Elements)

```lean
abbrev TL_elt := List (Matching × SparsePoly)
```

**Represents:** Linear combinations of matchings with polynomial coefficients

**Why this worked:**
1. **Computable multiplication** via matching composition
2. **Fuel-based merge** ensures termination for `native_decide`
3. **Decidable equality** via sorted matching lists

### Matching (Diagram Matchings)

```lean
abbrev Matching := List Nat  -- Pairing on 2n points
```

**For HOMFLY-PT:**
- Same representations can work!
- HOMFLY-PT uses 2-variable polynomials: `List (Int × Int × Int)` for `(a_power, z_power, coeff)`
- Or: `abbrev BivariatePoly := List (Int × Int × Int)`

---

## 3. Algorithmic Evolution (v4 → v5 → v6 → v7)

### Version 4 (Baseline)
- Basic Temperley-Lieb algebra implementation
- Kauffman bracket computation
- Polynomial division by monic polynomials (`div_monic`)
- **Problem:** Some knots too large

### Version 5 (Fuel-Based Merge)
- Added `TL_elt.merge_fuel` for termination guarantees
- Fuel = list length + 1 (provably sufficient)
- **Why:** Ensures `native_decide` can verify termination
- **Benefit:** Enables Lean kernel to execute proofs

### Version 6 (Laurent Polynomial Division)
- Implemented `SparsePoly.div_laurent` (allows negative powers in quotient)
- **Critical:** Jones polynomial normalization requires dividing by `A^2 + A^(-2) + 2`
- **Why v5 failed:** `div_monic` stopped when degree too low
- **Fix:** Remove degree check, allow negative quotient powers
- **Used for:** Knots 01, 03, 05, 07, 09 (5/20 knots)

### Version 7 (Aggressive Normalization)
- `SparsePoly.add_norm`, `SparsePoly.mul_norm` (normalize after EVERY operation)
- `TL_elt.merge_fuel_norm` (normalize during merge)
- **Why:** Control intermediate expression size (prevent exponential blowup)
- **Benefit:** Faster computation, handles more complex knots
- **Used for:** Knots 02, 04, 06, 08, 10-20 (15/20 knots)

### Predicted Evolution for HOMFLY-PT

Based on this pattern:

**v1 (Baseline):**
- Basic HOMFLY-PT computation via skein relation
- Bivariate polynomial arithmetic (`a`, `z` variables)
- No optimization

**v2 (Fuel-Based):**
- Add fuel to recursive skein computation
- Ensure termination for `native_decide`

**v3 (Efficient Polynomial Division):**
- HOMFLY-PT normalization may require division
- Implement bivariate polynomial division (if needed)

**v4 (Aggressive Normalization):**
- Normalize after every polynomial operation
- Critical for preventing intermediate expression blowup
- Expect this to be the final working version

**Recommendation:** Start with v1, but ANTICIPATE v4 will be needed. Don't be surprised if Aristotle evolves through 3-4 versions.

---

## 4. Termination Strategy

### Pattern: Fuel-Based Recursion

**Why fuel?**
- Lean 4 requires structural termination proofs
- Recursive functions must provably terminate
- `native_decide` needs guaranteed termination

**Implementation (from v5):**

```lean
def TL_elt.merge_fuel (fuel : Nat) (t : TL_elt) : TL_elt :=
  match fuel with
  | 0 => t -- Should not happen if fuel is sufficient
  | fuel + 1 =>
    match t with
    | [] => []
    | [x] => if x.2.is_zero then [] else [x]
    | x :: y :: rest =>
      if x.1 == y.1 then
        TL_elt.merge_fuel fuel ((x.1, SparsePoly.add x.2 y.2) :: rest)
      else
        if x.2.is_zero then TL_elt.merge_fuel fuel (y :: rest)
        else x :: TL_elt.merge_fuel fuel (y :: rest)
```

**Fuel choice:** `fuel = list.length + 1` (provably sufficient because each recursive call shrinks the list)

**For HOMFLY-PT:**

Apply same pattern to skein relation recursion:

```lean
def homfly_pt_with_fuel (fuel : Nat) (knot : BraidWord) : BivariatePoly :=
  match fuel with
  | 0 => [(0, 0, 0)] -- Should not happen
  | fuel + 1 =>
    match knot with
    | [] => [(0, 0, 1)] -- Unknot
    | op :: rest =>
      -- Skein relation: a * <L+> + a^(-1) * <L-> = z * <L0>
      -- Recurse with fuel-1
      ...
```

**Fuel choice for HOMFLY-PT:** `fuel = 2^(crossing_number)` (upper bound on skein tree size)

---

## 5. Test Case Selection

### 20 Knots with 25 Crossings

**Distribution:**
- **Knots 01-10:** 3-strand braids (12-28 operations)
  - Mix of positive/negative generators
  - Alternating patterns (e.g., `[1,2,-1,-2,1,2,-1,-2,...]`)
  - Pure positive (e.g., `[1,2,1,2,1,2,...]`)

- **Knots 11-20:** 4-strand and 5-strand braids (24-25 operations)
  - More complex topologies
  - Higher-genus surfaces
  - Generators: σ₁, σ₂, σ₃, σ₄

**Pattern diversity:**
1. Positive/negative mix
2. Alternating patterns
3. Repetitive structures
4. Different strand counts (3, 4, 5)
5. Different writhe values

### Recommended HOMFLY-PT Test Suite

**Goal:** 10-20 knots with 15-20 crossings (start smaller than Jones)

**Strategy:**

**Batch 1 (Low crossings, diverse types):**
1. Trefoil (3₁): `[1, 1, 1]` (3 crossings)
2. Figure-eight (4₁): `[1, 2, 1, 2]` (4 crossings)
3. Cinquefoil (5₁): `[1, 1, 1, 1, 1]` (5 crossings)
4. Knot 6₁: `[1, 2, 1, 2, 1, 2]` (6 crossings)
5. Knot 7₁: `[1, 1, 1, 1, 1, 1, 1]` (7 crossings)

**Batch 2 (Medium crossings, 10-15):**
6. 3-strand alternating: `[1, 2, -1, -2, 1, 2, -1, -2]` (8 crossings)
7. 3-strand positive: `[1, 2, 1, 2, 1, 2, 1, 2, 1, 2]` (10 crossings)
8. 4-strand torus: `[1, 2, 3, 1, 2, 3, 1, 2, 3]` (9 crossings)
9. 3-strand complex: `[1, 2, 1, 2, -1, -2, 1, 2, 1, 2]` (10 crossings)
10. 4-strand alternating: `[1, 2, 3, -1, -2, -3, 1, 2, 3, -1, -2, -3]` (12 crossings)

**Batch 3 (High crossings, if batches 1-2 succeed):**
11-20: 15-20 crossings (similar patterns to Jones 25-crossing)

**Key principle:** Start small, scale up gradually. Don't jump straight to 25 crossings.

---

## 6. Instruction Set Style

### What Worked for Jones Polynomial

**Tone:** Direct, mathematical, imperative

**Example opening (inferred from output structure):**

> "Prove that the Jones polynomial is NOT equal to 1 for the following 20 knots with 25 crossings.
>
> For each knot defined as a braid word, implement a computable Jones polynomial algorithm and prove:
> `jones_poly_norm(knot) ≠ [(0, 1)]`
>
> Use `native_decide` for all proofs."

**Structure:**
1. **Goal statement** (what to prove)
2. **Data provided** (20 knot definitions)
3. **Verification method** (`native_decide`)
4. **No implementation details** (let Aristotle design algorithm)

### Recommended Style for HOMFLY-PT

**Option A (Minimal, trust Aristotle):**

> "Implement a computable HOMFLY-PT polynomial algorithm and prove that HOMFLY-PT ≠ 1 for the following 10 knots.
>
> [Provide 10 braid words]
>
> Use `native_decide` for all proofs."

**Option B (More guidance):**

> "Implement the HOMFLY-PT polynomial using the skein relation:
>
> a * P(L+) - a^(-1) * P(L-) = z * P(L0)
>
> Represent polynomials as bivariate Laurent polynomials in a and z.
> Use fuel-based recursion for termination.
>
> Prove that HOMFLY-PT ≠ 1 for the following 10 knots:
> [Provide 10 braid words]
>
> Use `native_decide` for all proofs."

**Recommendation:** Start with Option A (minimal). Aristotle successfully designed the entire Jones algorithm autonomously. Only add guidance if first attempt fails.

**Template elements:**
- ✅ Clear verification goal
- ✅ Complete inline data (all test knots)
- ✅ Proof method (`native_decide`)
- ❌ DON'T provide target polynomial values (Aristotle won't match them anyway)
- ❌ DON'T over-specify algorithm (let Aristotle iterate)

---

## 7. Known Pitfalls to Avoid

### From Jones Experience

**Pitfall 1: Division Without Laurent Support**
- v4-v5 failed for some knots because `div_monic` couldn't handle negative quotient powers
- **Fix:** v6 implemented `div_laurent` (removed degree check)
- **Lesson:** HOMFLY-PT may need similar bivariate division

**Pitfall 2: Intermediate Expression Blowup**
- v6 worked but was slow for complex knots
- **Fix:** v7 normalized after EVERY operation (add_norm, mul_norm)
- **Lesson:** HOMFLY-PT should normalize aggressively from the start

**Pitfall 3: No Fuel for Recursion**
- Lean 4 requires termination proofs
- **Fix:** v5 added fuel-based merge
- **Lesson:** HOMFLY-PT needs fuel for skein recursion

**Pitfall 4: Asking for Full Polynomial Values**
- Jones v2 (earlier project) tried to match target polynomials → complex
- Jones 25-crossing just proves ≠ 1 → simple, worked
- **Lesson:** Verification of PROPERTY is easier than full polynomial computation

**Pitfall 5: Too Ambitious Initial Scale**
- Jones started with 9-crossing (successful), then jumped to 25-crossing (successful)
- **Lesson:** HOMFLY-PT should start with 3-7 crossings, THEN scale to 15-20

**Pitfall 6: Unclear Normalization Convention**
- Jones polynomial needs normalization factor `(-A^3)^(-w(L))`
- HOMFLY-PT needs similar normalization
- **Lesson:** Be explicit about normalization in problem statement OR let Aristotle figure it out

### What Didn't Cause Problems (Surprisingly)

✅ **No target polynomial values** (Aristotle just proved ≠ 1)
✅ **Multiple algorithm versions** (Aristotle iterated successfully)
✅ **Complex data structures** (SparsePoly, TL_elt, Matching all worked)
✅ **Large computations** (25 crossings handled by native_decide)
✅ **No examples** (Aristotle designed algorithm from scratch)

---

## 8. Success Pattern Summary

### Core Formula That Worked

**1. Complete inline data:** All 20 knots provided as braid words
**2. Simple verification goal:** Prove Jones ≠ 1 (not full polynomial)
**3. Decidable computation:** `native_decide` for all proofs
**4. Computable types:** SparsePoly, TL_elt all decidable
**5. No implementation details:** Let Aristotle design algorithm
**6. Iterative refinement:** Aristotle evolved v4→v5→v6→v7 autonomously

### Application to HOMFLY-PT

**Recommended approach:**

```
PROBLEM STATEMENT (Minimal Version)
────────────────────────────────────────────────────────────────

Implement a computable HOMFLY-PT polynomial algorithm and verify
that HOMFLY-PT ≠ 1 for the following knots:

Knot 1 (Trefoil): [1, 1, 1]
Knot 2 (Figure-eight): [1, 2, 1, 2]
Knot 3 (Cinquefoil): [1, 1, 1, 1, 1]
...
Knot 10: [1, 2, 3, 1, 2, 3, 1, 2]

Prove for each knot: homfly_pt_norm(knot) ≠ [(0, 0, 1)]

Use native_decide for all proofs.

────────────────────────────────────────────────────────────────
```

**Expected outcome:**
- Aristotle implements bivariate polynomial arithmetic
- Aristotle applies skein relation recursively
- Aristotle adds fuel for termination
- Aristotle normalizes aggressively (after 1-2 failed versions)
- Aristotle proves all theorems via `native_decide`

**Confidence level:** HIGH (80%+)

**Why:** Jones polynomial success demonstrates:
- Aristotle can handle complex polynomial invariants
- Aristotle iterates algorithmically (v4→v7 shows learning)
- `native_decide` scales to 25 crossings (HOMFLY-PT at 15-20 should work)
- Certificate-based verification is robust

---

## 9. Specific HOMFLY-PT Adaptations

### Data Structures

**Bivariate Laurent Polynomial:**

```lean
abbrev BivariatePoly := List (Int × Int × Int)  -- (a_power, z_power, coeff)
```

**Operations needed:**
- `add`, `mul`, `normalize` (similar to SparsePoly)
- `div_bivariate` (if normalization requires division)
- `power` (for loop factors)

**Skein relation implementation:**

```lean
def homfly_pt_skein (fuel : Nat) (knot : BraidWord) : BivariatePoly :=
  match fuel with
  | 0 => [(0, 0, 0)] -- Should not happen
  | fuel + 1 =>
    match knot with
    | [] => [(0, 0, 1)] -- Unknot: P = 1
    | op :: rest =>
      -- a * P(L+) - a^(-1) * P(L-) = z * P(L0)
      -- P(L+) = (a^(-1) * z * P(L0) + P(L-)) / a
      -- But this requires knowing L0 and L-
      -- Better: use oriented skein relation based on crossing sign
      if op > 0 then
        -- Positive crossing: a * P(this) = a^(-2) * P(L-) + z * P(L0)
        let p_minus := homfly_pt_skein fuel (flip_crossing 0 knot)
        let p_zero := homfly_pt_skein fuel (smooth_crossing 0 knot)
        BivariatePoly.add
          (BivariatePoly.mul_a_power p_minus (-2))
          (BivariatePoly.mul_z_power p_zero 1)
      else
        -- Negative crossing: a^(-1) * P(this) = a^2 * P(L+) + z * P(L0)
        ...
```

**Normalization:**
- HOMFLY-PT has similar normalization as Jones
- May need to multiply by `a^(-w(L))` where w is writhe
- Aristotle should figure this out (it did for Jones)

### Test Suite (10 knots, 3-15 crossings)

```lean
def homfly_test_01 : BraidWord := [1, 1, 1]                    -- Trefoil (3 crossings)
def homfly_test_02 : BraidWord := [1, 2, 1, 2]                 -- Figure-8 (4 crossings)
def homfly_test_03 : BraidWord := [1, 1, 1, 1, 1]              -- Cinquefoil (5 crossings)
def homfly_test_04 : BraidWord := [1, 2, 1, 2, 1, 2]           -- 6-crossing torus
def homfly_test_05 : BraidWord := [1, 1, 1, 1, 1, 1, 1]        -- 7-crossing torus
def homfly_test_06 : BraidWord := [1, 2, -1, -2, 1, 2, -1, -2] -- 8-crossing alternating
def homfly_test_07 : BraidWord := [1, 2, 1, 2, 1, 2, 1, 2, 1, 2] -- 10-crossing
def homfly_test_08 : BraidWord := [1, 2, 3, 1, 2, 3, 1, 2, 3]  -- 9-crossing (4-strand)
def homfly_test_09 : BraidWord := [1, 2, 1, 2, -1, -2, 1, 2, 1, 2] -- 10-crossing complex
def homfly_test_10 : BraidWord := [1, 2, 3, -1, -2, -3, 1, 2, 3, -1, -2, -3] -- 12-crossing
```

### Theorems to Prove

```lean
theorem homfly_neq_one_test_01 : homfly_pt_norm homfly_test_01 ≠ [(0, 0, 1)] := by native_decide
theorem homfly_neq_one_test_02 : homfly_pt_norm homfly_test_02 ≠ [(0, 0, 1)] := by native_decide
...
theorem homfly_neq_one_test_10 : homfly_pt_norm homfly_test_10 ≠ [(0, 0, 1)] := by native_decide
```

---

## 10. Predicted Timeline & Success Probability

### Based on Jones Experience

**Jones timeline:**
- Submission: Unknown (likely same day as completion)
- Completion: Same day (Aristotle projects typically 30min-5h)
- Versions: 4 (v4, v5, v6, v7)
- Result: 618 lines, 20 theorems, 0 sorries, 100% success

**HOMFLY-PT prediction:**

**Optimistic (50% probability):**
- First attempt succeeds with 3-4 algorithm versions
- 10 knots proven in single run
- Timeline: 1-5 hours
- Result: 400-600 lines, 10 theorems, 0 sorries

**Realistic (30% probability):**
- First attempt partially succeeds (5-7 knots proven)
- Second attempt with refined knot set completes
- Timeline: 2 attempts, 3-8 hours total
- Result: 500-700 lines, 10 theorems total, 0 sorries

**Pessimistic (15% probability):**
- First attempt fails (timeout or incomplete)
- Second attempt with simplified problem succeeds
- Timeline: 2-3 attempts, 6-12 hours total
- Result: 300-500 lines, 5-8 theorems, 0 sorries

**Failure (5% probability):**
- Bivariate polynomial arithmetic too complex
- Skein relation recursion depth too large
- Aristotle times out or produces partial proof
- Fallback: Manual Lean implementation needed

### Success Probability Breakdown

| Outcome | Probability | Reasoning |
|---------|------------|-----------|
| **Full success (10 knots)** | 60% | Jones succeeded at 25 crossings; HOMFLY-PT at 15 crossings should be easier |
| **Partial success (5-9 knots)** | 25% | Some knots may be too complex; need refinement |
| **Minimal success (1-4 knots)** | 10% | Bivariate arithmetic harder than univariate; may need simpler test cases |
| **Failure (0 knots)** | 5% | Unlikely given Jones success; but HOMFLY-PT is more complex |

**Overall confidence:** 85% that HOMFLY-PT verification will succeed to some degree

**Recommendation:** Proceed with HOMFLY-PT attempt. Success patterns strongly suggest viability.

---

## 11. Key Takeaways (TL;DR)

### What Made Jones Successful

1. **Certificate-based verification** (prove ≠ 1, not compute full polynomial)
2. **Complete inline data** (20 knots provided)
3. **Decidable computation** (native_decide for all proofs)
4. **Autonomous algorithm design** (Aristotle iterated v4→v7)
5. **Fuel-based termination** (ensures decidability)
6. **Aggressive normalization** (v7: normalize after every operation)
7. **Sparse data structures** (List-based for decidability)
8. **Simple instruction style** (minimal, trust Aristotle to iterate)

### Apply to HOMFLY-PT

1. ✅ Prove `HOMFLY-PT ≠ 1` (not full polynomial)
2. ✅ Provide 10 knots inline (3-15 crossings)
3. ✅ Use `native_decide` for proofs
4. ✅ Let Aristotle design algorithm (expect 3-4 versions)
5. ✅ Anticipate fuel-based skein recursion
6. ✅ Expect aggressive normalization in final version
7. ✅ Use `List (Int × Int × Int)` for bivariate polynomials
8. ✅ Minimal instructions, let Aristotle iterate

### Confidence

**HIGH (80%+)** that HOMFLY-PT verification will succeed based on Jones polynomial success patterns.

**Proceed with submission.**

---

**Date**: 2025-12-12
**Analyst**: Claude (claude-code)
**Next Step**: Prepare HOMFLY-PT problem statement and submit to Aristotle
