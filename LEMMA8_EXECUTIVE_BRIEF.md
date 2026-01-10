# Lemma 8 Executive Brief

**GitHub Issue**: #50
**Lemma**: apex_private_edge_covers_private_external
**Date**: 2026-01-03
**Reviewer**: Claude Code

---

## TL;DR

| Question | Answer | Confidence |
|----------|--------|------------|
| **Is it TRUE?** | ⚠️ Locally yes, globally NO | 85% |
| **Logical gap?** | YES - depends on false Lemma 3 | 95% |
| **Can Aristotle prove it?** | Maybe, but likely unsoundly | 60% |
| **Rating (1-5)** | **2/5** | 90% |
| **Should you attempt?** | **NO** | 95% |

---

## The Three Core Problems

### Problem 1: Depends on FALSE Lemma 3
The lemma assumes:
> "All externals of A that contain p also contain the fan apex x_A"

**This is FALSE** (proven by Pattern 6, Dec 29, 2025):
- Externals at shared vertex v_ab from A and B don't share a common external vertex
- Different externals use different M-edges, leading to different external vertices
- The "fan apex" is a myth for externals of a single M-element

### Problem 2: Underspecified Definition
What is a "private-type external"?
- If it means "externals using ONLY private edges of A": Still doesn't guarantee common apex
- If it means "any external containing p": Circular reasoning (some do, some don't)
- Issue statement is vague on this critical point

### Problem 3: Ineffective for τ ≤ 8
Even if TRUE, the lemma doesn't achieve the goal:
- Covers only one specific type of external
- Doesn't address externals from adjacent M-elements
- Doesn't reduce edge count below 12 without universal apex
- **Universal apex strategy is DEAD** (Pattern 6 disproved it)

---

## The Dependency Chain (All Broken)

```
Lemma 8 (apex_private_edge_covers_private_external)
    ↓
Lemma 3 (private_external_contains_apex) [UNPROVEN]
    ↓
fan_apex_exists [UNPROVEN]
    ↓
universal_apex_in_cycle4 [BLOCKED - line 127 `sorry`]
    ↓
τ_le_8_from_universal_apex [Can't work without universal apex]
    ↓
DEAD END - Pattern 6 counterexample shows external apexes differ
```

**Each step depends on the previous.** **All dependent on FALSE Lemma 3.**

---

## Proof Quality Assessment

### Local Logical Correctness: ✅ SOUND
```
If T is a triangle AND p ∈ T AND x_A ∈ T
Then s(p, x_A) ∈ T.sym2
```
This is trivially true. The statement is locally sound.

### Global Logical Correctness: ❌ UNSOUND
The lemma statement hides an assumption:
```
For ALL externals T of A with p ∈ T:
  MUST have x_A ∈ T
```
**This is unprovable** because Lemma 3 is false.

### Aristotle Proof Risk: 🟡 HIGH (60% chance of unsound proof)
**Why Aristotle might claim success**:
1. Accept Lemma 3 without verification (just `sorry` it)
2. Use proof-by-type-escape pattern (Pattern 14) to finalize
3. Output "PROVEN" header, burying `sorry` in proof text

**Why it would be unsound**:
- Lemma 3 contradicts Pattern 6 counterexample
- Proof chain is: assumption → assumption → trivial conclusion
- No actual verification of the hard part (Lemma 3)

---

## Why Pattern 6 Kills This Lemma

**Pattern 6 (Dec 29, 2025)**: `external_share_common_vertex` is FALSE

**Concrete counterexample**:
```
M = {A, B, C, D}
A = {0, 1, 2}
B = {0, 3, 4}

At shared vertex v_ab = 0:
  T₁ = {0, 1, 5}  -- uses A-edge {0,1}, external vertex is 5
  T₂ = {0, 3, 6}  -- uses B-edge {0,3}, external vertex is 6

  T₁ ∩ T₂ = {0}   -- only shared vertex, NO common edge!

Therefore: 5 ≠ 6, so externals don't share common external vertex.
```

**How this breaks Lemma 8**:
- The lemma assumes external vertex x_A is universal for all externals of A
- But at v_ab, externals from A and B coexist with different vertices
- Even restricting to "externals of A only", they don't cluster around one apex when adjacent M-elements are in play

---

## Specific Logical Gap: Question 2 from Issue

**Issue asks**: "Does triangle containing {p, x_A} have edge {p, x_A}?"

**Answer**: YES, trivially.

**But the REAL question should be**: "Do ALL externals of A containing p also contain x_A?"

**Answer**: NO.

**Why the issue's question is too weak**:
- It only asks about the consequence, not the premise
- The hard part is proving x_A ∈ T, not proving s(p,x_A) ∈ T.sym2
- Once x_A ∈ T is established, the rest is bookkeeping

---

## Recommendations

### DO NOT ATTEMPT THIS LEMMA

**Because**:
1. Lemma 3 (its prerequisite) is FALSE
2. Pattern 6 (Dec 29) explicitly disproves the fan apex framework
3. Even if provable, it doesn't advance τ ≤ 8
4. High risk of Aristotle producing unsound proof

### INSTEAD, FOCUS ON:

1. **Resolve the universal apex question** (slot185):
   - Can you prove ALL externals of cycle_4 share a single external vertex?
   - Or is Pattern 6 a total blocker?
   - **This is the CRITICAL QUESTION** - currently blocked at line 127

2. **Accept τ ≤ 12 as intermediate result**:
   - 3 edges per shared vertex (one per M-element + externals)
   - Already proven in slot113 or earlier
   - Gives lower bound while pursuing τ ≤ 8

3. **Explore non-spoke covers**:
   - Pattern 6 shows externals don't cluster by apex
   - Try covering by M-edge usage instead
   - May lead to different bound

---

## Confidence Breakdown

| Component | Confidence | Source |
|-----------|-----------|--------|
| Lemma 3 is false | 95% | Pattern 6 counterexample (Aristotle-verified) |
| Pattern 6 blocks universal apex | 90% | Dec 29, 2025 AI-verified |
| Lemma 8 locally sound | 99% | Basic logic |
| Lemma 8 globally unsound | 85% | Depends on false Lemma 3 |
| Aristotle might falsely "prove" it | 60% | Pattern 14 proof-by-type-escape risk |
| Should not attempt | 95% | Risk/reward analysis |

---

## Final Rating: 2/5

- ✅ **Local correctness** (+1): Statement is sound given assumptions
- ❌ **Global soundness** (-1.5): Assumptions are false
- ✅ **Proof mechanics** (+0.5): Trivial if premises work
- ❌ **Strategic value** (-1): Doesn't advance τ ≤ 8
- ⚠️ **Execution risk** (-0.5): High chance of unsound Aristotle output

**Verdict**: A locally-sound but globally-broken lemma that doesn't advance the proof and risks creating unsound artifacts. **Skip entirely.**

---

## References

- GitHub Issue #50
- FALSE_LEMMAS.md: Pattern 6 (external_share_common_vertex) - CRITICAL
- FALSE_LEMMAS.md: Pattern 14 (proof_by_type_escape) - CRITICAL
- FALSE_LEMMAS.md: Pattern 16 (helly_three_triangles) - related
- Slot185: universal_apex_in_cycle4 (the REAL blocker)
- Slot186: direct_8edge_cover (alternative approach)

---
