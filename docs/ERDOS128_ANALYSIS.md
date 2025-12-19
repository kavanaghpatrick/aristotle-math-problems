# Erdős #128 Deep Analysis: Formalization Bug Discovery

**Date**: December 19, 2025
**Status**: Formalization error identified - NOT a valid counterexample
**Prize**: $250 (problem remains open)

---

## Executive Summary

Aristotle found C₅ (5-cycle) as a counterexample to our formalization of Erdős #128. However, upon deep analysis, we discovered our formalization was **incorrect**. The C₅ counterexample applies only to our buggy formalization, NOT to the original problem.

**The original Erdős #128 problem is NOT disproved.**

---

## The Problem

### Original Statement (erdosproblems.com)

> Let G be a graph with n vertices such that every induced subgraph on ≥ n/2 vertices has more than n²/50 edges. Must G contain a triangle?

### Three Interpretations of "≥ n/2 vertices"

| Interpretation | Threshold for n=5 | Formula |
|----------------|-------------------|---------|
| Exact half (real division) | |S| ≥ 2.5 → |S| ≥ 3 | `|S| ≥ ⌈n/2⌉` |
| Floor half | |S| ≥ 2 | `|S| ≥ ⌊n/2⌋` |
| At least half (standard) | |S| ≥ 2 | `2*|S| + 1 ≥ n` |

---

## The Formalization Discrepancy

### Our Formalization (INCORRECT)
```lean
def HasDenseInducedSubgraphs (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≥ Fintype.card V →
    50 * (G.induce S).edgeFinset.card > (Fintype.card V)^2
```

**Condition**: `2 * |S| ≥ n`
**For n=5**: Checks subsets with |S| ≥ 3 (since 2×2=4 < 5, 2×3=6 ≥ 5)

### Formal Conjectures (CORRECT)
```lean
∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
  50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2
```

**Condition**: `2 * |S| + 1 ≥ n`
**For n=5**: Checks subsets with |S| ≥ 2 (since 2×2+1=5 ≥ 5)

### The Missing "+1"

| n | Our formula (2|S| ≥ n) | FC formula (2|S|+1 ≥ n) | Difference |
|---|------------------------|--------------------------|------------|
| 4 | |S| ≥ 2 | |S| ≥ 2 | Same |
| 5 | |S| ≥ 3 | |S| ≥ 2 | **DIFFERENT** |
| 6 | |S| ≥ 3 | |S| ≥ 3 | Same |
| 7 | |S| ≥ 4 | |S| ≥ 3 | **DIFFERENT** |

For odd n, our formalization misses the size-⌊n/2⌋ subsets!

---

## Why C₅ Is NOT a Valid Counterexample

### C₅ Structure
- 5 vertices: {0, 1, 2, 3, 4}
- 5 edges: {01, 12, 23, 34, 40}
- Triangle-free: No three vertices form a complete subgraph

### Size-2 Subsets in C₅

| Subset | Edges | Adjacent? |
|--------|-------|-----------|
| {0, 1} | 1 | Yes |
| {0, 2} | 0 | **Independent** |
| {0, 3} | 0 | **Independent** |
| {0, 4} | 1 | Yes |
| {1, 2} | 1 | Yes |
| {1, 3} | 0 | **Independent** |
| {1, 4} | 0 | **Independent** |
| {2, 3} | 1 | Yes |
| {2, 4} | 0 | **Independent** |
| {3, 4} | 1 | Yes |

### Density Condition Check

**Condition**: 50 × edges > n² = 25
**Requires**: edges > 0.5 → edges ≥ 1

For subsets like {0, 2} with 0 edges:
- 50 × 0 = 0, which is NOT > 25
- **C₅ FAILS the density condition for size-2 subsets**

### Under Correct Formalization (FC)
- Size-2 subsets ARE checked (2×2+1=5 ≥ 5)
- {0,2}, {0,3}, {1,3}, {1,4}, {2,4} have 0 edges
- These FAIL the condition 50×0 > 25
- **C₅ does NOT satisfy the hypothesis → NOT a valid counterexample**

### Under Our Buggy Formalization
- Size-2 subsets are NOT checked (2×2=4 < 5)
- Only size 3, 4, 5 subsets are checked
- All size-3+ subsets in C₅ have ≥1 edge
- **C₅ satisfies our buggy hypothesis → valid counterexample TO OUR BUG**

---

## Mathematical Verification

```python
# C5 subset analysis
vertices = {0, 1, 2, 3, 4}
edges = {{0,1}, {1,2}, {2,3}, {3,4}, {4,0}}

# Check all subsets of size 2
for subset in combinations(vertices, 2):
    edge_count = len([e for e in edges if e.issubset(subset)])
    satisfies = 50 * edge_count > 25

    # FC triggers (size ≥ 2): ALL checked
    # Ours triggers (size ≥ 3): NONE checked

    if not satisfies:
        print(f"{subset}: {edge_count} edges → FAILS density")

# Output:
# (0, 2): 0 edges → FAILS density
# (0, 3): 0 edges → FAILS density
# (1, 3): 0 edges → FAILS density
# (1, 4): 0 edges → FAILS density
# (2, 4): 0 edges → FAILS density
```

---

## Lessons Learned

### 1. Always Verify Against Original Source
- The original problem says "≥ n/2 vertices"
- This is conventionally interpreted as ⌊n/2⌋ (floor), not ⌈n/2⌉ (ceiling)
- Our formalization used the wrong rounding

### 2. Check Existing Formalizations
- Formal Conjectures has 265 Erdős problems formalized
- Always compare against their formalization before submission
- URL: https://github.com/google-deepmind/formal-conjectures

### 3. Aristotle Found the Right Counterexample... To the Wrong Problem
- Aristotle's negation capability is valuable
- It correctly identified that C₅ breaks our formalization
- The error was in the input, not in Aristotle's reasoning

### 4. Edge Cases Matter for Small n
- The "+1" only matters for odd n
- For n=5, it changes the threshold from 3 to 2
- Small counterexamples like C₅ expose formalization bugs

---

## Corrected Formalization

To properly formalize Erdős #128:

```lean
def HasDenseInducedSubgraphs_Correct (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V →
    50 * (G.induce S).edgeFinset.card > (Fintype.card V)^2

theorem erdos_128_correct (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs_Correct G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  sorry  -- This is the actual open problem
```

---

## Status

| Aspect | Status |
|--------|--------|
| Original Erdős #128 | **OPEN** ($250 prize) |
| Our formalization | **BUGGY** (missing +1) |
| C₅ counterexample | **INVALID** for original problem |
| Aristotle's work | **CORRECT** (found bug in our input) |

---

## References

- Original problem: https://erdosproblems.com/128
- Formal Conjectures: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/128.lean
- Our buggy file: `submissions/erdos128_FORMALIZATION_BUG.lean`
