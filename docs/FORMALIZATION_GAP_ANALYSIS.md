# Formalization Gap Analysis

## The Key Insight

Boris's success on #124 came from a **formalization gap** - the Lean statement was accidentally weaker than Erdős intended.

This suggests we should look for problems where:
1. The Formal Conjectures Lean statement differs from the original English
2. Erdős omitted hypotheses that Lean forces to be explicit
3. Quantifiers or edge cases differ between versions

---

## How to Find Formalization Gaps

### Step 1: Get Both Versions
- **English**: erdosproblems.com original statement
- **Lean**: Formal Conjectures .lean file

### Step 2: Compare Carefully

| Check | What to Look For |
|-------|------------------|
| **Quantifiers** | ∀ vs ∃, order differences |
| **Hypotheses** | Missing conditions in one version |
| **Edge cases** | n=0, n=1, empty set handling |
| **Types** | ℕ vs ℤ vs ℝ, finite vs infinite |
| **Definitions** | Does Lean definition match intent? |

### Step 3: Evaluate the Gap

**Promising gaps**:
- Lean is weaker (easier to prove)
- Known Mathlib lemmas might apply to Lean version
- The Lean statement is still mathematically interesting

**Unpromising gaps**:
- Lean is stronger (harder to prove)
- Gap is just a typo/error to be fixed
- Lean statement is trivially true/false

---

## Example: Erdős #124

**English** (from Erdős 1997):
> Is it true that if A is a complete sequence, then A ∪ {n} is complete for all sufficiently large n?

**What Erdős meant** (from BEGL96 paper):
> Additional hypothesis about the structure of A

**What Lean said**:
> [Weaker statement without the additional hypothesis]

**Result**: Brown's criterion (in Mathlib) directly implies the Lean statement!

---

## Candidate Problems for Gap Analysis

Priority problems to analyze for formalization gaps:

### From solvable_open.json (high tractability score + open)

1. **#141** - Consecutive primes in AP
2. **#931** - Same prime factors in products
3. **#313** - Primary pseudoperfect numbers
4. **#730** - Central binomial prime factors
5. **#1052** - Unitary perfect numbers
6. **#686** - Ratio of consecutive products
7. **#434** - Maximizing unrepresentable sums

### Analysis Template

For each problem:

```
## Problem #XXX

### English Statement (erdosproblems.com)
[paste]

### Lean Statement (Formal Conjectures)
[paste]

### Potential Gaps
- [ ] Quantifier differences
- [ ] Missing hypotheses
- [ ] Edge case handling
- [ ] Type differences
- [ ] Definition mismatches

### Relevant Mathlib
[What existing lemmas might apply?]

### Assessment
[ ] Strong gap candidate
[ ] Weak gap candidate
[ ] No meaningful gap

### Notes
[Analysis]
```

---

## Workflow Integration

This analysis should happen in **Phase 1: Problem Discovery** before submission.

The question is NOT "is this problem solvable?" but rather:
**"Is THIS FORMALIZATION accidentally tractable?"**
