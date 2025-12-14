# Aristotle Feasibility Filter

**Time to complete**: 10 minutes per problem
**Purpose**: Decide GO/NO-GO before wasting submission slots

---

## Quick Decision Tree

```
1. Check RED FLAGS → Any present? → INSTANT NO-GO
2. Score 4 criteria (0-2 each sub-question)
3. Total ≥ 14? → GO
4. Total 12-13? → Check GREEN FLAGS → If present → GO
5. Total < 12? → NO-GO
```

---

## RED FLAGS (Instant NO-GO)

Stop immediately if ANY of these apply:

### Structural Red Flags
- [ ] **Non-constructive core** - Relies on Axiom of Choice, Zorn's Lemma, excluded middle for existence
- [ ] **Unformalized prerequisites** - Key concept not in Mathlib (search mathlib4 docs)
- [ ] **Massive case analysis** - Proof requires >20 distinct cases
- [ ] **Asymptotic/limiting** - Statement involves limits, big-O, or "for sufficiently large n"
- [ ] **Tagged as hard** - Lean Zulip shows "stuck" or "open" with no progress
- [ ] **Requires novel insight** - No known proof strategy exists

### "Hostile Contractor" Red Flags (AI will exploit these)
- [ ] **Ambiguous terms** - "Optimal", "efficient", "best", "standard" → AI picks weakest interpretation
- [ ] **Missing degeneracy guards** - No explicit n>1, Nonempty, or non-trivial constraints
- [ ] **Calculation-heavy** - "Find the value" instead of "Prove X = 5"
- [ ] **No finisher tactics** - Domain lacks ring/linarith/decide automation
- [ ] **Long statement** - Requires >15 lines just to state the theorem
- [ ] **New structures needed** - Must define new Type/Class before stating problem

---

## Scoring Rubric

### Criterion 1: Mathlib Alignment (max 6)

**Where to look**: https://leanprover-community.github.io/mathlib4_docs/

| Question | 0 | 1 | 2 |
|----------|---|---|---|
| Are main definitions in Mathlib? | Not found | Partial | Yes, directly |
| Related lemmas cover 50%+ of proof? | None | Indirect helpers | Direct coverage |
| Domain well-represented? | Niche/new | Emerging | Mature (algebra, NT) |

**Score**: ___ / 6

### Criterion 2: Partial Human Progress (max 6)

**Where to look**: Wikipedia, Math Stack Exchange, arXiv, Lean Zulip

| Question | 0 | 1 | 2 |
|----------|---|---|---|
| Human proof outline available? | None | Hints only | Step-by-step |
| Partial Lean formalization exists? | Silent | Vague mentions | 50%+ done |
| Special cases already proven? | Isolated | Analogous exists | Base case in Mathlib |

**Score**: ___ / 6

### Criterion 3: Low Complexity (max 6)

**Where to look**: Read the problem statement, check proof length

| Question | 0 | 1 | 2 |
|----------|---|---|---|
| Short proof (<15 human steps)? | Long chains | Moderate | Simple |
| Constructive (builds object)? | Pure existence | Semi | Explicit construction |
| Low dependencies (<5 lemmas)? | Heavy prereqs | Some imports | Self-contained |

**Score**: ___ / 6

### Criterion 4: Exploration Potential (max 4)

**Where to look**: Multiple proof strategies, generalizations

| Question | 0 | 1 | 2 |
|----------|---|---|---|
| Multiple proof approaches? | Single rigid | One variant | Several paths |
| Explorable subproblems? | Standalone | Minor variants | Rich generalizations |

**Score**: ___ / 4

### Criterion 5: Statement Rigidity (max 4) - HOSTILE CONTRACTOR CHECK

**Purpose**: Can the AI find a cheaper interpretation?

| Question | 0 | 1 | 2 |
|----------|---|---|---|
| 1:1 English→Lean mapping? | Ambiguous terms | Some interpretation | Direct translation |
| Degeneracy excluded? | No guards | Implicit | Explicit (n>1, Nonempty) |

**Score**: ___ / 4

---

## Total Score

| Criterion | Score |
|-----------|-------|
| Mathlib Alignment | ___ / 6 |
| Partial Progress | ___ / 6 |
| Low Complexity | ___ / 6 |
| Exploration Potential | ___ / 4 |
| Statement Rigidity | ___ / 4 |
| **TOTAL** | ___ / 26 |

### Decision

- **≥ 20**: Strong GO
- **17-19**: GO
- **14-16**: Check Green Flags
- **< 14**: NO-GO

---

## GREEN FLAGS (Can upgrade 12-13 to GO)

- [ ] Recent Mathlib addition (last 6 months) for key lemma
- [ ] Similar problem already proven by Aristotle
- [ ] Tactic-friendly (induction, simp, decide work)
- [ ] Active Zulip discussion with positive progress
- [ ] Problem is from Formal Conjectures (pre-formalized)

---

## 10-Minute Assessment Protocol

### Minutes 1-3: Gather Inputs
```bash
# Search Mathlib
open "https://leanprover-community.github.io/mathlib4_docs/" # search key terms

# Search Zulip
open "https://leanprover.zulipchat.com/" # search problem name

# Search human proofs
open "https://math.stackexchange.com/" # search theorem name
```

### Minutes 4-8: Score Rubric
- Fill in each criterion score
- Note evidence for each

### Minutes 9-10: Check Flags & Decide
- Scan RED FLAGS (any = NO-GO)
- If borderline, check GREEN FLAGS
- Record decision with justification

---

## Example: Tuza's Conjecture (τ ≤ 2ν)

### Red Flags: None found

### Scores:
- **Mathlib Alignment**: 4/6 (SimpleGraph exists, some covering lemmas, graph theory maturing)
- **Partial Progress**: 5/6 (Known cases ν≤2, Zulip discussions, partial formalizations)
- **Low Complexity**: 4/6 (Case-based but not huge, semi-constructive, moderate deps)
- **Exploration**: 3/4 (Multiple approaches: LP, local, probabilistic)
- **Statement Rigidity**: 4/4 (Clean definitions: τ = min covering, ν = max packing, no ambiguity)

### Total: 20/26 → **Strong GO**

---

## Example: Van der Waerden W(3,k) bounds

### Red Flags:
- [x] **Asymptotic** - Statement is about growth rates
- [x] **Massive case analysis** - Known proofs use huge computations

### Decision: **INSTANT NO-GO** (Red flags present)

---

## Example: Erdős #153 (Average Squared Gap)

### Red Flags:
- [x] **Ambiguous terms** - "average squared gap → ∞" can mean ∃ family OR ∀ sets
- [x] **Missing degeneracy guards** - What if A is empty? Single element?

### What Happened:
AI proved "there EXISTS a Sidon family where gaps grow" instead of "for ALL Sidon sets"

### Lesson: This would have failed **Statement Rigidity** criterion
- 1:1 mapping? 0/2 (∃ vs ∀ ambiguity)
- Degeneracy excluded? 1/2 (implicit only)
- Score: 1/4 → RED FLAG territory

---

## After Submission: Iterate or Abandon?

| Result | Action |
|--------|--------|
| 0 sorries, compiles | Verify theorem matches intent |
| 1-3 holes | Iterate: resubmit with hole-filling prompt |
| 4+ holes | Decompose into sub-problems |
| Timeout, little progress | Check if infrastructure built; if yes, continue; if no, abandon |
| Exploration drift | Resubmit with locked theorem statement |
