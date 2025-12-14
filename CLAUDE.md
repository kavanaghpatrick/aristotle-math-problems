# CLAUDE.md - Math Project

## Mental Model

Aristotle recombines Mathlib tactics. It doesn't invent new math.

Only attack problems where the proof can be assembled from existing pieces.

---

## The Workflow

When user says "run the workflow on X problem":

### Phase 1: Feasibility (10 min)

**Step 1.1: Red Flag Scan**

Instant NO-GO if ANY present:
- Non-constructive (Axiom of Choice, Zorn's Lemma)
- Asymptotic ("for sufficiently large n", limits, big-O)
- Massive case analysis (>20 cases)
- Ambiguous terms ("optimal", "efficient", "best")
- Missing bounds (no explicit n>1, Nonempty)
- Calculation-heavy ("find the value" vs "prove X=5")
- No finisher tactics (domain lacks ring/linarith/decide)
- Unformalized prerequisites

**Step 1.2: Score (if no red flags)**

| Criterion | Question | Score 0-2 |
|-----------|----------|-----------|
| **Mathlib** | Definitions exist? Related lemmas? Domain mature? | /6 |
| **Progress** | Human proof outline? Partial Lean? Known cases? | /6 |
| **Complexity** | Short proof? Constructive? Few dependencies? | /6 |
| **Exploration** | Multiple approaches? Subproblems? | /4 |
| **Rigidity** | 1:1 English→Lean? Degeneracy excluded? | /4 |

**Decision**: ≥17 GO, 14-16 check green flags, <14 NO-GO

---

### Phase 2: Formalization (if GO)

**Step 2.1: Find or Create Lean Statement**

First, check Formal Conjectures: https://github.com/google-deepmind/formal-conjectures

If not found:
```
Create explicit Lean theorem with:
- Locked quantifier order (∀M, ∃N, ∀n>N, ...)
- Explicit bounds (n > 1, Nonempty, etc.)
- No ambiguous terms
```

**Step 2.2: Verify Formalization**

Ask Grok/Gemini:
```
Original problem: [paste]
Lean statement: [paste]

Does this EXACTLY match? Check quantifiers, hypotheses, conclusion.
```

Must get confirmation before proceeding.

---

### Phase 3: Submit

**Step 3.1: Create Submission File**

```lean
-- LOCKED - DO NOT MODIFY
import Mathlib

theorem [name] : [exact_statement] := by
  sorry
```

**Step 3.2: Submit to Aristotle**

```bash
aristotle prove-from-file problem.lean --no-wait
```

Record project ID.

---

### Phase 4: Verify Output (when complete)

**Step 4.1: Check for False Positives**

```
□ Does output have 0 sorries?
□ Does it compile?
□ Is the PROVEN theorem the same as SUBMITTED theorem?
□ Did AI add restrictive hypotheses?
□ Did AI prove ∃ instead of ∀?
□ Did AI just define statement without proving it?
```

If any mismatch → go to Phase 5 with "exploration drift" diagnosis.

**Step 4.2: Count Holes**

Count `exact?` and `sorry` occurrences. Record hole count.

---

### Phase 5: Iterate or Abort

**Decision Tree:**

```
0 holes + exact match → SUCCESS ✓
1-3 holes → Iterate (Phase 5.1)
>3 holes → Check iteration count
  - Iteration 1-2 → Iterate (Phase 5.1)
  - Iteration 3+ → Pivot to sub-problem (Phase 5.2)
Exploration drift → Resubmit with stricter lock (Phase 5.3)
```

**Step 5.1: Iterate on Holes**

Create resubmission:
```
Complete this proof. Fill the holes at lines [X, Y, Z].

[paste full output from previous iteration]

Constraints:
- Do not modify theorem statement
- Focus only on filling holes
- Use tactics: simp, rw, exact, linarith
```

Submit. Return to Phase 4.

**Step 5.2: Pivot to Sub-Problem**

If stuck after 2 iterations:
```
Instead of full theorem, prove:
[weaker version with smaller parameters]
e.g., "Prove for n ≤ 5" instead of "Prove for all n"
```

Return to Phase 2.

**Step 5.3: Fix Exploration Drift**

If AI explored instead of proving:
```
Your ONLY task is to prove this EXACT theorem:

[paste locked theorem statement]

Do NOT:
- Define the statement as a Prop
- Explore examples
- Prove related but different theorems
- Add hypotheses

DO:
- Fill the proof body with tactics
- Use sorry if stuck, explain why
```

Return to Phase 3.

---

### Phase 6: Record Outcome

| Field | Value |
|-------|-------|
| Problem | |
| Project ID | |
| Iterations | |
| Final Holes | |
| Outcome | SUCCESS / PARTIAL / ABORT |
| Notes | |

---

## Metrics to Track

- **Hole reduction rate**: Target 50% per iteration
- **Iteration count**: Most should complete in 1-3
- **Success rate**: If <20% after 10 problems, pivot strategy

---

## Resource Allocation

| Category | % | Focus |
|----------|---|-------|
| Iteration on near-wins | 70% | Finish what's close |
| New tractable problems | 20% | Problems passing filter |
| Moonshots | 10% | Expect failure |
