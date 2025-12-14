# Operational Strategy

Distilled from Grok's analysis of 12 failed submissions.

---

## Resource Allocation

| Category | % | Description |
|----------|---|-------------|
| Iteration on near-wins | 70% | Tuza (2 holes), #593 (1 hole), #152 (2 holes) |
| New tractable problems | 20% | Problems passing feasibility filter |
| Moonshots | 10% | Hard open problems (expect failure) |

---

## The Ladder Approach

Don't jump straight to open problems. Build a progression:

```
Level 1: Formalize KNOWN results (training wheels)
    ↓
Level 2: Prove KNOWN cases of open conjectures (e.g., Tuza for ν≤2)
    ↓
Level 3: Extend to OPEN variants (the actual goal)
```

**Why**: Each level builds Mathlib infrastructure and "trains" your process on success patterns.

---

## Iteration Protocol

### Structure: 3-5 Short Runs > 1 Long Run

| Iteration | Goal | Duration |
|-----------|------|----------|
| 1 | Build infrastructure, identify holes | 1-2 hours |
| 2 | Fill holes from iteration 1 | 1-2 hours |
| 3 | Strengthen lemmas, close remaining | 1-2 hours |
| 4+ | Generalize if needed | As needed |

### Hole Reduction Target

**Aim for 50% reduction per iteration.**

| Iteration | Holes | Target |
|-----------|-------|--------|
| 1 | 8 | - |
| 2 | 4 | 50% reduction |
| 3 | 2 | 50% reduction |
| 4 | 0-1 | Complete or manual |

### Abort Threshold

**If >3 holes remain after 2 iterations → Pivot to sub-conjecture.**

Example: Tuza full conjecture stuck? Prove τ ≤ 2ν for ν ≤ 3 instead.

---

## Success Metrics (Reframed)

Stop measuring only "complete proofs of open problems."

| Metric | What Counts |
|--------|-------------|
| **Complete proof** | Full theorem, 0 sorries |
| **Near-complete** | <3 holes, structure correct |
| **Key lemma** | Novel supporting result |
| **Counterexample** | Evidence conjecture is false |
| **Infrastructure** | Useful definitions/machinery |

**Track**: Lines proven, hole count per iteration, novel lemmas created.

---

## Submission Format (Structured)

```
HEADER:
Goal: Prove [exact Lean theorem]. Output complete proof file.
If stuck, mark with 'sorry' and explain why.

SCAFFOLDING:
Section 1: Definitions (import existing where possible)
Section 2: Supporting lemmas (prove at least 3-5)
Section 3: Main proof (use induction/cases/...)

CONSTRAINTS:
- Focus exclusively on the theorem
- No exploration unless it closes a gap
- Do not assume unproven statements
- Prioritize closing exact? with simp, rw, exact

HINTS:
- import Mathlib.X.Y.Z
- Relevant lemmas: lemma_a, lemma_b
- Suggested approach: [induction on n / cases on structure / ...]

LENGTH: Target 300-400 lines
```

---

## Tool Diversification

Don't rely solely on Aristotle.

| Tool | Use Case |
|------|----------|
| **Aristotle** | Primary prover |
| **LeanCopilot** | Tactic suggestions for stuck holes |
| **Manual** | Fill trivial exact? before resubmission |
| **Crowdsource** | Post stubborn holes to Lean Zulip |

---

## Reality Check Protocol

After 10 more submissions:

| Success Rate | Action |
|--------------|--------|
| >50% | Strategy working, continue |
| 20-50% | Refine, focus on what works |
| <20% | **Abandon open Erdős problems** |

If abandoning, redirect to:
- Formalizing undergrad theorems
- AI-assisted conjecture generation
- Building Mathlib infrastructure

---

## Immediate Actions

### This Week
1. **Iterate on Tuza** - Resubmit 502 lines, target holes at 457, 493
2. **Iterate on #593** - Single hole at line 167
3. **Iterate on #152** - 2 holes, solid infrastructure

### This Month
4. Apply feasibility filter to 10 candidate problems
5. Submit 5 that pass (≥17 score)
6. Track hole reduction metrics

### Decision Point (After 10 Submissions)
7. Calculate success rate
8. If <20%, pivot strategy entirely
