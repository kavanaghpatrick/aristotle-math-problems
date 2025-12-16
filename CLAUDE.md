# CLAUDE.md - Math Project

## Mental Model: What Aristotle Actually Is

Aristotle (by Harmonic) is a **200B+ parameter system** combining:
- **Monte Carlo Graph Search** over Lean proof states
- **Informal reasoning** - generates natural language proofs FIRST, then formalizes
- **Iterative error feedback** - learns from Lean verification errors
- **Massive parallel search** - explores hundreds of millions of strategies

**It CAN discover unexpected connections.** It found 4 counterexamples in Terence Tao's textbook.

**Runtime: 6+ hours per problem is normal.** Boris submitted, went to bed, woke up to success.

---

## The Boris Pattern: What Actually Worked

Boris Alexeev's success on Erdős #124 came from:

1. **Formalization gap** - The Lean statement was accidentally weaker than Erdős intended
2. **Olympiad-style proof** - Aristotle found elegant solution, not brute force
3. **Existing result applied** - Brown's criterion (in Mathlib) unexpectedly connected
4. **Minimal intervention** - Submit, wait 6 hours, check result

**Key insight**: Success came from the formalization being *accidentally tractable*, NOT from targeting "already solved" problems.

---

## Problem Selection: What to Look For

### High-Value Signals

| Signal | Why It Matters |
|--------|----------------|
| **Formalization might be weaker** | Erdős often omitted hypotheses; Lean forces explicitness |
| **Olympiad-style tractable** | Aristotle excels at elegant proofs |
| **Existing Mathlib might connect** | Unexpected applications of known results |
| **Finite/decidable structure** | Can verify specific instances |
| **Low prize / obscure** | Less attention = potential gaps missed |

### Neutral (Not Automatic Filters)

| Factor | Reality |
|--------|---------|
| Asymptotics | Depends on formalization - not automatic NO |
| "Open" status | Boris solved an "open" problem |
| Complex domain | Aristotle has deep search capability |

### Low-Value Signals

| Signal | Why |
|--------|-----|
| Already SOLVED variants | We're trying to SOLVE, not formalize |
| Famous hard problems | Extensively studied, unlikely gaps |
| High prize ($1000+) | Serious mathematicians have tried |

---

## Workflow

### Phase 1: Problem Discovery

**Goal**: Find problems where formalization might be accidentally tractable.

1. **Check Formal Conjectures repo** for pre-formalized statements
2. **Read the original problem** on erdosproblems.com
3. **Compare Lean to English** - look for:
   - Missing hypotheses in one or the other
   - Quantifier differences
   - Edge cases not handled
4. **Check related Mathlib** - what theorems exist nearby?

**Key Question**: Could an existing Mathlib result unexpectedly apply to this formalization?

### Phase 2: Formalization Analysis

**DO NOT** try to make formalization "exactly match" - that's backwards!

Instead, analyze:
- What does the Lean statement actually claim?
- Is it potentially weaker than the mathematical problem?
- What Mathlib lemmas are in the neighborhood?
- Would proving this Lean statement be interesting even if weaker?

### Phase 3: Submit and Wait

```bash
aristotle prove-from-file problem.lean --no-wait
```

**Expectations**:
- Runtime: 6+ hours normal
- Submit multiple problems in parallel
- Don't babysit - check results next day

### Phase 4: Analyze Results

**If SUCCESS**:
- Verify the proven theorem matches submission
- Check if it's the "real" problem or a weaker variant
- Understand WHY it worked (for future selection)

**If FAILURE**:
- Did Aristotle make partial progress?
- Was there a specific sticking point?
- Is there a weaker variant worth trying?

---

## Submission Strategy

### Parallel Portfolio Approach

| Category | Allocation | Rationale |
|----------|------------|-----------|
| **Formalization gap candidates** | 50% | Highest expected value |
| **Olympiad-style problems** | 30% | Aristotle's strength |
| **True moonshots** | 20% | Discovery potential |

### Per-Problem Time Budget

- **Selection**: 15-30 minutes research per problem
- **Submission**: 5 minutes
- **Runtime**: 6-24 hours (hands-off)
- **Analysis**: 15 minutes per result

---

## What We Learned (Dec 2024)

### Wrong Assumptions We Had

| Assumption | Reality |
|------------|---------|
| "Recombines tactics" | 200B+ param system with informal reasoning |
| "Can't discover math" | Found counterexamples in Tao's textbook |
| "Target SOLVED variants" | Boris succeeded on formalization gap |
| "Iterate on near-wins" | Either solves or doesn't; iteration rarely helps |
| "Asymptotics = impossible" | Depends on specific formalization |

### What Actually Matters

1. **Formalization quality** - Is the Lean statement tractable?
2. **Mathlib coverage** - Do relevant lemmas exist?
3. **Patience** - Let it run for hours
4. **Volume** - Submit multiple problems in parallel

---

## Tools and Resources

### Key Resources
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) - Pre-formalized problems
- [erdosproblems.com](https://erdosproblems.com) - Original problem statements
- [Aristotle Paper](https://arxiv.org/abs/2510.01346) - System architecture

### Local Database
- `boris_scores.json` - All 261 Erdős problems scored
- `solvable_open.json` - Open problems ranked by tractability
- `submissions/` - Our submission files and results

### Scoring Script
```bash
python3 scripts/extract_solvable_open.py
```

---

## Grok for Lean Code Review

**Key**: Tell Grok to check CODE, not solve MATH (or it times out reasoning).

```bash
# System prompt: "Lean 4 syntax checker. DO NOT solve math. ONLY check if code compiles."
# Settings: temperature=0, max_tokens=800, timeout=180s
```

**Use for**: Syntax errors, missing instances, Mathlib API issues
**Don't use for**: Theorem proving, deep math analysis (use Gemini)

---

## Lean/Mathlib Pitfalls

**Set vs Finset**: `(G.induce S).edgeFinset` needs `DecidablePred (· ∈ S)` → use `Finset V` not `Set V`

**Required instances**: `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`

**Aristotle error?** Check: missing `DecidableRel`, Set/Finset mismatch, missing `Fintype`

---

## Success Metrics

| Metric | Target | Notes |
|--------|--------|-------|
| Problems submitted per week | 10+ | Parallel portfolio |
| Runtime per problem | 6-24 hours | Don't rush |
| Success rate | Unknown | We're exploring |
| Learning per failure | High | Analyze why |

**The goal is discovery, not iteration.**

---

## Entry Points

**"Submit problems"** → Phase 1-3 (parallel batch)

**"Check results"** → Phase 4 analysis

**"Why did X fail?"** → Deep analysis of formalization vs. problem

---

## Algorithm Discovery Strategy

**Different from Erdős problems.** Algorithm discovery = finding that known math implies better algorithms.

### Core Principle: Connection Discovery

Aristotle doesn't invent - it finds that **Known Theorem T** from **Area A** implies **Better Algorithm**.

This is what Boris did: formalization exposed connection to Brown's criterion.

### Sweet Spot Targets (vs Ambitious Targets)

| Property | BAD Target | GOOD Target |
|----------|------------|-------------|
| Fame | Heavily studied | Underserved |
| Gap | Large (6+ units) | Tight (1-2 units) |
| Instance | Large n | Small n (≤15) |
| Competition | Many researchers | Few working on it |

### Current Algorithm Targets (IMPROVEMENT-FOCUSED)

| Problem | Prob | Goal | Gap |
|---------|------|------|-----|
| Matrix Mult ω | HIGH | Find ω < 2.371 | 0.37 to ω=2 |
| Integer Mult | MED-HIGH | Remove log* factor → pure O(n log n) | log* factor |
| APSP | MEDIUM | Truly subcubic O(n^{3-ε}) | polylog → constant ε |

**Key**: Only target problems where IMPROVEMENT is believed possible. Never target "prove optimality".

### Template Pattern

```lean
-- ONLY ask for improvement, never disjunctive with optimality
theorem problem_improvement :
  ∃ better, property better ∧ metric better < current_best
```

**Key**: Ask ONLY for improvement. Never "improve OR prove optimal" - that wastes effort on status quo.

### Iteration Protocol

1. **First run**: Minimal spec, let Aristotle explore
2. **If partial**: Extract proven lemmas → feed back as FULL PROOFS (see below)
3. **Build on Aristotle's work**, don't prescribe proof strategy

---

## Feeding Back Proven Work

**CRITICAL**: Aristotle rejects `axiom` declarations as "unexpected axioms".

### Wrong (will fail):
```lean
axiom my_lemma (n : ℕ) : n + 1 > n  -- REJECTED
```

### Right (works):
```lean
lemma my_lemma (n : ℕ) : n + 1 > n := by omega  -- Full proof included
```

### Pattern for Iteration:
1. Run v1 → Aristotle proves some lemmas, fails on others
2. Copy FULL PROVEN PROOFS from output file (not just statements)
3. Include them in v2 as regular lemmas with `:= by <proof>`
4. Aristotle typechecks them instantly, builds on them

**Example** (from Tuza success):
```lean
-- v1 output had this PROVEN lemma
lemma packing_one_implies_intersect ... := by
  contrapose! h
  refine' ne_of_gt (lt_of_lt_of_le _ ...)
  -- [full proof from Aristotle]
```

Include the entire proof. Aristotle won't re-prove, just typecheck and use.

### Key Files

- `ALGORITHM_CONNECTION_DISCOVERY.md` - Full framework
- `submissions/` - Algorithm submissions

---

## Appendix: Boris's Exact Process

From [Xena Project writeup](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/):

> "Boris Alexeev selected several problems by hand, launched Aristotle, and went to bed. He was not emotionally prepared to wake up to an email that Aristotle had successfully resolved Problem 124."

**Timeline**:
- Selection: By hand, from Formal Conjectures
- Submission: `aristotle prove-from-file`
- Runtime: 6 hours
- Lean verification: 1 minute
- Result: Olympiad-style proof

**Why it worked** (per Terence Tao):
> "Erdős... omitted a key hypothesis which made the problem a consequence of a known result (Brown's criterion)"

The formalization was accidentally tractable.
