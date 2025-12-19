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

### Prize Level Heuristics (Learned Dec 2025)

| Prize | Pattern |
|-------|---------|
| **$25-100** | Often have formalization gaps (less scrutiny) |
| **$250-500** | Moderate attention, gaps possible |
| **$500+** | Extensively studied, gaps unlikely |

**"Too easy" counterexample?** Usually means YOUR formalization is wrong, not the problem.

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

## Submission Patterns (Learned Dec 2025)

Three distinct patterns with different use cases:

| Pattern | Lines | When to Use | Expected Outcome |
|---------|-------|-------------|------------------|
| **Boris Minimal** | 35-47 | First attempt, exploration | Highest success rate |
| **Scaffolded** | 100+ | After gaps identified | Builds on proven lemmas |
| **Prescriptive** | 150+ | Test specific strategy | Often finds COUNTEREXAMPLES |

### Boris Minimal (Recommended Default)

- Just definitions + theorem statement
- **NO comments** - comments constrain Aristotle's search space
- Let Aristotle explore freely
- Example: v7 minimal proved τ ≤ 3ν + K₄/K₅ tightness

### Scaffolded (For Gap-Filling)

- Include FULL PROVEN PROOFS as helper lemmas (not axioms)
- No strategic comments
- Feeds Aristotle verified building blocks to extend

### Prescriptive (Strategy Testing)

- Explicit proof strategy in structure
- High discovery rate for FLAWED strategies
- Often leads Aristotle to disprove your approach
- **Counterexamples found this way are valuable** - they eliminate dead ends

### Submit BOTH Formal AND Informal

For important problems, submit two versions:
```
problem_v1.lean  → Aristotle (formal Lean)
problem_v1.md    → Aristotle (natural language proof)
```

**Why**: Informal sometimes proves what formal misses. Different search dynamics.

### Comments Hurt Exploration

From Grok analysis: strategic comments constrain search space.

```lean
-- BAD: "-- Use induction on triangle count"
-- GOOD: (no comment at all, just the theorem statement)
```

Aristotle's 200B+ parameter system explores better without human hints.

---

## Operational: Job Tracking

### Rate Limit

**5-7 concurrent Aristotle slots.** Project is bottlenecked here.

Check before submitting more:
```bash
aristotle list                    # Active jobs
cat submissions/monitor_log.txt   # Full history
```

### Submission Tracking

Each submission gets a UUID:
```bash
aristotle prove-from-file problem.lean --no-wait
# Returns: Job submitted with UUID: abc123...

aristotle status abc123           # Check specific job
```

Track in `submissions/monitor_log.txt` with status (Running/Queued/Complete/Failed).

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

## What We Learned (Dec 2025)

### New Tactical Knowledge

| Discovery | Implication |
|-----------|-------------|
| Comments hurt exploration | Submit minimal files, no strategic hints |
| Informal proofs work | Submit .md alongside .lean |
| Prescriptive → counterexamples | "Failures" often produce valuable negations |
| Counterexamples = value | 3 flawed strategies eliminated via negation |
| Parker proved ν≤3 | Pivot to ν=4 for genuinely open territory |
| Context folders work | Feed proven lemmas back via `--context-folder` |
| Multi-agent debate | Use Grok+Gemini+Codex to design submission portfolios |

### Pattern Refinements

- **Boris minimal** is the best default (35-47 lines, no comments)
- **Scaffolded** works for gap-filling (100+ lines, include full proofs)
- **Formal + Informal** dual submission increases success rate
- **Rate limit awareness** - 5-7 concurrent slots, plan submissions accordingly
- **Context folder iteration** - proven lemmas → context folder → next submission

### Context Folder Pattern (NEW Dec 2025)

```bash
# Create context folder with proven lemmas
mkdir -p submissions/parker_context
cp aristotle_output_proven.lean submissions/parker_context/

# Submit with context
aristotle prove-from-file problem.md --informal \
  --context-folder submissions/parker_context/ --no-wait

# Or formal with context
aristotle prove-from-file problem.lean \
  --context-folder submissions/parker_context/ --no-wait
```

This is how we feed Aristotle's proven lemmas back for completion work.

### Multi-Agent Debate Pattern (NEW Dec 2025)

For strategic decisions, run parallel debates:

1. **Grok-4**: Critical review, counterexample thinking
2. **Gemini**: Architecture analysis, literature connections
3. **Codex**: Implementation feasibility, code structure

Synthesize into a 7-slot portfolio:
| Slot | Pattern | Purpose |
|------|---------|---------|
| 1 | Boris Prime | Open exploration |
| 2 | Architect | Zero-comment structures |
| 3 | Surgeon | Attack known failure point |
| 4 | Finite Check | dec_trivial for small n |
| 5 | Conflict Graph | Structural analysis |
| 6 | Pessimist | Counterexample hunt |
| 7 | Slicer | Isolate obstructions |

Mix: 67% formal, 33% informal.

### Formalization Bug Lesson

Erdős #128 taught us: if counterexample seems "too easy," check formalization against Formal Conjectures. Our threshold was off by +1.

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

## Pre-Submission Validation (CRITICAL)

**Always validate formal submissions before sending to Aristotle.**

The v3_surgeon submission failed because of a Lean syntax error we could have caught locally.

### Validation Command

```bash
# Validate a single file
lake env lean submissions/file.lean

# Expected output for valid file:
# warning: declaration uses 'sorry'  ← This is OK, Aristotle fills these

# Bad output (DO NOT SUBMIT):
# error: unexpected token...
# error: unknown identifier...
```

### First-Time Setup

```bash
cd /Users/patrickkavanagh/math
lake update                  # Get Mathlib dependencies
lake exe cache get          # Download pre-built Mathlib (~5 min)
```

### Validation Script

```bash
./scripts/validate_submission.sh submissions/file.lean
```

### What Validation Catches

| Error Type | Example | Caught? |
|------------|---------|---------|
| Syntax errors | `{x | T // P}` mixed notation | ✓ |
| Missing imports | `import Mathlib` typo | ✓ |
| Type errors | Wrong function signature | ✓ |
| Unknown identifiers | Typo in Mathlib name | ✓ |
| `sorry` warnings | Expected - Aristotle fills | ✓ (OK) |

### Workflow

1. Write submission file
2. Run `lake env lean submissions/file.lean`
3. Fix any errors (not `sorry` warnings)
4. Only then: `aristotle prove-from-file submissions/file.lean --no-wait`

---

## Lean/Mathlib Pitfalls

**Set vs Finset**: `(G.induce S).edgeFinset` needs `DecidablePred (· ∈ S)` → use `Finset V` not `Set V`

**Required instances**: `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`

**Aristotle error?** Check: missing `DecidableRel`, Set/Finset mismatch, missing `Fintype`

**Set-builder vs Subtype**: Don't mix `{x | P}` with `{x : T // P}` - use proper syntax:
```lean
-- WRONG: {S.card | S : Finset V // P S}
-- RIGHT: {n : ℕ | ∃ S : Finset V, S.card = n ∧ P S}
```

---

## CRITICAL: Formalization Verification Protocol

**⚠️ Lesson from Erdős #128 (Dec 2025)**: We claimed C₅ was a counterexample to the $250 problem. It wasn't - our formalization was WRONG.

### The Bug
- **Original**: "≥ n/2 vertices" (conventionally means ⌊n/2⌋)
- **Formal Conjectures**: `2 * |S| + 1 ≥ n` ✓
- **Our submission**: `2 * |S| ≥ n` ✗ (missing +1)
- **For n=5**: FC checks |S|≥2, ours only checks |S|≥3

### Verification Checklist

Before claiming ANY counterexample or negation:

1. **Compare to Formal Conjectures**
   - URL: https://github.com/google-deepmind/formal-conjectures
   - 265 Erdős problems already formalized
   - If our formalization differs, WE are probably wrong

2. **Check original problem statement**
   - Read erdosproblems.com or original paper
   - Watch for floor/ceiling differences
   - Watch for ≤ vs < differences
   - Watch for strict vs non-strict inequalities

3. **Verify counterexample applies to BOTH**
   - Does it break our formalization? (Aristotle checked this)
   - Does it break the FC formalization? (WE must check this)
   - Does it break the original English statement? (WE must check this)

4. **Test edge cases mathematically**
   - For small n (especially odd n), calculate thresholds manually
   - Different rounding conventions matter for small n

### Red Flags

| Sign | Action |
|------|--------|
| Counterexample only works for small n | Verify threshold conditions |
| Our formalization differs from FC | Assume WE are wrong |
| Floor vs ceiling ambiguity | Check original paper |
| Counterexample is "too easy" | Probably formalization bug |

See `docs/ERDOS128_ANALYSIS.md` for the full postmortem.

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

## Current Study: Tuza's Conjecture (τ ≤ 2ν)

**The Conjecture**: For any graph G, τ(G) ≤ 2ν(G), where:
- τ(G) = minimum edges to hit all triangles (covering number)
- ν(G) = maximum edge-disjoint triangles (packing number)

### Proven Results

| Case | Status | Method |
|------|--------|--------|
| ν=0, ν=1 | ✅ Proven | Base case + K₄-extension |
| τ ≤ 3ν (weak bound) | ✅ Proven | Greedy algorithm (all graphs) |
| K₄, K₅ tightness | ✅ Proven | Direct verification |
| **Parker lemmas** | ✅ **PROVEN** | lemma_2_2, 2_3, inductive_bound, intersecting_structure |
| covering_number_le_two_of_subset_four | ✅ Proven | τ ≤ 2 if triangles in ≤4 vertices |

### Parker Lemmas Breakthrough (Dec 2025)

Aristotle has **fully proven** the core lemmas from Parker's 2025 paper:

```
submissions/aristotle_parker_proven.lean  (29KB) - lemma_2_2, lemma_2_3, inductive_bound, intersecting_structure
submissions/aristotle_nu1_proven.lean     (22KB) - covering_number_le_two_of_subset_four
```

**What remains for ν ≤ 3**: Assembly into final theorem. Submissions running with context folders.

### Counterexamples Found (Valuable Negations)

Three counterexamples to flawed proof strategies:

1. **TuzaReductionProperty** - Edge reduction doesn't preserve bounds
2. **two_edges_cover_nearby** - K₄ nearby triangles need 3+ edges
3. **two_K4_almost_disjoint** - "Disjoint" K₄s can share edges

### Open Frontier: ν=4 (Genuinely Open)

**Key Discovery (Dec 2025)**: Parker (arXiv:2406.06501, EJC May 2025) proved Tuza for **ν ≤ 3**.

**Why Parker fails at ν=4**:
- At ν=1,2,3: Can guarantee τ(T_e) ≤ 2 for some edge e in packing M
- At ν=4: Overlap patterns make this impossible
- Induction gives τ ≤ 3 + 2(3) = 9, but Tuza requires ≤ 8

**Current ν=4 portfolio** (7 submissions running):
- Boris Prime, Architect, Surgeon, Finite Check, Conflict Graph, Pessimist, Slicer

### Key Files

- `submissions/tuza_*.lean` - All Tuza submissions
- `submissions/tuza_nu4_*.lean` - ν=4 portfolio (7 files)
- `submissions/aristotle_*_proven.lean` - Proven lemma collections
- `submissions/parker_context/` - Context folder for completion
- `docs/TUZA_STRATEGY_DEC19.md` - Current strategy
- `docs/PARKER_NU4_ANALYSIS.md` - Why ν=4 is genuinely open

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
