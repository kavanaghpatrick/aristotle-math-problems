# Screening Criteria Analysis: Open Problems vs. Solved-Not-Formalized

**Date**: February 9, 2026
**User Goal**: Use Aristotle's INFORMAL mode to work on OPEN mathematical problems — not just formalize already-solved results.

---

## Executive Summary

**FINDING**: The current screening infrastructure (`/project:screen` and `screen_formal_conjectures.py`) **heavily biases toward solved-not-formalized results** rather than genuinely open problems.

**KEY INSIGHT**: The screening system assigns highest scores (10/10) to `answer(sorry)` problems, which are **questions about whether a claim is true or false**, NOT open problems with known-true statements needing proofs.

**RECOMMENDATION**: Create a parallel screening track for open problems with different criteria focused on:
1. Feasibility of novel proof approaches (not existence of known proofs)
2. Availability of partial progress/special cases
3. Computational angle for witness discovery
4. Bounded reductions that could provide insight

---

## Current Screening Bias: The Evidence

### 1. Gate G1 (Sketchability) — The Primary Filter

From `/project:screen` command (line 32-37):

```markdown
### G1: Sketchability (NEW — most important gate)
Can we write a 50-100 line proof sketch for this?
- PASS: Known proof exists, standard techniques, we can outline the argument
- SOFT PASS: Partial proof known, we can sketch most of it with gaps
- FAIL: Open problem requiring novel math, no known approach
```

**Analysis**: This gate **explicitly rejects** open problems without known proofs. It's the "most important gate" and any FAIL → instant REJECT.

### 2. Scoring Dimension S1 (Sketchability) — 25% Weight

From `/project:screen` command (line 96):

```markdown
| S1: Sketchability | 25% | ? | 10=known proof, clear sketch; 5=partial; 1=open problem |
```

**Analysis**: Open problems score **1/10** on the highest-weighted dimension. A truly open problem is penalized -9 points (22.5% of total score) relative to a solved problem.

### 3. Gate G7 (Novel Insight Required?) — Anti-Open Filter

From `/project:screen` command (line 71-75):

```markdown
### G7: Novel Insight Required?
Does solving this require a NEW mathematical idea?
- PASS: Known proof, standard techniques suffice
- SOFT PASS: Incremental extension of known results
- FAIL: "Has resisted decades of effort," requires new techniques
```

**Analysis**: Problems requiring novel mathematics → FAIL → instant REJECT.

### 4. The `answer(sorry)` Phenomenon

The screening script assigns **highest priority (TIER 2)** to problems with `answer(sorry)`, which it describes as:

```python
# Line 155-156
if 'answer(sorry)' in thm_text:
    score += 2.0  # BIG bonus: this is where we add value
    reasons.append('TIER2: answer(sorry) — True/False unknown, high-value target')
```

**What `answer(sorry)` Actually Means**: Looking at Erdos 1056:

```lean
theorem erdos_1056 : answer(sorry) ↔
    ∀ k ≥ 2, ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ) (_ : StrictMono boundaries),
    AllModProdEqualsOne p boundaries := by
  sorry
```

This is **NOT** an open problem needing a proof. It's a **meta-question**: "Is this claim true or false?"

The screening system treats "we don't know if this is true" as high-value because determining truth/falsehood is considered a contribution. But this is **orthogonal** to proof discovery.

---

## Screening Results: The Data

### High-Value Targets (score ≥ 8)

**Current System Output**:
```
HIGH-VALUE TARGETS: 298 open problems where computation could solve
Score  Tier             Problem
10     ANSWER_UNKNOWN   erdos_1056      (determine if claim is true/false)
10     ANSWER_UNKNOWN   erdos_1074      (determine if claim is true/false)
10     ANSWER_UNKNOWN   erdos_141       (determine if claim is true/false)
...
[256 total ANSWER_UNKNOWN problems scored 8-10]
```

### True Open Problems WITHOUT answer(sorry)

Running custom query on `open_problem_screening.json`:

```
OPEN RESEARCH PROBLEMS (not answer(sorry), score > 6): 93 total

Top examples:
1. four_exponentials_conjecture (score 10, FINITE) — but classified FINITE incorrectly
2. erdos_364 (score 9.7, WITNESS) — genuinely open: "no triple of consecutive powerful numbers"
3. juggler_conjecture (score 9.2, WITNESS)
4. oppermann_conjecture (score 9.2, WITNESS)
5. grimm_conjecture (score 8.9, WITNESS)
```

**Issue**: Many of these are **major open problems** (Juggler, Oppermann, Grimm) that scored high only because they're classified as "pure existential — witness search". The system doesn't understand that finding a *counterexample* to these conjectures would be the discovery, not a "witness" proving them.

**Example — Erdos 364** (score 9.7):

```lean
theorem erdos_364 :
    ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) := by
  sorry
```

This is a **genuinely open problem** — "there is no triple of consecutive powerful numbers." It scored 9.7 because:
- Pure existential (wait, it's a negation of existential — falsification target)
- Good domain (NT)
- Good signals (decidable, finite-checkable)

But the screening system **doesn't distinguish** between:
- "Find a counterexample to disprove this" (what Erdos 364 actually needs)
- "Find a witness to prove this" (what the WITNESS tier expects)

---

## What's Missing: Criteria for Open Problems

To use Aristotle's INFORMAL mode on open problems, we need NEW screening criteria:

### Proposed Gates for Open Problems

#### OG1: Bounded Special Cases
Does a bounded/finite special case provide meaningful progress?
- PASS: Proving for n ≤ 10^6 would be publishable partial progress
- SOFT PASS: Bounded case illuminates the general structure
- FAIL: Finite cases are trivial or uninformative

**Example**: Erdos 364 — checking n ≤ 10^12 for powerful triples would be valuable computational NT.

#### OG2: Partial Progress Available
Has the mathematical community made partial progress?
- PASS: Established lemmas, known sub-cases, standard conjectures available
- SOFT PASS: Related results proven, analogous problems solved
- FAIL: No prior work, completely novel territory

**Example**: Grimm's conjecture — connection to prime gaps and covering systems is well-studied.

#### OG3: Computational Discovery Angle
Can computation discover patterns/witnesses that inform a proof?
- PASS: Witness values, counterexamples, or patterns are computable and informative
- SOFT PASS: Numerical evidence can guide proof strategy
- FAIL: Pure existence proof, no computational angle

**Example**: Juggler conjecture — computing trajectories reveals structure (even though we can't prove termination).

#### OG4: Proof-of-Concept Scope
Can we attempt a proof-of-concept that demonstrates progress?
- PASS: Weaker version, special case, or bounded instance has a feasible proof
- SOFT PASS: Key lemma or structural result is within reach
- FAIL: No tractable sub-problem exists

**Example**: Erdos 364 — the "no quadruple" variant is proven (undergraduate level). The triple case could build on similar techniques.

#### OG5: Aristotle's Domain Strength
Is this in a domain where Aristotle has demonstrated novel proof construction?
- PASS: NT/algebra where Aristotle authored slot572 complexity proof from scratch
- SOFT PASS: Analysis with clear structure
- FAIL: Combinatorics (0/183 sorry=1 success), geometry without automation

**Evidence**: Aristotle CAN author novel proofs (slot572 complexity was first-ever, sorry=1→proven). But domain matters.

### Proposed Scoring for Open Problems

| Dimension | Weight | Description |
|-----------|--------|-------------|
| O1: Bounded Progress | 25% | Can we prove a meaningful bounded/finite case? |
| O2: Partial Scaffolding | 20% | Do we have lemmas, related results, analogous proofs? |
| O3: Computational Angle | 15% | Can we compute witnesses, patterns, counterexamples? |
| O4: Domain Strength | 15% | NT/algebra (strong) vs combinatorics (weak) |
| O5: Proof-of-Concept | 10% | Can we demonstrate progress on a sub-problem? |
| O6: Mathlib Support | 10% | Are the relevant definitions/lemmas available? |
| O7: Novel Insight Risk | 5% | How much new math is required? (lower is better) |

**Composite Score**: Weighted average

**Interpretation**:
- **7.0+**: Worth attempting — bounded case or partial progress is feasible
- **5.0-6.9**: Speculative — needs strong computational angle or sub-problem
- **< 5.0**: Too hard — requires breakthrough mathematics

---

## Case Studies: Current vs. Proposed Screening

### Case 1: Erdos 1056 (current score: 10/10)

**Current Classification**: ANSWER_UNKNOWN, TIER2 — "True/False unknown, high-value target"

**Reality**: This asks "Is it true that for all k ≥ 2, there exist intervals with modular products ≡ 1?"

**Current Scoring**:
- S1 (Sketchability): 1/10 (open problem — unknown if true)
- S2 (Domain): 8/10 (NT)
- S3 (Novelty): 10/10 (first-ever if solved)
- Result: High score because of answer(sorry) +2.0 bonus

**Proposed Open-Problem Scoring**:
- O1 (Bounded): 3/10 — checking specific k values doesn't prove ∀k
- O2 (Scaffolding): 4/10 — known examples for k=2,3 but no general technique
- O3 (Computational): 6/10 — can search for more examples
- O4 (Domain): 8/10 (NT)
- O5 (PoC): 2/10 — no clear path to general proof
- Result: **5.0/10** — marginal open problem, needs breakthrough insight

### Case 2: Erdos 364 (current score: 9.7/10)

**Current Classification**: WITNESS, TIER3 — "pure existential — witness search"

**Reality**: Prove ¬∃ triple of consecutive powerful numbers (open since ~1976)

**Current Scoring**:
- S1 (Sketchability): 1/10 (open problem)
- S2 (Domain): 8/10 (NT)
- Boosted by "witness search" classification (incorrectly — it's negation of ∃)
- Result: 9.7 (but for wrong reasons)

**Proposed Open-Problem Scoring**:
- O1 (Bounded): 8/10 — checking n ≤ 10^12 is publishable computational NT
- O2 (Scaffolding): 7/10 — "no quadruple" proven, powerful number theory well-developed
- O3 (Computational): 9/10 — can exhaustively search bounded ranges
- O4 (Domain): 8/10 (NT)
- O5 (PoC): 5/10 — general proof likely needs new technique, but bounded case is feasible
- O6 (Mathlib): 8/10 — Nat.Prime, divisibility well-supported
- O7 (Novel Insight): 3/10 — Erdős conjectured it, likely hard
- Result: **7.2/10** — Worth attempting bounded case (n ≤ 10^12), not general proof

### Case 3: Leinster Cyclic Perfect (slot562, PROVEN via INFORMAL)

**Current Classification**: Not in open_problem_screening.json (it was "solved not formalized")

**Reality**: Known theorem: cyclic groups of order n have sum of orders = σ(n). We sketched proof, Aristotle formalized (53 lines → 117 lines proven).

**Current Scoring** (if it were in the screening):
- S1 (Sketchability): 10/10 (known proof, clear sketch)
- S2 (Domain): 9/10 (algebra)
- S3 (Novelty): 8/10 (first-ever formalization)
- Result: **~8.5/10** — Excellent INFORMAL candidate

**This is the sweet spot**: Known proof, first-ever formalization, good domain.

### Case 4: Integer Complexity (slot572, PROVEN via FORMAL sorry=1)

**Reality**: First-ever formalization of complexity bounds. We provided definitions + statement (sorry=1), Aristotle **authored the entire proof from scratch** including:
- Inductive predicate for complexity
- Decidability instance
- `interval_cases` tactic usage
- Novel proof structure

**Current Scoring** (if it were screened):
- S1 (Sketchability): 5/10 (known result, but no proof sketch provided — just definitions)
- S2 (Domain): 9/10 (NT/algebra)
- S3 (Novelty): 10/10 (first-ever)
- Result: **~7.0/10**

**Key Insight**: This succeeded DESPITE low sketchability because:
1. Domain was NT/algebra (Aristotle's strength)
2. Definitions were provided (just needed proof construction)
3. sorry=1, not sorry=183 (small gap, not 183 gaps)

**Lesson**: Aristotle CAN author novel proofs in strong domains when given good setup.

---

## Recommendations: Dual-Track Screening

### Track 1: Solved-Not-Formalized (Current System)

**Keep the current `/project:screen` for**:
- Known proofs needing formalization (Leinster, Feit-Thompson, etc.)
- Literature results not yet in Mathlib
- Track A (INFORMAL sketch) candidates

**Current criteria work well here**: Sketchability, domain, Mathlib support.

### Track 2: Open Problems (NEW)

**Create `/project:screen-open` for**:
- Genuinely open problems (Erdos 364, Grimm, etc.)
- Bounded/finite special cases of open problems
- Computational discovery (witnesses, patterns, counterexamples)
- Proof-of-concept attempts

**New criteria needed**:
- Bounded progress feasibility (not sketchability)
- Partial scaffolding availability (not full proof)
- Computational discovery angle
- Proof-of-concept scope
- Domain strength for novel construction (Aristotle's NT/algebra authoring ability)

### Hybrid Cases: answer(sorry) Problems

**Question**: How to screen "answer(sorry)" problems?

**Recommendation**: Classify by whether determining truth is computationally tractable:

| Type | Example | Screening Track |
|------|---------|-----------------|
| Computationally decidable | ∀ n ≤ 100, P(n) | Track 2 (Open) — computational discovery |
| Requires proof | ∀ n, P(n) where proof is unknown | Track 2 (Open) — treat as open problem |
| Meta-question | "Does there exist..." without computational angle | REJECT — pure research, no tractable approach |

**For Erdos 1056** (answer(sorry) + ∀ k ≥ 2, ∃ p...):
- Current: TIER2, score 10/10
- Proposed: **REJECT** — no computational closure, no proof sketch, requires novel insight
- Alternative: Submit as Track C (Falsify) — check if claim is false for small k

---

## Proposed Implementation

### File: `/Users/patrickkavanagh/math/.claude/commands/screen-open.md`

```markdown
---
description: Screen an OPEN mathematical problem for feasibility of progress via Aristotle INFORMAL
allowed-tools: Read, Grep, Glob, Bash, Task, WebFetch, WebSearch
argument-hint: <problem-description-or-file>
---

Screen `$ARGUMENTS` as a genuinely OPEN problem: can we make meaningful progress via:
1. Bounded/finite special case
2. Partial proof with scaffolding from literature
3. Computational discovery of witnesses/patterns
4. Proof-of-concept for sub-problem

## Gates for Open Problems

### OG1: Bounded Progress
Can we prove a bounded/finite case that's publishable?
- PASS: n ≤ 10^12 case is meaningful computational number theory
- SOFT PASS: Bounded case illuminates general structure
- FAIL: Finite cases are trivial

### OG2: Partial Scaffolding
Has the mathematical community provided scaffolding?
- PASS: Key lemmas proven, related results available
- SOFT PASS: Analogous problems solved, standard techniques apply
- FAIL: No prior work

### OG3: Computational Angle
Can computation inform the proof?
- PASS: Witnesses/counterexamples/patterns are computable and informative
- SOFT PASS: Numerical evidence guides strategy
- FAIL: Pure existence, no computation helps

### OG4: Domain Strength
Is Aristotle strong in this domain?
- PASS: NT/algebra (Aristotle authored slot572 from scratch)
- SOFT PASS: Analysis with structure
- FAIL: Combinatorics (0/183), geometry

### OG5: Proof-of-Concept
Can we attempt a meaningful sub-problem?
- PASS: Weaker version or special case has feasible proof
- SOFT PASS: Key structural lemma is within reach
- FAIL: No tractable sub-problem

**Any 2+ FAIL → REJECT**

## Scoring (if gates pass)

| Dimension | Weight | Score Meaning |
|-----------|--------|---------------|
| O1: Bounded Progress | 25% | 10=bounded case publishable, 1=trivial |
| O2: Partial Scaffolding | 20% | 10=rich literature support, 1=novel territory |
| O3: Computational Angle | 15% | 10=computable witnesses/patterns, 1=pure existence |
| O4: Domain Strength | 15% | 10=NT/algebra, 5=analysis, 1=combinatorics |
| O5: Proof-of-Concept | 10% | 10=feasible sub-problem, 1=no tractable piece |
| O6: Mathlib Support | 10% | 10=full support, 1=build from scratch |
| O7: Novel Insight Risk | 5% | 10=standard techniques, 1=breakthrough needed (inverted) |

**Composite**: Weighted average

**Interpretation**:
- **7.0+**: Attempt it — bounded case or PoC is feasible
- **5.0-6.9**: Speculative — needs strong computational angle
- **< 5.0**: Too hard — requires breakthrough

## Output

```
## OPEN PROBLEM SCREENING: [name]

**VERDICT**: ATTEMPT / SPECULATIVE / TOO_HARD
**Composite Score**: X.X / 10.0
**Recommended Approach**:
  - Bounded case (n ≤ N)
  - Partial scaffolding (prove key lemma)
  - Computational discovery (find patterns)
  - Proof-of-concept (weaker version)

### Gate Results
[table]

### Scoring
[table]

### Feasibility Analysis
[What progress is tractable? What requires breakthrough?]

### Comparison
- vs Erdos 364 (7.2): [better/worse]
- vs threshold (7.0): [above/below]
```
```

### File: `scripts/screen_open_problems.py`

Modify `screen_formal_conjectures.py` to:

1. **Add `--open-only` flag**: Filter to problems WITHOUT `answer(sorry)` and WITHOUT `research solved`
2. **Add open-problem scoring function**:
   ```python
   def score_open_problem(thm_text, metadata):
       """Score genuinely open problems by feasibility of progress."""
       # O1: Bounded progress
       # O2: Partial scaffolding (check literature_lemmas table)
       # O3: Computational angle
       # O4: Domain strength
       # O5: Proof-of-concept (check for proven sub-cases in file)
       # O6: Mathlib support
       # O7: Novel insight risk (inverse of hard_signals)
       return score, reasons, recommendation
   ```
3. **Create separate tiers**:
   - **BOUNDED**: Finite case publishable
   - **PARTIAL**: Key lemma/scaffolding available
   - **COMPUTATIONAL**: Witness/pattern discovery
   - **POC**: Proof-of-concept for weaker version
   - **TOO_HARD**: Requires breakthrough

---

## Database Schema Addition

Add to `submissions/tracking.db`:

```sql
CREATE TABLE open_problem_attempts (
    id INTEGER PRIMARY KEY,
    problem_name TEXT NOT NULL,
    approach TEXT NOT NULL, -- 'bounded_n_1e12', 'key_lemma_scaffolding', 'witness_search', 'weak_version'
    scope TEXT, -- 'n ≤ 10^12', 'k ≤ 5', 'p < 1000'
    result TEXT, -- 'proven', 'partial', 'failed', 'abandoned'
    submission_id INTEGER, -- FK to submissions
    notes TEXT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (submission_id) REFERENCES submissions(id)
);

-- Examples:
INSERT INTO open_problem_attempts (problem_name, approach, scope, result, notes)
VALUES
  ('erdos_364', 'bounded_n_1e12', 'n ≤ 10^12', 'candidate', 'Exhaustive search for powerful triples'),
  ('grimm_conjecture', 'key_lemma_scaffolding', 'k ≤ 10', 'candidate', 'Use covering system lemmas from literature');
```

---

## Worked Example: Erdos 364

**Problem**: Prove there is no triple of consecutive powerful numbers.

### Current Screening (screen.md)

```
Gate Results:
G1 (Sketchability): FAIL — no known proof
→ INSTANT REJECT
```

### Proposed Open Screening (screen-open.md)

```
Gate Results:
OG1 (Bounded): PASS — n ≤ 10^12 case is publishable computational NT
OG2 (Scaffolding): PASS — "no quadruple" proven, powerful number theory rich
OG3 (Computational): PASS — exhaustive search feasible
OG4 (Domain): PASS — NT (Aristotle's strength)
OG5 (PoC): SOFT PASS — techniques from quadruple case may extend

Scoring:
O1: 8/10 (bounded publishable)
O2: 7/10 (rich scaffolding)
O3: 9/10 (computational search)
O4: 8/10 (NT domain)
O5: 5/10 (PoC uncertain)
O6: 8/10 (Mathlib support)
O7: 3/10 (likely needs new technique)

Composite: 7.2/10

VERDICT: ATTEMPT
Recommended Approach:
  1. Computational: Exhaustive search n ≤ 10^12 (native_decide or Rust)
  2. Bounded proof: Formalize "no powerful triples ≤ 10^12" as publishable result
  3. Scaffolding: Analyze "no quadruple" proof, attempt to adapt techniques
  4. Track: B (Computational) for bounded case, NOT Track A (INFORMAL) for general proof
```

**Outcome**: We would attempt the **bounded case** (n ≤ 10^12), not the general proof. This is tractable and publishable.

---

## Summary Table: Screening Philosophy

| Problem Type | Example | Current Score | Proposed Score | Should Attempt? |
|--------------|---------|---------------|----------------|-----------------|
| **Solved-not-formalized** | Leinster cyclic | ~8.5/10 | 8.5/10 (Track 1) | ✅ YES — Track A (INFORMAL) |
| **Open + bounded tractable** | Erdos 364 (n ≤ 10^12) | 9.7/10 (wrong reasons) | 7.2/10 (Track 2) | ✅ YES — Track B (Compute) |
| **Open + scaffolding rich** | Grimm conjecture (k ≤ 10) | 8.9/10 (witness search) | 6.5/10 (Track 2) | ⚠️ SPECULATIVE |
| **Open + no tractable piece** | Erdos 1056 (∀ k ≥ 2) | 10/10 (answer(sorry)) | 5.0/10 (Track 2) | ❌ NO — requires breakthrough |
| **Open + major conjecture** | Juggler, Oppermann | 9.2/10 (witness search) | 4.0/10 (Track 2) | ❌ NO — no tractable approach |
| **Formalize from sketch** | Integer complexity | ~7.0/10 | 7.5/10 (Track 1) | ✅ YES — definitions + sorry=1 |

---

## Conclusion

### Current Bias

The `/project:screen` system is **optimized for Track A (INFORMAL sketch)** where:
- Proof is known → we write sketch → Aristotle formalizes
- This is the **highest-value workflow** (slot562, 563, 564 proven)

It **correctly rejects** open problems requiring novel mathematics because we can't write sketches for unknown proofs.

### Gap

The system does NOT screen for:
- **Bounded/finite special cases** of open problems
- **Computational discovery** approaches
- **Partial progress** via scaffolding
- **Proof-of-concept** for weaker versions

These are DIFFERENT workflows than Track A, but they're **valid uses of Aristotle INFORMAL**.

### Recommendation

**Dual-track screening**:

1. **Keep `/project:screen`** for solved-not-formalized (Track A: sketch → formalize)
2. **Add `/project:screen-open`** for open problems (Track 2: bounded/computational/PoC)

**Key principle**: We're not trying to solve major open problems. We're trying to make **tractable progress** via:
- Bounded verification (Erdos 364: n ≤ 10^12)
- Computational witnesses (A375077: compute a(8), a(9))
- Scaffolding lemmas (Grimm: prove key sub-lemma)
- Weak versions (Erdos 364: quadruple already proven, triple is harder)

**Aristotle's role**: In Track 2, Aristotle formalizes:
- Computational proofs (native_decide on bounded cases)
- Scaffolding lemmas (INFORMAL from partial sketches)
- Weak versions (INFORMAL from analogous proofs)

NOT: Aristotle discovering novel mathematics to solve open problems.

---

## Next Steps

1. **Implement `/project:screen-open`** command with new gates/scoring
2. **Modify `screen_formal_conjectures.py`** to add `--open-only` mode
3. **Run screening on formal-conjectures** with open-problem criteria
4. **Curate 10-20 bounded/computational targets** (Erdos 364, etc.)
5. **Attempt bounded cases** via Track B (native_decide) or Track 1B (Aristotle authoring from definitions)
6. **Document successes/failures** in `open_problem_attempts` table

**Hypothesis to test**: Aristotle can formalize bounded cases and scaffolding lemmas for open problems, even when the general proof is out of reach.

**Evidence needed**: Attempt 5-10 bounded cases, measure success rate, compare to Track A baseline.
