# CLAUDE.md - Math Project

## CRITICAL: Database-First Architecture

**ALL project state lives in SQLite at `submissions/tracking.db`.** No JSON files, no scattered markdown. The database is the single source of truth.

### Database Schema Overview

```
submissions/tracking.db
├── Core Tables
│   ├── submissions        (52 rows)  - All Aristotle submissions + status
│   ├── proven_theorems    (-)        - Extracted proven results
│   └── audit_log          (-)        - All actions tracked
│
├── Research Knowledge
│   ├── papers             (15 rows)  - Literature (Parker, Haxell, etc.)
│   ├── literature_lemmas  (62 rows)  - Lemmas from papers
│   └── counterexample_constraints (30 rows) - What counterexamples must evade
│
├── Problem Databases
│   ├── erdos_full         (1111 rows) - All Erdős problems + Formal Conjectures
│   ├── erdos_problems     (219 rows)  - Scored tractable problems
│   ├── erdos_attempts     (10 rows)   - Our submission attempts
│   └── algorithm_candidates (14 rows) - Algorithm discovery targets
│
├── Frontier Research
│   ├── frontiers          (4 rows)   - Active frontier problems
│   ├── frontier_submissions (18 rows) - Links frontiers to submissions
│   ├── frontier_lemmas    (18 rows)  - Applicable lemmas per frontier
│   └── frontier_needed_lemmas (9 rows) - Lemmas we need to prove
│
└── Validation
    ├── definition_audits  (-)        - Formalization bug checks
    └── definition_patterns (-)       - Known buggy patterns
```

### Essential Database Queries

```bash
# Check all running submissions
sqlite3 submissions/tracking.db "SELECT uuid, filename, status FROM submissions WHERE status='running';"

# List proven lemmas from literature
sqlite3 submissions/tracking.db "SELECT name, paper_id, proof_status FROM literature_lemmas WHERE proof_status='proven';"

# Find top tractable Erdős problems
sqlite3 submissions/tracking.db "SELECT number, prize, tractability_score FROM erdos_full WHERE status='open' ORDER BY tractability_score DESC LIMIT 10;"

# Check frontier submission status
sqlite3 submissions/tracking.db "
  SELECT f.name, fs.submission_type, s.status
  FROM frontiers f
  JOIN frontier_submissions fs ON f.id=fs.frontier_id
  JOIN submissions s ON fs.submission_uuid=s.uuid;"

# Get counterexample constraints
sqlite3 submissions/tracking.db "SELECT constraint_text FROM counterexample_constraints;"

# Find all algorithm candidates
sqlite3 submissions/tracking.db "SELECT id, name, tractability_score, problem_type FROM algorithm_candidates ORDER BY tractability_score DESC;"
```

### Database Operations

```bash
# Track new submission (ALWAYS do this)
./scripts/track_submission.sh submissions/file.lean "problem_id" "pattern"

# Import data (if needed)
python3 scripts/import_all_to_sqlite.py

# Direct SQL for custom queries
sqlite3 submissions/tracking.db ".mode column" ".headers on" "YOUR QUERY HERE"
```

**NEVER create JSON files for tracking data.** All state goes into the database.

---

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

## Problem Selection: Database-Driven

### Query Tractable Problems

```bash
# Top 20 open Erdős problems by tractability
sqlite3 submissions/tracking.db "
  SELECT number, prize, tractability_score, tags
  FROM erdos_full
  WHERE status='open' AND has_lean4=1
  ORDER BY tractability_score DESC
  LIMIT 20;"

# Problems we haven't attempted yet
sqlite3 submissions/tracking.db "
  SELECT ef.number, ef.prize, ef.tractability_score
  FROM erdos_full ef
  LEFT JOIN erdos_attempts ea ON ef.number = ea.problem_num
  WHERE ef.status='open' AND ea.id IS NULL
  ORDER BY ef.tractability_score DESC
  LIMIT 10;"
```

### High-Value Signals

| Signal | Why It Matters |
|--------|----------------|
| **Formalization might be weaker** | Erdős often omitted hypotheses; Lean forces explicitness |
| **Olympiad-style tractable** | Aristotle excels at elegant proofs |
| **Existing Mathlib might connect** | Unexpected applications of known results |
| **Finite/decidable structure** | Can verify specific instances |
| **Low prize / obscure** | Less attention = potential gaps missed |

### Prize Level Heuristics (Learned Dec 2025)

| Prize | Pattern |
|-------|---------|
| **$25-100** | Often have formalization gaps (less scrutiny) |
| **$250-500** | Moderate attention, gaps possible |
| **$500+** | Extensively studied, gaps unlikely |

**"Too easy" counterexample?** Usually means YOUR formalization is wrong, not the problem.

---

## Workflow: Database-Tracked

### Phase 1: Problem Discovery

```bash
# Find promising problems from database
sqlite3 submissions/tracking.db "
  SELECT number, prize, tags, tractability_score
  FROM erdos_full
  WHERE status='open' AND has_lean4=1
  ORDER BY tractability_score DESC LIMIT 20;"
```

### Phase 2: Check Literature

```bash
# Find relevant proven lemmas
sqlite3 submissions/tracking.db "
  SELECT name, statement, proof_technique
  FROM literature_lemmas
  WHERE proof_status='proven'
  AND (name LIKE '%packing%' OR name LIKE '%cover%');"
```

### Phase 3: Submit and Track

```bash
# Validate first
./scripts/validate_submission.sh submissions/file.lean

# Track in database
./scripts/track_submission.sh submissions/file.lean "problem_id" "boris_minimal"

# Submit to Aristotle
aristotle prove-from-file submissions/file.lean --no-wait
# Returns UUID - update database with:
sqlite3 submissions/tracking.db "UPDATE submissions SET uuid='<UUID>', status='running' WHERE filename='submissions/file.lean';"
```

### Phase 4: Analyze Results

```bash
# Check submission status
sqlite3 submissions/tracking.db "SELECT uuid, status, sorry_count, proven_count FROM submissions WHERE status='completed';"
```

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

```bash
# Find proven lemmas to scaffold with
sqlite3 submissions/tracking.db "
  SELECT name, statement
  FROM literature_lemmas
  WHERE paper_id='parker2024' AND proof_status='proven';"
```

- Include FULL PROVEN PROOFS as helper lemmas (not axioms)
- No strategic comments
- Feeds Aristotle verified building blocks to extend

### Submit BOTH Formal AND Informal

For important problems, submit two versions:
```
problem_v1.lean  → Aristotle (formal Lean)
problem_v1.md    → Aristotle (natural language proof)
```

**Why**: Informal sometimes proves what formal misses. Different search dynamics.

---

## Operational: Database-Driven Job Tracking

### Rate Limit

**5-7 concurrent Aristotle slots.** Project is bottlenecked here.

```bash
# Check running submissions
sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='running';"

# List all running
sqlite3 submissions/tracking.db "SELECT uuid, filename, submitted_at FROM submissions WHERE status='running';"
```

### Submission Lifecycle

```sql
-- Draft → Validated → Submitted → Running → Completed/Failed
UPDATE submissions SET status='validated' WHERE uuid='...';
UPDATE submissions SET status='running', submitted_at=datetime('now') WHERE uuid='...';
UPDATE submissions SET status='completed', completed_at=datetime('now'), sorry_count=0, proven_count=5 WHERE uuid='...';
```

---

## Current Frontiers (Database-Tracked)

```bash
# Check frontier status
sqlite3 submissions/tracking.db "
  SELECT f.name, f.status, f.priority,
         COUNT(fs.id) as submissions
  FROM frontiers f
  LEFT JOIN frontier_submissions fs ON f.id=fs.frontier_id
  GROUP BY f.id
  ORDER BY f.priority;"
```

### Active Frontiers

| Frontier | Status | Key Question |
|----------|--------|--------------|
| Split Graphs | SUBMITTED | Does Tuza hold for all split graphs? |
| Counterexample Hunt | SUBMITTED | Does a counterexample to Tuza exist? |
| Hypergraph r=4 | SUBMITTED | Can we prove τ ≤ 2.5ν for 4-uniform? |
| Bound Improvement | NOT_SUBMITTED | Can we improve 2.87→2.5? |

### Frontier Lemmas

```bash
# Get applicable lemmas for a frontier
sqlite3 submissions/tracking.db "
  SELECT lemma_name, lemma_status, applicability, how_to_use
  FROM frontier_lemmas
  WHERE frontier_id='split_graphs';"

# Get lemmas we still need to prove
sqlite3 submissions/tracking.db "
  SELECT name, statement, why_needed
  FROM frontier_needed_lemmas
  WHERE frontier_id='split_graphs';"
```

---

## Literature Knowledge (In Database)

### Papers

```bash
sqlite3 submissions/tracking.db "SELECT id, title, year, main_result FROM papers ORDER BY year DESC;"
```

### Proven Lemmas

```bash
# All proven lemmas we can use as scaffolding
sqlite3 submissions/tracking.db "
  SELECT l.name, l.english, p.title as source
  FROM literature_lemmas l
  JOIN papers p ON l.paper_id = p.id
  WHERE l.proof_status='proven';"
```

### Counterexample Constraints

```bash
# What any counterexample must satisfy
sqlite3 submissions/tracking.db "SELECT constraint_text, source FROM counterexample_constraints;"
```

Current constraints from literature:
- mad(G) ≥ 7 (Puleo 2015)
- χ(G) ≥ 5 (Lakshmanan 2012)
- NOT tripartite (Haxell-Kohayakawa 1998)
- treewidth(G) ≥ 7 (Botler 2020)
- NOT threshold graph (Threshold 2021)

---

## Pre-Submission Validation (CRITICAL)

**Always validate formal submissions before sending to Aristotle.**

```bash
# Full validation workflow
./scripts/validate_submission.sh submissions/file.lean
./scripts/track_submission.sh submissions/file.lean "problem_id" "pattern"
aristotle prove-from-file submissions/file.lean --no-wait
```

### What Validation Catches

| Error Type | Example | Caught? |
|------------|---------|---------|
| Syntax errors | `{x | T // P}` mixed notation | ✓ |
| Missing imports | `import Mathlib` typo | ✓ |
| **sInf unrestricted** | `sInf` without `E ⊆ G.edgeFinset` | ✓ |
| **sym2 self-loops** | `t.sym2` for triangle edges | ✓ |
| **Set/Finset issues** | `Set V` without `DecidablePred` | ✓ |

Files using `sInf` without `E ⊆ G.edgeFinset` are **INVALID** - archived in `submissions/CORRUPTED/`.

---

## Lean/Mathlib Pitfalls

**Set vs Finset**: `(G.induce S).edgeFinset` needs `DecidablePred (· ∈ S)` → use `Finset V` not `Set V`

**Required instances**: `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`

### CRITICAL: Finset.sym2 Includes Self-Loops!

```lean
#eval ({1, 2, 3} : Finset ℕ).sym2
-- Output: {s(1,1), s(1,2), s(1,3), s(2,2), s(2,3), s(3,3)}
--         ^^^^^^ SELF-LOOPS INCLUDED!
```

**Triangle covering MUST restrict to actual graph edges**:
```lean
-- WRONG: allows self-loops and non-edges
def coveringNumber ... : ℕ :=
  sInf {n | ∃ E : Finset (Sym2 V), E.card = n ∧ ...}

-- CORRECT: restricts to actual graph edges
def coveringNumber ... : ℕ :=
  G.edgeFinset.powerset.filter (...) |>.image Finset.card |>.min |>.getD 0
```

---

## Formalization Verification Protocol

**⚠️ Lesson from Erdős #128 (Dec 2025)**: We claimed C₅ was a counterexample. It wasn't - our formalization was WRONG.

### Before claiming ANY counterexample:

1. **Compare to Formal Conjectures** - If our formalization differs, WE are probably wrong
2. **Check original problem statement** - Watch for floor/ceiling differences
3. **Verify counterexample applies to BOTH** our formalization AND FC formalization
4. **Test edge cases mathematically** - Different rounding conventions matter for small n

---

## Algorithm Discovery (Database-Tracked)

```bash
# List algorithm candidates by tractability
sqlite3 submissions/tracking.db "
  SELECT id, name, tractability_score, gap, why_hard
  FROM algorithm_candidates
  ORDER BY tractability_score DESC;"
```

### Current Targets

| Problem | Score | Goal | Gap |
|---------|-------|------|-----|
| Matrix Mult ω | 2 | Find ω < 2.371 | 0.37 to ω=2 |
| Integer Mult | - | Remove log* factor | log* factor |
| APSP | - | Truly subcubic | polylog → constant ε |

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
1. Run v1 → Aristotle proves some lemmas
2. Query database for proven lemmas
3. Copy FULL PROVEN PROOFS into v2
4. Aristotle typechecks them instantly, builds on them

---

## Multi-Agent Debate Pattern

For strategic decisions, run parallel debates:

1. **Grok-4**: Critical review, counterexample thinking
2. **Gemini**: Architecture analysis, literature connections
3. **Codex**: Implementation feasibility, code structure

Synthesize into a 7-slot portfolio tracked in database.

---

## Quick Reference: Database Tables

| Table | Purpose | Key Columns |
|-------|---------|-------------|
| `submissions` | Track all Aristotle jobs | uuid, filename, status, sorry_count |
| `papers` | Literature metadata | id, title, year, main_result |
| `literature_lemmas` | Extracted lemmas | name, statement, proof_status |
| `frontiers` | Frontier problems | id, name, status, priority |
| `erdos_full` | All 1111 Erdős problems | number, status, tractability_score |
| `algorithm_candidates` | Algorithm targets | id, name, tractability_score |
| `counterexample_constraints` | What counterexamples must satisfy | constraint_text |

---

## Entry Points

**"Submit problems"** → Query `erdos_full` for tractable problems → validate → track → submit

**"Check results"** → Query `submissions WHERE status='completed'`

**"Find proven lemmas"** → Query `literature_lemmas WHERE proof_status='proven'`

**"Check frontiers"** → Query `frontiers` and `frontier_submissions`

**"Why did X fail?"** → Query `submissions` + `audit_log` for history

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
