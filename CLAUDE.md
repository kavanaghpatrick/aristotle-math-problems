# CLAUDE.md - Math Project

## Mission

**Goal**: Use Aristotle to make genuine progress on open mathematical problems.

**Primary Focus**: Tuza's Conjecture frontiers
- ν = 4 case (genuinely OPEN - Parker's proof fails here)
- Split graphs general case (OPEN - only threshold subset proven)
- Counterexample search (OPEN - none known)
- Hypergraph r=4 Aharoni-Zerbib (OPEN)

**Secondary**: Erdős problems (opportunistic portfolio when slots available)

**Key Principle**: Discovery, not re-formalization. If someone already proved it, we build on their work—we don't re-prove it.

---

## Progress Verification (BEFORE ANY WORK)

The goal is **discovery**, not re-proving known results.

### Pre-Submission Checklist

Before spending an Aristotle slot, answer these:

**1. Is this actually open?**
- Check the source (erdosproblems.com, original paper, arXiv)
- If solved → STOP or pivot to genuine extension
- Example: ν ≤ 3 is SOLVED (Parker 2024). Don't reprove it.

**2. Has someone made progress?**
- Search for partial results in literature
- If yes → import their lemmas into our database
- Build ON their work, don't ignore it

**3. What specifically is the contribution?**
- State it: "If this succeeds, the new knowledge is ___"
- If you can't articulate it, reconsider the submission

**4. Is prior work integrated?**
- Check `literature_lemmas` table for relevant proven results
- Include proven lemmas as scaffolding, not starting from scratch

### Contribution Levels (Be Honest)

| Level | What It Means | Worth a Slot? |
|-------|---------------|---------------|
| **Discovery** | Prove genuinely open conjecture | ✓ Absolutely |
| **Extension** | New case beyond known results | ✓ Yes |
| **New Technique** | Novel proof of known theorem | ✓ Maybe |
| **Formalization+** | Formalize + find/fix gap | ~ Low priority |
| **Pure Formalization** | Just translate existing proof | ✗ Not primary goal |
| **Duplication** | Redo existing Lean proof | ✗ Never |

### Honest Self-Assessment

Most of our ν ≤ 3 work was **formalization** of Parker's 2024 result, not discovery. That work built valuable scaffolding, but the real targets are the genuinely open problems listed in the Mission.

---

## Database Architecture

All project state lives in SQLite at `submissions/tracking.db`.

### Schema Overview

```
submissions/tracking.db
├── Core: submissions, proven_theorems, audit_log
├── Research: papers (15), literature_lemmas (62), counterexample_constraints (10)
├── Problems: erdos_full (1111), erdos_problems (219), erdos_attempts
├── Frontiers: frontiers (4), frontier_submissions, frontier_lemmas
├── Validation: definition_audits, definition_patterns
├── NEW: lemma_dependencies (11) - Dependency graph between lemmas
├── NEW: proof_techniques (10) - Standardized proof technique categories
├── NEW: lemma_techniques (8) - Many-to-many lemma↔technique mapping
├── NEW: submission_scaffolding - Which lemmas were used in each submission
├── NEW: failed_approaches (2) - What we tried that didn't work
└── NEW: axiom_confidence_history - Track confidence level changes
```

### Essential Queries

```bash
# What's currently running?
sqlite3 submissions/tracking.db "SELECT uuid, filename FROM submissions WHERE status='running';"

# Proven lemmas available for scaffolding
sqlite3 submissions/tracking.db "SELECT name, english FROM literature_lemmas WHERE proof_status='proven';"

# Open Erdős problems we haven't tried
sqlite3 submissions/tracking.db "
  SELECT ef.number, ef.prize, ef.tractability_score
  FROM erdos_full ef
  LEFT JOIN erdos_attempts ea ON ef.number = ea.problem_num
  WHERE ef.status='open' AND ea.id IS NULL
  ORDER BY ef.tractability_score DESC LIMIT 10;"

# Frontier status
sqlite3 submissions/tracking.db "SELECT name, status, priority FROM frontiers ORDER BY priority;"
```

### Database Operations

```bash
# Track new submission
./scripts/track_submission.sh submissions/file.lean "problem_id" "pattern"

# Direct queries
sqlite3 submissions/tracking.db ".mode column" ".headers on" "YOUR QUERY"
```

**Rule**: No JSON files for tracking. All state in the database.

### Scripts Reference

**Pre-Submission (run before `aristotle prove-from-file`):**

| Script | Purpose | When to Use |
|--------|---------|-------------|
| `./scripts/pre_submit.sh <file>` | Check prior work, scaffolding recommendations, past failures | Always - comprehensive check |
| `./scripts/validate_submission.sh <file>` | Syntax check, definition audit, instance check | Always - catches Lean errors |
| `./scripts/audit_definitions.sh <file>` | Deep check for sInf bugs, Finset.sym2 issues | Called by validate_submission.sh |
| `./scripts/get_scaffolding.sh [--full]` | Generate scaffolding code from proven lemmas | When building scaffolded submission |

**Post-Result (run after `aristotle download <uuid>`):**

| Script | Purpose | When to Use |
|--------|---------|-------------|
| `./scripts/verify_output.sh <file>` | Sorry count, axiom check, compilation test, extract theorems | Always - validates claimed proofs |
| `./scripts/post_result.sh <uuid> <file>` | Update DB, document failures, prompt for insights | Always - captures learnings |
| `./scripts/record_scaffolding.sh <id> <lemma> <type>` | Track which scaffolding was used | After submission for effectiveness tracking |

**Maintenance:**

| Script | Purpose | When to Use |
|--------|---------|-------------|
| `./scripts/find_contaminated.sh <def> <pattern>` | Find files with buggy definition patterns | When hunting down systematic bugs |
| `./scripts/track_submission.sh <file> <id> <pattern>` | Record submission in database | Part of submission workflow |

### New Query Patterns

```bash
# Get transitive dependencies for a lemma (what must be included)
sqlite3 submissions/tracking.db "
WITH RECURSIVE deps AS (
    SELECT depends_on_id as id, 1 as depth
    FROM lemma_dependencies WHERE lemma_id = 'parker2024_tau_S_le_2'
    UNION ALL
    SELECT ld.depends_on_id, d.depth + 1
    FROM lemma_dependencies ld JOIN deps d ON ld.lemma_id = d.id
    WHERE d.depth < 5
)
SELECT DISTINCT ll.name, ll.proof_status FROM deps d
JOIN literature_lemmas ll ON d.id = ll.id;"

# What proof techniques have worked?
sqlite3 submissions/tracking.db "
SELECT pt.name, COUNT(*) as uses FROM lemma_techniques lt
JOIN proof_techniques pt ON lt.technique_id = pt.id
GROUP BY pt.id ORDER BY uses DESC;"

# Check past failures before re-attempting
sqlite3 submissions/tracking.db "
SELECT approach_name, why_failed, avoid_pattern
FROM failed_approaches WHERE frontier_id = 'nu_4';"

# Low-confidence axioms (use with caution)
sqlite3 submissions/tracking.db "
SELECT name, axiom_confidence FROM literature_lemmas
WHERE axiom_confidence IN ('folklore', 'should_prove');"
```

---

## What Aristotle Is

Aristotle (by Harmonic) is a **200B+ parameter system** combining:
- Monte Carlo Graph Search over Lean proof states
- Informal reasoning (generates natural language proofs first)
- Iterative error feedback from Lean verification
- Massive parallel search (hundreds of millions of strategies)

**Key facts**:
- Runtime: 6+ hours is normal
- It CAN discover unexpected connections (found 4 counterexamples in Tao's textbook)
- Boris Alexeev's success on Erdős #124 came from a formalization gap exposing a connection to Brown's criterion

---

## Submission Workflow

### Phase 1: Problem Selection

Check it's genuinely open (see Progress Verification above), then:

```bash
# For Erdős: find tractable open problems
sqlite3 submissions/tracking.db "
  SELECT number, prize, tractability_score FROM erdos_full
  WHERE status='open' AND has_lean4=1
  ORDER BY tractability_score DESC LIMIT 10;"

# For Tuza: check frontier status
sqlite3 submissions/tracking.db "SELECT * FROM frontiers;"
```

### Phase 2: Check Prior Work

```bash
# RECOMMENDED: Run comprehensive pre-submission check
./scripts/pre_submit.sh submissions/file.lean

# Or manually query lemmas:
sqlite3 submissions/tracking.db "
  SELECT name, statement FROM literature_lemmas
  WHERE proof_status='proven' AND paper_id='parker2024';"
```

The pre_submit.sh script checks: proven lemmas, past failures, axiom risks, and dependencies.
Integrate relevant lemmas as scaffolding.

### Phase 3: Submit

```bash
# Validate
./scripts/validate_submission.sh submissions/file.lean

# Track
./scripts/track_submission.sh submissions/file.lean "problem_id" "pattern"

# Submit
aristotle prove-from-file submissions/file.lean --no-wait
```

### Phase 4: Process Results

```bash
# Download output
aristotle download <UUID>

# 1. Verify the output (sorry count, axiom check, compilation, definition audit)
./scripts/verify_output.sh output.lean

# 2. Update database and document learnings
./scripts/post_result.sh <UUID> output.lean

# 3. Record scaffolding effectiveness (if scaffolding was used)
./scripts/record_scaffolding.sh <submission_id> <lemma_id> full_proof
```

If claimed proven: verify_output.sh will compile and re-audit definitions.
If partial progress: post_result.sh prompts you to document what failed and why.

### Phase 5: End-of-Session Verification (CRITICAL)

**Before ending any work session, ALWAYS run:**

```bash
# Check for forgotten submissions
sqlite3 submissions/tracking.db "SELECT filename FROM submissions WHERE status='pending' AND uuid IS NULL;"

# This should return ZERO rows. If not, submit them!
```

**Lessons from Dec 22, 2024 incident:**
- 6 files were created, tracked as "pending", but NEVER submitted to Aristotle
- Root causes: context switching, high-level todos, no verification step
- Files sat unsubmitted while we moved on to other work

**Prevention rules:**
1. **Track = Submit**: After `track_submission.sh`, IMMEDIATELY run `aristotle prove-from-file`
2. **Individual todos**: Track EACH file submission, not "create portfolio"
3. **End-of-session check**: Run the query above before stopping work
4. **Naming consistency**: Use same filename in tracking DB and Aristotle

---

## Submission Patterns

| Pattern | Lines | When to Use | Outcome |
|---------|-------|-------------|---------|
| **Boris Minimal** | 35-47 | First attempt | Highest success rate |
| **Scaffolded** | 100+ | After identifying gaps | Builds on proven lemmas |
| **Prescriptive** | 150+ | Testing specific strategy | Often finds counterexamples |

### Boris Minimal (Default)

- Just definitions + theorem statement
- **No comments** — comments constrain Aristotle's search
- Let it explore freely

### Scaffolded

- Include FULL PROVEN PROOFS as helper lemmas (not axioms)
- Query `literature_lemmas` for available scaffolding
- No strategic comments

**CRITICAL RULE**: NEVER delete proven code and replace with `sorry` just to make local compilation faster. Aristotle has much more compute than local machines. If scaffolded files timeout locally due to heartbeats, that's OK - increase `maxHeartbeats` or accept the timeout. The proven proofs are valuable and must be preserved.

### Dual Submission

For important problems, submit both:
```
problem.lean  → formal
problem.md    → informal (natural language proof)
```

Informal sometimes succeeds where formal fails.

---

## Pre-Submission Validation

**Always validate before submitting.**

```bash
./scripts/validate_submission.sh submissions/file.lean
```

### Critical Pitfalls

| Issue | Problem | Fix |
|-------|---------|-----|
| `sInf` unrestricted | Allows invalid edge sets | Require `E ⊆ G.edgeFinset` |
| `Finset.sym2` | Includes self-loops s(v,v) | Filter to actual edges |
| `Set` vs `Finset` | Missing decidability | Use `Finset V` with `DecidableEq` |

Files with these bugs → `submissions/CORRUPTED/`

### Required Instances

```lean
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
```

---

## Multi-Agent Strategy

For strategic decisions, use multiple AI models in parallel:

| Agent | Best For | Avoid |
|-------|----------|-------|
| **Grok-4** | Lean syntax review, finding code bugs | Math reasoning (times out) |
| **Gemini** | Literature connections, proof strategy, architecture | Detailed code review |
| **Claude** | Long context synthesis, planning, writing | - |

### Pattern

1. Ask all three the same strategic question in parallel
2. Look for consensus and disagreements
3. Disagreements often reveal the interesting considerations
4. Synthesize into a decision

### Grok for Lean Review

```bash
# System prompt: "Lean 4 syntax checker. Check if code compiles. DO NOT solve math."
# temperature=0, max_tokens=800
```

---

## Currently Open Targets

### Tuza Frontiers (Primary)

| Target | Status | Why Open |
|--------|--------|----------|
| ν = 4 | Active | Parker's proof breaks here |
| Split graphs (general) | Submitted | Only threshold subset proven |
| Counterexample | Submitted | None known to exist |
| Hypergraph r=4 | Submitted | Aharoni-Zerbib conjecture |

### Counterexample Constraints

Any counterexample to Tuza must satisfy (from literature):
- mad(G) ≥ 7
- χ(G) ≥ 5
- NOT tripartite, NOT threshold
- treewidth ≥ 7

### Erdős Problems (Secondary)

Query for tractable open problems:
```bash
sqlite3 submissions/tracking.db "
  SELECT number, prize, tractability_score FROM erdos_full
  WHERE status='open' ORDER BY tractability_score DESC LIMIT 10;"
```

---

## Rate Limits

**5-7 concurrent Aristotle slots.** This is the bottleneck.

```bash
# Check current usage
sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='running';"
```

Prioritize genuinely open problems over re-formalization.

---

## Quick Reference

### Key Tables

| Table | Purpose |
|-------|---------|
| `submissions` | All Aristotle jobs |
| `literature_lemmas` | Proven lemmas for scaffolding |
| `lemma_dependencies` | What lemmas depend on what (for transitive scaffolding) |
| `proof_techniques` | Standardized proof method categories |
| `lemma_techniques` | Which techniques each lemma uses |
| `submission_scaffolding` | Which lemmas were used in each submission + effectiveness |
| `failed_approaches` | What we tried that didn't work (avoid repeating) |
| `frontiers` | Open problems we're attacking |
| `erdos_full` | 1111 Erdős problems |
| `counterexample_constraints` | What counterexamples must satisfy |

### Entry Points

| Task | Action |
|------|--------|
| Submit new problem | `pre_submit.sh` → `validate_submission.sh` → `track_submission.sh` → submit |
| Process results | `verify_output.sh` → `post_result.sh` → `record_scaffolding.sh` |
| Check past failures | `SELECT * FROM failed_approaches WHERE frontier_id='...'` |
| Get dependencies | Use recursive CTE on `lemma_dependencies` |
| Find scaffolding | `SELECT * FROM literature_lemmas WHERE proof_status='proven'` |
| Find contaminated files | `./scripts/find_contaminated.sh <def> <pattern>` |
| Audit progress | See query below |

### Audit: Discovery vs Formalization

```bash
# How much of our work is genuine discovery?
sqlite3 submissions/tracking.db "
  SELECT novelty_level, COUNT(*) as count
  FROM submissions
  WHERE novelty_level IS NOT NULL
  GROUP BY novelty_level
  ORDER BY count DESC;"

# Submissions missing novelty assessment
sqlite3 submissions/tracking.db "
  SELECT uuid, filename, problem_id
  FROM submissions
  WHERE novelty_level IS NULL
  LIMIT 10;"
```

### Track with Novelty

```bash
# Full tracking with novelty level
./scripts/track_submission.sh submissions/file.lean "tuza_nu4" "boris_minimal" "discovery" "First proof of Tuza for ν=4"
```
