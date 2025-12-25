# CLAUDE.md - Math Project (v2 Draft)

## Mission

**Goal**: Prove genuinely open mathematical conjectures using Aristotle, with compounding learning.

**Primary Target**: Tuza's Conjecture ν=4 (Parker's proof breaks here)

**Core Principle**: Every submission should be better than the last. Learning compounds.

---

## System Invariants

These MUST always be true. Violations are bugs.

| Invariant | Enforcement | Check |
|-----------|-------------|-------|
| Every .lean in `submissions/` is tracked | `submit.sh` wrapper blocks untracked | `find submissions -name "*.lean" \| wc -l` == `SELECT COUNT(*) FROM submissions` |
| No submission has blank `problem_id` | DB constraint NOT NULL | `SELECT COUNT(*) FROM submissions WHERE problem_id IS NULL OR problem_id=''` → 0 |
| Every completed result is analyzed | Auto-analyze on download | `SELECT COUNT(*) FROM submissions WHERE status='completed' AND id NOT IN (SELECT submission_id FROM audit_log)` → 0 |
| Every failure updates `failed_approaches` | Prompted by `post_result.sh` | Manual review |
| Every success updates `literature_lemmas` | Prompted by `post_result.sh` | `SELECT COUNT(*) FROM submissions WHERE sorry_count=0` ≤ `SELECT COUNT(*) FROM literature_lemmas WHERE paper_id='aristotle_proven'` |

---

## State Machine

```
                    ┌─────────────┐
                    │   CREATED   │ File exists, not yet validated
                    └──────┬──────┘
                           │ validate_submission.sh passes
                           ▼
                    ┌─────────────┐
                    │  VALIDATED  │ Syntax OK, definitions audited
                    └──────┬──────┘
                           │ track_submission.sh (with problem_id, pattern)
                           ▼
                    ┌─────────────┐
                    │   TRACKED   │ In database, awaiting submission
                    └──────┬──────┘
                           │ aristotle prove-from-file (captures UUID)
                           ▼
                    ┌─────────────┐
                    │   RUNNING   │ Aristotle processing (6+ hours)
                    └──────┬──────┘
                           │ aristotle download <uuid>
                           ▼
                    ┌─────────────┐
                    │ DOWNLOADED  │ Output file exists locally
                    └──────┬──────┘
                           │ post_result.sh (analysis + learning capture)
                           ▼
              ┌────────────┴────────────┐
              ▼                         ▼
    ┌─────────────────┐       ┌─────────────────┐
    │     PROVEN      │       │    ANALYZED     │
    │  (sorry_count=0)│       │ (sorry_count>0) │
    └────────┬────────┘       └────────┬────────┘
             │                         │
             ▼                         ▼
    ┌─────────────────┐       ┌─────────────────┐
    │ SCAFFOLDING     │       │  NEEDS_FOLLOWUP │ (if 1-2 sorry)
    │ EXTRACTED       │       │  or CLOSED      │ (if hopeless)
    └─────────────────┘       └─────────────────┘
```

**Illegal Transitions:**
- CREATED → RUNNING (must validate and track first)
- TRACKED → DOWNLOADED (must submit to Aristotle first)
- DOWNLOADED → any terminal state (must analyze first)

---

## Decision Rules (Priority Order)

Before ANY new submission, evaluate in this order:

### Rule 1: Complete Near-Misses First
```sql
SELECT * FROM submissions
WHERE status='completed' AND sorry_count BETWEEN 1 AND 2 AND proven_count > 0
ORDER BY sorry_count, completed_at DESC;
```
**IF results exist → work on these BEFORE new submissions**

Rationale: 15% conversion rate on near-misses is unacceptable. These are almost-wins.

### Rule 2: Respect Saturation Limits
```sql
SELECT COUNT(*) FROM submissions
WHERE problem_id = :target AND status IN ('running', 'submitted');
```
**IF count > 3 → WAIT for results before submitting more**

Rationale: Parallel submissions without learning between them wastes slots.

### Rule 3: Cover Uncovered Cases
```sql
SELECT * FROM nu4_cases WHERE status = 'open' ORDER BY priority;
```
**IF open cases exist → target those, not already-attempted cases**

Rationale: Systematic coverage beats random exploration.

### Rule 4: Use All Available Scaffolding
```sql
SELECT name, statement FROM literature_lemmas
WHERE proof_status = 'proven'
ORDER BY created_at DESC;
```
**Every new submission MUST include relevant proven lemmas**

Rationale: Scaffolded submissions have 1.7 avg sorry vs 2.5 for minimal.

### Rule 5: Check Failed Approaches
```sql
SELECT approach_name, why_failed, avoid_pattern
FROM failed_approaches WHERE frontier_id = :target;
```
**IF new submission matches avoid_pattern → BLOCK or redesign**

Rationale: We have 12 documented failures. Stop repeating them.

---

## Atomic Operations

These operations are indivisible. Cannot do step N without completing step N-1.

### Operation: SUBMIT
```bash
#!/bin/bash
# scripts/submit.sh - Atomic submission
set -e

FILE="$1"
PROBLEM_ID="$2"
PATTERN="${3:-scaffolded}"

# Gate 1: File must exist
[ -f "$FILE" ] || { echo "ERROR: File not found"; exit 1; }

# Gate 2: Must pass validation
./scripts/validate_submission.sh "$FILE" || { echo "ERROR: Validation failed"; exit 1; }

# Gate 3: Must not match failed approaches
MATCHES=$(sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM failed_approaches WHERE '$FILE' LIKE '%' || avoid_pattern || '%';")
[ "$MATCHES" -eq 0 ] || { echo "WARNING: Matches failed approach pattern. Review required."; }

# Gate 4: Track in database (returns ID)
ID=$(./scripts/track_submission.sh "$FILE" "$PROBLEM_ID" "$PATTERN" | tail -1)

# Gate 5: Submit to Aristotle (returns UUID)
UUID=$(aristotle prove-from-file "$FILE" --no-wait 2>&1 | grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' | head -1)

# Gate 6: Update database with UUID
sqlite3 submissions/tracking.db "UPDATE submissions SET uuid='$UUID', status='running', submitted_at=datetime('now') WHERE id=$ID;"

echo "SUCCESS: Submitted $FILE as $UUID (DB ID: $ID)"
```

### Operation: PROCESS_RESULT
```bash
#!/bin/bash
# scripts/process_result.sh - Atomic result processing
set -e

UUID="$1"

# Gate 1: Download output
OUTPUT="/tmp/aristotle_outputs/${UUID}.lean"
mkdir -p /tmp/aristotle_outputs
aristotle download "$UUID" -o "$OUTPUT" || { echo "ERROR: Download failed"; exit 1; }

# Gate 2: Run verification
./scripts/verify_output.sh "$OUTPUT" || echo "WARNING: Verification issues"

# Gate 3: Update database and capture learnings
./scripts/post_result.sh "$UUID" "$OUTPUT"

# Gate 4: Extract proven lemmas to scaffolding
SORRY_COUNT=$(grep -c 'sorry' "$OUTPUT" || echo 0)
if [ "$SORRY_COUNT" -eq 0 ]; then
    echo "FULL PROOF - extracting to literature_lemmas"
    ./scripts/extract_proven.sh "$OUTPUT"
fi

echo "SUCCESS: Processed $UUID"
```

---

## Learning Capture

Every Aristotle result teaches us something. This section defines what we learn and how.

### From Successful Proofs (sorry_count = 0)
1. **Extract proven lemmas** → Add to `literature_lemmas` with `paper_id='aristotle_proven'`
2. **Record proof technique** → Add to `lemma_techniques`
3. **Update case coverage** → Mark case as 'proven' in `nu4_cases`

### From Partial Proofs (sorry_count = 1-2)
1. **Identify what succeeded** → Which sub-lemmas proved?
2. **Identify what blocked** → What was the remaining sorry about?
3. **Create follow-up submission** → Target specifically the blocked lemma
4. **Queue for priority processing** → Near-misses go to front of queue

### From Failures (sorry_count > 2 or counterexample)
1. **Document failure reason** → Add to `failed_approaches` with specific `avoid_pattern`
2. **Extract any proven sub-lemmas** → Still valuable for scaffolding
3. **Identify if approach is fundamentally flawed** → Update strategy

### From Counterexamples
1. **This is valuable negative knowledge** → Document in `failed_approaches`
2. **The lemma is FALSE** → Never assume it again
3. **Update literature_lemmas** → Mark as `proof_status='disproven'`
4. **Propagate to dependent submissions** → Any submission using this lemma is suspect

---

## Case Coverage (ν=4)

Explicit tracking of which cases have been attempted/proven.

| Case | Description | Status | Best Submission | Sorry | Notes |
|------|-------------|--------|-----------------|-------|-------|
| `star_all_4` | All 4 packing elements share vertex v | **PROVEN** | slot29 | 0 | tau_le_8_star |
| `three_share_v` | 3 share vertex v, 1 disjoint | **PROVEN** | slot29 | 0 | tau_le_8_three_share_v |
| `two_two_vw` | 2 share v, 2 share w, v≠w | OPEN | - | - | Not yet attempted |
| `path_4` | Sharing graph is path P4 | PARTIAL | slot32 | 2 | Needs follow-up |
| `cycle_4` | Sharing graph is C4 | PARTIAL | slot33 | 2 | Needs follow-up |
| `matching_2` | Sharing graph is 2K2 (matching) | OPEN | - | - | Not yet attempted |
| `scattered` | No vertex in >1 packing element | OPEN | - | - | Hardest case |

**Target**: All cases PROVEN or IMPOSSIBLE → ν=4 complete

---

## Metrics Dashboard

Run at start of each session:

```sql
-- SESSION BRIEFING
SELECT '════════════════════════════════════════' as '';
SELECT 'ARISTOTLE SESSION BRIEFING' as header, datetime('now') as time;
SELECT '════════════════════════════════════════' as '';

SELECT 'Currently running:' as metric, COUNT(*) as value
FROM submissions WHERE status='running';

SELECT 'Near-misses (HIGH priority):' as metric, COUNT(*) as value
FROM submissions WHERE status='completed' AND sorry_count=1;

SELECT 'Near-misses (MEDIUM priority):' as metric, COUNT(*) as value
FROM submissions WHERE status='completed' AND sorry_count=2;

SELECT 'Cases proven (ν=4):' as metric, COUNT(*) as value
FROM nu4_cases WHERE status='proven';

SELECT 'Cases open (ν=4):' as metric, COUNT(*) as value
FROM nu4_cases WHERE status='open';

SELECT 'Tracking coverage:' as metric,
       ROUND(100.0 * (SELECT COUNT(*) FROM submissions) /
             (SELECT COUNT(*) FROM (SELECT 1)), 1) || '%' as value;

SELECT '════════════════════════════════════════' as '';
SELECT 'RECOMMENDED NEXT ACTION:' as header;
-- Priority: near-misses > open cases > new exploration
SELECT CASE
    WHEN (SELECT COUNT(*) FROM submissions WHERE status='completed' AND sorry_count=1) > 0
    THEN 'Follow up on HIGH priority near-miss'
    WHEN (SELECT COUNT(*) FROM nu4_cases WHERE status='open') > 0
    THEN 'Attempt open case: ' || (SELECT case_name FROM nu4_cases WHERE status='open' LIMIT 1)
    ELSE 'Explore new approach'
END as recommendation;
```

### Target Metrics

| Metric | Current | Target | How to Improve |
|--------|---------|--------|----------------|
| Tracking coverage | 24% | 100% | Use atomic submit.sh |
| Near-miss conversion | 15% | 50% | Prioritize follow-ups |
| Result capture rate | ~50%? | 100% | Auto-download daemon |
| Failed approach repeats | ~20%? | 0% | Pre-submit check |
| Avg sorry (scaffolded) | 1.7 | 1.0 | Better scaffolding |

---

## Session Protocol

### Session Start
1. Run metrics dashboard query
2. Check recommended action
3. Review any completed submissions from background

### During Session
1. Use atomic `submit.sh` for all submissions (NEVER raw aristotle command)
2. Process results immediately when available
3. Update case coverage after each result

### Session End (MANDATORY)
```bash
# BEFORE CLOSING - MUST PASS
./scripts/session_end_check.sh

# This checks:
# 1. No pending submissions (tracked but not submitted)
# 2. No unprocessed downloads
# 3. All state is consistent
```

**If check fails → FIX BEFORE CLOSING**

---

## Scaffolding Rules

### What to Include
1. **All proven lemmas relevant to target** (from `literature_lemmas`)
2. **Full proof code** (never sorry placeholders)
3. **Dependency chain** (use recursive CTE on `lemma_dependencies`)

### What NOT to Include
1. Comments suggesting strategy (constrains Aristotle's search)
2. Sorry placeholders for proven lemmas (wastes compute)
3. Axioms without confidence (propagates risk)

### Scaffolding Template
```lean
/-
Target: [specific theorem]
Case: [which nu4_case]
Prior attempts: [list relevant submission IDs]
-/

import Mathlib

-- SCAFFOLDING: Proven lemmas (DO NOT MODIFY)
[full proofs from literature_lemmas]

-- TARGET: What we want Aristotle to prove
theorem main_target ... := by sorry
```

---

## Anti-Patterns (BANNED)

| Pattern | Why Banned | Instead Do |
|---------|------------|------------|
| Portfolio submissions (10+ files at once) | No learning between submissions | Submit 2-3, wait for results, iterate |
| Blank problem_id | Can't track or analyze | Always specify: `tuza_nu4_[case]` |
| Skip validation | Wastes Aristotle compute | Atomic submit.sh enforces validation |
| Sorry in scaffolding | Aristotle reproves known results | Include full proof code |
| Ignore partial results | Lose near-wins | Always follow up on 1-2 sorry |
| Repeat failed approach | Wastes slots | Check `failed_approaches` first |

---

## Quick Reference

### Essential Commands
```bash
# Submit (atomic - validates, tracks, submits)
./scripts/submit.sh file.lean problem_id pattern

# Check what's running
sqlite3 submissions/tracking.db "SELECT uuid, filename FROM submissions WHERE status='running';"

# Process a completed result
./scripts/process_result.sh <UUID>

# Session end check
./scripts/session_end_check.sh

# Near-misses needing follow-up
sqlite3 submissions/tracking.db "SELECT * FROM v_needs_followup;"

# Failed approaches to avoid
sqlite3 submissions/tracking.db "SELECT approach_name, avoid_pattern FROM failed_approaches WHERE frontier_id='nu_4';"
```

### When Stuck
1. Check failed_approaches - are we repeating a mistake?
2. Check near-misses - is there a 1-sorry to complete?
3. Check case coverage - what's actually open?
4. Consult Grok/Gemini with full context
5. Try informal (.md) submission

---

## Changelog

- v2.0: Complete rewrite. Constraint-based architecture. State machine. Atomic operations.
- v1.x: Procedural documentation (deprecated)
