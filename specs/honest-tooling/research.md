---
spec: honest-tooling
phase: research
created: 2026-02-15
---

# Research: honest-tooling

## Executive Summary

Five files need changes to implement honest labels (`compiled_clean` instead of `proven`), split duplicate/rate-limit checks, add batch mode, extend the mk CLI, and align downstream consumers. The `submissions` table has 203 rows with status `proven` (189 verified) that will need migration. The knowledge.db schema has CHECK constraints that must be updated to accept a new status value or the `proven` value must be preserved there while only changing display strings.

## File-by-File Analysis

### 1. `scripts/aristotle_fetch.py` (481 lines)

**Verdict assignment** (line 132-141):
```python
# Line 132-141: audit_file() verdict logic
if has_load_error and sorry_count > 0:
    verdict = "failed"
elif sorry_count == 0 and axiom_count == 0 and not has_negation:
    verdict = "proven"          # <-- CHANGE to "compiled_clean"
elif has_negation:
    verdict = "disproven"
elif sorry_count == 1:
    verdict = "near_miss"
else:
    verdict = "completed"
```

**DB writes referencing "proven"** (lines 175, 192):
```python
# Line 175 (UPDATE path):
1 if audit["verdict"] == "proven" else 0,     # verified column
# Line 192 (INSERT path):
1 if audit["verdict"] == "proven" else 0,     # verified column
```
Both set `verified = 1` when verdict is "proven". Must change to check `"compiled_clean"`.

**Display strings referencing "PROVEN"** (lines 264, 372, 380, 387):
```python
# Line 264 (cmd_status, fetched results):
emoji = "✅" if verdict == "PROVEN" else "📝" if verdict == "NEAR_MISS" else "❌"
# Line 372 (cmd_fetch, fresh downloads):
emoji = "✅" if verdict == "PROVEN" else "📝" if verdict == "NEAR_MISS" else "⚠️"
# Line 380:
if verdict == "PROVEN":
    proven += 1
# Line 387:
print(f"Done: {fetched} fetched, {proven} proven.")
```
All use `.upper()` on verdict, so comparisons are against "PROVEN". Must change to "COMPILED_CLEAN".

**target_resolved column**: Does not exist in submissions schema. Must be added via `ALTER TABLE submissions ADD COLUMN target_resolved INTEGER DEFAULT 0`.

**Total changes in this file: 7 locations**

---

### 2. `scripts/safe_aristotle_submit.py` (387 lines)

**`check_recent_submissions()` (lines 76-103)**: Currently does two things in one function:
1. **Duplicate detection** (lines 81-89): Checks transaction log for same `task_hash` in window
2. **Rate limiting** (lines 92-103): Calls `Project.list_projects(limit=20)` API to find recent submissions

```python
async def check_recent_submissions(task_hash: str, window_minutes: int = 10) -> list:
    # Part 1: Transaction log duplicate check (fast, local)
    if TRANSACTION_LOG.exists():
        recent_cutoff = datetime.now() - timedelta(minutes=window_minutes)
        with open(TRANSACTION_LOG) as f:
            for line in f:
                entry = json.loads(line)
                timestamp = datetime.fromisoformat(entry['timestamp']).replace(tzinfo=None)
                if timestamp > recent_cutoff:
                    if entry['details'].get('task_hash') == task_hash:
                        return [entry]
    # Part 2: API rate limit check (slow, network)
    projects, _ = await Project.list_projects(limit=20)
    # ...counts projects created in last window_minutes
```

**Split plan**:
- `check_duplicate(task_hash, window_minutes)` -> transaction log only, returns bool
- `check_rate_limit(window_minutes)` -> API call only, returns `{count, has_capacity}`

**`safe_submit()` (lines 121-258)**: Currently calls `check_recent_submissions()` at line 168. Must call both new functions separately.

**--batch flag**: Not present. CLI parsing at lines 312-386. Need to:
1. Add `--batch` to flag parsing
2. When `--batch`, skip interactive rate-limit check (still do duplicate check)
3. Or: `--batch` accepts multiple input files

**`check_queue_capacity()` (lines 106-118)**: Already separate. Calls `Project.list_projects(limit=10)`. Note: this makes a SECOND API call (the first is in `check_recent_submissions`). After split, `check_rate_limit` and `check_queue_capacity` both call `list_projects` -- could be merged to one API call.

**Total changes in this file: 3-4 locations** (function split, callers, CLI flags)

---

### 3. `math-forge/scripts/mk` (310 lines)

**Existing commands**: search, find, strategies, failed, stats, init, help

**New commands to add**:

| Command | Purpose | Data Source |
|---------|---------|-------------|
| `submit` | Submit sketch via safe_aristotle_submit.py | Wrapper around scripts/safe_aristotle_submit.py |
| `status` | Show Aristotle queue status | Wrapper around scripts/aristotle_fetch.py status |
| `partials` | List near-miss submissions (sorry=1) | tracking.db query |
| `resubmittable` | List failed/partial submissions eligible for resub | tracking.db query |
| `query` | Run arbitrary SQL against tracking.db | sqlite3 pass-through |

**Architecture**: Uses `case` statement (line 64-309). Each command is a `case` branch. New commands follow same pattern.

**Helper functions available**: `run_sql()` (line 35-46), `escape_sql()` (line 31-33), `check_db()` (line 54-60). Also has `TRACKING_DB` variable (line 17-21).

**DB badge display** (line 95): `WHEN 'theorem' THEN '[PROVEN]'` -- this is in the FTS search display, refers to finding_type='theorem', not the status. This should probably change to `[COMPILED]` or stay as-is since it's about theorem findings, not submission status.

**Total changes: 5 new case branches + help text update**

---

### 4. `math-forge/scripts/extract_findings.py` (384 lines)

**Status assignment** (line 357):
```python
status = 'proven' if extracted['sorry_count'] == 0 and extracted['axiom_count'] == 0 else 'partial'
if extracted['sorry_count'] > 2:
    status = 'open'
```
This assigns status for the `problems` table in knowledge.db. The knowledge.db `problems.status` CHECK constraint is: `'open', 'proven', 'partial', 'false', 'in_flight'` (schema.sql line 86).

**UPSERT logic** (lines 361-370):
```python
cursor.execute("""
    INSERT INTO problems (id, name, domain_id, status, submission_count, proven_count, failed_count, statement)
    VALUES (?, ?, ?, ?, 1, ?, ?, ?)
    ON CONFLICT(id) DO UPDATE SET
        submission_count = submission_count + 1,
        proven_count = proven_count + excluded.proven_count,
        failed_count = failed_count + excluded.failed_count,
        status = CASE WHEN excluded.status = 'proven' THEN 'proven' ELSE status END,
        updated_at = datetime('now')
""", (problem_id, problem_id, domain, status, proven_count, failed_count, ''))
```
The UPSERT's CASE uses `'proven'` to promote problem status. If we change the status string, this CASE must match.

**Decision**: The knowledge.db `problems.status` CHECK constraint allows `'proven'`. Changing this would require:
1. ALTER TABLE to update CHECK constraint (SQLite doesn't support ALTER CHECK -- requires table recreation)
2. Updating all 19 existing `proven` rows in problems table
3. Updating schema.sql
4. Updating migrate_tracking.py status_map (line 180)

**Recommendation**: Keep `'proven'` in knowledge.db problems table (it means "problem is proven"). Change only `extract_findings.py` status string if desired, but the knowledge.db concept of "proven problem" is semantically correct -- the issue is only with tracking.db's submission status.

**Alternative**: Only change tracking.db submission status. Leave knowledge.db alone. The display badge `[PROVEN]` in mk search (line 95) refers to findings of type='theorem', which IS correct -- a theorem finding IS a proven result.

**Total changes: 1-2 locations** (if changing) or **0** (if scoped to tracking.db only)

---

### 5. `scripts/audit_proven.py` (248 lines)

**IN clauses with 'proven'**:

```python
# Line 95:
WHERE status IN ('proven', 'PROVEN')

# Line 237:
"SELECT COUNT(*) FROM submissions WHERE status IN ('proven', 'PROVEN') AND verified = 1"

# Line 240:
"SELECT COUNT(*) FROM submissions WHERE status IN ('proven', 'PROVEN') AND (notes LIKE '%AUDIT WARNING%')"
```

All three query the tracking.db `submissions.status` column. Must add `'compiled_clean'` to each IN clause.

**Also**: Display strings at lines 98, 127, 192, 223, 242 use "proven" in print statements. These are human-readable labels, not DB queries. Should be updated for consistency.

**Total changes: 3 SQL IN clauses + 5 display string updates**

---

## Submissions Table Schema

```sql
CREATE TABLE submissions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    uuid TEXT UNIQUE,
    filename TEXT NOT NULL,
    problem_id TEXT,
    pattern TEXT,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    submitted_at TEXT,
    completed_at TEXT,
    status TEXT DEFAULT 'draft',
    syntax_valid INTEGER,
    definition_audit_passed INTEGER,
    definition_issues TEXT,
    aristotle_status TEXT,
    sorry_count INTEGER,
    proven_count INTEGER,     -- NOTE: this is "proven theorem count", not "is proven"
    output_file TEXT,
    grok_issues TEXT,
    gemini_issues TEXT,
    verified INTEGER,
    verification_notes TEXT,
    novelty_level TEXT,
    contribution_statement TEXT,
    prior_work_checked INTEGER DEFAULT 0,
    notes TEXT,
    execution_seconds INTEGER,
    helper_count INTEGER,
    fin_size INTEGER,
    frontier_id TEXT
);
```

**Missing column**: `target_resolved` (INTEGER DEFAULT 0)
**Current status distribution**: 203 `proven`, 449 `completed`, 76 `near_miss`, 42 `failed`, etc.

## Migration Plan for Existing Data

Option A: Update all 203 `proven` rows to `compiled_clean`:
```sql
ALTER TABLE submissions ADD COLUMN target_resolved INTEGER DEFAULT 0;
UPDATE submissions SET status = 'compiled_clean' WHERE status = 'proven';
```
- **Risk**: Any other scripts/queries using `status = 'proven'` will break
- **Must also update**: backfill_slots.py (line 111), backfill_all_files.py (line 83), context-loader.sh (line 32 query uses `verified=1` not status, so OK)

Option B: Keep `proven` in DB, only change display:
- Less disruptive but inconsistent

**Recommendation**: Option A (full migration). The whole point is honest labels.

## Cross-File "proven" References (beyond 5 target files)

| File | Line(s) | Nature | Action |
|------|---------|--------|--------|
| `scripts/backfill_slots.py` | 111, 167, 176 | Sets/checks `status = 'proven'` | Update to `compiled_clean` |
| `scripts/backfill_all_files.py` | 83 | Sets `status = 'proven'` | Update to `compiled_clean` |
| `math-forge/hooks/scripts/context-loader.sh` | 32 | Queries `verified=1 AND sorry_count=0` (not status) | No change needed |
| `math-forge/scripts/migrate_tracking.py` | 180-181 | Maps old statuses to `'proven'` in knowledge.db | Keep as-is (different DB) |
| `math-forge/data/schema.sql` | 66, 86 | CHECK constraints include `'proven'` | Keep as-is (knowledge.db) |
| `scripts/pre_submit.sh` | 36, 52 | `proof_status='proven'` (literature_lemmas table) | Different table, no change |
| `scripts/get_scaffolding.sh` | 17, 35 | `proof_status IN ('definition','proven')` | Different table, no change |
| `scripts/verify_output.sh` | 23-95 | Display string "PROVEN" | Update display |
| `scripts/post_result.sh` | 44, 53 | Display string | Update display |
| `scripts/submit_parker_batch.py` | 21+ | Dict key `"proven"` (counter) | Internal counter, rename optional |

## Risks and Edge Cases

1. **Active in-flight submissions**: 6 `submitted` status rows. Fetching these after the change will assign `compiled_clean` instead of `proven`. This is the desired behavior.

2. **knowledge.db vs tracking.db semantics**: knowledge.db `problems.status = 'proven'` means "we have proven results for this problem" -- semantically different from "Lean compiled clean". Recommend NOT changing knowledge.db.

3. **DB migration atomicity**: The `ALTER TABLE` + `UPDATE` must be done in same transaction (or at least same script run) to avoid inconsistency.

4. **Existing views in tracking.db**: Check for views using `status = 'proven'`:
   - `v_actionable_near_misses` -- uses `sorry_count = 1`, not `status = 'proven'`
   - `v_false_lemmas_summary` -- doesn't reference submission status
   - `v_candidate_ranking` -- uses `candidate_problems` table, not `submissions`
   No tracking.db views need updating.

5. **BATS tests**: `math-forge/tests/test_helper.bash` line 37 inserts test data with status `'proven'` (into knowledge.db strategies table, not tracking.db). This is knowledge.db, so no change needed.

## Related Specs

| Spec | Relevance | mayNeedUpdate |
|------|-----------|---------------|
| math-forge | Low: shares mk CLI, extract_findings.py. Changes are additive (new commands). extract_findings.py change is in tracking.db status only | false |
| erdos364 | None: problem-specific research | false |
| sierpinski-5n | None: problem-specific research | false |

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| BATS Tests | `bats math-forge/tests/` | math-forge/tests/*.bats |
| Lint | Not found | N/A |
| TypeCheck | Not found | N/A |
| Build | Not found | N/A |
| Python Tests | Not found | N/A |

**Local CI**: `bats math-forge/tests/` (only available quality check)

## Feasibility Assessment

| Aspect | Assessment | Notes |
|--------|------------|-------|
| Technical Viability | High | Straightforward string replacements + function split |
| Effort Estimate | M | 5 files + DB migration + test updates |
| Risk Level | Low | All changes are in display/status strings. DB migration is one UPDATE. |

## Recommendations for Requirements

1. **Scope knowledge.db changes carefully**: Do NOT change `problems.status = 'proven'` or `strategies.outcome = 'proven'` in knowledge.db. These are semantically correct ("the problem is proven"). Only change tracking.db `submissions.status` from `'proven'` to `'compiled_clean'`.

2. **Add `target_resolved` column** to tracking.db submissions table. Default 0. Set manually when a submission actually resolves an open problem. This is the honest signal.

3. **Split `check_recent_submissions()`** into `check_duplicate()` (local log check) and `check_rate_limit()` (API call). Merge `check_rate_limit()` with `check_queue_capacity()` to avoid double API calls.

4. **New mk commands** should use `run_sql "$TRACKING_DB"` for submission queries, not knowledge.db. The `submit` command should delegate to `python3 scripts/safe_aristotle_submit.py` with passthrough args.

5. **Migration script**: Write a one-shot script or inline SQL to: (a) ALTER TABLE add target_resolved, (b) UPDATE status='compiled_clean' WHERE status='proven'.

6. **Also update these files** not in the original 5-file list:
   - `scripts/backfill_slots.py` (line 111)
   - `scripts/backfill_all_files.py` (line 83)
   - `scripts/verify_output.sh` (display strings)

7. **mk search badge**: The `[PROVEN]` badge for `finding_type='theorem'` in mk search (mk line 95) should stay as-is -- it describes a theorem finding, not a submission status.

## Open Questions

1. Should `--batch` accept a file listing multiple sketch paths, or should it accept multiple positional args? (e.g., `--batch sketch1.txt sketch2.txt` vs `--batch batch_list.txt`)

2. Should `mk submit` be a simple wrapper or should it do additional pre-checks (like `mk failed` query)?

3. The `proven_count` column name in tracking.db means "number of theorems proven in the file". Should this be renamed to `theorem_count` for clarity, or is that out of scope?

4. `extract_findings.py` line 357 sets problem status to `'proven'` in knowledge.db. The task description says to change this, but recommendation #1 says don't. Which takes precedence?

## Sources

- `/Users/patrickkavanagh/math/scripts/aristotle_fetch.py` (481 lines)
- `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` (387 lines)
- `/Users/patrickkavanagh/math/math-forge/scripts/mk` (310 lines)
- `/Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py` (384 lines)
- `/Users/patrickkavanagh/math/scripts/audit_proven.py` (248 lines)
- `/Users/patrickkavanagh/math/submissions/tracking.db` (schema + status distribution query)
- `/Users/patrickkavanagh/math/math-forge/data/schema.sql` (215 lines)
- `/Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh` (119 lines)
- `/Users/patrickkavanagh/math/math-forge/scripts/migrate_tracking.py` (lines 178-184)
- `/Users/patrickkavanagh/math/scripts/backfill_slots.py` (lines 104-116)
- `/Users/patrickkavanagh/math/scripts/backfill_all_files.py` (line 83)
- `/Users/patrickkavanagh/math/scripts/verify_output.sh` (lines 23-95)
