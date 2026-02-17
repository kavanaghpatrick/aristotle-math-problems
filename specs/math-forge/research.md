---
spec: math-forge
phase: research
created: 2026-02-14T21:40:00Z
---

# Research: Math-Forge Harness Cleanup & Wiring

## Executive Summary

Math-forge has solid foundations (502 findings, 48 problems, all 32 BATS tests passing) but three systemic gaps: the strategies table is unpopulated (0 rows), KB queries are absent from 7 of 11 pipeline skills, and several stale artifacts remain. All 10 issues are fixable with moderate effort and no risk to the active pipeline.

## Issue-by-Issue Research

---

### Issue 1: Strategies Table Wiring (0 rows, never populated)

**Current state**: `strategies` table exists in `math-forge/data/schema.sql` (lines 58-76) with schema: `problem_id, problem_name, domain_id, approach_name, approach_description, outcome, submission_slot, submission_uuid, finding_ids, attempts, last_attempted, learned`. Currently 0 rows in production DB.

**Source of data**: `extract_findings.py` generates findings of type `theorem`, `technique`, and `failure` but never inserts into `strategies`. The strategies table tracks *problem-level approaches* (e.g., "QR + Euler criterion for FT p=3" with outcome "proven"), while findings track individual theorems/techniques.

**Signals for strategy vs finding**:
- A **strategy** = a named approach to a problem (e.g., "Kummer symbol for FT p=3 q71mod72"). It groups multiple findings (theorems proved, techniques used) under one problem-level approach.
- Strategies should have a `problem_id` + `approach_name` unique pair.
- Outcome data comes from: `submissions.status` (proven/completed/failed) mapped to the approach name derived from the sketch filename or description.

**How to populate**:
1. **Automated path**: Extend `extract_findings.py` to also insert a strategy record per result file. The approach_name can be inferred from the filename/description. The outcome maps from sorry_count: 0 sorry = proven, 1 sorry = partial, 2+ sorry = failed.
2. **Backfill**: Write a one-time migration that reads `submissions` table from tracking.db and creates strategy records for all existing submissions.
3. **The `mk strategies` command already works** -- it queries `findings` with `proof_technique` aggregation, not the strategies table. So there are actually TWO "strategies" concepts: the table and the CLI command. The CLI command works fine. The table is for problem-level approach tracking.

**Recommendation**: Extend `extract_findings.py` to insert strategies. Add a `backfill_strategies.py` script to populate from historical submissions. Rename `mk strategies` to `mk techniques` to avoid confusion, or make it query both.

**Effort**: M (extend extract_findings + backfill script)

---

### Issue 2: Audit.md Tuza-Specific Checks

**Current state**: `/Users/patrickkavanagh/math/.claude/commands/audit.md` checks 3-6 are Tuza/graph-specific:
- Check 3: Self-loop check (`Sym2.mk(v,v)`) -- only relevant for `SimpleGraph` proofs
- Check 4: `Finset.sym2` usage -- only relevant for graph edge set constructions
- Check 5: Cover definition check (`E ⊆ G.edgeFinset`) -- only relevant for triangle cover problems
- Check 6: False lemma check -- lists 6 hardcoded Tuza false lemmas by name, plus queries `false_lemmas` table

**Universal checks**: 1 (sorry), 2 (axiom), 7 (import/structure), 8 (novelty). The false_lemmas DB query in check 6 IS universal, but the hardcoded names are Tuza-specific.

**Can they be conditional on domain?** Yes. The file's imports/namespace reveal domain:
- `Mathlib.Combinatorics`, `SimpleGraph`, `Finset.sym2`, `Hypergraph` -> run checks 3-5
- Otherwise -> skip checks 3-5, report as N/A

**For check 6**: Keep the DB query (universal), remove the 6 hardcoded Tuza lemma names or make them conditional. The DB query already catches everything.

**Recommendation**: Add domain auto-detection at the top of audit.md. If domain is not combinatorics/graph, checks 3-5 = N/A. Remove hardcoded false lemma names from check 6 (the DB query covers them).

**Effort**: S (conditional logic, no new code)

---

### Issue 3: Sweep.md Track D References

**Current state**: `sweep.md` has Track D in Step 5 (line 97: "A: Known-Result Formalization"), Step 6 (line 108: Tier D -- KNOWN RESULT), and Step 7 output template (line 132: "Tier D -- KNOWN RESULTS").

Other files with Track D references:
- `sketch.md` lines 67, 142: "For known results (Track D)"
- `screen-batch.md` lines 36, 58, 69: "D -- RESEARCH: Track D backlog"
- `screen.md` line 67: "Track D: Formalize"
- `sweep.md` line 132: "Tier D -- KNOWN RESULTS"

**What CLAUDE.md says**: "Track D -- Known-Result Formalization (DEPRECATED -- 0% of effort)" and "NEVER replace existing proof code with sorry" and "OPEN PROBLEMS ONLY".

**What removal looks like**:
- `sweep.md`: Remove Track D row from Step 5 table, remove Tier D from Step 6 table, remove "Tier D" section from Step 7 output template. Add explicit "SKIP known results" note.
- `sketch.md`: Remove "For known results (Track D)" template (lines 142-164). Keep the open-problem template.
- `screen-batch.md`: Rename "D -- RESEARCH" to something else or merge into Tier A backlog. Note: screen-batch.md's "Tier D" is actually "RESEARCH" (open + no known proof), which is NOT the same as Track D (known results). This is a naming collision, not a content issue.
- `screen.md`: Remove Track D from the recommendation table.

**Dependency check**: Nothing depends on Track D existing as a viable path. All code that references Track D is in markdown instructions, not executable code.

**Recommendation**: Remove Track D from sweep.md, submit.md, sketch.md, screen.md. Rename screen-batch.md's "D -- RESEARCH" to "D -- BACKLOG" to avoid confusion with the deprecated Track D.

**Effort**: S (markdown edits only)

---

### Issue 4: Unified Submission Path (INFORMAL bypasses safe_aristotle_submit.py)

**Current state**: Two submission paths exist:

1. **INFORMAL (.txt)**: `submit.md` Step 5 uses raw `aristotlelib.Project.prove_from_file()` inline Python (lines 108-119). No safety checks, no lockfile, no dedup, no transaction log.

2. **FORMAL (.lean)**: `submit.md` Step 5 uses `safe_aristotle_submit.py` (line 124) which provides lockfile, dedup via task hash, queue capacity check, transaction logging, retry with backoff.

**Can safe_aristotle_submit.py handle INFORMAL?** YES. It already has `--informal` flag (line 355: `input_type = "informal" if '--informal' in flags else "formal"`) and passes `input_type` through to `safe_submit()` which maps it to `ProjectInputType.INFORMAL` (line 214).

**What changes are needed**:
- `submit.md`: Replace the raw inline Python for INFORMAL with a call to `safe_aristotle_submit.py --informal`. Remove the separate INFORMAL code block.
- No changes needed to `safe_aristotle_submit.py` itself -- it already supports both modes.

**Risk**: None. The `--informal` flag is already implemented and tested.

**Recommendation**: Update `submit.md` to route ALL submissions through `safe_aristotle_submit.py`. Use `--informal` for .txt/.md files. Remove the raw inline Python submission block.

**Effort**: S (edit submit.md Step 5)

---

### Issue 5: Fetch.md Step 0 Bash For-Loop

**Current state**: `fetch.md` Step 0 (lines 13-24) uses a bash for-loop to reconcile local results:

```bash
for f in submissions/nu4_final/slot*_result.lean; do
  slot=$(echo "$f" | grep -o 'slot[0-9]*' | head -1)
  db_status=$(sqlite3 submissions/tracking.db "SELECT status FROM submissions WHERE filename LIKE '${slot}%' AND status='submitted'" 2>/dev/null)
  if [ -n "$db_status" ]; then
    sorry=$(grep -cw 'sorry' "$f" 2>/dev/null)
    axiom=$(grep -c '^axiom ' "$f" 2>/dev/null)
    echo "UNPROCESSED: $f (sorry=$sorry, axiom=$axiom, DB still says 'submitted')"
  fi
done
```

**Problems**:
- `filename LIKE '${slot}%'` is brittle -- `slot6` matches `slot60`, `slot600`, etc.
- No quoting around `$f` in grep calls
- `grep -cw 'sorry'` counts lines not occurrences (but close enough for reconciliation)
- For-loop globbing fails silently if no files match (bash prints literal glob)

**Better pattern**: Add a `reconcile` subcommand to `aristotle_fetch.py` that does this in Python with proper slot number extraction and exact matching. Or fix the bash: use `LIKE '${slot}\_%'` (underscore after slot number) for exact prefix matching.

**Recommendation**: Add `aristotle_fetch.py reconcile` subcommand. Short-term: fix the LIKE clause to use exact slot matching (`WHERE filename LIKE '${slot}_%' ESCAPE '\'`).

**Effort**: S-M (Python subcommand is cleaner but more work than fixing the bash)

---

### Issue 6: Problem-Researcher.md Placeholder Path

**Current state**: `math-forge/agents/problem-researcher.md` lines 40-41:
```bash
find /path/to/formal-conjectures -name "*.lean" | head -20
grep -r "<problem keyword>" /path/to/formal-conjectures/ --include="*.lean"
```

**Real path**: `formal-conjectures/` exists at project root (`/Users/patrickkavanagh/math/formal-conjectures/`).

**Fix**: Replace `/path/to/formal-conjectures` with `formal-conjectures/` (relative to project root, which is the working directory for all commands).

**Effort**: XS (two-line find-and-replace)

---

### Issue 7: Duplicate knowledge.db

**Current state**:
- `math-forge/knowledge.db`: 0 bytes, git-tracked, stray empty file
- `math-forge/data/knowledge.db`: 585,728 bytes, gitignored, real production DB (502 findings, 48 problems)

**How it got there**: The `math-forge/.gitignore` excludes `data/*.db` but not `*.db` at root. An empty `knowledge.db` was likely created during development and committed.

**Fix**:
1. `git rm math-forge/knowledge.db` -- remove stray from git
2. Add `knowledge.db` to `math-forge/.gitignore` (root-level) to prevent recurrence
3. Verify no code references the stray path

**Code path check**:
- `mk` script: resolves to `data/knowledge.db` via `$(dirname "$0")/../data/knowledge.db` -- correct
- `extract_findings.py`: resolves to `plugin_root / 'data' / 'knowledge.db'` -- correct
- `context-loader.sh`: uses `${PLUGIN_ROOT}/data/knowledge.db` -- correct
- No code references `math-forge/knowledge.db` directly

**Recommendation**: `git rm` the stray file, update `.gitignore`.

**Effort**: XS

---

### Issue 8: Auto-Extract After Fetch

**Current state**: `fetch.md` Step 2b (lines 52-58) documents the `extract_findings.py` call but it's a MANUAL step -- the operator must remember to run it. Similarly, `process-result.md` Step 7 (lines 104-114) documents it as a manual step.

The `aristotle_fetch.py` `fetch` command downloads results and updates `tracking.db` but does NOT call `extract_findings.py`.

**What "auto" would look like**:
1. After `aristotle_fetch.py` downloads a result file, it calls `extract_findings.py` automatically.
2. OR: `process-result.md` becomes the single entry point (already combines extract + audit + DB update), and `fetch.md` Step 2b just says "run `/project:process-result` on each downloaded file."
3. OR: Add `--extract` flag to `aristotle_fetch.py fetch` that runs `extract_findings.py` for each downloaded result.

**Recommendation**: Option 3 is cleanest -- add `--extract` flag (default on) to `aristotle_fetch.py fetch`. When a result is downloaded, automatically invoke `extract_findings.py` on it. On failure, log warning but don't block.

**Effort**: M (extend aristotle_fetch.py)

---

### Issue 9: mk find Cross-DB Query Resilience

**Current state**: `mk` `find` command (lines 170-180) queries `$TRACKING_DB` for false lemmas:

```bash
if [ -f "$TRACKING_DB" ]; then
    echo "--- False Lemmas (tracking.db) ---"
    run_sql "$TRACKING_DB" -header -column "
        SELECT lemma_name, why_false, counterexample
        FROM false_lemmas
        WHERE lemma_name LIKE '%${PROBLEM}%' OR impact LIKE '%${PROBLEM}%';
    "
fi
```

**What fails silently**:
1. `$TRACKING_DB` path resolution: uses `$(dirname "$0")/../../submissions/tracking.db` which requires `mk` to be invoked from within the math-forge tree. If invoked from elsewhere (e.g., via PATH), the path is wrong and `[ -f "$TRACKING_DB" ]` silently skips.
2. The `run_sql` function (line 36) catches errors via `2>&1` and returns non-zero, but the `find` command doesn't check the return code. On schema mismatch or missing column, the error message goes to stderr (already captured) but the user sees "[math-forge] ERROR:" inline.
3. `CLAUDE_PROJECT_DIR` env var is only set during Claude sessions (via hooks). Outside sessions, the fallback path may be wrong.

**What should happen**: If the cross-DB query fails, show a clear message like "tracking.db not available for cross-reference" instead of blank output.

**Recommendation**: Add explicit fallback messaging when `$TRACKING_DB` doesn't exist or query fails. Also: consider migrating false_lemmas from tracking.db to knowledge.db so the cross-DB query becomes unnecessary. (The migration script `migrate_tracking.py` already migrates false_lemmas as `finding_type='false_lemma'`, and 43 such findings exist in knowledge.db.)

**Effort**: S (add fallback message) or M (eliminate cross-DB query by using knowledge.db findings)

---

### Issue 10: Pipeline KB Integration

**Current state of KB querying across 11 pipeline skills**:

| Skill | Queries tracking.db | Queries knowledge.db (mk) | Gap |
|-------|--------------------|-----------------------------|-----|
| sketch.md | YES (false_lemmas, failed_approaches, submissions) | YES (mk search, mk find, mk failed) | None -- best integrated |
| submit.md | YES (false_lemmas) | NO | Missing: mk failed before submit |
| fetch.md | YES (submissions) | NO | Missing: auto-extract, not query |
| sweep.md | YES (submissions, candidate_problems) | NO | Missing: mk search/mk failed for prior work |
| screen.md | YES (candidate_problems, false_lemmas) | NO | Missing: mk search for related findings |
| audit.md | YES (false_lemmas, submissions) | NO | Missing: mk find for context |
| optimize.md | YES (false_lemmas, failed_approaches, submissions) | NO | Missing: mk strategies for technique suggestions |
| process-result.md | YES (submissions) | Calls extract_findings but doesn't QUERY KB | Missing: mk find before processing |
| status.md | NO (delegates to aristotle_fetch.py) | NO | N/A -- status check only |
| debate.md | NO | NO | Could benefit from mk search for context |
| screen-batch.md | YES (candidate_problems) | NO | Missing: mk search for batch screening |

**Already integrated**: `sketch.md` (Step 1b-extended) is the ONLY skill that queries knowledge.db via `mk search`, `mk find`, `mk failed`.

**Highest-value additions**:
1. `submit.md` Step 2: Add `mk failed "<problem keywords>"` before submission to catch known dead ends
2. `sweep.md` Step 3c: Add `mk search "<keyword>"` and `mk failed "<keyword>"` to check for existing work in KB
3. `screen.md` Step 2: Add `mk search "<problem>"` to find related proven techniques
4. `optimize.md` Step 3: Add `mk strategies` to suggest proven techniques for the domain
5. `audit.md` Step 6: Add `mk find "<problem>"` to check for related false lemmas in KB (supplements tracking.db query)

**Recommendation**: Add 3-line KB query blocks to submit.md, sweep.md, screen.md, optimize.md, and audit.md. Pattern:
```bash
mk search "<keywords>"
mk failed "<keywords>"
```

**Effort**: S (markdown additions, same pattern repeated)

---

## Additional Issues Discovered (Easy Wins)

### Issue 11: screen-batch.md "Tier D" naming collision
`screen-batch.md` uses "Tier D -- RESEARCH" (open problems needing research) which collides with the deprecated "Track D -- Known Result Formalization". Renaming to "Tier D -- BACKLOG" avoids confusion.

**Effort**: XS

### Issue 12: `mk find` could query knowledge.db false_lemmas instead of tracking.db
The 43 false_lemma findings already in knowledge.db make the cross-DB tracking.db query redundant. The `find` command could query `findings WHERE finding_type = 'false_lemma'` instead.

**Effort**: S

### Issue 13: `extract_findings.py` doesn't populate `source_submission_uuid`
Line 246-270: the insert statement includes `source_submission_uuid` but `generate_findings()` never sets it. The UUID could be passed via CLI or extracted from the corresponding `_ID.txt` file.

**Effort**: S

### Issue 14: No `mk add` command for manual finding insertion
Users can't manually add findings/insights without writing raw SQL. A `mk add <type> <title> <description> [--problem-id X] [--domain Y]` command would help.

**Effort**: S-M

### Issue 15: context-loader.sh doesn't surface failed approaches
The session briefing shows queue status, ready-to-fetch, recent proven, and near-misses, but doesn't show recent failures or false lemmas -- exactly the things you need to know before sketching.

**Effort**: S

---

## Test Situation

**Framework**: BATS 1.13.0 (installed and working)

**Test files** (8 files, 32 tests, ALL PASSING):

| File | Tests | Description |
|------|-------|-------------|
| `test_golden_queries.bats` | 8 | FTS5 relevance: cubic, Euler, smooth, apex, quartic, failed, strategies, find |
| `test_lean_validator_hook.bats` | 4 | Hook: non-lean pass, sorry-free pass, sorry-replacement block, missing file |
| `test_mk_find.bats` | 4 | Find: usage, summary, findings, non-existent |
| `test_mk_search.bats` | 6 | Search: usage, keyword, false lemma, no results, limit, domain filter |
| `test_mk_stats.bats` | 3 | Stats: counts, domains, totals |
| `test_mk_utils.bats` | 3 | Utils: help, no-args, init |
| `test_session_start_hook.bats` | 4 | Context-loader: JSON validity, hookSpecificOutput, additionalContext, header |

**Test gaps**:
- No tests for `mk failed` command
- No tests for `mk strategies` with domain filter
- No tests for `extract_findings.py`
- No tests for `migrate_tracking.py`
- No tests for `safe_aristotle_submit.py` (requires API key)

**Tests needing updates after changes**:
- If `mk strategies` is renamed to `mk techniques`: update golden query test (test 7)
- If `mk find` drops cross-DB query: update find tests
- New tests needed for any new commands (e.g., `mk add`)

---

## Knowledge Base State

| Metric | Value |
|--------|-------|
| Total findings | 502 |
| Theorems (verified) | 383 |
| Failures | 56 |
| False lemmas | 43 |
| Techniques | 20 |
| Strategies (table) | **0** (unpopulated) |
| Problems tracked | 48 |
| Problems open | 27 |
| Problems proven | 19 |
| Problems in-flight | 1 |
| Domain: NT | 403 |
| Domain: combinatorics | 43 |
| Domain: NULL | 56 |
| Top technique | `finite computation (decide)` (169 uses) |
| Second technique | `finite computation (native_decide)` (100 uses) |
| DB size | 585,728 bytes |

---

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| BATS Tests | `bats math-forge/tests/` | test directory |
| Lint | Not found | No package.json/Makefile/CI |
| TypeCheck | Not found | N/A (bash/python project) |
| Build | Not found | N/A (no build step) |

**Local CI**: `bats math-forge/tests/`

---

## Feasibility Assessment

| Aspect | Assessment | Notes |
|--------|------------|-------|
| Technical Viability | High | All changes are markdown edits or small Python/bash extensions |
| Effort Estimate | M | 10 issues, most S/XS, two M-sized (strategies backfill, auto-extract) |
| Risk Level | Low | All changes are additive (no existing behavior removed). Tests pass. |
| Pipeline disruption | None | Changes are to instruction files + support scripts, not core pipeline code |

---

## Related Specs

| Spec | Relevance | mayNeedUpdate |
|------|-----------|---------------|
| `erdos364` | Low -- uses pipeline skills that will get KB queries added | false |
| `sierpinski-5n` | Low -- same as above | false |

No high-relevance spec conflicts found.

---

## Recommendations for Requirements

1. **Batch the 10 issues into 3 priority tiers**:
   - **P0 (do first, highest value)**: Issue 1 (strategies), Issue 10 (KB integration), Issue 7 (stray DB)
   - **P1 (do next, fixes stale content)**: Issue 2 (audit Tuza), Issue 3 (Track D), Issue 4 (unified submit), Issue 6 (placeholder path)
   - **P2 (do when convenient)**: Issue 5 (fetch loop), Issue 8 (auto-extract), Issue 9 (mk find resilience)

2. **For Issue 1 (strategies)**: Don't rename `mk strategies` -- it works fine querying findings. Instead, populate the strategies table separately and add a `mk approaches <problem-id>` command that queries it. The strategies table serves a different purpose (problem-level approach tracking) than `mk strategies` (technique frequency).

3. **For Issue 10 (KB integration)**: Create a standard 3-line KB query block and add it to submit, sweep, screen, optimize, and audit. Same pattern everywhere for consistency.

4. **For Issue 7 (stray DB)**: Do this first -- it's 30 seconds and removes confusion.

5. **For Issue 3 (Track D)**: Don't delete Track D sections entirely -- replace with explicit "DEPRECATED: Track D is dead, skip known results" notes. This is more informative than silent removal.

6. **Add easy wins**: Issues 11-15 are all XS-S effort and add value.

7. **Test strategy**: Add `test_mk_failed.bats` and `test_extract_findings.bats` during implementation. Update golden queries if any command names change.

## Open Questions

- Should `mk find` stop querying tracking.db entirely (Issue 12)? The 43 false_lemma findings in knowledge.db overlap with tracking.db's false_lemmas table but may not be identical. Need to verify.
- Should `extract_findings.py` be the ONLY way to populate knowledge.db, or should `mk add` exist for manual insertion?
- The `strategies` table has a `UNIQUE(problem_id, approach_name)` constraint. What naming convention for approach_name? Derived from filename? Manual?

## Sources

| Source | Key Point |
|--------|-----------|
| `/Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py` | Generates theorem/technique/failure findings but not strategies |
| `/Users/patrickkavanagh/math/math-forge/data/schema.sql` | strategies table schema with outcome CHECK constraint |
| `/Users/patrickkavanagh/math/.claude/commands/audit.md` | Checks 3-6 are Tuza-specific |
| `/Users/patrickkavanagh/math/.claude/commands/sweep.md` | Track D still viable in Steps 5-7 |
| `/Users/patrickkavanagh/math/.claude/commands/submit.md` | Dual submission paths, no KB queries |
| `/Users/patrickkavanagh/math/.claude/commands/fetch.md` | Fragile bash loop, manual extract step |
| `/Users/patrickkavanagh/math/math-forge/agents/problem-researcher.md` | `/path/to/formal-conjectures` placeholder on lines 40-41 |
| `/Users/patrickkavanagh/math/math-forge/knowledge.db` | 0-byte stray file, git-tracked |
| `/Users/patrickkavanagh/math/math-forge/data/knowledge.db` | Real DB: 502 findings, 0 strategies, 48 problems |
| `/Users/patrickkavanagh/math/math-forge/scripts/mk` | `find` cross-DB query at lines 170-180 |
| `/Users/patrickkavanagh/math/.claude/commands/sketch.md` | Only skill with KB integration (Step 1b-extended) |
| `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` | Already supports `--informal` flag |
| `/Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh` | Session briefing, no failed approach surfacing |
| `/Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh` | Sorry-replacement blocking + false lemma warnings |
| `/Users/patrickkavanagh/math/math-forge/scripts/migrate_tracking.py` | Migrates proven_theorems, false_lemmas, failed_approaches, candidate_problems |
