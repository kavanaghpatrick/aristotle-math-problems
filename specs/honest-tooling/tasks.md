---
spec: honest-tooling
phase: tasks
created: 2026-02-15
---

# Tasks: Honest Tooling

## Phase 1: Make It Work (POC)

Focus: Migrate DB, replace all `proven` status writes/reads with `compiled_clean`, split submit functions, add batch mode, extend mk CLI. All changes are mechanical string replacements and function restructuring per design.md.

- [x] 1.1 Create migration script and run it against tracking.db
  - **Do**:
    1. Create `scripts/migrate_honest_labels.py` using the design Step 0 template
    2. Script does: `ALTER TABLE submissions ADD COLUMN target_resolved INTEGER DEFAULT 0` (idempotent)
    3. Script does: `UPDATE submissions SET status = 'compiled_clean' WHERE status IN ('proven', 'PROVEN')`
    4. Run the migration: `python3 scripts/migrate_honest_labels.py`
  - **Files**: `scripts/migrate_honest_labels.py` (new)
  - **Done when**: `sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='proven'"` returns 0, and `SELECT COUNT(*) FROM submissions WHERE status='compiled_clean'` returns ~203, and `PRAGMA table_info(submissions)` shows `target_resolved` column
  - **Verify**: `python3 scripts/migrate_honest_labels.py && sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='proven'" && sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='compiled_clean'"`
  - **Commit**: `feat(honest-tooling): add migration script and migrate proven->compiled_clean`
  - _Requirements: FR-2, AC-1.4, AC-2.1, AC-2.2, AC-2.3_
  - _Design: Step 0_

- [x] 1.2 Update aristotle_fetch.py verdict and DB writes
  - **Do**:
    1. Line 135: change `verdict = "proven"` to `verdict = "compiled_clean"` (Change 1.1)
    2. Line 175: change `"proven"` to `"compiled_clean"` in verified check (Change 1.2)
    3. Line 192: change `"proven"` to `"compiled_clean"` in verified check (Change 1.3)
    4. Lines 161-178: add `target_resolved = ?` to UPDATE SQL, add `0` param (Change 1.8)
    5. Lines 182-195: add `target_resolved` to INSERT SQL column list and `0` value (Change 1.9)
  - **Files**: `scripts/aristotle_fetch.py`
  - **Done when**: `grep -n '"proven"' scripts/aristotle_fetch.py` shows zero matches in verdict/verified logic (only in backward-compat contexts if any)
  - **Verify**: `grep -c 'compiled_clean' scripts/aristotle_fetch.py` returns >= 3 && `grep -c 'target_resolved' scripts/aristotle_fetch.py` returns >= 2
  - **Commit**: `feat(honest-tooling): aristotle_fetch verdict and DB writes use compiled_clean`
  - _Requirements: FR-1, FR-14, AC-1.1, AC-1.3, AC-2.4_
  - _Design: Step 1 (Changes 1.1-1.3, 1.8-1.9)_

- [x] 1.3 Update aristotle_fetch.py display strings
  - **Do**:
    1. Line 264: change `verdict == "PROVEN"` to `verdict == "COMPILED_CLEAN"` (Change 1.4)
    2. Line 372: change `verdict == "PROVEN"` to `verdict == "COMPILED_CLEAN"` (Change 1.5)
    3. Line 380: change `verdict == "PROVEN"` to `verdict == "COMPILED_CLEAN"` (Change 1.6)
    4. Line 387: change `{proven} proven.` to `{proven} compiled clean.` (Change 1.7)
  - **Files**: `scripts/aristotle_fetch.py`
  - **Done when**: `grep -n 'PROVEN' scripts/aristotle_fetch.py` returns zero matches
  - **Verify**: `grep -c 'COMPILED_CLEAN' scripts/aristotle_fetch.py` returns >= 2 && `grep -c '"PROVEN"' scripts/aristotle_fetch.py` returns 0
  - **Commit**: `feat(honest-tooling): aristotle_fetch display strings use COMPILED CLEAN`
  - _Requirements: FR-1, AC-1.2_
  - _Design: Step 1 (Changes 1.4-1.7)_

- [x] 1.4 Update backfill_slots.py status strings
  - **Do**:
    1. Line 111: change `return 'proven'` to `return 'compiled_clean'` (Change 2.1)
    2. Line 167: change `status == 'proven'` to `status == 'compiled_clean'` (Change 2.2)
    3. Line 176: change `status == 'proven'` to `status == 'compiled_clean'` (Change 2.3)
  - **Files**: `scripts/backfill_slots.py`
  - **Done when**: `grep "'proven'" scripts/backfill_slots.py` returns zero matches
  - **Verify**: `grep -c 'compiled_clean' scripts/backfill_slots.py` returns >= 3
  - **Commit**: `feat(honest-tooling): backfill_slots uses compiled_clean status`
  - _Requirements: FR-5, AC-1.8, AC-6.1_
  - _Design: Step 2_

- [x] 1.5 Update backfill_all_files.py status string
  - **Do**:
    1. Line 83: change `status = 'proven'` to `status = 'compiled_clean'` (Change 3.1)
  - **Files**: `scripts/backfill_all_files.py`
  - **Done when**: `grep "'proven'" scripts/backfill_all_files.py` returns zero matches
  - **Verify**: `grep -c 'compiled_clean' scripts/backfill_all_files.py` returns >= 1
  - **Commit**: `feat(honest-tooling): backfill_all_files uses compiled_clean status`
  - _Requirements: FR-5, AC-1.8, AC-6.2_
  - _Design: Step 3_

- [ ] 1.6 [VERIFY] Quality checkpoint: bats math-forge/tests/
  - **Do**: Run existing BATS tests to catch regressions from status string changes
  - **Verify**: `bats math-forge/tests/` exits 0
  - **Done when**: All BATS tests pass
  - **Commit**: `chore(honest-tooling): pass quality checkpoint` (only if fixes needed)

- [x] 1.7 Update audit_proven.py SQL and display strings
  - **Do**:
    1. Lines 3-5: update docstring from "proven" to "compiled_clean" (Change 4.3)
    2. Line 95: add `'compiled_clean'` to IN clause (Change 4.1)
    3. Line 98: change display "proven" to "compiled clean" (Change 4.2)
    4. Line 180: update comment from "proven" to "compiled_clean" (Change 4.4)
    5. Line 192: update comment from "proven" to "compiled_clean" (Change 4.5)
    6. Line 216: change display label (Change 4.6)
    7. Line 223: change header from "TRULY PROVEN" to "COMPILED CLEAN" (Change 4.7)
    8. Line 237: add `'compiled_clean'` to final count IN clause (Change 4.8)
    9. Line 240: add `'compiled_clean'` to flagged count IN clause (Change 4.9)
    10. Line 242: change print from "proven" to "compiled clean" (Change 4.10)
  - **Files**: `scripts/audit_proven.py`
  - **Done when**: All 10 edits applied. IN clauses include both `'proven'` and `'compiled_clean'` for backward compat.
  - **Verify**: `grep -c 'compiled_clean' scripts/audit_proven.py` returns >= 5 && `python3 scripts/audit_proven.py 2>&1 | head -1` shows "compiled clean" (not "proven")
  - **Commit**: `feat(honest-tooling): audit_proven uses compiled_clean labels`
  - _Requirements: FR-3, AC-1.5, AC-1.6_
  - _Design: Step 4_

- [x] 1.8 Update verify_output.sh display strings
  - **Do**:
    1. Line 23: change "claimed PROVEN" to "COMPILED CLEAN" (Change 5.1)
    2. Line 47: change comment from "proven" to "compiled clean" (Change 5.2)
    3. Line 76: change "not claimed as proven" to "not compiled clean" (Change 5.3)
    4. Line 81: change "proven theorems" to "compiled theorems" (Change 5.4)
    5. Line 96: change "claims to be proven" to "compiled clean" (Change 5.5)
  - **Files**: `scripts/verify_output.sh`
  - **Done when**: No instance of the word "proven" remains in verify_output.sh display strings (variable name `CLAIMED_PROVEN` is internal, rename optional)
  - **Verify**: `grep -ic 'proven' scripts/verify_output.sh` returns 0 or only matches internal variable `CLAIMED_PROVEN`
  - **Commit**: `feat(honest-tooling): verify_output.sh uses COMPILED CLEAN labels`
  - _Requirements: FR-4, AC-1.7_
  - _Design: Step 5_

- [x] 1.9 Update post_result.sh display strings
  - **Do**:
    1. Line 42: change "Full proof achieved" to "COMPILED CLEAN -- 0 sorry, 0 axiom." (Change 6.1)
    2. Line 44: change "EXTRACTING NEW PROVEN LEMMAS" to "EXTRACTING COMPILED LEMMAS" (Change 6.2)
    3. Line 53 stays as-is (literature_lemmas reference, out of scope)
  - **Files**: `scripts/post_result.sh`
  - **Done when**: Lines 42 and 44 updated, line 53 unchanged
  - **Verify**: `grep -c 'COMPILED' scripts/post_result.sh` returns >= 2
  - **Commit**: `feat(honest-tooling): post_result.sh uses honest labels`
  - _Requirements: FR-15, AC-6.3_
  - _Design: Step 6_

- [ ] 1.10 [VERIFY] Quality checkpoint + grep scan for remaining `proven` writes
  - **Do**:
    1. Run `bats math-forge/tests/`
    2. Run grep scan: `grep -rn "status.*=.*'proven'" scripts/ --include='*.py' --include='*.sh'`
    3. Run grep scan: `grep -rn '"PROVEN"' scripts/ --include='*.py' --include='*.sh'`
    4. Verify only backward-compat IN clauses in audit_proven.py remain
  - **Verify**: `bats math-forge/tests/` exits 0 && grep scans show no writes of `status='proven'` (only reads in IN clauses alongside 'compiled_clean')
  - **Done when**: All tests pass, no script writes `proven` to tracking.db
  - **Commit**: `chore(honest-tooling): pass quality checkpoint` (only if fixes needed)

- [x] 1.11 Split check_recent_submissions() and add batch mode to safe_aristotle_submit.py
  - **Do**:
    1. Replace `check_recent_submissions()` (lines 76-103) with `check_duplicate()` (sync, local log only) and `check_rate_limit_and_capacity()` (async, single API call merging rate-limit + capacity) per design Change 7.1
    2. Delete `check_queue_capacity()` (lines 106-118) per Change 7.2
    3. Add `batch: bool = False` param to `safe_submit()` signature (Change 7.4)
    4. Update `safe_submit()` safety checks: use `check_duplicate()` for check 2, use `check_rate_limit_and_capacity()` for check 3 (skipped in batch mode) per Change 7.3
    5. Add `batch: bool = False` param to `submit_with_retry()` signature (Change 7.5)
    6. Pass `batch=batch` through in `submit_with_retry()` call to `safe_submit()` (Change 7.6)
    7. Replace CLI `__main__` block (lines 307-387) with batch-aware CLI per Change 7.7: proper arg parsing, `--batch` flag, multi-file loop with per-file error handling, single-file fallback
  - **Files**: `scripts/safe_aristotle_submit.py`
  - **Done when**: `check_duplicate` and `check_rate_limit_and_capacity` exist as separate functions; `check_recent_submissions` and `check_queue_capacity` removed; `--batch` flag in CLI; single-file mode preserved
  - **Verify**: `grep -c 'def check_duplicate' scripts/safe_aristotle_submit.py` returns 1 && `grep -c 'def check_rate_limit_and_capacity' scripts/safe_aristotle_submit.py` returns 1 && `grep -c 'check_recent_submissions' scripts/safe_aristotle_submit.py` returns 0 && `grep -c 'def check_queue_capacity' scripts/safe_aristotle_submit.py` returns 0 && `grep -c 'batch' scripts/safe_aristotle_submit.py` returns >= 5 && `python3 scripts/safe_aristotle_submit.py 2>&1 | grep -c 'batch'` returns >= 1
  - **Commit**: `feat(honest-tooling): split submit checks, add --batch mode`
  - _Requirements: FR-6, FR-7, AC-3.1, AC-3.2, AC-3.3, AC-3.4, AC-3.5, AC-4.1, AC-4.2, AC-4.3, AC-4.4, AC-4.5_
  - _Design: Step 7_

- [x] 1.12 Add 5 new mk CLI commands
  - **Do**:
    1. Add `submit)` case branch before `help|*)` in mk (delegates to safe_aristotle_submit.py) per Change 8.1
    2. Add `status)` case branch (delegates to aristotle_fetch.py status) per Change 8.2
    3. Add `partials)` case branch (queries tracking.db for sorry_count=1) per Change 8.3
    4. Add `resubmittable)` case branch (queries tracking.db for failed/partial candidates) per Change 8.4
    5. Add `query)` case branch (read-only SQL, rejects non-SELECT) per Change 8.5
    6. Update `help|*)` text to include all new commands per Change 8.6
  - **Files**: `math-forge/scripts/mk`
  - **Done when**: All 5 commands registered. `mk help` shows Pipeline commands section.
  - **Verify**: `bash math-forge/scripts/mk help 2>&1 | grep -c 'submit\|status\|partials\|resubmittable\|query'` returns >= 5 && `bash math-forge/scripts/mk query "SELECT 1" 2>&1 | grep -q '1'` && `bash math-forge/scripts/mk query "DELETE FROM x" 2>&1 | grep -q 'ERROR'`
  - **Commit**: `feat(honest-tooling): add submit, status, partials, resubmittable, query to mk CLI`
  - _Requirements: FR-8, FR-9, FR-10, FR-11, FR-12, FR-13, AC-5.1 through AC-5.7_
  - _Design: Step 8_

- [ ] 1.13 POC Checkpoint
  - **Do**: Verify all changes work end-to-end:
    1. `sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='proven'"` returns 0
    2. `sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='compiled_clean'"` returns ~203
    3. `sqlite3 submissions/tracking.db "PRAGMA table_info(submissions)" | grep target_resolved` shows column
    4. `grep -rn "status.*=.*'proven'" scripts/ --include='*.py' | grep -v 'IN ('` returns nothing (no direct proven writes)
    5. `python3 scripts/safe_aristotle_submit.py 2>&1 | grep batch` shows batch usage
    6. `bash math-forge/scripts/mk query "SELECT COUNT(*) FROM submissions WHERE status='compiled_clean'"`
    7. `bash math-forge/scripts/mk help | grep partials`
    8. `bats math-forge/tests/`
  - **Done when**: All 8 checks pass
  - **Verify**: All commands above exit 0 with expected output
  - **Commit**: `feat(honest-tooling): complete POC`

## Phase 2: Refactoring

After POC validated, clean up code.

- [ ] 2.1 Clean up variable naming in aristotle_fetch.py
  - **Do**:
    1. Rename `proven` counter variable in `cmd_fetch()` (line 331, 380-381) to `clean_count` for clarity
    2. Ensure all comments reference "compiled clean" not "proven" where they describe submission status
  - **Files**: `scripts/aristotle_fetch.py`
  - **Done when**: Internal variable names aligned with new status terminology
  - **Verify**: `grep -n 'proven' scripts/aristotle_fetch.py` returns only backward-compat or out-of-scope references (like `proven_count` column name)
  - **Commit**: `refactor(honest-tooling): rename internal variables for consistency`
  - _Design: Step 1 cleanup_

- [ ] 2.2 [VERIFY] Quality checkpoint: bats math-forge/tests/
  - **Do**: Run BATS tests after refactoring
  - **Verify**: `bats math-forge/tests/` exits 0
  - **Done when**: All tests pass
  - **Commit**: `chore(honest-tooling): pass quality checkpoint` (only if fixes needed)

## Phase 3: Testing

- [ ] 3.1 Verify migration script is idempotent
  - **Do**:
    1. Run `python3 scripts/migrate_honest_labels.py` a second time
    2. Verify output says "target_resolved column already exists" and "Migrated 0 rows"
    3. Verify DB state unchanged: `SELECT COUNT(*) FROM submissions WHERE status='compiled_clean'` still ~203
  - **Files**: `scripts/migrate_honest_labels.py`
  - **Done when**: Second run produces no errors and no data changes
  - **Verify**: `python3 scripts/migrate_honest_labels.py 2>&1 | grep -c 'already exists'` returns 1 && `python3 scripts/migrate_honest_labels.py 2>&1 | grep 'Migrated 0 rows'`
  - **Commit**: none (verification only)
  - _Requirements: NFR-2_

- [ ] 3.2 Verify mk query read-only enforcement
  - **Do**:
    1. Test SELECT works: `bash math-forge/scripts/mk query "SELECT COUNT(*) FROM submissions"`
    2. Test DELETE rejected: `bash math-forge/scripts/mk query "DELETE FROM submissions"` exits non-zero
    3. Test UPDATE rejected: `bash math-forge/scripts/mk query "UPDATE submissions SET status='x'"` exits non-zero
    4. Test INSERT rejected: `bash math-forge/scripts/mk query "INSERT INTO submissions (filename) VALUES ('x')"` exits non-zero
    5. Test WITH works: `bash math-forge/scripts/mk query "WITH x AS (SELECT 1) SELECT * FROM x"`
  - **Files**: none (verification only)
  - **Done when**: All 5 checks produce expected behavior
  - **Verify**: Run all 5 commands and check exit codes
  - **Commit**: none (verification only)
  - _Requirements: AC-5.5_

- [ ] 3.3 Verify safe_aristotle_submit.py CLI help and batch usage
  - **Do**:
    1. `python3 scripts/safe_aristotle_submit.py` (no args) shows usage including `--batch`
    2. `python3 scripts/safe_aristotle_submit.py --batch` (no files) shows usage
    3. Verify single-file mode preserved: usage still shows `<input_file> [slot_number]`
  - **Files**: none (verification only)
  - **Done when**: CLI help is correct for both single and batch modes
  - **Verify**: `python3 scripts/safe_aristotle_submit.py 2>&1 | grep -c 'batch'` returns >= 1
  - **Commit**: none (verification only)
  - _Requirements: AC-3.1, AC-4.5_

- [ ] 3.4 [VERIFY] Quality checkpoint: bats math-forge/tests/
  - **Do**: Run BATS tests after all testing tasks
  - **Verify**: `bats math-forge/tests/` exits 0
  - **Done when**: All tests pass
  - **Commit**: `chore(honest-tooling): pass quality checkpoint` (only if fixes needed)

## Phase 4: Quality Gates

- [ ] 4.1 [VERIFY] Full local CI: bats math-forge/tests/ && grep scan
  - **Do**:
    1. Run `bats math-forge/tests/`
    2. Run `grep -rn "status.*=.*'proven'" scripts/ --include='*.py' --include='*.sh' | grep -v "IN ("` -- should return nothing
    3. Run `grep -rn '"PROVEN"' scripts/ --include='*.py' --include='*.sh'` -- should return nothing
    4. Run `sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='proven'"` -- returns 0
    5. Run `bash math-forge/scripts/mk query "SELECT COUNT(*) FROM submissions WHERE status='compiled_clean'"` -- returns ~203
  - **Verify**: All commands pass with expected output
  - **Done when**: BATS green, no proven writes, DB migrated, mk query functional
  - **Commit**: `chore(honest-tooling): pass local CI` (if fixes needed)

- [ ] 4.2 Create PR and verify CI
  - **Do**:
    1. Verify current branch is a feature branch: `git branch --show-current`
    2. If on default branch, STOP and alert user
    3. Push branch: `git push -u origin feat/math-forge` (or current branch)
    4. Create PR: `gh pr create --title "feat: honest tooling labels + batch submit + mk CLI" --body "..."`
    5. Wait for CI: `gh pr checks --watch`
  - **Verify**: `gh pr checks` shows all green
  - **Done when**: PR created, CI passes
  - **If CI fails**: Read failure, fix locally, push, re-verify

- [ ] 4.3 [VERIFY] AC checklist
  - **Do**: Programmatically verify each acceptance criterion:
    1. AC-1.1: `grep 'compiled_clean' scripts/aristotle_fetch.py | grep verdict` (exists)
    2. AC-1.2: `grep '"PROVEN"' scripts/aristotle_fetch.py` (empty)
    3. AC-1.3: `grep 'compiled_clean.*else 0' scripts/aristotle_fetch.py` (exists -- verified column logic)
    4. AC-1.4: `sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='proven'"` (returns 0)
    5. AC-1.5: `grep "'compiled_clean'" scripts/audit_proven.py` (exists in IN clauses)
    6. AC-1.6: `grep '"proven"' scripts/audit_proven.py | grep -v IN | grep -v 'status'` (only comments/backward compat)
    7. AC-1.7: `grep -i 'proven' scripts/verify_output.sh | grep -v CLAIMED_PROVEN` (empty or only variable refs)
    8. AC-1.8: `grep 'compiled_clean' scripts/backfill_slots.py scripts/backfill_all_files.py` (both present)
    9. AC-2.1: `sqlite3 submissions/tracking.db "PRAGMA table_info(submissions)" | grep target_resolved`
    10. AC-2.4: `grep 'target_resolved' scripts/aristotle_fetch.py` (present in DB writes)
    11. AC-3.1: `grep 'batch' scripts/safe_aristotle_submit.py` (present)
    12. AC-4.1: `grep 'def check_duplicate' scripts/safe_aristotle_submit.py` (exists)
    13. AC-4.2: `grep 'def check_rate_limit_and_capacity' scripts/safe_aristotle_submit.py` (exists)
    14. AC-5.1-5.7: `bash math-forge/scripts/mk help | grep -c 'submit\|status\|partials\|resubmittable\|query'` (>= 5)
    15. AC-6.1-6.2: `grep "'proven'" scripts/backfill_slots.py scripts/backfill_all_files.py` (empty)
    16. AC-6.3: `grep 'COMPILED' scripts/post_result.sh` (present)
    17. AC-6.4: `grep -rn "status.*=.*'proven'" scripts/ --include='*.py' --include='*.sh' | grep -v "IN ("` (empty)
  - **Verify**: All 17 checks pass
  - **Done when**: All acceptance criteria confirmed met
  - **Commit**: none

## Phase 5: PR Lifecycle

- [ ] 5.1 Monitor CI and fix failures
  - **Do**:
    1. `gh pr checks` -- check status
    2. If any failures, read details, fix locally, commit, push
    3. Re-run `gh pr checks --watch`
  - **Done when**: All CI checks green
  - **Verify**: `gh pr checks` shows all passing

- [ ] 5.2 Address review comments
  - **Do**:
    1. `gh pr view --comments` -- read reviewer feedback
    2. Implement requested changes
    3. Push fixes
    4. Re-verify CI
  - **Done when**: All review comments addressed, CI green
  - **Verify**: `gh pr checks` all green, no unresolved comments

- [ ] 5.3 [VERIFY] Final validation
  - **Do**:
    1. `bats math-forge/tests/` -- all pass
    2. `sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='proven'"` -- returns 0
    3. `bash math-forge/scripts/mk query "SELECT COUNT(*) FROM submissions WHERE status='compiled_clean'"` -- returns ~203
    4. `grep -rn "status.*=.*'proven'" scripts/ --include='*.py' --include='*.sh' | grep -v "IN ("` -- empty
    5. `python3 scripts/safe_aristotle_submit.py 2>&1 | grep batch` -- shows batch in usage
  - **Done when**: All 5 checks pass, PR is mergeable
  - **Verify**: All commands exit 0 with expected output

## Notes

- **POC shortcuts taken**: No new BATS tests for mk submit/status/partials/resubmittable/query (follow-up spec per requirements). No live Aristotle API test for batch mode (would consume real slots).
- **Production TODOs**: Add BATS tests for new mk commands. Consider renaming `CLAIMED_PROVEN` variable in verify_output.sh. Consider adding `--dry-run` to batch mode.
- **knowledge.db untouched**: All changes scoped to tracking.db and display strings. knowledge.db `problems.status='proven'` and `strategies.outcome='proven'` preserved (semantically correct at problem level, per NFR-5).
- **Backward compat**: `audit_proven.py` IN clauses accept both `'proven'` and `'compiled_clean'` so the script works even on unmigrated data.
- **Largest change**: `safe_aristotle_submit.py` CLI rewrite (~80 lines replaced). Design has full before/after code.
