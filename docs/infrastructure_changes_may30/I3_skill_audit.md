# I3 — Skill / Script Status-Enum Audit (2026-05-30)

## Context

On 2026-05-28 the `submissions.status` vocabulary was renamed (commit
`migrate_honest_labels.py`). The old buckets collapsed into a new
canonical set, but many code paths kept filtering on the old strings,
producing silent no-ops (most notoriously `gather_context()` returning
zero rows — fixed under I1).

I3 is a full sweep across every project skill and Python/shell script
to find and repair every dead enum reference, plus a regression test
that fails CI if the next rename leaves stale references behind.

## Canonical status enum

The complete list of valid `submissions.status` values as of 2026-05-28:

| Status | Meaning |
|---|---|
| `submitted` | Aristotle job in flight; no terminal verdict yet. |
| `compile_failed` | Aristotle returned a Lean file that fails `lake build`, OR Aristotle's loader rejected the prompt, OR the file is structurally invalid (axiom-only, etc.). |
| `compiled_partial` | Compiles but has `sorry_count >= 1` (residual sorry) or contains a fresh `axiom` declaration. Both the historical `near_miss` and `completed` buckets collapsed here. |
| `compiled_no_advance` | Compiles clean (`sorry=0`, no fresh axiom, not negated), but the target conjecture is NOT resolved — typically infrastructure or known math. This is the **default** for a clean compile; promotion to `compiled_advance` is opt-in. |
| `compiled_advance` | Compiles clean AND the target was genuinely resolved. Requires all three: `target_resolved=1` AND `axiomatizes_prior_work=0` AND `contribution_statement NOT NULL`. Never set automatically. |
| `disproven` | Aristotle returned a counterexample (the conjecture was wrong / negated). |

`status_legacy` preserves the pre-2026-05-28 label and is read-only.

## Per-file audit results

Files with broken status references (path + line at time of audit; all fixed in this changeset):

| File | Lines | What was broken | Fix |
|---|---|---|---|
| `scripts/safe_aristotle_submit.py` | 530 | (Already fixed by I1; comment only — see below.) Was: `status IN ('compiled_clean','near_miss','completed')` returning 0 rows. | I1 replaced with artifact-presence gate. |
| `scripts/aristotle_fetch.py` | 134-144 | `verdict` literals were the old vocabulary (`failed`, `compiled_clean`, `near_miss`, `completed`). | Remapped to canonical (`compile_failed`, `compiled_no_advance`, `compiled_partial`, `disproven`). |
| `scripts/aristotle_fetch.py` | 179, 197, 273, 385, 389, 404 | Display / `verified` logic compared against `compiled_clean` / `near_miss`. | Updated to `compiled_no_advance`/`compiled_advance` and `compiled_partial`. |
| `scripts/workflow.py` | 176-183, 197, 218 | `WHERE status IN ('validated','submitted','running')` and `('completed','failed')`. | Replaced with canonical set. |
| `scripts/submission_queue.py` | 59, 73 | `status = 'running' OR status = 'pending'` and `status = 'completed'`. | Replaced with canonical (`submitted` and terminal-status set). |
| `scripts/init_tracking_db.py` | 28, 119 | Schema default `'draft'` with old-vocab comment; view filtered on `'completed'`. | Updated comment to canonical; view now filters terminal statuses. |
| `scripts/backfill_slots.py` | 110-113, 167-168, 176 | `determine_status()` returned `compiled_clean`/`completed`/`draft`. | Returns canonical names; axiom case → `compile_failed`. |
| `scripts/backfill_all_files.py` | 83, 86 | Status assignment used `compiled_clean`/`completed`. | Returns canonical names. |
| `scripts/track_submission.sh` | 123 | Help text suggested `UPDATE … status='running'`. | Suggests `status='submitted'`. |
| `agentic/generators/pool.py` | 77 | Submissions query filtered `status = 'completed'`. | Filters `compiled_partial`. |
| `agentic/learning/extractor.py` | 322 | UPDATE submissions SET status='completed'. | Computes canonical status from sorry/negation. |
| `agentic/monitor/dashboard.py` | 121 | Submissions query filtered `status = 'completed'`. | Filters canonical terminal set. |
| `math-forge/scripts/mk` | 336, 354, 411, 450-452 | `mk partials`, `mk resubmittable`, `mk context`, `mk gaps` all filtered on dead vocab. | `partials` → `compiled_partial`; `resubmittable` → `(compiled_partial, compile_failed)`; `context` → artifact-presence gate (mirrors `gather_context()`); `gaps` → priority-mapped CASE over canonical statuses. |
| `math-forge/scripts/mk` | 371 | Help-text example used `status='compiled_clean'`. | Uses `status='compiled_no_advance'`. |
| `math-forge/hooks/scripts/context-loader.sh` | 26, 42 | SessionStart briefing queries used `status = 'completed'`. | Use canonical terminal set / `compiled_partial`. |
| `math-forge/tests/test_mk_gaps.bats` | 21-22 | Test fixture INSERTed `compiled_clean`, `near_miss`. | INSERTs `compiled_no_advance`, `compiled_partial`. |
| `.claude/commands/submit.md` | 45 | Suggested SQL filtered `status IN ('compiled_clean',…)`. | Uses artifact-presence gate. |
| `.claude/commands/fetch.md` | 64 | "if result is compiled_clean". | "if result is compiled_no_advance". |
| `.claude/commands/process-result.md` | 44-49 | Verdict table mapped to `proven`/`completed`/`invalid`. | Maps to canonical statuses. |
| `.claude/commands/audit.md` | 108-117 | After-audit SQL set `status='proven'`/`'invalid'`. | Sets canonical statuses with axis comments. |
| `submissions/TRIAGE_STATUS.md` | 51 | Example SQL set `status='completed'`. | Sets `status='compiled_no_advance'`. |
| `tests/test_aristotle_fetch.py` | 394, 407, 422, 447, 463, 484 | Verdict assertions pinned to dead vocab. | Pinned to canonical vocab. |

**Total dead references fixed: 22 files, ~45 lines.**

The single most impactful broken skill: `mk context` in `math-forge/scripts/mk`.
This is the user-facing tool for gathering prior Aristotle results before submitting.
Its inner query mirrored the broken `gather_context()` and would have silently
returned no prior context for every problem in `submissions.tracking.db`. The fix
mirrors I1's approach: gate on `output_file IS NOT NULL` and `status != 'compile_failed'`,
not on a specific status set.

## Regression test design

`tests/test_schema_consistency.py` runs three assertions:

1. `test_canonical_matches_db` — every distinct `status` value in the live DB is in `CANONICAL_STATUSES`. (Catches rot the other direction — DB writes of dead vocab.)
2. `test_no_dead_code_status_references` — scans every `.py`, `.sh`, `.md`, `.bats` file in repo (excluding `specs/`, `docs/`, `analysis/`, `ai/`, `archive/`, `.lake/`, `problem-databases/`, `formal-conjectures/`, `.claude/worktrees/`) for SQL/Python references to `submissions.status` and asserts every literal is canonical (or grandfathered in `KNOWN_HISTORICAL`).
3. `test_canonical_documented_in_claude_md` — every canonical status string must appear in `CLAUDE.md` so reviewers can find the source of truth.

The matcher uses a tightened heuristic to avoid false positives from sibling tables:

- Matches only `status` (NOT `proof_status`, `analysis_status`, etc.).
- For each `status <op> 'X'` hit, scans backwards to the most recent `FROM`/`UPDATE`/`INTO` in scope; only flags if that table is `submissions` (or unidentified).
- Falls back to file-level heuristics that check for `submissions` vs other table names in the immediate window.

`KNOWN_HISTORICAL` lists `(path_suffix, literal)` pairs that are deliberately allowed (migration scripts must reference old vocab; some files have docstring comments explaining the rename).

### Regression test pass status

```
tests/test_schema_consistency.py::test_canonical_matches_db PASSED
tests/test_schema_consistency.py::test_no_dead_code_status_references PASSED
tests/test_schema_consistency.py::test_canonical_documented_in_claude_md PASSED
```

Full suite (`pytest tests/`): **98 passed, 7 deselected** (the 7 are live-API skip-by-default tests).

## How to add a new status safely

1. Migrate any existing rows first. `audit_proven.py` is the right reference shape.
2. Add the new value to `CANONICAL_STATUSES` in `tests/test_schema_consistency.py`.
3. Document it in `CLAUDE.md` (test 3 requires this).
4. Update code that needs to act on the new bucket. The test will fail until references are updated or grandfathered.
5. Decide whether `gather_context()` and `mk context` should include the new status (currently they gate on artifact presence; new statuses inherit that gate automatically).

## How to retire a status

1. Migrate all DB rows away from the deprecated status.
2. Remove all code references (test 2 will fail until they are gone or moved into `KNOWN_HISTORICAL`).
3. Remove the value from `CANONICAL_STATUSES` and `CLAUDE.md`.

## Files NOT modified

- `scripts/migrate_honest_labels.py` — migration script must reference old vocab. Grandfathered in `KNOWN_HISTORICAL`.
- `scripts/audit_proven.py` — has comments explaining the rename; literals are inside docstrings/comments, not active filters. Grandfathered.
- `specs/`, `analysis/`, `docs/` — these are historical / documentation directories that intentionally describe the rename and pre-rename state. Excluded from the scan.
- `problem-databases/` — uses an unrelated `problems.status` vocabulary (Erdos problem status: `open`/`solved`/`falsifiable`/...). Excluded.
- `.lake/`, `formal-conjectures/.lake/` — mathlib upstream. Excluded.

## Acknowledged limitations

- The static-analysis heuristic in test 2 is conservative. It may miss dynamic SQL constructed via string concatenation, but those are anti-patterns we already avoid.
- The scan does not enforce the `compiled_advance` opt-in invariant (that requires DB-side validation, which `audit_proven.py` handles).
- The test does not catch dead references in newly-added subdirectories — if a new top-level directory is added, the scan will include it by default (which is the safer choice).
