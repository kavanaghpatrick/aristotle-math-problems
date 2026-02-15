---
spec: honest-tooling
phase: requirements
created: 2026-02-15
---

# Requirements: Honest Tooling

## Goal

Replace misleading "PROVEN" labels in submission tooling with honest "COMPILED CLEAN" labels, add batch submission support, and unify pipeline commands under the `mk` CLI. No existing pipeline behavior should break.

## User Decisions

| Question | Response |
|----------|----------|
| Problem scope | All four areas: honest labels, batch fix, unified CLI, alignment |
| Constraints | Don't break active pipeline -- existing submission/fetch commands must keep working |
| Success criteria | Honest output labels -- "COMPILED CLEAN" instead of "PROVEN" for compilations |
| Primary users | All pipeline users |
| Priority tradeoffs | Speed of delivery |
| Additional context | Detailed plan exists with exact code changes for all files |

## User Stories

### US-1: Honest Compilation Labels

**As a** pipeline user
**I want** compilation results labeled "COMPILED CLEAN" instead of "PROVEN"
**So that** I don't confuse "Lean compiled without sorry/axiom" with "open problem resolved"

**Acceptance Criteria:**
- [ ] AC-1.1: `aristotle_fetch.py` assigns verdict `compiled_clean` (not `proven`) when sorry=0, axiom=0, no negation
- [ ] AC-1.2: `aristotle_fetch.py` display strings show "COMPILED CLEAN" (not "PROVEN") in status and fetch output
- [ ] AC-1.3: `verified` column still set to 1 when verdict is `compiled_clean`
- [ ] AC-1.4: All 203 existing `status='proven'` rows in tracking.db migrated to `compiled_clean`
- [ ] AC-1.5: `audit_proven.py` SQL IN clauses include `'compiled_clean'` alongside `'proven'` for backward compat
- [ ] AC-1.6: `audit_proven.py` display strings say "compiled clean" not "proven"
- [ ] AC-1.7: `verify_output.sh` display strings say "COMPILED CLEAN" not "PROVEN"
- [ ] AC-1.8: `backfill_slots.py` and `backfill_all_files.py` write `compiled_clean` instead of `proven`

### US-2: Target Resolution Tracking

**As a** pipeline user
**I want** a `target_resolved` column on submissions
**So that** I can distinguish "compiled clean" from "actually resolved an open problem"

**Acceptance Criteria:**
- [ ] AC-2.1: `submissions` table has `target_resolved INTEGER DEFAULT 0` column
- [ ] AC-2.2: Column added via `ALTER TABLE` migration (no table recreation)
- [ ] AC-2.3: Existing rows default to `target_resolved = 0`
- [ ] AC-2.4: `aristotle_fetch.py` includes `target_resolved` in DB writes (default 0, manually settable)

### US-3: Batch Submission Support

**As a** pipeline user
**I want** a `--batch` flag on `safe_aristotle_submit.py`
**So that** I can submit multiple sketches without interactive rate-limit prompts

**Acceptance Criteria:**
- [ ] AC-3.1: `--batch` flag accepted by CLI parser
- [ ] AC-3.2: In batch mode, duplicate check still runs (prevents resubmission of same sketch)
- [ ] AC-3.3: In batch mode, interactive rate-limit confirmation skipped (auto-proceeds)
- [ ] AC-3.4: In batch mode, multiple input files accepted as positional args
- [ ] AC-3.5: Each file submitted sequentially with per-file error handling (one failure doesn't abort batch)

### US-4: Split Duplicate/Rate-Limit Checks

**As a** developer
**I want** `check_recent_submissions()` split into `check_duplicate()` and `check_rate_limit()`
**So that** batch mode can skip rate-limit prompts while keeping duplicate protection

**Acceptance Criteria:**
- [ ] AC-4.1: `check_duplicate(task_hash, window_minutes)` reads local transaction log only, returns bool
- [ ] AC-4.2: `check_rate_limit(window_minutes)` calls API, returns `{count, has_capacity}`
- [ ] AC-4.3: `check_queue_capacity()` and `check_rate_limit()` share a single `list_projects` API call (no double API hit)
- [ ] AC-4.4: `safe_submit()` calls both functions where it previously called `check_recent_submissions()`
- [ ] AC-4.5: Existing single-file submission behavior unchanged (duplicate + rate limit + interactive prompt)

### US-5: Unified mk CLI Commands

**As a** pipeline user
**I want** `mk submit`, `mk status`, `mk partials`, `mk resubmittable`, `mk query`
**So that** I have one CLI entry point for all pipeline operations

**Acceptance Criteria:**
- [ ] AC-5.1: `mk submit <file> [args...]` delegates to `safe_aristotle_submit.py` with passthrough args
- [ ] AC-5.2: `mk status [uuid-or-slot]` delegates to `aristotle_fetch.py status`
- [ ] AC-5.3: `mk partials` queries tracking.db for submissions with sorry_count=1 (near misses)
- [ ] AC-5.4: `mk resubmittable` queries tracking.db for failed/partial submissions eligible for resubmission
- [ ] AC-5.5: `mk query <sql>` runs arbitrary SQL against tracking.db via sqlite3
- [ ] AC-5.6: `mk help` includes all new commands
- [ ] AC-5.7: All new commands use existing `run_sql` / `check_db` helpers where applicable

### US-6: Downstream Script Alignment

**As a** developer
**I want** all scripts that write `status='proven'` to tracking.db updated
**So that** no script re-introduces the old label

**Acceptance Criteria:**
- [ ] AC-6.1: `backfill_slots.py` line 111 writes `compiled_clean` instead of `proven`
- [ ] AC-6.2: `backfill_all_files.py` line 83 writes `compiled_clean` instead of `proven`
- [ ] AC-6.3: `post_result.sh` display strings updated
- [ ] AC-6.4: No script in `scripts/` writes `status = 'proven'` to tracking.db after changes

## Functional Requirements

| ID | Requirement | Priority | Acceptance Criteria |
|----|-------------|----------|---------------------|
| FR-1 | `aristotle_fetch.py` verdict changes from `proven` to `compiled_clean` | P0 | AC-1.1, AC-1.2, AC-1.3 |
| FR-2 | DB migration: rename status + add `target_resolved` column | P0 | AC-1.4, AC-2.1, AC-2.2, AC-2.3 |
| FR-3 | `audit_proven.py` SQL and display updates | P0 | AC-1.5, AC-1.6 |
| FR-4 | `verify_output.sh` display string updates | P0 | AC-1.7 |
| FR-5 | `backfill_*.py` status string updates | P0 | AC-1.8, AC-6.1, AC-6.2 |
| FR-6 | Split `check_recent_submissions()` into two functions | P1 | AC-4.1, AC-4.2, AC-4.3, AC-4.4, AC-4.5 |
| FR-7 | `--batch` flag for `safe_aristotle_submit.py` | P1 | AC-3.1, AC-3.2, AC-3.3, AC-3.4, AC-3.5 |
| FR-8 | `mk submit` command | P1 | AC-5.1 |
| FR-9 | `mk status` command | P1 | AC-5.2 |
| FR-10 | `mk partials` command | P1 | AC-5.3 |
| FR-11 | `mk resubmittable` command | P1 | AC-5.4 |
| FR-12 | `mk query` command | P2 | AC-5.5 |
| FR-13 | `mk help` updated with all new commands | P1 | AC-5.6 |
| FR-14 | `target_resolved` column in DB writes | P1 | AC-2.4 |
| FR-15 | `post_result.sh` display alignment | P2 | AC-6.3 |

## Non-Functional Requirements

| ID | Requirement | Metric | Target |
|----|-------------|--------|--------|
| NFR-1 | Backward compatibility | Existing commands | All `aristotle_fetch.py` and `safe_aristotle_submit.py` CLI invocations work unchanged |
| NFR-2 | Migration safety | Data integrity | Zero data loss during status rename; migration idempotent |
| NFR-3 | API efficiency | API calls per submission | No increase (merge rate-limit + capacity into single `list_projects` call) |
| NFR-4 | Test coverage | BATS tests | Existing `bats math-forge/tests/` pass after changes |
| NFR-5 | knowledge.db isolation | Schema changes | Zero changes to knowledge.db schema, data, or CHECK constraints |

## Glossary

- **compiled_clean**: New tracking.db status. Lean file compiled with 0 sorry, 0 axiom, no negation. Replaces `proven`.
- **target_resolved**: Boolean column. 1 = submission actually resolved an open problem. Manually set. Distinguished from "compiled clean".
- **tracking.db**: `submissions/tracking.db`. Stores submission status, audit results, per-slot data.
- **knowledge.db**: `math-forge/data/knowledge.db`. Stores findings, strategies, problem-level status. NOT changed by this spec.
- **mk**: CLI entry point from math-forge plugin (`math-forge/scripts/mk`). Shell script with `case` branches.
- **batch mode**: `--batch` flag. Submits multiple files, skips interactive prompts, keeps duplicate protection.
- **near miss**: Submission with sorry_count=1. Candidate for targeted resubmission.

## Out of Scope

- Changing `problems.status = 'proven'` in knowledge.db (semantically correct at problem level)
- Changing `strategies.outcome = 'proven'` in knowledge.db
- Changing mk search `[PROVEN]` badge for `finding_type='theorem'` findings
- Renaming `proven_count` column in tracking.db (means "theorem count in file", not submission status)
- Changing `literature_lemmas.proof_status = 'proven'` (different table, different meaning)
- Changing `pre_submit.sh` or `get_scaffolding.sh` (use `literature_lemmas`, not `submissions`)
- Renaming `submit_parker_batch.py` internal counter keys (cosmetic, no user impact)
- Adding new BATS tests for new mk commands (follow-up spec)
- `extract_findings.py` status assignment for knowledge.db `problems.status` (keep as `proven`)

## Dependencies

- **tracking.db access**: Migration must run before any other code changes take effect
- **No active backfills**: `backfill_*.py` should not be mid-run during migration
- **Aristotle API**: `--batch` and function split depend on existing `anthropic` SDK patterns in `safe_aristotle_submit.py`
- **In-flight submissions**: 6 currently `submitted` slots. Post-migration fetches will correctly assign `compiled_clean`.

## Risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Script uses `status='proven'` not caught by research | Low | Medium | FR-6.4: grep scan for `'proven'` in all `scripts/` after changes |
| Migration runs twice | Low | None | UPDATE is idempotent (no rows match `'proven'` after first run) |
| Batch mode submits duplicates | Low | Low | Duplicate check still active in batch mode (AC-3.2) |
| mk query allows destructive SQL | Medium | High | Document as power-user command; read-only wrapper optional in P2 |

## Unresolved Questions

1. Should `mk query` be read-only (SELECT only) or allow writes? Recommend read-only for safety.
2. Should `--batch` accept multiple positional args or a file listing paths? Research suggests positional args (simpler).
3. Should `mk resubmittable` auto-generate resub commands or just list candidates? Recommend list-only for v1.

## Success Criteria

- `aristotle_fetch.py` never outputs the word "PROVEN" for compilation results
- All 203 existing `status='proven'` rows migrated to `compiled_clean` in tracking.db
- `mk submit`, `mk status`, `mk partials` all functional
- `bats math-forge/tests/` passes
- No double API calls in submission flow
- knowledge.db completely untouched

## Next Steps

1. Approve requirements
2. Generate design.md with implementation plan per file
3. Generate tasks.md with ordered implementation tasks
4. Implement migration script first (FR-2), then code changes, then new mk commands
