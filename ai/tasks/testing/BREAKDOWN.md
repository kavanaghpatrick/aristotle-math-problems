---
id: testing.BREAKDOWN
module: testing
priority: 9
status: failing
version: 1
origin: spec-workflow
dependsOn: [cli.BREAKDOWN, hooks.BREAKDOWN, extraction.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/testing/**/*.test.*"
---
# Testing: BATS Tests, Golden Queries, Integration Tests

## Context
math-forge targets ~60 test cases across 12 files using BATS (Bash Automated Testing System) for hook and CLI tests, and pytest for the Python extraction pipeline. Tests use real SQLite databases (no mocks), golden query regression tests for FTS5 relevance, and performance benchmarks with hard-fail gates. The test suite targets <30s total execution with parallel BATS jobs. Reference: QA.md (complete test strategy, all test cases, and test helper code provided).

## Acceptance Criteria

### Test Infrastructure
1. `math-forge/tests/test_helper.bash` exists with: `PLUGIN_ROOT`, `MK` path exports, `setup_test_db()`, `teardown_test_db()`, and fallback assertion functions
2. BATS is available (`brew install bats-core` if needed)
3. `bats tests/*.bats --jobs 8` runs all tests and exits 0

### Hook Tests (12 cases)
4. `tests/test_session_start_hook.bats` (6 cases): Valid JSON output, in-flight count, ready-to-fetch detection, 5s timeout compliance, <500 token budget, auto-init of missing DB
5. `tests/test_lean_validator_hook.bats` (6 cases): Valid file allow, sorry replacement block, new sorry allow, false lemma warning, non-.lean skip, 3s timeout compliance

### CLI Tests (20 cases)
6. `tests/test_mk_search.bats` (6 cases): No-args usage, BM25 ranking, --limit flag, --domain filter, no-results case, <500ms performance
7. `tests/test_mk_find.bats` (4 cases): Problem summary, findings+strategies aggregation, fuzzy matching, non-existent problem handling
8. `tests/test_mk_stats.bats` (3 cases): KB counts, domain distribution, pipeline status
9. `tests/test_mk_utils.bats` (3 cases): escape_sql, normalize_problem

### Extraction Tests (9 cases)
10. `tests/test_extract_findings.py` (pytest, 9 cases): Declaration extraction, import detection, sorry count, domain inference (NT, combinatorics), finding generation (proven, failed), deduplication

### Golden Query Tests (8 cases)
11. `tests/test_golden_queries.bats` (8 cases): Problem-specific searches (Erdos 364, FT p=3, Tuza), technique searches (pigeonhole, smooth), status-specific (greedy failed, Tuza apex false), BM25 weight regression (title > description)

### Performance Tests (4 cases)
12. `tests/test_performance.bats` (4 cases): mk search <500ms with 1K findings, mk find <500ms, mk stats <200ms, SessionStart hook <2s

### Integration Tests (3 cases)
13. `tests/test_integration_workflows.bats` (3 E2E cases): extract -> search -> find roundtrip, migration -> stats -> search, SessionStart context relevance

### Quality Gates
14. All BATS tests pass: `bats tests/*.bats --jobs 8` exit 0
15. All pytest tests pass: `pytest tests/test_*.py -v` exit 0
16. DB integrity: `sqlite3 knowledge.db "PRAGMA integrity_check"` returns "ok" after full suite
17. Full suite completes in <30s

## Technical Notes
- Reference: QA.md has complete test implementations for all test files, including test_helper.bash
- UX: Tests validate UX.md output formats (badges, truncation, color behavior)
- Test: QA.md is the primary reference. Golden queries modeled after gpu-forge's 72 golden queries.

## Subtasks
- [ ] Write `math-forge/tests/test_helper.bash` with setup/teardown and assertions
- [ ] Write `math-forge/tests/test_session_start_hook.bats` (6 cases)
- [ ] Write `math-forge/tests/test_lean_validator_hook.bats` (6 cases)
- [ ] Write `math-forge/tests/test_mk_search.bats` (6 cases)
- [ ] Write `math-forge/tests/test_mk_find.bats` (4 cases)
- [ ] Write `math-forge/tests/test_mk_stats.bats` (3 cases)
- [ ] Write `math-forge/tests/test_mk_utils.bats` (3 cases)
- [ ] Write `math-forge/tests/test_extract_findings.py` (9 pytest cases)
- [ ] Write `math-forge/tests/test_golden_queries.bats` (8 golden query cases)
- [ ] Write `math-forge/tests/test_performance.bats` (4 performance benchmarks)
- [ ] Write `math-forge/tests/test_integration_workflows.bats` (3 E2E workflows)
- [ ] Create `math-forge/tests/fixtures/` directory with sample .lean files for extraction tests
- [ ] Verify full suite runs in <30s with parallel BATS jobs
- [ ] Verify all quality gates pass
