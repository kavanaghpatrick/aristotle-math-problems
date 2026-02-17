---
id: cli.BREAKDOWN
module: cli
priority: 3
status: failing
version: 1
origin: spec-workflow
dependsOn: [database.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/cli/**/*.test.*"
---
# CLI: The `mk` Knowledge Base CLI Tool

## Context
`mk` (math-knowledge) is the primary query interface for the knowledge base. It is a bash script (~350 lines) that dispatches subcommands to sqlite3 queries against knowledge.db. It serves both Claude (during sketch writing via Bash tool) and Patrick (direct terminal use). The tool follows the gpu-forge `kb` pattern: 3-level DB path resolution, SQL injection prevention, TTY-aware color output, and BM25-ranked FTS5 search. Reference: TECH.md "KB CLI Tool" section, UX.md "Command Design" section.

## Acceptance Criteria
1. `math-forge/scripts/mk` exists as executable bash script
2. **3-level DB resolution**: `MATH_FORGE_DB` env var > `${CLAUDE_PLUGIN_ROOT}/data/knowledge.db` > script-relative `../data/knowledge.db`
3. **`mk search <query>`**: Returns FTS5 BM25-ranked results with `[PROVEN]`/`[FAILED]`/`[FALSE]` badges. Default limit 5, respects `--limit`, `--domain`, `--verbose` flags.
4. **`mk find <problem-id>`**: Returns complete problem view with findings, strategies, submissions (cross-DB from tracking.db), false lemmas, and "NEXT" action suggestion. Supports fuzzy matching (strip spaces, underscores, case-fold).
5. **`mk strategies [domain]`**: Lists proven techniques grouped by frequency with slot references. Optionally filtered by domain.
6. **`mk failed [keyword]`**: Returns failed approaches and false lemmas matching keyword. Shows attempt counts and WARNING footer.
7. **`mk stats`**: Dashboard showing finding counts by type, domain distribution with progress bars, freshness, and pipeline status.
8. **`mk init`**: Creates knowledge.db from schema.sql if it does not exist.
9. **`mk help`**: Shows usage for all subcommands. Running `mk` with no args shows help.
10. **Color**: Semantic colors (green=proven, red=failed, yellow=in-flight, cyan=headers) gated on `[ -t 1 ] && [ -z "${NO_COLOR:-}" ]`.
11. **`escape_sql()`**: Escapes single quotes for SQL injection prevention.
12. **Performance**: All subcommands complete in <500ms with 1000 findings.
13. **Error messages**: Follow `[math-forge] ERROR: <what>. <how to fix>.` pattern.
14. **No box-drawing characters**: Uses horizontal rules (`---`) and 2-space indentation.
15. **Truncation**: `... +N more (use --limit 20 or --verbose for all)` when results exceed limit.

## Technical Notes
- Reference: TECH.md "KB CLI Tool" section has full architecture, command routing, and core SQL queries
- UX: UX.md "Command Design" section specifies output format for each subcommand with example output
- Test: QA.md has dedicated test files: `test_mk_search.bats` (6 cases), `test_mk_find.bats` (4 cases), `test_mk_stats.bats` (3 cases), `test_mk_utils.bats` (3 cases)

## Subtasks
- [ ] Create `math-forge/scripts/mk` with shebang, set -uo pipefail, 3-level DB resolution
- [ ] Implement `escape_sql()` and `run_sql()` helper functions
- [ ] Implement `normalize_problem()` for fuzzy matching
- [ ] Implement TTY-aware color support
- [ ] Implement `mk search` with FTS5 MATCH, BM25 weights, --limit, --domain, --verbose
- [ ] Implement `mk find` with cross-DB query (ATTACH tracking.db), fuzzy matching, section output
- [ ] Implement `mk strategies` with GROUP BY proof_technique, domain filter
- [ ] Implement `mk failed` with dual-source query (knowledge.db + tracking.db false_lemmas)
- [ ] Implement `mk stats` with finding counts, domain distribution, freshness, pipeline
- [ ] Implement `mk init` (create DB from schema.sql)
- [ ] Implement `mk help` (usage text for all subcommands)
- [ ] Add truncation logic and "... +N more" footer
- [ ] Add error message formatting
- [ ] Set executable permission (`chmod +x`)
