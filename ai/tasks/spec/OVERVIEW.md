---
id: spec.OVERVIEW
type: overview
version: 1
origin: spec-workflow
status: complete
---
# math-forge Spec Overview

## Executive Summary

math-forge is a Claude Code plugin that converts the math project's scattered knowledge artifacts (1,063 submissions, 201 proven results, 43 false lemmas, 56 failed approaches across SQLite tables, .lean files, and markdown notes) into a searchable, structured knowledge base that compounds with every session. The plugin provides three core capabilities: (1) automatic session orientation via a SessionStart hook that injects a ~300-token briefing into Claude's context, (2) a fast FTS5-powered CLI tool (`mk`) for querying proven theorems, failed approaches, and proof strategies, and (3) an extraction pipeline that parses Aristotle result files into structured findings stored in a separate `knowledge.db`.

The system follows a three-layer progressive disclosure model: Layer 0 (hook injection, ~300 tokens, automatic), Layer 1 (CLI summary, ~10-20 lines, on demand), and Layer 2 (verbose detail, ~50-200 lines, explicit request). The architecture is a full Claude Code plugin at `math-forge/` with hooks, scripts, agents, and BATS test suite, modeled after the gpu-forge reference implementation.

---

## Role Summaries

### Product Manager (PM.md)

- **Core problem**: Knowledge decay across sessions. Each session starts from near-zero; 947 .lean result files are opaque blobs with unextracted insights; no feedback loop from proven results to future sketches.
- **Scope**: Separate `knowledge.db` with FTS5, SessionStart hook, PostToolUse lean validator, `mk` CLI tool, result extraction pipeline, migration bootstrap from tracking.db.
- **ROI**: ~2-3 days to build; breaks even in ~10-15 sessions (~1 week). Compounding returns as KB grows.
- **Key decision**: Separate knowledge.db (derived, reconstructible) rather than extending tracking.db. Full plugin architecture rather than standalone .claude/ configuration.
- **Success metrics**: Session orientation <10s (from 5-10 min), 500+ findings at 30 days, <2% duplicate submission rate, 90%+ extraction coverage on new results.

### UX/UI (UX.md)

- **Information architecture**: Three-layer progressive disclosure (Hook ~300 tokens, CLI summary ~10-20 lines, verbose detail ~50-200 lines).
- **CLI design**: `mk` tool with verb-first subcommands (`search`, `find`, `strategies`, `failed`, `stats`). 5 results default, `[PROVEN]`/`[FAILED]`/`[FALSE]` status badges, semantic colors gated on TTY detection.
- **Hook output**: Optimized for LLM consumption (structured key-value pairs, numbered ACTION ITEMS, no decorative formatting). `[math-forge]` prefix on all messages.
- **Output formatting**: No box-drawing characters in `mk` output (pipe-friendly). Two-space indentation. Horizontal rules with `---`. Pipe margin (`| code`) for code snippets. Truncation with `... +N more` indicators.
- **Error pattern**: `[math-forge] ERROR: <what happened>. <how to fix>.` — every error suggests remediation.

### Technical Architecture (TECH.md)

- **Database schema**: `knowledge.db` with 5 tables (`domains`, `findings`, `strategies`, `problems`, `queue_cache`), FTS5 virtual table with `porter unicode61` tokenizer, 3 sync triggers, 11 indexes, 4 views.
- **Plugin structure**: `math-forge/` with `.claude-plugin/plugin.json`, `data/`, `hooks/`, `scripts/`, `agents/`, `tests/` directories.
- **Hooks**: `context-loader.sh` (SessionStart, 5s timeout) queries tracking.db + knowledge.db for ~300-token briefing. `lean-validator.sh` (PostToolUse, 3s timeout) blocks sorry replacement, warns on false lemma references.
- **CLI**: `mk` bash script (~350 lines) with 3-level DB path resolution, `escape_sql()` injection prevention, FTS5 BM25-weighted search, cross-DB queries via ATTACH for `mk find`.
- **Extraction**: `extract_findings.py` Python3 script with regex-based Lean parsing (declarations, imports, sorry count, tactic usage), domain inference from imports, automatic finding generation and insertion.
- **Migration**: `migrate_tracking.py` one-time bootstrap copying proven_theorems, false_lemmas, failed_approaches, candidate_problems. Idempotent via INSERT OR IGNORE. Expected yield: ~255 findings.

### QA Strategy (QA.md)

- **Philosophy**: Real execution, no mocks. Golden query regression tests. BATS for bash, pytest for Python.
- **Test suite**: ~60 test cases across 12 files. Target <30s full suite with `bats --jobs 8`.
- **Coverage**: Hooks (12 cases), mk CLI (20 cases), extraction (9 cases), integration workflows (3 E2E), golden queries (8), performance benchmarks (4), helpers (4).
- **Performance budgets**: SessionStart <5s, PostToolUse <3s, all mk commands <500ms. Hard-fail CI gates.
- **Quality gates**: All BATS/pytest green, golden queries pass, DB integrity validated, zero false positives on sorry-replacement blocking, extraction works on 3+ real .lean files.

---

## Key Decisions (Consolidated)

| # | Decision | Source | Impact |
|---|----------|--------|--------|
| 1 | Separate `knowledge.db` (not extending tracking.db) | PM Q1, TECH Q5 | Plugin has own `data/knowledge.db`. Schema evolves independently. Derived and reconstructible. |
| 2 | Full plugin at `math-forge/` in project repo | PM Q2, Q3 | All components namespaced under `/math-forge:*`. `${CLAUDE_PLUGIN_ROOT}` resolves to `<project>/math-forge/`. |
| 3 | SessionStart hook: ~300 tokens, cached status | PM Q4, Q5 | No live API calls. Reads tracking.db + knowledge.db. Staleness indicator if >6h stale. |
| 4 | Partial migration bootstrap (structured tables only) | PM Q6 | Copy proven_theorems, false_lemmas, failed_approaches, candidate_problems. Skip raw .lean parsing. |
| 5 | FTS5 external content table with porter tokenizer | TECH Q1, Q6 | `findings` is source of truth; `findings_fts` is derived index. Three sync triggers. Supplement with LIKE on structured fields. |
| 6 | BM25 weights: title=10, desc=5, stmt=5, technique=3, tags=2, why_failed=3 | TECH Q2 | Title matches rank highest. problem_id is UNINDEXED (exact SQL only). |
| 7 | `mk` is bash wrapper calling sqlite3 (not Python) | UX Q10 | Fastest startup (~50ms). No interpreter overhead. ~350 lines bash. |
| 8 | PostToolUse: tiered blocking (sorry=block, false lemma=warn) | UX Q4, TECH Q7 | Only sorry replacement gets hard block. All else advisory via `additionalContext`. |
| 9 | No `mk add` in MVP | UX Q6, TECH Q14 | Primary ingestion: migration + extraction. Manual insertion deferred to v2. |
| 10 | `mk find` cross-queries tracking.db | TECH Q9 | ATTACH tracking.db for submissions/false_lemmas. Single command, complete picture. |
| 11 | PATH via CLAUDE_ENV_FILE | TECH Q10 | SessionStart hook adds `${PLUGIN_ROOT}/scripts` to PATH for bare `mk` invocation. |
| 12 | BATS for bash tests, pytest for Python | QA Q1 | Standard TAP-compliant framework. Golden queries hardcoded as individual test cases. |
| 13 | Hybrid DB for tests (on-disk temp files) | QA Q2 | `setup_test_db()` creates temp dir with real DB. Unit <100ms, integration <1s, E2E <5s. |
| 14 | No box-drawing in `mk` output | UX Q1 | Pipe-friendly, copy-paste clean. Horizontal rules and indentation instead. |
| 15 | Extraction runs as part of `/fetch` (zero-effort) | UX Q8 | Knowledge accumulation is invisible side effect of existing workflow. |
| 16 | Queue cache populated by `/status`, not SessionStart | TECH Q11 | Keeps hook fast (<2s). Staleness indicator if cache empty or >6h old. |
| 17 | Migration is idempotent | TECH Q12 | INSERT OR IGNORE. Can re-run safely. Reports 0 new records on re-run. |
| 18 | Fuzzy matching on problem IDs in `mk find` | UX Q7 | Normalize input (strip spaces, underscores, case-fold). LIKE '%normalized%'. |

---

## Module Roadmap (Dependency Order)

```
Priority 0:  devops          Plugin directory structure, plugin.json, bootstrap
    |
Priority 1:  database        SQLite schema, FTS5, triggers, indexes, views
    |
Priority 2:  migration       Bootstrap migration from tracking.db to knowledge.db
    |
Priority 3:  cli             The `mk` KB CLI tool with all subcommands
    |
Priority 4:  hooks           SessionStart hook, PostToolUse hook
    |
Priority 5:  extraction      Result extraction pipeline (.lean -> findings)
    |
Priority 6:  skills          Skill files for number-theory, open-problems, proof-strategies
    |
Priority 7:  commands        Slash commands (/math-forge:search, /math-forge:knowledge, etc.)
    |
Priority 8:  agents          Agent configurations (knowledge-retriever, problem-researcher)
    |
Priority 9:  testing         BATS tests, golden queries, integration tests
    |
Priority 999999: integration Integration with existing /fetch, /sketch, /submit commands
```

**Critical path**: devops -> database -> migration -> cli -> hooks -> extraction. This chain produces the core value: a searchable knowledge base with session briefings and automatic knowledge accumulation.

**Parallel work**: skills (P6), commands (P7), and agents (P8) can be developed in parallel once cli (P3) is complete. Testing (P9) can begin as soon as database (P1) and cli (P3) are available.

**Integration (P999999)**: Deliberately last. Modifies existing `.claude/commands/` files to call `mk` and `extract_findings.py`. Requires all other modules to be stable.
