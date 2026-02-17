---
id: database.BREAKDOWN
module: database
priority: 1
status: failing
version: 1
origin: spec-workflow
dependsOn: [devops.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/database/**/*.test.*"
---
# Database: SQLite Schema, FTS5, Triggers, Indexes, Views

## Context
knowledge.db is the core data store for math-forge. It holds discrete mathematical findings (theorems, techniques, failures, false lemmas), problem-level strategies, and a problem summary table. FTS5 provides full-text search with BM25 ranking. The schema is defined in `math-forge/data/schema.sql` and is the foundation for the CLI tool, hooks, and extraction pipeline. Reference: TECH.md "Database Schema" section (complete SQL provided).

## Acceptance Criteria
1. `math-forge/data/schema.sql` contains complete CREATE TABLE statements for: `domains`, `findings`, `strategies`, `problems`, `queue_cache`
2. `domains` table is pre-populated with 4 rows: `nt`, `algebra`, `combinatorics`, `analysis`
3. `findings` table has CHECK constraints on `finding_type` (7 values) and `confidence` (5 values)
4. `findings_fts` FTS5 virtual table is created with `content=findings`, `content_rowid=id`, `tokenize='porter unicode61'`, and columns: `title`, `description`, `problem_id` (UNINDEXED), `theorem_name`, `theorem_statement`, `proof_technique`, `tags`, `why_failed`
5. Three FTS5 sync triggers exist: `findings_fts_insert`, `findings_fts_delete`, `findings_fts_update` (UPDATE trigger deletes old then inserts new)
6. 11 indexes created on: findings (type, domain, problem, slot, confidence, created_at), strategies (problem, outcome, domain), problems (domain, status)
7. 4 views created: `v_proven_techniques`, `v_failed_approaches`, `v_problem_dashboard`, `v_near_miss_findings`
8. `PRAGMA journal_mode=WAL` and `PRAGMA foreign_keys=ON` are set
9. Running `sqlite3 knowledge.db < schema.sql` produces a valid DB with `PRAGMA integrity_check` returning "ok"
10. FTS5 sync triggers work correctly: INSERT a finding, query FTS MATCH, UPDATE the finding, verify FTS reflects change, DELETE, verify FTS no longer returns it

## Technical Notes
- Reference: TECH.md "Database Schema" section has complete SQL
- UX: BM25 weights specified in TECH.md Q2: title=10, description=5, theorem_statement=5, proof_technique=3, tags=2, why_failed=3
- Test: QA.md "FTS5 Trigger Synchronization Testing" describes the CRUD cycle test (Q8)

## Subtasks
- [ ] Write `math-forge/data/schema.sql` with all tables, constraints, and domain seed data
- [ ] Add FTS5 virtual table definition with porter unicode61 tokenizer
- [ ] Add three FTS5 sync triggers (INSERT, DELETE, UPDATE)
- [ ] Add all 11 indexes
- [ ] Add all 4 views
- [ ] Set WAL journal mode and foreign keys pragma
- [ ] Test: create DB from schema, insert sample data, verify FTS5 MATCH works
- [ ] Test: CRUD cycle on findings + FTS5 trigger sync verification
