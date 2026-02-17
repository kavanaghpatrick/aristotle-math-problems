---
id: migration.BREAKDOWN
module: migration
priority: 2
status: failing
version: 1
origin: spec-workflow
dependsOn: [database.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/migration/**/*.test.*"
---
# Migration: Bootstrap from tracking.db to knowledge.db

## Context
The existing `submissions/tracking.db` contains 1,063 submissions worth of structured data across tables like `proven_theorems`, `false_lemmas`, `failed_approaches`, and `candidate_problems`. The migration script copies this data into knowledge.db as a one-time bootstrap, seeding the knowledge base with ~255 findings from day one. The migration is idempotent (INSERT OR IGNORE) and does NOT parse raw .lean files. Reference: TECH.md "Migration & Bootstrap" section (complete Python script provided).

## Acceptance Criteria
1. `math-forge/scripts/migrate_tracking.py` exists and runs with `python3`
2. Script migrates `proven_theorems` -> findings (type: `theorem`, confidence: `verified`)
3. Script migrates `false_lemmas` -> findings (type: `false_lemma`, confidence: `disproven`)
4. Script migrates `failed_approaches` -> findings (type: `failure`, confidence: `high`)
5. Script migrates `candidate_problems` -> `problems` table with domain mapping
6. All inserts use `INSERT OR IGNORE` for idempotency
7. Script reports count of records migrated per category and total
8. Running the script twice produces 0 new records on the second run
9. After migration, `mk stats` shows non-zero counts in all finding type categories
10. After migration, `mk search "erdos"` returns results from migrated data
11. Script handles missing tables gracefully (some tracking.db tables may not exist)
12. Domain mapping: `number_theory`/`nt`/`number-theory` -> `nt`, `algebra` -> `algebra`, etc.

## Technical Notes
- Reference: TECH.md "scripts/migrate_tracking.py" has complete implementation
- UX: Migration output follows `[math-forge] Migrated N <category>` format
- Test: QA.md Q10 describes manual test process (migration -> mk stats -> mk search verification). QA.md "WORKFLOW: migration -> stats -> search" integration test covers the full path.

## Subtasks
- [ ] Write `math-forge/scripts/migrate_tracking.py` with all 4 migration stages
- [ ] Implement proven_theorems migration with slot number extraction from filenames
- [ ] Implement false_lemmas migration with counterexample and avoid_pattern fields
- [ ] Implement failed_approaches migration with submission UUID cross-reference
- [ ] Implement candidate_problems migration with domain mapping
- [ ] Add idempotency via INSERT OR IGNORE
- [ ] Add summary report output
- [ ] Test: run on real tracking.db, verify counts match expectations (~255 records)
- [ ] Test: run twice, verify second run reports 0 new records
