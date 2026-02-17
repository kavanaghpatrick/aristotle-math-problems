---
id: extraction.BREAKDOWN
module: extraction
priority: 5
status: failing
version: 1
origin: spec-workflow
dependsOn: [database.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/extraction/**/*.test.*"
---
# Extraction: Result Extraction Pipeline (.lean -> findings)

## Context
The extraction pipeline parses Aristotle result files (.lean) and inserts structured findings into knowledge.db. This is the primary mechanism for knowledge accumulation after the initial migration. The pipeline uses regex-based extraction for Lean 4 syntax (theorem/lemma/def declarations, Mathlib imports, sorry locations, tactic usage) and heuristic domain inference from import patterns. Reference: TECH.md "Result Extraction Pipeline" section (complete Python script provided).

## Acceptance Criteria
1. `math-forge/scripts/extract_findings.py` exists and runs with `python3`
2. **Declaration extraction**: Identifies `theorem`, `lemma`, `def`, `noncomputable def`, `instance` declarations with name, statement, and per-declaration sorry detection
3. **Import extraction**: Captures all `import Mathlib.*` lines
4. **Metric extraction**: Total sorry count, axiom count, total lines
5. **Tactic analysis**: Counts usage of 16 tactics (native_decide, decide, omega, simp, ring, norm_num, induction, cases, contradiction, exact, apply, calc, interval_cases, field_simp, zify, push_cast)
6. **Technique inference**: Maps dominant tactic to technique name (e.g., `native_decide` -> "finite computation (native_decide)")
7. **Domain inference**: Infers mathematical domain from Mathlib imports (NT signals, algebra signals, combinatorics signals, analysis signals). Defaults to `nt`.
8. **Finding generation**: Creates one `theorem` finding per proven declaration (no sorry), one `technique` finding for fully proven files, one `failure` finding if >2 sorry
9. **Auto-detection**: Slot number and problem_id auto-detected from filename patterns (e.g., `slot622_erdos364_result.lean`)
10. **DB insertion**: Findings inserted into knowledge.db via parameterized queries. Duplicates handled with INSERT OR IGNORE.
11. **Problem record update**: `problems` table updated with submission_count, proven_count, status via UPSERT
12. **CLI interface**: `python3 extract_findings.py <file> [--slot N] [--problem-id ID] [--db PATH]`
13. **Output**: Reports extraction summary: `[math-forge] Extracted N findings from slotM (filename)`
14. **Error handling**: Graceful on empty files, malformed Lean, missing DB. Never crashes.

## Technical Notes
- Reference: TECH.md "scripts/extract_findings.py" has complete implementation (~200 lines)
- UX: UX.md "Flow 3: Processing a Result into KB" describes the zero-effort integration pattern
- Test: QA.md `test_extract_findings.py` (9 pytest cases) covers declarations, imports, sorry count, domain inference, finding generation, deduplication. QA.md Q15 covers malformed file handling.

## Subtasks
- [ ] Write `math-forge/scripts/extract_findings.py`
- [ ] Implement `extract_from_lean()`: regex for declarations, imports, sorry, axioms, tactics
- [ ] Implement `infer_domain()`: score-based domain classification from imports
- [ ] Implement `generate_findings()`: create finding dicts from extracted data
- [ ] Implement `insert_findings()`: parameterized INSERT into knowledge.db
- [ ] Implement problem record UPSERT logic
- [ ] Implement CLI argument parsing with auto-detection of slot and problem_id
- [ ] Implement auto-init of knowledge.db from schema.sql if missing
- [ ] Add error handling for empty files, missing files, malformed content
- [ ] Test: extract from sample proven .lean file, verify findings generated
- [ ] Test: extract from sample failed .lean file (many sorry), verify failure finding generated
- [ ] Test: verify domain inference for NT, algebra, combinatorics imports
