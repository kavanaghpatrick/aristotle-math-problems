# Tasks: Gap-Targeting Pivot

## Phase 1: Make It Work (POC)

Focus: Get the core enforcement working end-to-end. Philosophy docs set the frame, core skills implement the workflow, pipeline gate enforces it.

### Batch 1: Philosophy Docs

- [ ] 1.1 Rewrite CLAUDE.md to gap-targeting-only philosophy
  - **Do**:
    1. Read current `/Users/patrickkavanagh/math/CLAUDE.md` (273 lines)
    2. Rewrite to ~100-120 lines following design section 6 structure
    3. Single-phase pipeline: GAP -> SUBMIT (remove IDEATE/SKETCH/FORMALIZE phases)
    4. Remove Tracks A-D, case studies, multi-agent strategy table, Lean pitfalls, proof state (Tuza), subagent prompt rules, decision priority matrix
    5. New sketch format: bare conjecture <=30 lines (OPEN GAP / English / Lean / Status)
    6. Hard rules: gap-targeting only, no proof strategy, INFORMAL only, no override
    7. Simplified commands section with gap-targeting descriptions
    8. Add `mk context` and `mk gaps` to CLI reference
    9. Keep math-forge CLI section (mk search/find/failed/context/gaps/stats)
    10. Keep "When Stuck" section (reframed: mk failed, mk context, try different problem, debate)
  - **Files**: `/Users/patrickkavanagh/math/CLAUDE.md`
  - **Done when**: CLAUDE.md is <=120 lines, contains no references to Track B/C/D, IDEATE phase, "50-100 lines", "proof strategy development", or case studies of known-result work
  - **Verify**: `wc -l /Users/patrickkavanagh/math/CLAUDE.md | awk '{print ($1 <= 120) ? "PASS" : "FAIL: "$1" lines"}'` && `grep -ciE '(Track [BCD]|IDEATE|50-100 lines|proof strategy development|Leinster|Wolstenholme|Carmichael)' /Users/patrickkavanagh/math/CLAUDE.md | awk '{print ($1 == 0) ? "PASS" : "FAIL: "$1" old references"}'`
  - **Commit**: `feat(gap-pivot): rewrite CLAUDE.md to gap-targeting-only philosophy`
  - _Requirements: FR-6, AC-4.1_
  - _Design: Section 6 (CLAUDE.md Rewrite Structure)_

- [ ] 1.2 Simplify MEMORY.md to gap-targeting mandate
  - **Do**:
    1. Read current `/Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md` (98 lines)
    2. Rewrite to ~40-50 lines following design section 7 structure
    3. Prime directive: gap-targeting ONLY, bare conjecture, zero proof guidance
    4. Hard rules: <=30 lines, INFORMAL .txt only, auto-context, no override
    5. Keep falsified approaches section (prevents repeating dead ends)
    6. Keep user directives (condensed)
    7. Remove: detailed track record of known-math formalizations, FT p=3 case status table, old in-flight list, tooling fixes, "What NOT to Do" (subsumed by hard rules)
  - **Files**: `/Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md`
  - **Done when**: MEMORY.md is <=60 lines, no detailed track record of known-math formalizations, no FT p=3 case table
  - **Verify**: `wc -l /Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md | awk '{print ($1 <= 60) ? "PASS" : "FAIL: "$1" lines"}'` && `grep -ciE '(slot590|slot610|slot611|slot603|q.*mod.*4.*Eliminated|Leinster.*2001|ZERO VALUE.*NO EXCEPTIONS)' /Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md | awk '{print ($1 == 0) ? "PASS" : "FAIL: "$1" old references"}'`
  - **Commit**: `feat(gap-pivot): simplify MEMORY.md to gap-targeting mandate`
  - _Requirements: FR-7, AC-4.2_
  - _Design: Section 7 (MEMORY.md Simplification)_

### Batch 2: Core Skills (sketch, submit, sweep)

- [ ] 1.3 Rewrite sketch.md to bare-gap template
  - **Do**:
    1. Read current `/Users/patrickkavanagh/math/.claude/commands/sketch.md` (218 lines)
    2. Rewrite to ~60 lines following design section 2 (Bare-Gap Sketch Template)
    3. New template: OPEN GAP / Source / Domain / English statement / Lean statement / Status (~10 lines max)
    4. Remove: IDEATE phase, strategy template, computational exploration, "What's Known", "Proposed Strategy", "Key Lemmas", "Main Proof Assembly", "Computational Evidence", "Mathlib" sections
    5. New 5-step workflow: identify gap -> check mk failed + mk find -> write bare sketch -> auto-assign slot -> report
    6. Remove separate OPEN vs KNOWN templates (KNOWN is dead)
  - **Files**: `/Users/patrickkavanagh/math/.claude/commands/sketch.md`
  - **Done when**: sketch.md is <=80 lines, no "Proof Strategy"/"Key Lemma"/"Proposed Approach" sections in template, uses bare-gap format
  - **Verify**: `wc -l /Users/patrickkavanagh/math/.claude/commands/sketch.md | awk '{print ($1 <= 80) ? "PASS" : "FAIL: "$1" lines"}'` && `grep -ciE '(Proof Strategy|Key Lemma|Proposed Approach|Main Proof Assembly|Computational Evidence|IDEATE)' /Users/patrickkavanagh/math/.claude/commands/sketch.md | awk '{print ($1 == 0) ? "PASS" : "FAIL: "$1" old patterns"}'`
  - **Commit**: `feat(gap-pivot): rewrite sketch.md to bare-gap template`
  - _Requirements: FR-2, AC-1.1, AC-1.2, AC-6.1_
  - _Design: Section 2 (Bare-Gap Sketch Template)_

- [ ] 1.4 Rewrite submit.md with gap-targeting gate
  - **Do**:
    1. Read current `/Users/patrickkavanagh/math/.claude/commands/submit.md` (180 lines)
    2. Rewrite to ~80 lines with gap-targeting gate as Step 1
    3. Add: call `check_gap_targeting()` before all other checks
    4. Add: auto-context step using `gather_context()` / `mk context`
    5. Remove: FORMAL paths entirely (gap-targeting = INFORMAL only)
    6. Remove: mode detection (always INFORMAL)
    7. Keep: pre-flight checks (false lemmas, prior attempts), queue check, submit, track
  - **Files**: `/Users/patrickkavanagh/math/.claude/commands/submit.md`
  - **Done when**: submit.md references check_gap_targeting(), INFORMAL only, no FORMAL paths
  - **Verify**: `grep -c 'gap_targeting\|check_gap' /Users/patrickkavanagh/math/.claude/commands/submit.md | awk '{print ($1 > 0) ? "PASS" : "FAIL: no gap-targeting reference"}'` && `grep -ciE '(FORMAL_LEAN|input_type.*formal|\.lean.*submission)' /Users/patrickkavanagh/math/.claude/commands/submit.md | awk '{print ($1 == 0) ? "PASS" : "FAIL: still has FORMAL paths"}'`
  - **Commit**: `feat(gap-pivot): rewrite submit.md with gap-targeting gate`
  - _Requirements: AC-6.2, AC-1.3_
  - _Design: Section 1 (check_gap_targeting), Section 3 (Auto-Context)_

- [ ] 1.5 Rewrite sweep.md to single-tier open gaps
  - **Do**:
    1. Read current `/Users/patrickkavanagh/math/.claude/commands/sweep.md` (170 lines)
    2. Rewrite to ~60 lines: single tier (OPEN gaps only)
    3. Remove: Tiers B/C/D, Track D "KNOWN RESULT", computational discovery, falsification tracks
    4. New flow: scan formal-conjectures -> filter OPEN only -> state bare gap -> submit
  - **Files**: `/Users/patrickkavanagh/math/.claude/commands/sweep.md`
  - **Done when**: sweep.md has no Tier B/C/D references, single workflow
  - **Verify**: `grep -ciE '(Tier [BCD]|Track [BCD]|KNOWN.RESULT|Known-Result)' /Users/patrickkavanagh/math/.claude/commands/sweep.md | awk '{print ($1 == 0) ? "PASS" : "FAIL: old tiers present"}'`
  - **Commit**: `feat(gap-pivot): rewrite sweep.md to single-tier open gaps`
  - _Requirements: AC-6.3_
  - _Design: Section 11 (Skill Rewrites Summary)_

- [ ] 1.6 [VERIFY] Quality checkpoint: `bats /Users/patrickkavanagh/math/math-forge/tests/`
  - **Do**: Run all 32 BATS tests to verify doc/skill rewrites haven't broken anything
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -5`
  - **Done when**: All 32 tests pass
  - **Commit**: `chore(gap-pivot): pass quality checkpoint` (only if fixes needed)

### Batch 3: Pipeline Hard Block

- [ ] 1.7 Add check_gap_targeting() to safe_aristotle_submit.py
  - **Do**:
    1. Read `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` (462 lines)
    2. Add `GapTargetingError(SubmissionError)` exception class
    3. Add `check_gap_targeting(input_file: Path) -> dict` function per design section 1
    4. Implement 5 checks in order: C1 (.lean rejection), C2 (empty file), C3 (>30 non-blank lines), C4 (strategy keyword regex patterns), C5 (>5 lines Lean code)
    5. Add 8 `STRATEGY_PATTERNS` regex list and 3 `FALSIFICATION_PATTERNS` regex list per design
    6. Falsification patterns checked BEFORE strategy patterns
    7. Gap statement extraction: first non-blank line after removing comment markers
    8. Return dict: `{"pass": True, "submission_type": "gap_targeting"|"falsification", "gap_statement": str, "line_count": int}`
    9. Wire into `safe_submit()` as first check before lockfile
  - **Files**: `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py`
  - **Done when**: `check_gap_targeting()` exists, is called from `safe_submit()`, rejects .lean files, >30 line .txt, strategy keywords. No override.
  - **Verify**: `python3 -c "import sys; sys.path.insert(0, '/Users/patrickkavanagh/math/scripts'); exec(open('/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py').read().split('ARISTOTLE_API_KEY')[0]); print('PASS: module structure valid')" 2>&1 | head -5` && `grep -c 'check_gap_targeting\|GapTargetingError\|STRATEGY_PATTERNS' /Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py | awk '{print ($1 >= 3) ? "PASS" : "FAIL: missing gap-targeting code"}'`
  - **Commit**: `feat(gap-pivot): add check_gap_targeting() hard block to submit pipeline`
  - _Requirements: FR-1, AC-2.1, AC-2.2, AC-2.3, AC-2.4, AC-2.5, AC-2.6_
  - _Design: Section 1 (check_gap_targeting -- Hard Block)_

- [ ] 1.8 Add extract_problem_id() and gather_context() to safe_aristotle_submit.py
  - **Do**:
    1. Add `extract_problem_id(input_file: Path) -> str | None` per design section 3
    2. Parse filename: strip `slot\d+_` prefix, strip `.txt` suffix
    3. Content fallback: read first 5 lines, look for `OPEN GAP:` line
    4. Normalize: lowercase, strip spaces/underscores, truncate at 50 chars
    5. Add `gather_context(problem_id: str) -> list[Path]` per design section 3
    6. Query tracking.db: `SELECT output_file FROM submissions WHERE problem_id LIKE '%{id}%' AND output_file IS NOT NULL AND status IN ('compiled_clean','near_miss','completed')`
    7. Filter to files that exist on disk, return list of Paths
    8. Wire into `safe_submit()`: after `check_gap_targeting()`, call `extract_problem_id()` then `gather_context()`, merge with explicit `context_files`
  - **Files**: `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py`
  - **Done when**: `extract_problem_id()` and `gather_context()` exist and are called from `safe_submit()`, context files merged with explicit context
  - **Verify**: `grep -c 'extract_problem_id\|gather_context' /Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py | awk '{print ($1 >= 4) ? "PASS" : "FAIL: missing context functions"}'`
  - **Commit**: `feat(gap-pivot): add auto-context attachment to submit pipeline`
  - _Requirements: FR-3, AC-3.2, AC-3.3, AC-3.4, AC-3.5_
  - _Design: Section 3 (Auto-Context Attachment)_

- [ ] 1.9 [VERIFY] Quality checkpoint: `bats /Users/patrickkavanagh/math/math-forge/tests/`
  - **Do**: Run all BATS tests to verify pipeline changes haven't broken anything
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -5`
  - **Done when**: All 32 tests pass
  - **Commit**: `chore(gap-pivot): pass quality checkpoint` (only if fixes needed)

### Batch 4: mk CLI Commands + Schema

- [ ] 1.10 Add `mk context` command
  - **Do**:
    1. Read `/Users/patrickkavanagh/math/math-forge/scripts/mk` (411 lines)
    2. Add `context)` case block per design section 4
    3. Takes `<problem_id>` argument, queries tracking.db for result files matching problem_id
    4. Lists found files with status, line count, and MISSING label for deleted files
    5. Outputs `--context` flag format for easy copy-paste into submit command
    6. Uses existing patterns: `check_db`, `run_sql`, `escape_sql`, `normalize_problem`
    7. Handle: no args -> usage, no results -> "first submission", missing tracking.db -> error
    8. Update help text to include `context` command
  - **Files**: `/Users/patrickkavanagh/math/math-forge/scripts/mk`
  - **Done when**: `mk context erdos_11` produces output, `mk context` shows usage, `mk help` lists context
  - **Verify**: `grep -c 'context)' /Users/patrickkavanagh/math/math-forge/scripts/mk | awk '{print ($1 > 0) ? "PASS" : "FAIL: context command missing"}'` && `grep 'context' /Users/patrickkavanagh/math/math-forge/scripts/mk | grep -c 'help\|Usage\|context.*problem' | awk '{print ($1 > 0) ? "PASS" : "FAIL: no help text"}'`
  - **Commit**: `feat(gap-pivot): add mk context command for prior result lookup`
  - _Requirements: FR-4, AC-3.1_
  - _Design: Section 4 (mk context Command)_

- [ ] 1.11 Add `mk gaps` command
  - **Do**:
    1. Add `gaps)` case block per design section 5
    2. Queries tracking.db for gap-targeting submissions grouped by problem
    3. Shows: problem, gap_statement, submission count, best status, resolved flag
    4. Shows total resolved count at bottom
    5. Handles NULL gap_statement with COALESCE fallback
    6. Handles missing tracking.db gracefully
    7. Update help text to include `gaps` command
  - **Files**: `/Users/patrickkavanagh/math/math-forge/scripts/mk`
  - **Done when**: `mk gaps` produces formatted output, `mk help` lists gaps
  - **Verify**: `grep -c 'gaps)' /Users/patrickkavanagh/math/math-forge/scripts/mk | awk '{print ($1 > 0) ? "PASS" : "FAIL: gaps command missing"}'`
  - **Commit**: `feat(gap-pivot): add mk gaps command for open gap tracking`
  - _Requirements: FR-5, AC-5.5_
  - _Design: Section 5 (mk gaps Command)_

- [ ] 1.12 Run tracking.db schema migration
  - **Do**:
    1. Run ALTER TABLE on `/Users/patrickkavanagh/math/submissions/tracking.db`
    2. Add `gap_statement TEXT` column to submissions
    3. Add `submission_type TEXT` column to submissions
    4. Verify columns exist after migration
    5. No CHECK constraint (SQLite ALTER TABLE limitation -- validation in Python)
    6. Existing rows get NULL for both columns (backward compatible)
  - **Files**: `/Users/patrickkavanagh/math/submissions/tracking.db`
  - **Done when**: Both columns exist in submissions table
  - **Verify**: `sqlite3 /Users/patrickkavanagh/math/submissions/tracking.db ".schema submissions" | grep -c 'gap_statement\|submission_type' | awk '{print ($1 >= 2) ? "PASS" : "FAIL: columns missing"}'`
  - **Commit**: `feat(gap-pivot): add gap_statement and submission_type to tracking.db`
  - _Requirements: FR-12, AC-5.1, AC-5.2_
  - _Design: Section 8 (tracking.db Schema Migration)_

- [ ] 1.13 Add knowledge.db schema columns
  - **Do**:
    1. Run ALTER TABLE on knowledge.db (if exists): add `targets_open_gap INTEGER DEFAULT 0` and `gap_id TEXT` to findings
    2. Update `/Users/patrickkavanagh/math/math-forge/data/schema.sql` to include new columns in CREATE TABLE
    3. Defer CHECK constraint expansion for finding_type (table recreation not needed now)
    4. Add columns after `notes TEXT` in schema.sql findings table definition
  - **Files**: `/Users/patrickkavanagh/math/math-forge/data/schema.sql`
  - **Done when**: schema.sql includes `targets_open_gap` and `gap_id` columns, `mk init` creates DB with new columns
  - **Verify**: `grep -c 'targets_open_gap\|gap_id' /Users/patrickkavanagh/math/math-forge/data/schema.sql | awk '{print ($1 >= 2) ? "PASS" : "FAIL: columns missing from schema"}'`
  - **Commit**: `feat(gap-pivot): add gap-targeting columns to knowledge.db schema`
  - _Requirements: FR-13, AC-5.3_
  - _Design: Section 9 (knowledge.db Schema Changes)_

- [ ] 1.14 [VERIFY] Quality checkpoint: `bats /Users/patrickkavanagh/math/math-forge/tests/`
  - **Do**: Run all BATS tests, verify mk help shows new commands
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -5`
  - **Done when**: All 32 tests pass (including help tests that should now show context/gaps)
  - **Commit**: `chore(gap-pivot): pass quality checkpoint` (only if fixes needed)

### Batch 5: Remaining Skills

- [ ] 1.15 Rewrite screen.md and screen-batch.md to binary OPEN/SKIP
  - **Do**:
    1. Rewrite `/Users/patrickkavanagh/math/.claude/commands/screen.md` (103 lines) to ~30 lines
    2. Binary decision: OPEN -> submit, NOT OPEN -> SKIP. No scoring, no track assignment
    3. Rewrite `/Users/patrickkavanagh/math/.claude/commands/screen-batch.md` (81 lines) to ~30 lines
    4. Binary: OPEN vs SKIP. No tier system, no AMS tags, no finite structure signals
  - **Files**: `/Users/patrickkavanagh/math/.claude/commands/screen.md`, `/Users/patrickkavanagh/math/.claude/commands/screen-batch.md`
  - **Done when**: Both files are <=40 lines, no Tier/Track references
  - **Verify**: `grep -ciE '(Tier [A-D]|Track [A-D])' /Users/patrickkavanagh/math/.claude/commands/screen.md /Users/patrickkavanagh/math/.claude/commands/screen-batch.md | awk -F: '{sum+=$2} END{print (sum == 0) ? "PASS" : "FAIL: old tiers present"}'`
  - **Commit**: `feat(gap-pivot): simplify screen skills to binary OPEN/SKIP`
  - _Requirements: AC-6.4, AC-6.5_
  - _Design: Section 11 (Skill Rewrites Summary)_

- [ ] 1.16 Update fetch.md, process-result.md, audit.md with gap-resolution assessment
  - **Do**:
    1. Modify `/Users/patrickkavanagh/math/.claude/commands/fetch.md` (81 lines): add target_resolved prompt after audit step
    2. Modify `/Users/patrickkavanagh/math/.claude/commands/process-result.md` (115 lines): add target_resolved assessment step
    3. Modify `/Users/patrickkavanagh/math/.claude/commands/audit.md` (125 lines): replace FIRST-EVER/EXTENSION/RE-PROOF novelty with gap-resolution assessment ("Did this resolve the open gap?")
  - **Files**: `/Users/patrickkavanagh/math/.claude/commands/fetch.md`, `/Users/patrickkavanagh/math/.claude/commands/process-result.md`, `/Users/patrickkavanagh/math/.claude/commands/audit.md`
  - **Done when**: All 3 files reference target_resolved or gap-resolution assessment
  - **Verify**: `grep -cl 'target_resolved\|gap.resolution\|resolve.*gap' /Users/patrickkavanagh/math/.claude/commands/fetch.md /Users/patrickkavanagh/math/.claude/commands/process-result.md /Users/patrickkavanagh/math/.claude/commands/audit.md | wc -l | awk '{print ($1 == 3) ? "PASS" : "FAIL: not all files updated"}'`
  - **Commit**: `feat(gap-pivot): add gap-resolution assessment to fetch/process-result/audit`
  - _Requirements: AC-6.7, AC-6.8, FR-14_
  - _Design: Section 11, Section 13_

- [ ] 1.17 Simplify optimize.md and update debate.md
  - **Do**:
    1. Rewrite `/Users/patrickkavanagh/math/.claude/commands/optimize.md` (108 lines) to ~30 lines: single recommendation "State the gap bare, submit INFORMAL"
    2. Modify `/Users/patrickkavanagh/math/.claude/commands/debate.md` (97 lines): focus debates on "identify the exact open gap" not "develop proof strategy"
  - **Files**: `/Users/patrickkavanagh/math/.claude/commands/optimize.md`, `/Users/patrickkavanagh/math/.claude/commands/debate.md`
  - **Done when**: optimize.md recommends only bare gap + INFORMAL, debate.md focuses on gap identification
  - **Verify**: `grep -ci 'bare.*gap\|gap.*bare\|INFORMAL' /Users/patrickkavanagh/math/.claude/commands/optimize.md | awk '{print ($1 > 0) ? "PASS" : "FAIL: no bare gap recommendation"}'`
  - **Commit**: `feat(gap-pivot): simplify optimize and debate skills for gap-targeting`
  - _Requirements: AC-6.6, AC-6.9_
  - _Design: Section 11_

- [ ] 1.18 Rewrite math-forge skills (open-problems, number-theory, proof-strategies)
  - **Do**:
    1. Rewrite `/Users/patrickkavanagh/math/math-forge/skills/open-problems.md` (47 lines): query KB for prior results only, no strategy proposals
    2. Modify `/Users/patrickkavanagh/math/math-forge/skills/number-theory.md` (45 lines): keep KB queries, remove "proven techniques" focus
    3. Rename `/Users/patrickkavanagh/math/math-forge/skills/proof-strategies.md` to `prior-results.md`: surfaces what Aristotle tried, not what WE should try
  - **Files**: `/Users/patrickkavanagh/math/math-forge/skills/open-problems.md`, `/Users/patrickkavanagh/math/math-forge/skills/number-theory.md`, `/Users/patrickkavanagh/math/math-forge/skills/proof-strategies.md` (-> `prior-results.md`)
  - **Done when**: No "propose NEW approach" in open-problems.md, no "proven techniques" focus in number-theory.md, proof-strategies.md renamed to prior-results.md
  - **Verify**: `grep -ciE '(propose.*approach|proven techniques|strategy comparison)' /Users/patrickkavanagh/math/math-forge/skills/open-problems.md /Users/patrickkavanagh/math/math-forge/skills/number-theory.md | awk -F: '{sum+=$2} END{print (sum == 0) ? "PASS" : "FAIL: old strategy focus remains"}'` && `test -f /Users/patrickkavanagh/math/math-forge/skills/prior-results.md && echo "PASS" || echo "FAIL: prior-results.md not created"`
  - **Commit**: `feat(gap-pivot): rewrite math-forge skills for gap-targeting`
  - _Requirements: FR-9, AC-6.11, AC-6.12_
  - _Design: Section 12 (Math-Forge Skill Changes)_

- [ ] 1.19 [VERIFY] Quality checkpoint: `bats /Users/patrickkavanagh/math/math-forge/tests/`
  - **Do**: Run all BATS tests after skill rewrites
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -5`
  - **Done when**: All 32 tests pass
  - **Commit**: `chore(gap-pivot): pass quality checkpoint` (only if fixes needed)

### Batch 6: Hooks

- [ ] 1.20 Add gap-targeting reminder to context-loader.sh
  - **Do**:
    1. Read `/Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh` (118 lines)
    2. Add gap-targeting reminder text to BRIEFING variable after initialization, before action items
    3. Text: "GAP-TARGETING: Bare conjecture only. No proof guidance. Let Aristotle find the path."
    4. Ensure existing BATS tests still pass (they check for `[math-forge]` header, valid JSON, `hookSpecificOutput`, `additionalContext`)
  - **Files**: `/Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh`
  - **Done when**: Session briefing includes gap-targeting reminder text
  - **Verify**: `bash /Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); assert 'GAP-TARGETING' in d['hookSpecificOutput']['additionalContext']; print('PASS')" 2>&1 || echo "FAIL"`
  - **Commit**: `feat(gap-pivot): add gap-targeting reminder to session briefing`
  - _Requirements: FR-10, AC-4.4_
  - _Design: Section 10 (Hook Updates -- context-loader.sh)_

- [ ] 1.21 Add sketch validation to lean-validator.sh
  - **Do**:
    1. Read `/Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh` (87 lines)
    2. BEFORE the `.lean` extension check (line 22), add `.txt` sketch validation block per design section 10
    3. Check if file is `.txt` AND filename contains `sketch` or `slot`
    4. If so: grep for strategy keywords (Proof Strategy, Key Lemma, APPROACH, Main Proof, Proposed Strategy)
    5. Count non-blank lines, warn if >30
    6. Output JSON warning via `hookSpecificOutput.additionalContext` (advisory, not block)
    7. Exit 0 after .txt processing (don't fall through to .lean checks)
    8. Ensure existing BATS tests pass (.lean file tests unaffected)
  - **Files**: `/Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh`
  - **Done when**: .txt sketch files with strategy keywords trigger a warning, .lean file behavior unchanged
  - **Verify**: `echo '## Proof Strategy' > /tmp/test_sketch.txt && echo '{"tool_input":{"file_path":"/tmp/test_sketch.txt"},"tool_name":"Write"}' | bash /Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh 2>/dev/null | grep -c 'WARNING' | awk '{print ($1 > 0) ? "PASS" : "FAIL: no warning for strategy keyword"}'` && `rm -f /tmp/test_sketch.txt`
  - **Commit**: `feat(gap-pivot): add sketch validation to lean-validator hook`
  - _Requirements: FR-11, AC-4.5_
  - _Design: Section 10 (Hook Updates -- lean-validator.sh)_

- [ ] 1.22 Update aristotle_fetch.py with target_resolved prompt
  - **Do**:
    1. Read `/Users/patrickkavanagh/math/scripts/aristotle_fetch.py` (483 lines)
    2. In `cmd_fetch()`, after audit section, add target_resolved prompt
    3. If audit verdict is `compiled_clean`: print prompt asking "Did this resolve the OPEN GAP?"
    4. Provide sqlite3 command for manual target_resolved=1 update
    5. No automatic classification (requires human judgment per design)
  - **Files**: `/Users/patrickkavanagh/math/scripts/aristotle_fetch.py`
  - **Done when**: Fetch output includes target_resolved prompt for compiled_clean results
  - **Verify**: `grep -c 'target_resolved\|OPEN GAP' /Users/patrickkavanagh/math/scripts/aristotle_fetch.py | awk '{print ($1 >= 2) ? "PASS" : "FAIL: target_resolved prompt missing"}'`
  - **Commit**: `feat(gap-pivot): add target_resolved prompt to aristotle_fetch.py`
  - _Requirements: FR-14, AC-5.4_
  - _Design: Section 13 (aristotle_fetch.py Changes)_

- [ ] 1.23 Update extract_findings.py with gap columns
  - **Do**:
    1. Read `/Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py` (384 lines)
    2. Add `targets_open_gap` and `gap_id` to finding INSERT statements
    3. Default `targets_open_gap = 0`, `gap_id = None`
    4. Pass through from submission record if available
    5. Minimal change: just add columns with defaults
  - **Files**: `/Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py`
  - **Done when**: INSERT statements include targets_open_gap and gap_id
  - **Verify**: `grep -c 'targets_open_gap\|gap_id' /Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py | awk '{print ($1 >= 2) ? "PASS" : "FAIL: gap columns missing"}'`
  - **Commit**: `feat(gap-pivot): add gap-targeting columns to extract_findings.py`
  - _Requirements: FR-13_
  - _Design: Section 14 (extract_findings.py Changes)_

- [ ] 1.24 POC Checkpoint
  - **Do**: Verify the full gap-targeting pipeline works end-to-end:
    1. Create a test bare-gap sketch (<30 lines, no strategy) in /tmp
    2. Verify `check_gap_targeting()` would pass it (grep for function, verify logic)
    3. Create a test strategy-heavy sketch (>30 lines, has "Proof Strategy") in /tmp
    4. Verify lean-validator hook warns on the strategy sketch
    5. Verify `mk context` and `mk gaps` produce output (may be empty, but no errors)
    6. Verify session briefing includes GAP-TARGETING reminder
    7. Verify all 32 BATS tests still pass
  - **Done when**: Bare sketch passes gate, strategy sketch triggers warnings, mk commands work, BATS pass
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -1 | grep -c 'ok' | awk '{print ($1 > 0) ? "PASS" : "FAIL"}'` && `bash /Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); assert 'GAP-TARGETING' in d['hookSpecificOutput']['additionalContext']; print('PASS: briefing has reminder')"` && `grep -c 'check_gap_targeting' /Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py | awk '{print ($1 > 0) ? "PASS: gate exists" : "FAIL"}'`
  - **Commit**: `feat(gap-pivot): complete POC`

## Phase 2: Refactoring

After POC validated, clean up code.

- [ ] 2.1 Extract gap-targeting constants to shared config
  - **Do**:
    1. Review strategy keyword patterns duplicated between safe_aristotle_submit.py and lean-validator.sh
    2. If patterns are only in 2 places and small, this is acceptable duplication -- skip extraction
    3. If extraction warranted: create a shared constants file or ensure patterns are consistent
    4. Ensure STRATEGY_PATTERNS list in safe_aristotle_submit.py matches keywords in lean-validator.sh
  - **Files**: `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py`, `/Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh`
  - **Done when**: Strategy patterns are consistent across both files
  - **Verify**: `grep -iE 'Proof.Strategy|Key.Lemma|APPROACH' /Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py /Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh | wc -l | awk '{print ($1 >= 2) ? "PASS: patterns present in both" : "FAIL"}'`
  - **Commit**: `refactor(gap-pivot): align strategy patterns across gate and hook`
  - _Design: Section 1, Section 10_

- [ ] 2.2 Add error handling for gather_context() edge cases
  - **Do**:
    1. Ensure gather_context() handles: missing tracking.db, no problem_id column, empty results, sqlite3 errors
    2. Add try/except around DB query in gather_context()
    3. Log warning if DB unavailable but don't block submission
    4. Handle pre-migration state (gap_statement/submission_type columns might not exist yet)
  - **Files**: `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py`
  - **Done when**: gather_context() gracefully handles all error paths
  - **Verify**: `grep -A5 'def gather_context' /Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py | grep -c 'try\|except\|None' | awk '{print ($1 > 0) ? "PASS" : "FAIL: no error handling"}'`
  - **Commit**: `refactor(gap-pivot): add error handling to gather_context()`
  - _Design: Error Handling table_

- [ ] 2.3 [VERIFY] Quality checkpoint: `bats /Users/patrickkavanagh/math/math-forge/tests/`
  - **Do**: Run all BATS tests after refactoring
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -5`
  - **Done when**: All 32 tests pass
  - **Commit**: `chore(gap-pivot): pass quality checkpoint` (only if fixes needed)

## Phase 3: Testing

- [ ] 3.1 Create BATS tests for mk context command
  - **Do**:
    1. Create `/Users/patrickkavanagh/math/math-forge/tests/test_mk_context.bats`
    2. Use existing patterns: `load test_helper`, temp DB, `assert_output_contains`
    3. Tests: no args shows usage, lists result files for known problem (need tracking.db fixture), handles no prior results gracefully, shows MISSING for deleted files
    4. Create tracking.db test fixture with sample submissions data including output_file paths
  - **Files**: `/Users/patrickkavanagh/math/math-forge/tests/test_mk_context.bats`
  - **Done when**: Test file exists with >=3 tests, all pass
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/test_mk_context.bats 2>&1 | tail -3`
  - **Commit**: `test(gap-pivot): add BATS tests for mk context command`
  - _Requirements: FR-15_
  - _Design: Test Strategy_

- [ ] 3.2 Create BATS tests for mk gaps command
  - **Do**:
    1. Create `/Users/patrickkavanagh/math/math-forge/tests/test_mk_gaps.bats`
    2. Tests: shows header, lists problems with submissions (need tracking.db fixture with gap_statement/submission_type), shows resolved count
    3. Use tracking.db test fixture created in 3.1
  - **Files**: `/Users/patrickkavanagh/math/math-forge/tests/test_mk_gaps.bats`
  - **Done when**: Test file exists with >=2 tests, all pass
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/test_mk_gaps.bats 2>&1 | tail -3`
  - **Commit**: `test(gap-pivot): add BATS tests for mk gaps command`
  - _Requirements: FR-15_
  - _Design: Test Strategy_

- [ ] 3.3 Create BATS tests for lean-validator sketch validation
  - **Do**:
    1. Create `/Users/patrickkavanagh/math/math-forge/tests/test_gap_targeting.bats`
    2. Tests: warns on strategy keywords in .txt sketch, passes clean bare-gap sketch, warns on >30 line sketch
    3. Use temp files for test sketches
  - **Files**: `/Users/patrickkavanagh/math/math-forge/tests/test_gap_targeting.bats`
  - **Done when**: Test file exists with >=3 tests, all pass
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/test_gap_targeting.bats 2>&1 | tail -3`
  - **Commit**: `test(gap-pivot): add BATS tests for sketch validation`
  - _Requirements: FR-15_
  - _Design: Test Strategy_

- [ ] 3.4 Update existing BATS tests for new mk help output
  - **Do**:
    1. Read `/Users/patrickkavanagh/math/math-forge/tests/test_mk_utils.bats`
    2. Verify the `help: shows usage` test passes with new `context` and `gaps` commands in help output
    3. Add assertions for `context` and `gaps` in help output if not already covered
  - **Files**: `/Users/patrickkavanagh/math/math-forge/tests/test_mk_utils.bats`
  - **Done when**: Help test asserts `context` and `gaps` are in help output
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/test_mk_utils.bats 2>&1 | tail -3`
  - **Commit**: `test(gap-pivot): update help tests for new mk commands`
  - _Requirements: FR-15_
  - _Design: Test Strategy_

- [ ] 3.5 [VERIFY] Quality checkpoint: `bats /Users/patrickkavanagh/math/math-forge/tests/`
  - **Do**: Run full BATS suite (32 original + new tests)
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -5`
  - **Done when**: All tests pass (should be 32 + ~8 new = ~40 tests)
  - **Commit**: `chore(gap-pivot): pass quality checkpoint` (only if fixes needed)

## Phase 4: Quality Gates

- [ ] 4.1 [VERIFY] Full local CI: `bats /Users/patrickkavanagh/math/math-forge/tests/`
  - **Do**:
    1. Run complete BATS test suite
    2. Verify all original 32 tests still pass (zero regressions)
    3. Verify new gap-targeting tests pass
    4. Verify CLAUDE.md line count <=120
    5. Verify MEMORY.md line count <=60
    6. Verify no Track B/C/D references in any command skill
    7. Verify check_gap_targeting() exists in safe_aristotle_submit.py
    8. Verify mk context and mk gaps commands exist in mk CLI
    9. Verify schema columns exist in tracking.db and schema.sql
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -5` && `wc -l /Users/patrickkavanagh/math/CLAUDE.md | awk '{print ($1 <= 120) ? "PASS" : "FAIL"}'` && `grep -rciE 'Track [BCD]' /Users/patrickkavanagh/math/.claude/commands/ | awk -F: '{sum+=$2} END{print (sum == 0) ? "PASS: no old tracks" : "FAIL: "$sum" old track refs"}'`
  - **Done when**: All checks pass, zero regressions
  - **Commit**: `chore(gap-pivot): pass local CI` (if fixes needed)

- [ ] 4.2 Create PR and verify CI
  - **Do**:
    1. Verify current branch is a feature branch: `git branch --show-current`
    2. If on default branch, STOP and alert user
    3. Stage all modified files (CLAUDE.md, MEMORY.md, commands/*.md, math-forge/skills/*.md, math-forge/hooks/scripts/*.sh, math-forge/scripts/mk, math-forge/data/schema.sql, scripts/safe_aristotle_submit.py, scripts/aristotle_fetch.py, math-forge/scripts/extract_findings.py, math-forge/tests/*.bats, submissions/tracking.db)
    4. Push branch: `git push -u origin <branch-name>`
    5. Create PR: `gh pr create --title "feat: gap-targeting pivot" --body "..."`
  - **Verify**: `gh pr checks --watch` or `gh pr checks`
  - **Done when**: PR created, CI checks pass (if CI exists; otherwise PR created successfully)
  - **If CI fails**: Read failure details, fix locally, push fixes, re-verify

## Phase 5: PR Lifecycle

- [ ] 5.1 Monitor CI and fix failures
  - **Do**:
    1. Check PR status: `gh pr checks`
    2. If any check fails: read failure details, fix locally, push
    3. If no CI configured (this project has no CI): verify locally with `bats math-forge/tests/`
  - **Verify**: `gh pr checks` or `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -1`
  - **Done when**: All checks green or local BATS pass
  - **Commit**: `fix(gap-pivot): address CI failures` (if needed)

- [ ] 5.2 Address review comments
  - **Do**:
    1. Check for review comments: `gh pr view --json reviews`
    2. Address each comment with code changes
    3. Push fixes
  - **Verify**: `gh pr view --json reviews | python3 -c "import json,sys; d=json.load(sys.stdin); print('PASS' if not d.get('reviews') else f'{len(d[\"reviews\"])} reviews pending')"`
  - **Done when**: All review comments addressed
  - **Commit**: `fix(gap-pivot): address review comments` (if needed)

- [ ] 5.3 [VERIFY] AC checklist
  - **Do**: Verify each acceptance criterion is met:
    1. AC-1.1: Sketch template <=30 lines, bare gap format -> grep sketch.md
    2. AC-1.2: No strategy sections in template -> grep sketch.md
    3. AC-2.1: safe_aristotle_submit.py rejects >30 line .txt -> grep check_gap_targeting
    4. AC-2.2: Rejects strategy keywords -> grep STRATEGY_PATTERNS
    5. AC-2.3: Rejects .lean files -> grep check C1
    6. AC-2.4: No override flag -> grep for --force-gap or --skip-gap (should be 0)
    7. AC-3.1: mk context command exists -> grep mk script
    8. AC-4.1: CLAUDE.md rewritten -> line count check
    9. AC-4.2: MEMORY.md simplified -> line count check
    10. AC-4.4: Session briefing has gap-targeting -> test hook
    11. AC-5.1: gap_statement column exists -> sqlite3 .schema
    12. AC-5.5: mk gaps command exists -> grep mk script
    13. AC-6.1-6.12: All skills rewritten -> grep each for old patterns
  - **Verify**: `bats /Users/patrickkavanagh/math/math-forge/tests/ 2>&1 | tail -1` && `wc -l /Users/patrickkavanagh/math/CLAUDE.md` && `grep -c 'check_gap_targeting' /Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` && `grep -c 'context)\|gaps)' /Users/patrickkavanagh/math/math-forge/scripts/mk`
  - **Done when**: All acceptance criteria confirmed met
  - **Commit**: None

## Notes

- **POC shortcuts taken**:
  - Strategy pattern regex list may need tuning during real-world use (8 patterns cover known sketch structures, but new patterns may emerge)
  - `target_resolved` is manual-only in POC (no automation)
  - knowledge.db CHECK constraint expansion for `gap_progress` finding_type deferred
  - Auto-context matching uses LIKE '%problem_id%' which may be imprecise (erdos11 matches erdos110)

- **Production TODOs**:
  - Tune strategy keyword patterns based on real submission attempts
  - Consider fuzzy matching for problem_id in gather_context()
  - knowledge.db table recreation migration for finding_type CHECK constraint
  - Automated target_resolved classification (LLM-assisted) in future iteration

- **In-flight submission safety**: All changes apply only to FUTURE submissions. Existing slot646-650+ can be fetched/processed normally. The gate only runs at submit time.

- **Quality gate**: `bats math-forge/tests/` is the only automated test suite. No lint, typecheck, or build commands exist. All VERIFY steps use this plus grep-based code verification.
