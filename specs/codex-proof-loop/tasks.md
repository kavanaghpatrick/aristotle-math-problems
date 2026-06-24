# Tasks: Codex Proof Loop

## Quality Commands

- **Build**: `python3 -m py_compile scripts/codex_proof_loop.py`
- **Typecheck**: N/A (no mypy/pyright configured in project)
- **Lint**: N/A (no flake8/ruff configured in project)
- **Test**: `python3 -c "import scripts.codex_proof_loop" 2>/dev/null || python3 scripts/codex_proof_loop.py --help`

## Phase 1: Make It Work (POC)

Focus: Get a working compile-fix loop end-to-end. Codex writes Lean, lake builds it, errors feed back, best result saved. Skip tests, accept hardcoded values.

- [ ] 1.1 Create core script skeleton with CLI and dataclasses
  - **Do**:
    1. Create `scripts/codex_proof_loop.py` with shebang, docstring, imports (subprocess, tempfile, sqlite3, json, argparse, dataclasses, pathlib, signal, re, time, shutil, os, sys)
    2. Define `MATH_DIR = Path(__file__).resolve().parent.parent`
    3. Define dataclasses: `LoopConfig`, `IterationResult`, `LoopResult` (matching design.md interfaces)
    4. Implement `count_sorries(lean_code: str) -> int` -- regex `r'\bsorry\b'` excluding lines starting with `--` or inside `/-...-/` block comments
    5. Implement `extract_theorem_statement(lean_code: str) -> str | None` -- extract first `theorem` or `lemma` declaration line(s) up to `:=`
    6. Implement `check_statement_locked(original: str, revised: str) -> bool` -- normalize whitespace, compare
    7. Implement `select_best(iterations: list[IterationResult]) -> IterationResult` -- prefer compiled+fewer sorries, break ties by later iteration
    8. Add argparse CLI at bottom: positional `problem` (str or file path), `--context` (repeatable), `--max-iterations` (default 5), `--build-timeout` (default 300), `--reasoning-effort` (default high), `--keep-temp`, `--problem-id`
    9. Add `--help` that prints usage
  - **Files**: `scripts/codex_proof_loop.py`
  - **Done when**: `python3 scripts/codex_proof_loop.py --help` prints usage and exits 0
  - **Verify**: `python3 scripts/codex_proof_loop.py --help`
  - **Commit**: `feat(codex): scaffold proof loop script with CLI and dataclasses`
  - _Requirements: FR-1, FR-4, FR-11, FR-12, FR-13_
  - _Design: Core Script, Interfaces_

- [ ] 1.2 Implement temp Lean project factory
  - **Do**:
    1. Implement `create_temp_project() -> Path` in `codex_proof_loop.py`
    2. Create temp dir via `tempfile.mkdtemp(prefix="codex_proof_")`
    3. Symlink `lean-toolchain` -> `MATH_DIR / "lean-toolchain"`
    4. Copy `lake-manifest.json` from `MATH_DIR / "lake-manifest.json"` (not symlink -- lake writes to it)
    5. Create `.lake/` dir, symlink `.lake/packages/` -> `MATH_DIR / ".lake" / "packages"`
    6. Generate `lakefile.toml` with content from design.md (name="codex-proof", mathlib rev from main lakefile, lean_lib name="CodexProof")
    7. Create `CodexProof/` subdirectory for generated .lean files
    8. Add startup check: if `MATH_DIR / ".lake" / "packages"` doesn't exist, abort with message "Run `lake build` in main project first"
    9. Implement `cleanup_temp(temp_dir: Path, keep: bool)` -- shutil.rmtree unless keep=True
  - **Files**: `scripts/codex_proof_loop.py`
  - **Done when**: Running the function creates a valid temp project with correct symlinks
  - **Verify**: `python3 -c "import sys; sys.path.insert(0,'.'); exec(open('scripts/codex_proof_loop.py').read().split('if __name__')[0]); p = create_temp_project(); print(p); import os; assert os.path.islink(str(p/'lean-toolchain')); assert os.path.islink(str(p/'.lake'/'packages')); assert (p/'lakefile.toml').exists(); assert (p/'CodexProof').is_dir(); import shutil; shutil.rmtree(str(p)); print('OK')"`
  - **Commit**: `feat(codex): implement isolated temp Lean project factory`
  - _Requirements: AC-2.1, AC-2.2, AC-2.3, AC-2.4, AC-2.5_
  - _Design: Temp Lean Project Factory_

- [ ] 1.3 Implement Codex invocation and Lean code extraction
  - **Do**:
    1. Implement `invoke_codex(prompt: str, reasoning_effort: str = "high") -> str` in `codex_proof_loop.py`
    2. Write prompt to temp file, run `codex exec --full-auto` via `subprocess.run(["bash", "-c", ...])` with timeout=180s
    3. Capture stdout, strip markdown fences (```lean ... ```) if present
    4. Handle errors: FileNotFoundError (codex not installed), TimeoutExpired, empty output
    5. Implement `build_initial_prompt(problem: str, context_files: list[Path]) -> str` -- format with problem description, optional context file contents, rules (import Mathlib, minimize sorry, don't change statement)
    6. Implement `build_revision_prompt(problem: str, prior_code: str, errors: str, locked_statement: str | None, sorry_count: int, iteration: int) -> str` -- include prior code, compiler errors, locked statement, sorry count
  - **Files**: `scripts/codex_proof_loop.py`
  - **Done when**: `invoke_codex()` calls codex exec and returns extracted Lean code
  - **Verify**: `python3 -c "exec(open('scripts/codex_proof_loop.py').read().split('if __name__')[0]); r = invoke_codex('Write a Lean 4 file that proves 1+1=2. Output only valid Lean 4 code.'); print(r[:200]); assert len(r) > 10, 'Codex returned too little'"`
  - **Commit**: `feat(codex): implement Codex invocation with prompt templates`
  - _Requirements: FR-1, FR-3, FR-11_
  - _Design: Codex Invocation, Prompt Templates_

- [ ] 1.4 Implement lake build runner
  - **Do**:
    1. Implement `run_lake_build(project_dir: Path, timeout: int = 300) -> tuple[bool, str]` in `codex_proof_loop.py`
    2. Run `subprocess.run(["lake", "build"], cwd=project_dir, capture_output=True, text=True, timeout=timeout)`
    3. Return `(returncode == 0, stderr)`
    4. Handle TimeoutExpired -- kill process, return (False, "Build timed out")
    5. Write Lean code to `project_dir / "CodexProof" / "Attempt.lean"` before building
  - **Files**: `scripts/codex_proof_loop.py`
  - **Done when**: Function can build a trivial .lean file in a temp project
  - **Verify**: `python3 -c "exec(open('scripts/codex_proof_loop.py').read().split('if __name__')[0]); p = create_temp_project(); (p / 'CodexProof' / 'Attempt.lean').write_text('import Mathlib\n\ntheorem one_plus_one : 1 + 1 = 2 := by norm_num\n'); ok, err = run_lake_build(p); print(f'success={ok}'); import shutil; shutil.rmtree(str(p)); assert ok or 'error' in err.lower(), f'Unexpected: {err[:200]}'"`
  - **Commit**: `feat(codex): implement lake build runner with timeout handling`
  - _Requirements: AC-1.3, AC-1.4, FR-13_
  - _Design: Core Script, run_lake_build_

- [ ] 1.5 [VERIFY] Quality checkpoint
  - **Do**: Verify script imports correctly and --help works
  - **Verify**: `python3 scripts/codex_proof_loop.py --help && python3 -m py_compile scripts/codex_proof_loop.py`
  - **Done when**: No syntax errors, help prints cleanly
  - **Commit**: `chore(codex): pass quality checkpoint` (only if fixes needed)

- [ ] 1.6 Implement main loop orchestration and result saving
  - **Do**:
    1. Implement `run_loop(config: LoopConfig) -> LoopResult` as the main entry point
    2. Loop up to `config.max_iterations`:
       a. Build prompt (initial or revision)
       b. Call `invoke_codex()`, extract Lean code
       c. Skip iteration if empty/garbage output
       d. Check theorem statement locked (after iteration 1)
       e. Count sorries -- reject if sorry count increased vs prior best
       f. Write .lean to temp project, run `run_lake_build()`
       g. Create `IterationResult`, append to list
       h. Log progress: iteration #, build success, sorry count, wall time
       i. Short-circuit if compiled + 0 sorries
    3. Call `select_best()` to pick best iteration
    4. Implement `save_result(result: LoopResult, config: LoopConfig) -> Path`:
       a. Create `codex_proofs/<problem_id>/attempt_NNN/` (auto-increment)
       b. Save `proof.lean`, `metadata.json`, `build.log`
       c. Symlink `best.lean` -> best attempt's `proof.lean`
       d. Create `codex_proofs/` dir if not exists
    5. Add SIGINT handler: save current best on Ctrl-C, cleanup temp dir
    6. Wire CLI `__main__` block to call `run_loop()` and `save_result()`
    7. Print final summary: compiled/partial/failed, sorry count, file path, wall time
  - **Files**: `scripts/codex_proof_loop.py`
  - **Done when**: `python3 scripts/codex_proof_loop.py "Prove 1+1=2" --max-iterations 2` runs end-to-end, saves result to `codex_proofs/`
  - **Verify**: `python3 scripts/codex_proof_loop.py "Prove that 1 + 1 = 2 in Lean 4. The theorem should be: theorem one_plus_one : 1 + 1 = 2 := by sorry" --max-iterations 2 --problem-id test_1_plus_1 && test -d codex_proofs/test_1_plus_1 && test -f codex_proofs/test_1_plus_1/best.lean && echo "POC loop works"`
  - **Commit**: `feat(codex): implement full proof loop with result saving`
  - _Requirements: AC-1.1 through AC-1.7, AC-3.1 through AC-3.5, FR-1, FR-4, FR-5, FR-11_
  - _Design: Core Script, Result Storage_

- [ ] 1.7 Add DB migration and recording
  - **Do**:
    1. Implement `ensure_db_table()` in `codex_proof_loop.py` -- `CREATE TABLE IF NOT EXISTS codex_proofs` with schema from design.md
    2. Create indexes: `idx_codex_proofs_problem`, `idx_codex_proofs_compiled`, `idx_codex_proofs_parent`
    3. Implement `record_to_db(result: LoopResult, config: LoopConfig)` -- parameterized INSERT
    4. Call `ensure_db_table()` + `record_to_db()` from `save_result()`
    5. Use `MATH_DIR / "submissions" / "tracking.db"` as DB path
    6. Wrap DB operations in try/except -- log warning on failure, don't abort (files already saved)
  - **Files**: `scripts/codex_proof_loop.py`
  - **Done when**: After a proof loop run, `sqlite3 submissions/tracking.db "SELECT * FROM codex_proofs"` shows a row
  - **Verify**: `python3 scripts/codex_proof_loop.py "Prove 1+1=2 in Lean 4" --max-iterations 1 --problem-id db_test && sqlite3 submissions/tracking.db "SELECT problem_id, iterations, compiled FROM codex_proofs WHERE problem_id='db_test'" | grep -q "db_test" && echo "DB recording works"`
  - **Commit**: `feat(codex): add codex_proofs DB table and recording`
  - _Requirements: AC-5.1, AC-5.2, FR-6_
  - _Design: DB Schema_

- [ ] 1.8 [VERIFY] Quality checkpoint + POC validation
  - **Do**: Run the full loop, verify files + DB, clean up test artifacts
  - **Verify**: `python3 -m py_compile scripts/codex_proof_loop.py && python3 scripts/codex_proof_loop.py --help && test -f scripts/codex_proof_loop.py && echo "Phase 1 POC validated"`
  - **Done when**: Script compiles, help works, prior verify commands from 1.6 and 1.7 passed
  - **Commit**: `chore(codex): pass POC quality checkpoint` (only if fixes needed)

## Phase 2: Refactoring + Remaining Features

After POC validated, add remaining features: sorry extraction, context bridging, mk commands, skill, .gitignore.

- [ ] 2.1 Implement sorry extraction and sub-problem generation
  - **Do**:
    1. Implement `extract_sorry_targets(lean_code: str, problem_id: str, output_dir: Path) -> list[Path]` in `codex_proof_loop.py`
    2. Parse .lean line-by-line, track current theorem/lemma scope
    3. On `sorry` found (not in comment): extract enclosing theorem/lemma declaration + signature
    4. Generate standalone `.lean` sub-problem file: `import Mathlib` + extracted theorem + `sorry`
    5. Generate `.txt` informal sketch: `OPEN GAP: Sub-goal from <problem_id>` with theorem statement
    6. Save to `codex_proofs/<problem_id>/sorry_targets/sorry_N.lean` and `sorry_N.txt`
    7. Call from `save_result()` when sorry_count > 0
    8. Add `--sorry-target` mode to CLI: accepts a sub-problem .lean file from a prior run, re-runs the loop on it
    9. Add `parent_proof_id` tracking: when `--sorry-target` used, look up parent in DB
  - **Files**: `scripts/codex_proof_loop.py`
  - **Done when**: A proof loop with sorries generates sub-problem files in `sorry_targets/`
  - **Verify**: `python3 -c "exec(open('scripts/codex_proof_loop.py').read().split('if __name__')[0]); code='import Mathlib\n\ntheorem foo : 1 = 1 := by sorry\n\nlemma bar : 2 = 2 := by sorry\n'; from pathlib import Path; import tempfile, os; d=Path(tempfile.mkdtemp()); r = extract_sorry_targets(code, 'test', d); print(f'extracted {len(r)} targets'); assert len(r) == 2; import shutil; shutil.rmtree(str(d))"`
  - **Commit**: `feat(codex): implement sorry extraction and sub-problem generation`
  - _Requirements: AC-8.1, AC-8.2, AC-8.3, AC-8.4, AC-8.5, FR-9_
  - _Design: Sorry Extraction_

- [ ] 2.2 Add --codex-context flag to safe_aristotle_submit.py
  - **Do**:
    1. In CLI arg parsing section (~line 563), add handler for `--codex-context`:
       ```python
       elif arg == '--codex-context' and i + 1 < len(all_args):
           problem_id = all_args[i + 1]
           best_path = MATH_DIR / "codex_proofs" / problem_id / "best.lean"
           if best_path.exists():
               context_files.append(best_path.resolve())
               print(f"   Codex context: {best_path}")
           else:
               print(f"WARNING: No Codex best proof found for '{problem_id}'")
           i += 2
       ```
    2. Add to usage string: `--codex-context <problem_id>  Auto-locate best Codex proof as context`
    3. No changes to `safe_submit()`, `check_gap_targeting()`, or `gather_context()` -- purely additive
  - **Files**: `scripts/safe_aristotle_submit.py`
  - **Done when**: `python3 scripts/safe_aristotle_submit.py --help` shows `--codex-context` in usage
  - **Verify**: `python3 scripts/safe_aristotle_submit.py 2>&1 | grep -q "codex-context" && echo "Flag added"`
  - **Commit**: `feat(codex): add --codex-context flag to safe_aristotle_submit.py`
  - _Requirements: AC-4.1, AC-4.4, FR-8_
  - _Design: Context Bridging_

- [ ] 2.3 [VERIFY] Quality checkpoint
  - **Do**: Verify both scripts compile and parse correctly
  - **Verify**: `python3 -m py_compile scripts/codex_proof_loop.py && python3 -m py_compile scripts/safe_aristotle_submit.py && echo "Both scripts compile"`
  - **Done when**: No syntax errors in either script
  - **Commit**: `chore(codex): pass quality checkpoint` (only if fixes needed)

- [ ] 2.4 Add mk codex and mk codex-best commands
  - **Do**:
    1. In `math-forge/scripts/mk`, add two new case blocks before `help|*)`:
    2. `codex)` subcommand:
       ```bash
       codex)
           shift
           if [ ! -f "$TRACKING_DB" ]; then
               echo "[math-forge] ERROR: tracking.db not found" >&2; exit 1
           fi
           PROBLEM="${1:-}"
           if [ -z "$PROBLEM" ]; then
               echo "[math-forge] Codex proof history (all)"; echo "---"
               run_sql "$TRACKING_DB" -header -column "
                   SELECT problem_id, iterations, sorry_count, CASE compiled WHEN 1 THEN 'YES' ELSE 'no' END as compiled,
                          model, wall_time_seconds as secs, created_at
                   FROM codex_proofs ORDER BY created_at DESC LIMIT 20;"
           else
               ESCAPED=$(escape_sql "$PROBLEM")
               echo "[math-forge] Codex proofs for '${PROBLEM}'"; echo "---"
               run_sql "$TRACKING_DB" -header -column "
                   SELECT id, iterations, sorry_count, CASE compiled WHEN 1 THEN 'YES' ELSE 'no' END as compiled,
                          reasoning_effort, wall_time_seconds as secs, lean_file, created_at
                   FROM codex_proofs WHERE problem_id LIKE '%${ESCAPED}%'
                   ORDER BY created_at DESC;"
           fi
           ;;
       ```
    3. `codex-best)` subcommand:
       ```bash
       codex-best)
           shift
           if [ $# -eq 0 ]; then echo "Usage: mk codex-best <problem-id>"; exit 1; fi
           ESCAPED=$(escape_sql "$1")
           BEST=$(run_sql "$TRACKING_DB" "SELECT lean_file FROM codex_proofs WHERE problem_id LIKE '%${ESCAPED}%' AND compiled=1 ORDER BY sorry_count ASC, created_at DESC LIMIT 1;")
           if [ -n "$BEST" ]; then
               echo "$BEST"
           else
               echo "[math-forge] No compiled Codex proof for '${1}'" >&2; exit 1
           fi
           ;;
       ```
    4. Add to help text under "Pipeline commands:"
  - **Files**: `math-forge/scripts/mk`
  - **Done when**: `mk codex` and `mk codex-best` subcommands are recognized
  - **Verify**: `bash math-forge/scripts/mk codex 2>&1 | grep -qE "Codex|codex_proofs" && echo "mk codex works"`
  - **Commit**: `feat(codex): add mk codex and mk codex-best CLI commands`
  - _Requirements: AC-5.3, AC-5.4, FR-10_
  - _Design: mk CLI extension_

- [ ] 2.5 Create /codex-prove skill
  - **Do**:
    1. Create `.claude/commands/codex-prove.md` following existing skill patterns (audit.md, submit.md)
    2. YAML frontmatter: description, allowed-tools (Read, Grep, Glob, Bash, Write), argument-hint
    3. Steps:
       - Parse `$ARGUMENTS` for problem description and flags
       - Run `python3 scripts/codex_proof_loop.py $ARGUMENTS`
       - Report per-iteration progress: iteration #, build status, sorry count
       - On completion display verdict table: compiled/partial/failed, sorry count, file path
       - Suggest next action: `/audit <path>` if 0 sorry, `/submit <sketch> --codex-context <id>` if partial
  - **Files**: `.claude/commands/codex-prove.md`
  - **Done when**: Skill file exists with proper YAML frontmatter and instructions
  - **Verify**: `test -f .claude/commands/codex-prove.md && head -5 .claude/commands/codex-prove.md | grep -q "description:" && echo "Skill created"`
  - **Commit**: `feat(codex): create /codex-prove skill`
  - _Requirements: AC-6.1 through AC-6.5, FR-7_
  - _Design: /codex-prove Skill_

- [ ] 2.6 Update .gitignore and create codex_proofs directory
  - **Do**:
    1. Add `codex_proofs/` line to `.gitignore` (after the `iterations/` line, in the "Temporary files" section)
    2. Create `codex_proofs/.gitkeep` so the directory exists in git but contents are ignored
    3. Actually: since `codex_proofs/` is gitignored, just ensure the script creates it on first run (already done in 1.6). Add the .gitignore entry only.
  - **Files**: `.gitignore`
  - **Done when**: `codex_proofs/` appears in .gitignore
  - **Verify**: `grep -q "codex_proofs/" .gitignore && echo "gitignore updated"`
  - **Commit**: `chore(codex): add codex_proofs/ to .gitignore`
  - _Design: File Structure_

- [ ] 2.7 [VERIFY] Quality checkpoint: full feature set
  - **Do**: Verify all scripts compile, skill exists, mk commands work
  - **Verify**: `python3 -m py_compile scripts/codex_proof_loop.py && python3 -m py_compile scripts/safe_aristotle_submit.py && test -f .claude/commands/codex-prove.md && bash math-forge/scripts/mk help 2>&1 | grep -q "codex" && echo "All features present"`
  - **Done when**: All new files exist and are syntactically valid
  - **Commit**: `chore(codex): pass feature-complete quality checkpoint` (only if fixes needed)

## Phase 3: Testing

- [ ] 3.1 Unit tests for pure functions
  - **Do**:
    1. Create `scripts/test_codex_proof_loop.py`
    2. Test `count_sorries()`:
       - 0 sorries in clean code
       - 1 sorry in `theorem foo : T := by sorry`
       - Commented sorry (`-- sorry`) not counted
       - Block comment sorry (`/- sorry -/`) not counted
       - String sorry (`"sorry"`) -- implementation may count this, document behavior
       - Multiple sorries
    3. Test `extract_theorem_statement()`:
       - Single theorem
       - Multiple lemmas + theorem (returns first theorem)
       - No theorem (returns None)
    4. Test `check_statement_locked()`:
       - Exact match -> True
       - Whitespace differences -> True
       - Changed statement -> False
    5. Test `select_best()`:
       - All fail (no compile) -> picks fewest sorries
       - One compiles -> picks it
       - Multiple compile, different sorry counts -> picks fewest
       - Tie on sorries -> picks later iteration
  - **Files**: `scripts/test_codex_proof_loop.py`
  - **Done when**: All unit tests pass
  - **Verify**: `python3 scripts/test_codex_proof_loop.py`
  - **Commit**: `test(codex): add unit tests for pure functions`
  - _Requirements: AC-1.6, FR-4, FR-11_
  - _Design: Test Strategy_

- [ ] 3.2 Integration smoke test with real Codex + lake
  - **Do**:
    1. Run full proof loop on trivial problem: "Prove that 1 + 1 = 2 in Lean 4"
    2. Verify: result in `codex_proofs/`, DB row created, best.lean exists
    3. Verify: metadata.json has correct fields
    4. Verify: sorry count is 0 (trivial problem should compile clean)
    5. Clean up test artifacts after verification
  - **Files**: (no new files -- uses existing script)
  - **Done when**: End-to-end run produces correct output structure
  - **Verify**: `python3 scripts/codex_proof_loop.py "Prove that 1 + 1 = 2 in Lean 4. theorem one_eq : 1 + 1 = 2 := by sorry" --max-iterations 3 --problem-id smoke_test_e2e && test -f codex_proofs/smoke_test_e2e/best.lean && python3 -c "import json; m=json.load(open('codex_proofs/smoke_test_e2e/attempt_001/metadata.json')); assert 'problem_id' in m; assert 'iterations' in m; print('E2E smoke test passed')" && sqlite3 submissions/tracking.db "SELECT problem_id, compiled FROM codex_proofs WHERE problem_id='smoke_test_e2e'" | grep -q "smoke_test_e2e"`
  - **Commit**: `test(codex): validate end-to-end proof loop with real Codex + lake`
  - _Requirements: AC-1.1 through AC-1.7, AC-3.1 through AC-3.5_
  - _Design: Smoke Test_

- [ ] 3.3 [VERIFY] Quality checkpoint
  - **Do**: Run unit tests + verify script compiles
  - **Verify**: `python3 scripts/test_codex_proof_loop.py && python3 -m py_compile scripts/codex_proof_loop.py && echo "Tests pass"`
  - **Done when**: All tests pass, no syntax errors
  - **Commit**: `chore(codex): pass testing quality checkpoint` (only if fixes needed)

## Phase 4: Quality Gates

- [ ] 4.1 [VERIFY] Full local CI: compile + tests + script validation
  - **Do**: Run complete local validation suite
  - **Verify**: All commands must pass:
    - `python3 -m py_compile scripts/codex_proof_loop.py`
    - `python3 -m py_compile scripts/safe_aristotle_submit.py`
    - `python3 scripts/test_codex_proof_loop.py`
    - `python3 scripts/codex_proof_loop.py --help`
    - `bash math-forge/scripts/mk help | grep -q codex`
    - `test -f .claude/commands/codex-prove.md`
    - `grep -q codex_proofs .gitignore`
  - **Done when**: All validation commands exit 0
  - **Commit**: `chore(codex): pass local CI` (if fixes needed)

- [ ] 4.2 Create PR and verify CI
  - **Do**:
    1. Verify current branch is a feature branch: `git branch --show-current`
    2. If on default branch, STOP and alert user
    3. Stage files: `scripts/codex_proof_loop.py`, `scripts/test_codex_proof_loop.py`, `scripts/safe_aristotle_submit.py`, `math-forge/scripts/mk`, `.claude/commands/codex-prove.md`, `.gitignore`
    4. Push branch: `git push -u origin <branch-name>`
    5. Create PR: `gh pr create --title "feat(codex): add Codex proof loop with compile-fix iteration" --body "..."`
  - **Verify**: `gh pr checks` shows all green (or no CI configured -- verify push succeeded)
  - **Done when**: PR created, CI passes (if configured)
  - **Commit**: None (PR creation, not a code commit)

## Phase 5: PR Lifecycle

- [ ] 5.1 Monitor CI and fix failures
  - **Do**:
    1. Check PR status: `gh pr checks`
    2. If CI fails, read failure details, fix locally, push
    3. Re-verify: `gh pr checks`
  - **Verify**: `gh pr checks` shows all passing or no CI configured
  - **Done when**: CI green or confirmed no CI pipeline

- [ ] 5.2 [VERIFY] AC checklist
  - **Do**: Programmatically verify each acceptance criterion is met:
    1. AC-1.1: `python3 scripts/codex_proof_loop.py --help | grep -q "problem"`
    2. AC-1.2-1.5: Verified by smoke test in 3.2
    3. AC-2.1-2.5: `grep -q "create_temp_project" scripts/codex_proof_loop.py`
    4. AC-3.1-3.5: `grep -q "codex_proofs" scripts/codex_proof_loop.py && grep -q "best.lean" scripts/codex_proof_loop.py`
    5. AC-4.1,4.4: `grep -q "codex-context" scripts/safe_aristotle_submit.py`
    6. AC-5.1-5.2: `grep -q "codex_proofs" scripts/codex_proof_loop.py && grep -q "CREATE TABLE" scripts/codex_proof_loop.py`
    7. AC-5.3-5.4: `grep -q "codex)" math-forge/scripts/mk && grep -q "codex-best)" math-forge/scripts/mk`
    8. AC-6.1-6.5: `test -f .claude/commands/codex-prove.md`
    9. AC-8.1-8.4: `grep -q "extract_sorry_targets" scripts/codex_proof_loop.py`
  - **Verify**: All grep/test commands above exit 0
  - **Done when**: All acceptance criteria confirmed via automated checks
  - **Commit**: None

## Notes

- **POC shortcuts taken**: Phase 1 uses `--max-iterations 1-2` for fast validation. Theorem statement locking may use simple string comparison (not AST). Sorry counting uses regex, not Lean parser.
- **Production TODOs**:
  - `promoted_to_aristotle` DB field update when Codex proof submitted as Aristotle context (requires modifying safe_aristotle_submit.py to write back to codex_proofs table after successful submit)
  - AC-7.1-7.3 (audit integration) works already since `/audit` accepts any .lean path -- no changes needed
  - Parallel loop safety is inherent from temp dir isolation + auto-incrementing attempt dirs
- **No test runner in project**: Python scripts tested via direct execution (`python3 test_file.py`). No pytest/unittest framework configured.
- **Codex CLI confirmed**: v0.107.0 at `/opt/anaconda3/envs/claude-code/bin/codex`. Model gpt-5.3-codex.
- **Warm cache required**: `.lake/packages/` must exist before running proof loop. Script checks and aborts if missing.
