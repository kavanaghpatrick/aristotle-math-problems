---
spec: fix-skill-infrastructure
phase: tasks
total_tasks: 6
created: 2026-02-17
generated: auto
---

# Tasks: fix-skill-infrastructure

## Phase 1: Make It Work (POC)

Focus: Fix both files so they work correctly.

- [ ] 1.1 Rewrite submit.md Step 5 to delegate to safe_aristotle_submit.py
  - **Do**: Replace the inline Python block in Step 5 (lines 68-86) with a bash code block calling `python3 scripts/safe_aristotle_submit.py <file> --informal`. Include `--context <path>` flags for any context files gathered in Step 3. The script handles gap-targeting gate, auto-context, retry, lockfile, dedup, and transaction logging internally.
  - **Files**: `.claude/commands/submit.md`
  - **Done when**: Step 5 contains `python3 scripts/safe_aristotle_submit.py` call with `--informal` flag, no `$CONTEXT_FILES` or `$FILE_PATH` template placeholders remain anywhere in file
  - **Verify**: `grep -c '\$CONTEXT_FILES\|\$FILE_PATH' .claude/commands/submit.md` returns 0; `grep 'safe_aristotle_submit' .claude/commands/submit.md` returns match
  - **Commit**: `fix(submit): delegate to safe_aristotle_submit.py instead of inline Python`
  - _Requirements: FR-1, FR-2_
  - _Design: Component A_

- [ ] 1.2 Simplify submit.md Step 4 pre-flight check
  - **Do**: Remove the inline Python queue check block (lines 57-66) from Step 4. Keep only the sqlite3 false-lemma check and prior-attempts check. The safe_aristotle_submit.py script does its own queue capacity check internally.
  - **Files**: `.claude/commands/submit.md`
  - **Done when**: Step 4 has no inline `python3 -c` block; still has sqlite3 false_lemmas check
  - **Verify**: `grep -c 'python3 -c' .claude/commands/submit.md` returns 0; `grep 'false_lemmas' .claude/commands/submit.md` returns match
  - **Commit**: `fix(submit): remove redundant inline queue check from Step 4`
  - _Requirements: FR-4_
  - _Design: Component A_

- [ ] 1.3 Add skill reminder to context-loader.sh
  - **Do**: Before the closing `mk search`/`mk find` line (line 101), append a SKILLS block to the BRIEFING variable listing key /project:* commands. Format: `SKILLS: /project:submit | /project:fetch | /project:status | /project:sketch | /project:sweep | /project:screen | /project:audit | /project:process-result`. Keep to 1-2 lines.
  - **Files**: `math-forge/hooks/scripts/context-loader.sh`
  - **Done when**: BRIEFING includes skill list with `/project:submit` and other key commands
  - **Verify**: `grep '/project:submit' math-forge/hooks/scripts/context-loader.sh` returns match; `bash math-forge/hooks/scripts/context-loader.sh 2>/dev/null` produces valid JSON (or at minimum doesn't error on the new lines)
  - **Commit**: `fix(hooks): add /project:* skill reminder to session briefing`
  - _Requirements: FR-3_
  - _Design: Component B_

- [ ] 1.4 POC Checkpoint
  - **Do**: Verify both files are correct. Read submit.md end-to-end and confirm no template placeholders. Read context-loader.sh and confirm skill reminder present.
  - **Done when**: Both files pass manual review
  - **Verify**: Read both files, confirm changes are coherent
  - **Commit**: (no commit -- verification only)

## Phase 2: Refactoring

- [ ] 2.1 Final cleanup pass
  - **Do**: Read both modified files. Ensure submit.md Steps flow logically (Step 5 output feeds Step 6 tracking). Ensure context-loader.sh briefing reads naturally. Fix any awkward wording.
  - **Files**: `.claude/commands/submit.md`, `math-forge/hooks/scripts/context-loader.sh`
  - **Done when**: Both files read cleanly with no leftover artifacts from old code
  - **Verify**: Full file review of both files
  - **Commit**: `refactor(skills): clean up submit and context-loader wording` (if changes needed)

## Phase 3: Quality Gates

- [ ] 3.1 Verify and create PR
  - **Do**: Run `bash -n math-forge/hooks/scripts/context-loader.sh` to syntax-check the shell script. Grep both files for any remaining issues. Push branch and create PR.
  - **Verify**: Shell syntax check passes, no template placeholders in submit.md, PR created
  - **Done when**: PR is open and checks pass
  - **Commit**: (no commit -- PR creation only)

## Notes

- **POC shortcuts taken**: None needed -- this is a small refactor
- **No tests needed**: These are markdown instruction files and a shell hook -- no unit tests apply
- **safe_aristotle_submit.py is NOT modified**: We only change how submit.md calls it
