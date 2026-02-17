---
spec: fix-skill-infrastructure
phase: design
created: 2026-02-17
generated: auto
---

# Design: fix-skill-infrastructure

## Overview

Replace inline Python in submit.md with a shell delegation to safe_aristotle_submit.py, and append a skill reminder block to context-loader.sh briefing output.

## Components

### Component A: submit.md Step 5 Rewrite
**Purpose**: Delegate submission to safe_aristotle_submit.py CLI
**Changes**:
- Replace inline Python block (lines 71-86) with bash call to `python3 scripts/safe_aristotle_submit.py`
- Pass `--informal` flag (gap-targeting always uses INFORMAL)
- Pass `--context <file>` for any explicit context files from Step 3
- Script handles auto-context, gap-targeting gate, retry, lockfile, deduplication internally
- Also simplify Step 4: remove inline Python queue check (script does this already), keep only the sqlite3 false-lemma and prior-attempts checks

### Component B: context-loader.sh Skill Reminder
**Purpose**: Inject /project:* skill list into session briefing
**Changes**:
- Add SKILLS block to BRIEFING variable before the closing `mk search`/`mk find` line
- List the most important skills: submit, fetch, status, sketch, sweep, screen, audit, process-result
- Keep it to 2-3 lines max to stay within token budget

## Data Flow

1. User invokes `/project:submit <file>`
2. Steps 1-3 parse args, run gap-targeting gate, gather context (unchanged)
3. Step 4 checks false lemmas and prior attempts (simplified, no inline Python)
4. Step 5 calls `python3 scripts/safe_aristotle_submit.py <file> --informal [--context ...]`
5. Script handles all safety checks, submission, ID saving, transaction logging
6. Steps 6-7 track in DB and confirm (unchanged, uses script output)

## Technical Decisions

| Decision | Options | Choice | Rationale |
|----------|---------|--------|-----------|
| Step 5 delegation | Inline Python / Script call | Script call | Script already has all logic, inline has broken placeholders |
| Step 4 simplification | Keep inline Python / Remove | Remove queue check | Script does its own queue check; keep only DB checks |
| Skill list format | Full descriptions / Compact list | Compact list | Token budget constraint |

## File Structure

| File | Action | Purpose |
|------|--------|---------|
| `.claude/commands/submit.md` | Modify | Replace Step 5 inline Python with script delegation, simplify Step 4 |
| `math-forge/hooks/scripts/context-loader.sh` | Modify | Add SKILLS reminder block to briefing |

## Error Handling

| Error | Handling | User Impact |
|-------|----------|-------------|
| safe_aristotle_submit.py fails | Script has built-in retry (3 attempts, exponential backoff) | Error message shown to user |
| Script not found | Claude reports missing file | User fixes path |

## Existing Patterns to Follow
- fetch.md delegates to `python3 scripts/aristotle_fetch.py` -- same pattern for submit.md
- context-loader.sh already builds BRIEFING string incrementally -- append skill block the same way
