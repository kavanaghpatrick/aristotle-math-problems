---
spec: fix-skill-infrastructure
phase: research
created: 2026-02-17
generated: auto
---

# Research: fix-skill-infrastructure

## Executive Summary

Two maintenance fixes to existing skill infrastructure. Both files exist, both changes are straightforward text edits. No new dependencies, no architectural changes.

## Codebase Analysis

### Existing Patterns

- **submit.md** (`.claude/commands/submit.md`): 7-step skill orchestrating Aristotle submissions. Step 5 has inline Python with broken template placeholders (`$CONTEXT_FILES`, `$FILE_PATH`) instead of calling `scripts/safe_aristotle_submit.py`.
- **safe_aristotle_submit.py** (`scripts/safe_aristotle_submit.py`): Full CLI with `--informal`, `--context`, `--batch`, `--force` flags. Has gap-targeting gate, auto-context, retry logic, lockfile, deduplication, transaction logging. Already does everything submit.md Step 5 tries to do inline.
- **context-loader.sh** (`math-forge/hooks/scripts/context-loader.sh`): SessionStart hook outputting JSON `additionalContext`. Currently mentions `mk search` and `mk find` but not `/project:*` skills.
- **fetch.md** (`.claude/commands/fetch.md`): Reference skill that delegates to `python3 scripts/aristotle_fetch.py` -- pattern to follow for submit.md.

### Dependencies

- `scripts/safe_aristotle_submit.py` already exists and is production-tested
- 11 command files in `.claude/commands/` already exist and work

### Constraints

- submit.md must preserve Steps 1-4 and Steps 6-7 (only Step 5 changes)
- context-loader.sh must stay under token budget (~300 tokens briefing)
- Hook output must remain valid JSON with `additionalContext`

## Feasibility Assessment

| Aspect | Assessment | Notes |
|--------|------------|-------|
| Technical Viability | High | Pure text edits to 2 files |
| Effort Estimate | S | ~30 min total |
| Risk Level | Low | No new code, just rewiring existing pieces |

## Recommendations

1. Replace submit.md Step 5 inline Python with `python3 scripts/safe_aristotle_submit.py <file> --informal` call
2. Append skill reminder block to context-loader.sh briefing output
3. Also fix Step 4 pre-flight check (inline Python) to use the script's built-in capacity check
