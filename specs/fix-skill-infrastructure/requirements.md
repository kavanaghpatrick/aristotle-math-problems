---
spec: fix-skill-infrastructure
phase: requirements
created: 2026-02-17
generated: auto
---

# Requirements: fix-skill-infrastructure

## Summary

Fix two skill infrastructure files so (1) submit.md delegates to the existing safe_aristotle_submit.py script instead of broken inline Python, and (2) context-loader.sh reminds Claude about available /project:* skills at session start.

## User Stories

### US-1: Submit skill delegates to safe_aristotle_submit.py
As a user, I want `/project:submit` to call the battle-tested safe_aristotle_submit.py script so that submissions get retry logic, deduplication, lockfile protection, and proper auto-context.

**Acceptance Criteria**:
- AC-1.1: submit.md Step 5 calls `python3 scripts/safe_aristotle_submit.py <file> --informal` instead of inline Python
- AC-1.2: No `$CONTEXT_FILES` or `$FILE_PATH` template placeholders remain in submit.md
- AC-1.3: Step 4 pre-flight check reuses script capabilities or is simplified to avoid duplication
- AC-1.4: Steps 1-3 and 6-7 remain functionally unchanged

### US-2: SessionStart reminds about /project:* skills
As a user, I want the session briefing to list available `/project:*` skills so Claude uses them instead of calling Python scripts directly.

**Acceptance Criteria**:
- AC-2.1: context-loader.sh briefing includes a SKILLS section listing key /project:* commands
- AC-2.2: Briefing stays concise (skill list is compact, not verbose)
- AC-2.3: Hook output remains valid JSON with `additionalContext`

## Functional Requirements

| ID | Requirement | Priority | Source |
|----|-------------|----------|--------|
| FR-1 | submit.md Step 5 delegates to safe_aristotle_submit.py CLI | Must | US-1 |
| FR-2 | Remove broken template placeholders from submit.md | Must | US-1 |
| FR-3 | context-loader.sh appends skill reminder to briefing | Must | US-2 |
| FR-4 | Simplify submit.md Step 4 to avoid duplicating script logic | Should | US-1 |

## Non-Functional Requirements

| ID | Requirement | Category |
|----|-------------|----------|
| NFR-1 | No new dependencies introduced | Simplicity |
| NFR-2 | Briefing token budget ~300 tokens maintained | Performance |

## Out of Scope
- Changing the other 10 command files
- Modifying safe_aristotle_submit.py itself
- Changing hook infrastructure or JSON format

## Dependencies
- `scripts/safe_aristotle_submit.py` exists and is functional
- `.claude/commands/` directory has 11 skill files
