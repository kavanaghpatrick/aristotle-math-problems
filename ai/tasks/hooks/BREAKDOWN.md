---
id: hooks.BREAKDOWN
module: hooks
priority: 4
status: failing
version: 1
origin: spec-workflow
dependsOn: [cli.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/hooks/**/*.test.*"
---
# Hooks: SessionStart & PostToolUse Lifecycle Hooks

## Context
math-forge uses two Claude Code lifecycle hooks in MVP: a SessionStart hook that injects a ~300-token briefing into Claude's context (queue status, ready-to-fetch results, KB size, action items), and a PostToolUse hook that validates .lean file writes/edits (blocks sorry replacement, warns on false lemma references). Hooks are bash scripts invoked by Claude Code's plugin system. Reference: TECH.md "Hook Implementations" section (complete scripts provided), UX.md "Hook Message Design" section.

## Acceptance Criteria

### SessionStart Hook (`hooks/scripts/context-loader.sh`)
1. Outputs valid JSON with `hookSpecificOutput.additionalContext` field
2. Queries tracking.db for: in-flight count, completed-unfetched results, recent proven, top near-miss
3. Queries knowledge.db for: finding count, most recent finding
4. Token budget: additionalContext word count * 1.33 < 500
5. Completes within 5-second timeout
6. Auto-initializes knowledge.db from schema.sql if missing
7. Displays staleness indicator if last tracking.db update >6 hours ago
8. Includes numbered ACTION ITEMS list
9. Includes `mk` tool hints footer
10. Adds `${PLUGIN_ROOT}/scripts` to PATH via `CLAUDE_ENV_FILE` if available
11. Uses `[math-forge]` prefix in briefing header

### PostToolUse Hook (`hooks/scripts/lean-validator.sh`)
1. Only acts on .lean files (silently exits for non-.lean files)
2. Reads JSON from stdin with `tool_name`, `tool_input`, `tool_response` fields
3. **Sorry replacement detection (BLOCK)**: If tool is Edit, old_string had proof content (by/exact/apply/simp/etc.), and new_string introduces sorry where old had none -> outputs `{"decision": "block", "reason": "..."}`
4. **False lemma reference (WARN)**: If .lean file references a lemma name from `false_lemmas` table in tracking.db -> outputs advisory warning via `hookSpecificOutput.additionalContext`
5. Completes within 3-second timeout
6. Handles missing jq gracefully (fallback to grep-based JSON parsing)
7. Never modifies the .lean file (read-only)
8. Block reason includes: what was detected, rule citation, what to do instead

### hooks/hooks.json
1. Valid JSON with `description` field and `hooks` object
2. SessionStart hook configured with `matcher: "startup|resume"`, `type: "command"`, `timeout: 5`
3. PostToolUse hook configured with `matcher: "Write|Edit"`, `type: "command"`, `timeout: 3`
4. All paths use `${CLAUDE_PLUGIN_ROOT}` variable

## Technical Notes
- Reference: TECH.md "Hook Implementations" section has complete bash scripts for both hooks
- UX: UX.md "Hook Message Design" section specifies output format, audience (LLM not human), and tiered blocking strategy
- Test: QA.md `test_session_start_hook.bats` (6 cases) and `test_lean_validator_hook.bats` (6 cases)

## Subtasks
- [ ] Write `math-forge/hooks/hooks.json` with SessionStart and PostToolUse configurations
- [ ] Write `math-forge/hooks/scripts/context-loader.sh` (SessionStart hook)
- [ ] Implement tracking.db queries: in-flight, completed-unfetched, recent proven, near-miss
- [ ] Implement knowledge.db queries: finding count, recent finding
- [ ] Implement staleness check (>6h since last tracking.db update)
- [ ] Implement ACTION ITEMS generation
- [ ] Implement JSON output with proper escaping (python3 json.dumps for newlines)
- [ ] Implement CLAUDE_ENV_FILE PATH injection
- [ ] Write `math-forge/hooks/scripts/lean-validator.sh` (PostToolUse hook)
- [ ] Implement sorry replacement detection (Edit: old has proof, new has sorry)
- [ ] Implement false lemma reference scanning (grep against false_lemmas table)
- [ ] Implement tiered output (block for sorry, advisory for false lemma)
- [ ] Set executable permissions on all hook scripts
