---
id: integration.BREAKDOWN
module: integration
priority: 999999
status: failing
version: 1
origin: spec-workflow
dependsOn: [cli.BREAKDOWN, hooks.BREAKDOWN, extraction.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/integration/**/*.test.*"
---
# Integration: Connect math-forge to Existing /fetch, /sketch, /submit Commands

## Context
The existing math project has 11 slash commands in `.claude/commands/` that handle the proof pipeline (/sketch, /submit, /fetch, /process-result, /status, etc.). math-forge needs to integrate with these existing commands so that: (1) `/fetch` and `/process-result` automatically extract findings into knowledge.db after processing results, (2) `/sketch` queries the KB for relevant prior findings and auto-populates a "Prior Knowledge" section, and (3) the SessionStart hook and `mk` CLI are seamlessly available. This module modifies existing files outside the plugin directory. Reference: TECH.md "Integration Points" section, UX.md interaction flows.

## Acceptance Criteria

### /project:fetch Integration
1. `/project:fetch` command (`.claude/commands/fetch.md`) updated to include a Step 2b that runs `python3 math-forge/scripts/extract_findings.py` on the fetched result file
2. Extraction runs after the existing audit step, not before
3. If extraction fails, a warning is logged but the fetch result is NOT blocked
4. Output includes `[math-forge] Extracted N findings from slotM`

### /project:sketch Integration
1. `/project:sketch` command (`.claude/commands/sketch.md`) updated to include a Step 1b-extended that runs `mk search` and `mk find` for the target problem
2. The sketch template includes a "## Prior Knowledge (auto-populated by math-forge)" section
3. Prior Knowledge section contains: related proven techniques, failed approaches, false lemmas, max 10 items ranked by FTS5 relevance
4. If KB has no results, section says "No prior knowledge in KB for this problem"

### /project:process-result Integration
1. `/project:process-result` command updated to call extraction pipeline at the end of processing
2. Same extraction call as `/fetch` integration

### CLAUDE.md Update
1. CLAUDE.md updated with a section documenting math-forge plugin: what it provides, how to use `mk`, how the hooks work
2. Instructions for Claude to run `mk search` and `mk find` during sketch writing
3. Reference to `mk failed` for pre-sketch duplicate avoidance checks

### Path Availability
1. `mk` is available as a bare command during sessions (via CLAUDE_ENV_FILE PATH injection in SessionStart hook)
2. Fallback: Claude can invoke `math-forge/scripts/mk` via full path

## Technical Notes
- Reference: TECH.md "Integration Points" section describes all 6 integration points
- UX: UX.md "Flow 2: Writing a KB-Informed Sketch" and "Flow 3: Processing a Result into KB" describe the end-user experience
- Test: QA.md "WORKFLOW: SessionStart hook provides search-relevant context" integration test validates the SessionStart -> fetch -> search chain. QA.md Q11 defers sketch template testing to v2.

## Subtasks
- [ ] Read existing `.claude/commands/fetch.md` and add Step 2b for extraction
- [ ] Read existing `.claude/commands/sketch.md` and add Step 1b-extended for KB queries
- [ ] Add "## Prior Knowledge" template section to sketch output format
- [ ] Read existing `.claude/commands/process-result.md` and add extraction step
- [ ] Update CLAUDE.md with math-forge documentation section
- [ ] Verify `mk` is available via PATH after SessionStart hook runs
- [ ] Test: run /fetch on a real result, verify findings extracted into knowledge.db
- [ ] Test: run /sketch on a known problem, verify Prior Knowledge section populated
