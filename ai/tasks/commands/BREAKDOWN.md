---
id: commands.BREAKDOWN
module: commands
priority: 7
status: failing
version: 1
origin: spec-workflow
dependsOn: [cli.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/commands/**/*.test.*"
---
# Commands: Slash Commands for math-forge

## Context
Claude Code slash commands are user-invoked actions (e.g., `/math-forge:search`, `/math-forge:knowledge`). These provide a user-facing interface to the knowledge base that supplements the `mk` CLI tool. Commands are markdown files in the `commands/` directory that Claude interprets and executes. They wrap `mk` invocations with natural language orchestration. Reference: PM.md scope items, TECH.md plugin structure.

## Acceptance Criteria
1. `math-forge/commands/` directory exists with command markdown files
2. **`/math-forge:search`**: Accepts a query string, runs `mk search` with the query, and presents results to the user with Claude's synthesis and recommendations
3. **`/math-forge:knowledge`**: Accepts a problem ID, runs `mk find` for a comprehensive knowledge report, synthesizes findings into actionable summary
4. **`/math-forge:stats`**: Runs `mk stats` and presents the KB dashboard
5. **`/math-forge:failed`**: Accepts optional keyword, runs `mk failed`, warns against repeating known-bad approaches
6. Each command markdown file includes: description, argument specification, step-by-step instructions for Claude, expected output format
7. Commands use the `mk` CLI as their backend (not raw SQL)
8. Commands include error handling instructions (e.g., "if mk returns no results, suggest broader search terms")

## Technical Notes
- Reference: TECH.md plugin structure shows `commands/` directory
- UX: UX.md interaction flows describe how commands integrate with workflows (Flow 2: sketch writing, Flow 4: checking failed approaches, Flow 5: knowledge questions)
- Test: Commands are tested through integration tests. No dedicated command unit tests in QA.md.

## Subtasks
- [ ] Create `math-forge/commands/` directory
- [ ] Write `math-forge/commands/search.md` for `/math-forge:search`
- [ ] Write `math-forge/commands/knowledge.md` for `/math-forge:knowledge`
- [ ] Write `math-forge/commands/stats.md` for `/math-forge:stats`
- [ ] Write `math-forge/commands/failed.md` for `/math-forge:failed`
- [ ] Include argument specs, step-by-step instructions, and error handling in each
