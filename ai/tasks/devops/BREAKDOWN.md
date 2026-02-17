---
id: devops.BREAKDOWN
module: devops
priority: 0
status: failing
version: 1
origin: spec-workflow
dependsOn: []
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/devops/**/*.test.*"
---
# DevOps: Plugin Directory Structure & Bootstrap

## Context
math-forge is a full Claude Code plugin living at `math-forge/` in the project repo. This module creates the foundational directory structure, the `plugin.json` manifest, and the bootstrap scripts that initialize the plugin for first use. All other modules depend on this directory structure existing. Reference: TECH.md "Plugin Structure" section, PM.md ADR-2 (full plugin architecture).

## Acceptance Criteria
1. `math-forge/` directory exists at project root with the complete directory tree: `.claude-plugin/`, `data/`, `hooks/`, `hooks/scripts/`, `scripts/`, `agents/`, `tests/`, `tests/fixtures/`
2. `math-forge/.claude-plugin/plugin.json` exists with valid JSON containing `name`, `version`, `description`, `author`, `keywords` fields as specified in TECH.md
3. `math-forge/data/` contains `schema.sql` (the knowledge.db schema) and a `.gitkeep` (knowledge.db itself is gitignored)
4. `math-forge/.gitignore` excludes `data/knowledge.db` and any `*.db` files in `data/`
5. A bootstrap script `math-forge/scripts/bootstrap.sh` exists that: (a) creates knowledge.db from schema.sql, (b) runs the migration, (c) verifies with `mk stats`
6. All shell scripts have execute permissions (`chmod +x`)
7. Running `claude --plugin-dir ./math-forge` loads the plugin without errors

## Technical Notes
- Reference: TECH.md "Plugin Structure" diagram and `plugin.json` specification
- UX: Plugin name is `math-forge`, version `0.1.0`
- Test: Verify directory structure exists and plugin.json is valid JSON (QA.md does not have dedicated devops tests; validation is implicit in all other test setups)

## Subtasks
- [ ] Create `math-forge/` directory tree (all subdirectories)
- [ ] Write `math-forge/.claude-plugin/plugin.json` with manifest fields
- [ ] Create `math-forge/.gitignore` excluding data/*.db
- [ ] Create placeholder `.gitkeep` files in empty directories
- [ ] Write `math-forge/scripts/bootstrap.sh` (init DB + migrate + verify)
- [ ] Set execute permissions on all scripts
- [ ] Verify plugin loads with `--plugin-dir`
