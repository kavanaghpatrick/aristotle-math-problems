---
id: skills.BREAKDOWN
module: skills
priority: 6
status: failing
version: 1
origin: spec-workflow
dependsOn: [cli.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/skills/**/*.test.*"
---
# Skills: Model-Invoked Skill Files

## Context
Claude Code skills are model-invoked workflows with progressive disclosure. math-forge skills provide Claude with domain-specific knowledge retrieval capabilities that it can invoke during proof strategy development. Skills are markdown files in the `skills/` directory that describe when and how to use the `mk` CLI and knowledge base. They teach Claude the patterns for KB-informed sketch writing. Reference: PM.md "Claude Code Plugin Architecture" (skills as progressive disclosure), TECH.md plugin structure.

## Acceptance Criteria
1. `math-forge/skills/` directory exists with skill markdown files
2. **number-theory skill**: Describes how to query NT-specific findings, proven techniques in NT domain, and common NT failure modes. Includes example `mk` invocations.
3. **open-problems skill**: Describes the workflow for approaching open problems with KB context: search for prior attempts, check failed approaches, find related proven techniques, compose Prior Knowledge section.
4. **proof-strategies skill**: Describes how to query and compare proof strategies across problems and domains. Includes patterns for technique reuse across related problems.
5. Each skill file has YAML frontmatter with `name`, `description`, and `tags`
6. Skill descriptions are concise (<200 tokens metadata) with detailed instructions loaded on invocation
7. Skills reference `mk` subcommands with concrete examples relevant to the math project

## Technical Notes
- Reference: PM.md describes Claude Code skills as "model-invoked workflows with progressive disclosure"
- UX: UX.md "Flow 2: Writing a KB-Informed Sketch" and "Flow 5: Patrick Asks a Knowledge Question" show how Claude uses the KB during work
- Test: Skills are tested indirectly through integration tests (sketch workflow uses KB queries). No dedicated skill unit tests in QA.md.

## Subtasks
- [ ] Create `math-forge/skills/` directory
- [ ] Write `math-forge/skills/number-theory.md` with NT-specific KB query patterns
- [ ] Write `math-forge/skills/open-problems.md` with open-problem approach workflow
- [ ] Write `math-forge/skills/proof-strategies.md` with cross-domain technique comparison
- [ ] Add YAML frontmatter with name, description, tags to each skill
- [ ] Include concrete `mk` command examples in each skill
