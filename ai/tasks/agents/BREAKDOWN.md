---
id: agents.BREAKDOWN
module: agents
priority: 8
status: failing
version: 1
origin: spec-workflow
dependsOn: [cli.BREAKDOWN, extraction.BREAKDOWN]
tags: [math-forge]
testRequirements:
  unit:
    required: false
    pattern: "tests/agents/**/*.test.*"
---
# Agents: Specialized Subagent Configurations

## Context
Claude Code agents are specialized subagents with independent context and tool access. math-forge defines agent configurations for knowledge-intensive tasks: a knowledge-retriever agent for complex KB queries, and a problem-researcher agent for multi-step investigation of mathematical problems. Agents are markdown files in the `agents/` directory. The investigation agent (v2 in PM.md scope) has access to Read, Grep, Glob, and the `mk` tool for progressive disclosure queries. Reference: PM.md "Investigation agent" (scope item 7), TECH.md plugin structure.

## Acceptance Criteria
1. `math-forge/agents/` directory exists with agent markdown files
2. **`investigate.md`**: Agent configuration for complex knowledge queries. Has access to Read, Grep, Glob, and Bash (for `mk` invocations). Includes instructions to: search KB first, then read relevant .lean files for detail, synthesize findings into structured response.
3. **`problem-researcher.md`**: Agent configuration for multi-step problem investigation. Searches formal-conjectures repo, checks KB for prior work, identifies related proven techniques, outputs structured problem assessment.
4. Each agent has: name, description, tools list, system prompt with domain-specific instructions
5. Agent system prompts include the directive: "We ONLY target OPEN/UNSOLVED problems. Known-result formalizations have ZERO value."
6. Agents use progressive disclosure: search summary first, detail on explicit request

## Technical Notes
- Reference: PM.md scope item 7 describes the investigation agent with progressive disclosure pattern
- UX: UX.md "Flow 5: Patrick Asks a Knowledge Question" shows how the agent would be invoked
- Test: No dedicated agent tests in QA.md MVP. Agents are tested through manual invocation.

## Subtasks
- [ ] Create `math-forge/agents/` directory
- [ ] Write `math-forge/agents/investigate.md` with tool access and KB query instructions
- [ ] Write `math-forge/agents/problem-researcher.md` with formal-conjectures integration
- [ ] Include open-problems-only directive in all agent system prompts
- [ ] Include progressive disclosure instructions (summary first, detail on request)
