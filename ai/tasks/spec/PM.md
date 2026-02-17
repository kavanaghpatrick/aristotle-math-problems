# Product Manager Analysis: math-forge

## Research Findings

### Claude Code Plugin Architecture (2026)
The Claude Code plugin system provides a mature, well-documented extension framework with six core component types: **Skills** (model-invoked workflows with progressive disclosure), **Commands** (user-invoked slash commands), **Agents** (specialized subagents with independent context), **Hooks** (lifecycle event handlers), **MCP Servers** (external tool integration), and **LSP Servers** (code intelligence). Plugins follow a standardized directory structure with `.claude-plugin/plugin.json` manifest, and components at the plugin root in `commands/`, `agents/`, `skills/`, `hooks/` directories.

Key architectural features relevant to math-forge:
- **SessionStart hooks** can inject context via `additionalContext` field or stdout, and persist environment variables via `CLAUDE_ENV_FILE`
- **PostToolUse hooks** fire after tool success with access to both `tool_input` and `tool_response`, can provide feedback to Claude via `decision: "block"` with `reason`
- **PreToolUse hooks** can modify tool input via `updatedInput` before execution
- **Hook input** is JSON on stdin with `session_id`, `transcript_path`, `cwd`, `tool_name`, `tool_input` fields
- **Async hooks** run in background without blocking, results delivered on next conversation turn
- **`${CLAUDE_PLUGIN_ROOT}`** environment variable provides absolute path to plugin directory in all hook scripts
- Hooks can be `command` (bash), `prompt` (single LLM call), or `agent` (multi-turn subagent with tool access)

Sources: [Claude Code Plugin Docs](https://code.claude.com/docs/en/plugins), [Hooks Reference](https://code.claude.com/docs/en/hooks), [Plugins Reference](https://code.claude.com/docs/en/plugins-reference)

### Mathematical Knowledge Management Systems
The field of mathematical knowledge management (MKM) has a core tension: formal libraries are either specialized for a single client system, or general-purpose but limited in services. The QED manifesto proposed a computer-based database of all mathematical knowledge. Current systems (Lean/Mathlib, Isabelle, Metamath) formalize knowledge but lack cross-system retrieval and strategy-level knowledge capture. No existing system captures **proof strategy metadata** (what approaches worked, what failed, why) -- they only store the final formal artifacts.

Sources: [MKM Across Formal Libraries](https://researchgate.net/publication/337195839_Mathematical_Knowledge_Management_Across_Formal_Libraries), [Bridging Theorem Proving and Knowledge Retrieval](https://link.springer.com/chapter/10.1007/978-3-540-32254-2_17)

### SQLite FTS5 Best Practices
FTS5 virtual tables provide full-text search with BM25 ranking. Best practices include: use an external-content FTS table backed by a canonical data table; add insert/update/delete triggers for sync; use the `porter` tokenizer for English stemming; mark non-searchable columns as `UNINDEXED`; use `MATCH` for queries with `rank` in `ORDER BY` for relevance. The `snippet()` function generates highlighted excerpts for display.

Sources: [SQLite FTS5 Extension](https://www.sqlite.org/fts5.html), [FTS5 Practical Guide](https://medium.com/@johnidouglasmarangon/full-text-search-in-sqlite-a-practical-guide-80a69c3f42a4), [FTS5 in Practice](https://thelinuxcode.com/sqlite-full-text-search-fts5-in-practice-fast-search-ranking-and-real-world-patterns/)

### Reference Architecture: claude-mem
The [claude-mem](https://github.com/thedotmack/claude-mem) plugin demonstrates a knowledge persistence pattern for Claude Code: it uses 6 lifecycle hooks (SessionStart, UserPromptSubmit, PostToolUse, Stop, SessionEnd) to automatically capture session observations, stores them in SQLite with FTS5, compresses via AI-driven semantic summarization, and injects context back via progressive disclosure (~50-100 token search layer, then ~500-1000 token detail layer). This provides a validated architectural pattern for the knowledge capture pipeline.

### Reference Architecture: gpu-forge (from requirement)
The gpu-forge plugin referenced in the requirement demonstrates the domain-specific knowledge base pattern: 753 findings accumulated over time, FTS5 search, investigation-agent for complex queries, 212 BATS tests for reliability. This establishes the target maturity level: a plugin that compounds domain knowledge into searchable, structured findings that inform future work.

---

## Problem Statement

### The Core Problem: Knowledge Decay in a High-Volume Proof Pipeline

The math project has produced **1,063 submissions**, **201 proven results**, **76 near-misses**, **114 proven theorems**, **43 false lemmas**, and **56 failed approaches** over its lifetime. This is a rich body of mathematical knowledge -- but it exists as scattered artifacts across SQLite tables, .lean result files, .txt sketches, MEMORY.md notes, and CLAUDE.md rules. The knowledge compounds poorly:

1. **Session amnesia**: Each new Claude Code session starts without awareness of what's been proven, what's failed, and what's in the Aristotle queue. The MEMORY.md file is manually maintained and already 200+ lines -- it will hit context limits.

2. **Search friction**: To check if a technique was tried before, Claude must manually query 3+ SQLite tables with ad-hoc SQL. There is no unified search across proven theorems, failed approaches, false lemmas, and proof strategies. The `/sketch` command includes DB checks but they are keyword-based and fragile.

3. **Result extraction gap**: Aristotle returns .lean files with formal proofs, but the mathematical insights (what technique worked, what Mathlib APIs were key, what the proof structure looks like) are never extracted into structured, searchable form. The 947 .lean result files are opaque blobs.

4. **No feedback loop**: When Aristotle proves something, the insight should inform the next sketch. Currently, the human researcher must manually read the proof, understand the technique, and remember to apply it. The proven_theorems table has `theorem_name` and `statement` but no strategy/technique metadata.

5. **Sketch quality bottleneck**: CLAUDE.md says "the bottleneck is generating viable proof approaches." But the system has no mechanism to surface relevant prior successes when writing new sketches. A sketch for an Erdos problem cannot automatically pull up what worked for similar Erdos problems.

6. **Queue blindness**: The researcher must run `/status` to check Aristotle's queue. There is no automatic briefing on session start about what's ready to fetch, what's in flight, what recently completed.

### Evidence from Workflow Analysis

- `/sketch` command manually queries `false_lemmas` and `failed_approaches` but NOT `proven_theorems` or `proof_techniques` for positive guidance
- `/submit` checks queue status inline but this is lost between sessions
- `/fetch` extracts sorry/axiom counts but does not extract mathematical findings
- No existing hook infrastructure (no hooks directory, no hooks.json)
- MEMORY.md is manually maintained -- last updated Feb 13 2026 with session-specific state that will become stale
- 60+ Python scripts are point solutions, not a unified knowledge system

---

## Users & Personas

### Primary User: Patrick (Researcher)
- **Role**: Solo mathematical researcher using Claude Code as primary interface
- **Goal**: Solve open mathematical problems by submitting proof sketches to Aristotle
- **Pain points**: Manual memory maintenance, no automatic briefing, can't search across all knowledge, results don't inform future sketches
- **Interaction**: Starts sessions, uses slash commands (/sketch, /submit, /fetch), reads Claude's analysis
- **Volume**: Multiple sessions per day, 5+ submissions in flight at any time

### Primary User: Claude Code Agent
- **Role**: AI agent that ideates, writes sketches, submits to Aristotle, and processes results
- **Goal**: Generate high-quality proof sketches informed by all prior knowledge
- **Pain points**: Context window limits prevent loading all history; no automatic access to relevant prior proofs; manual SQL queries for each check
- **Interaction**: Reads hook-injected context at session start; queries KB during sketch writing; records findings from results
- **Volume**: Continuous within sessions; needs sub-second search latency

### Secondary User: Subagents (Debate, Research, Explore)
- **Role**: Specialized subagents spawned for multi-agent debates and research tasks
- **Goal**: Access relevant mathematical knowledge within their constrained context windows
- **Pain points**: SubagentStart hook could inject relevant context, but no mechanism exists today

---

## Value Proposition

### Why Build This

**Compounding returns on 1,063 submissions.** The project's greatest asset is its accumulated knowledge -- but that knowledge is trapped in formats that don't compound. Every session starts nearly from zero. math-forge converts scattered artifacts into a searchable, structured knowledge base that makes each future session more productive than the last.

**Quantified impact estimates:**
- **Session startup**: Currently 5-10 minutes of manual orientation (check queue, read MEMORY.md, recall state). SessionStart hook reduces to 5 seconds of automated briefing.
- **Sketch quality**: Currently no automatic access to related proven techniques. KB-informed sketch templates surface relevant prior successes, potentially improving Aristotle success rate.
- **Duplicate avoidance**: Currently relies on manual SQL queries and researcher memory. FTS5 search across all knowledge reduces wasted submissions on already-failed approaches.
- **Result extraction**: Currently 947 .lean files with unextracted insights. Automated extraction creates searchable findings from every result, growing the KB with zero additional effort.

### ROI Calculation
- **Cost**: ~2-3 days of plugin development
- **Payoff per session**: ~10 minutes saved on orientation + higher sketch quality + fewer duplicate submissions
- **Break-even**: ~10-15 sessions (approximately 1 week of use)
- **Long-term**: Knowledge base grows with every submission, making the system more valuable over time (compounding returns)

---

## Scope

### In Scope (MVP)

1. **Knowledge DB with FTS5** (`knowledge.db`)
   - `findings` table: discrete mathematical findings extracted from results (theorem proven, technique worked, Mathlib API useful, approach failed)
   - `proof_strategies` table: what approach was used, for what problem, what was the outcome
   - FTS5 virtual table over findings for full-text search
   - Migration/sync from existing `tracking.db` tables (one-time bootstrap)
   - Separate DB file to avoid polluting the existing tracking.db

2. **SessionStart hook** (`hooks/session_start.sh`)
   - Query Aristotle queue status (active/completed/failed jobs)
   - Surface recently completed results that need fetching
   - Report current submission pipeline state (slots available, in-flight count)
   - Display top actionable items (near-misses to close, results to process)
   - Output as `additionalContext` injected into Claude's context

3. **PostToolUse hook for .lean validation** (`hooks/post_lean_write.sh`)
   - Matcher: `Write|Edit` on `.lean` files
   - Check for sorry replacement (CLAUDE.md rule: "NEVER replace existing proof code with sorry")
   - Check for known false lemma names in written code
   - Provide warning/feedback to Claude via `decision: "block"` if violations detected

4. **KB CLI tool** (`scripts/mk`)
   - `mk search <query>` -- FTS5 search across all findings
   - `mk find <problem-id>` -- all knowledge related to a specific problem
   - `mk strategies <domain>` -- successful proof strategies by domain
   - `mk failed <keyword>` -- failed approaches and why
   - `mk stats` -- dashboard of KB size, coverage, freshness
   - Bash wrapper calling `sqlite3` with formatted output

5. **Result extraction pipeline** (`scripts/extract_findings.py`)
   - Input: .lean result file from Aristotle
   - Output: structured findings inserted into knowledge.db
   - Extracts: theorem names, proof techniques used, Mathlib imports, sorry locations, proof line counts
   - Integrates with `/fetch` and `/process-result` workflows

6. **Sketch template enhancement**
   - `/sketch` command updated to query knowledge.db for relevant prior findings
   - Automatically includes related proven techniques and failed approaches in sketch context
   - Template section: "## Prior Knowledge" auto-populated from KB

### In Scope (Future Iterations)

7. **Investigation agent** (`agents/investigate.md`)
   - Subagent with access to Read, Grep, Glob, and mk tool
   - For complex queries: "What techniques have worked for Erdos problems in number theory?"
   - Progressive disclosure: search first, then read relevant .lean files
   - Integrates with `/debate` for strategy development

8. **Automated result extraction on fetch**
   - PostToolUse hook on Bash matching `aristotle_fetch` or `process-result` patterns
   - Automatically runs extraction pipeline when results are fetched
   - Zero-effort knowledge accumulation

9. **Problem dashboard command** (`/math-forge:dashboard`)
   - Hierarchical view: Problem > Approaches > Submissions > Results
   - Status indicators: proven, near-miss, failed, in-flight, untried
   - Approach tracking: which strategies have been tried, what's left to try

10. **SubagentStart context injection**
    - Inject relevant KB findings when debate/research subagents spawn
    - Prevents subagents from recommending already-failed approaches

11. **BATS test suite** (`tests/`)
    - Automated tests for hooks, CLI tool, extraction pipeline
    - CI-compatible validation of plugin functionality

### Out of Scope

- **Replacing tracking.db**: The existing database remains the source of truth for submissions. math-forge adds a knowledge layer on top, not a replacement.
- **Lean code generation**: math-forge stores and retrieves knowledge; it does not generate Lean code or modify proof files.
- **Vector embeddings / semantic search**: FTS5 with BM25 is sufficient for the current corpus size (~1000 findings). Semantic search adds complexity without proportional benefit at this scale.
- **Web UI / dashboard viewer**: CLI-only for MVP. The researcher works entirely in Claude Code's terminal.
- **Multi-user collaboration**: Single researcher + AI agent. No access control, no concurrent writes.
- **Aristotle API integration**: math-forge reads results after fetch; it does not call the Aristotle API directly. Existing scripts handle API communication.
- **Automatic proof strategy generation**: math-forge surfaces relevant prior knowledge; Claude/researcher still makes strategy decisions.

---

## User Stories

### P0 (Must Have for MVP)

1. **As Claude, when starting a new session**, I want to automatically see the Aristotle queue status, recently completed results, and top actionable items, so I can orient immediately without manual queries.

2. **As Claude, when writing a proof sketch**, I want to search all prior findings for relevant techniques and failures, so I can write sketches informed by everything we've learned.

3. **As Claude, when processing an Aristotle result**, I want the mathematical findings to be automatically extracted and stored, so the knowledge base grows with every result.

4. **As Patrick, when I ask "what do we know about Erdos 364?"**, I want a single command that returns all related findings -- proven theorems, failed approaches, false lemmas, prior submissions -- so I don't have to query multiple tables manually.

5. **As Claude, when writing or editing .lean files**, I want automatic validation against known false lemmas and sorry-replacement rules, so I don't introduce known-bad patterns.

### P1 (Should Have for MVP)

6. **As Claude, when writing a sketch**, I want the sketch template to auto-populate a "Prior Knowledge" section with relevant findings from the KB, so every sketch builds on accumulated knowledge.

7. **As Patrick, when reviewing the pipeline**, I want a quick stats command showing KB size, coverage by domain, and recent additions, so I can track knowledge accumulation.

8. **As Claude, when querying knowledge**, I want FTS5 relevance-ranked results with highlighted snippets, so the most relevant findings surface first.

### P2 (Nice to Have, Future)

9. **As a debate subagent**, I want relevant KB findings injected into my context when I start, so I don't waste turns rediscovering known information.

10. **As Patrick, when planning what to work on next**, I want a problem dashboard showing the full approach tree for each problem, so I can identify gaps and untried strategies.

---

## Success Metrics

### Quantitative
| Metric | Baseline | Target (30 days) | How Measured |
|--------|----------|-------------------|--------------|
| Session orientation time | ~5-10 min manual | <10 sec automatic | SessionStart hook execution time |
| Knowledge base size | 0 findings | 500+ findings | `mk stats` |
| Duplicate submission rate | Unknown (estimated 5-10%) | <2% | Submissions on already-failed approaches |
| Result extraction coverage | 0% automated | 90%+ of new results | Findings per result processed |
| Sketch "Prior Knowledge" sections | 0% of sketches | 80%+ of sketches | Sketches with auto-populated KB context |

### Qualitative
- Claude reports feeling "oriented" at session start without manual MEMORY.md reading
- Researcher stops manually maintaining MEMORY.md for session state (still used for strategic directives)
- Sketch quality improves as evidenced by Aristotle success rate on KB-informed sketches
- "What do we know about X?" becomes a 2-second query instead of a 5-minute investigation

---

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| **FTS5 search quality insufficient for math** -- mathematical notation, theorem names, and LaTeX don't tokenize well | Medium | Medium | Use custom tokenizer config; supplement FTS5 with exact-match queries on structured fields (problem_id, domain, technique_name) |
| **Result extraction quality** -- automated extraction from .lean files may miss or misclassify findings | Medium | Low | Start with conservative extraction (theorem names, imports, sorry counts); add richer extraction iteratively; human-in-the-loop review for first 50 results |
| **SessionStart hook latency** -- querying DB + Aristotle queue adds startup delay | Low | Medium | Target <3 sec; async queue check if API is slow; cache queue status locally with 5-min TTL |
| **knowledge.db schema churn** -- wrong table design requires painful migrations | Medium | Medium | Start minimal (findings + strategies); use `ALTER TABLE ADD COLUMN` for additions; avoid breaking changes to FTS5 virtual table |
| **Plugin maintenance burden** -- hooks/scripts need updating as Claude Code plugin API evolves | Low | Low | Minimal dependency surface (bash hooks + sqlite3); pin to stable hook events (SessionStart, PostToolUse) |
| **Stale knowledge** -- old findings mislead rather than help | Low | Medium | Add `created_at` and `confidence` fields; weight recent findings higher in search; allow manual deprecation |
| **Context window bloat** -- too much KB context injected overwhelms Claude | Medium | High | Progressive disclosure: SessionStart injects <500 tokens; mk search returns top 5 results; full details on demand only |

---

## Dependencies

### Technical Dependencies
| Dependency | Status | Notes |
|-----------|--------|-------|
| SQLite3 with FTS5 | Available | macOS ships with SQLite 3.x including FTS5 |
| Python 3 | Available | conda claude-code environment active |
| Bash | Available | zsh on macOS, bash-compatible |
| Claude Code plugin system | Available | v1.0.33+; hooks, commands, skills all supported |
| Existing tracking.db | Available | 1,063 submissions, 8+ tables, serves as bootstrap data source |
| Existing scripts | Available | aristotle_fetch.py, safe_aristotle_submit.py provide API integration |
| Existing commands | Available | 11 slash commands in .claude/commands/ provide workflow integration points |

### Process Dependencies
| Dependency | Status | Notes |
|-----------|--------|-------|
| Plugin directory structure decision | Needed | Local plugin in project vs. separate repo? |
| Knowledge DB location decision | Needed | In submissions/ alongside tracking.db, or in plugin directory? |
| Bootstrap strategy | Needed | One-time migration from tracking.db to seed knowledge.db |
| Integration with existing /fetch and /process-result | Needed | These commands need to call extraction pipeline |

---

## Architecture Decision Records

### ADR-1: Separate knowledge.db vs. extending tracking.db
**Decision needed.** Options:
- **(A) Separate knowledge.db**: Clean separation of concerns; tracking.db remains source of truth for submissions; knowledge.db is a derived, searchable layer. Easier to rebuild if schema needs changing.
- **(B) Add FTS5 tables to tracking.db**: Single database, no sync issues, simpler queries with JOINs across tables. Risk: tracking.db already has 50+ tables/views; adding FTS5 increases complexity.
- **Recommendation**: (A) Separate knowledge.db. The knowledge layer is derived and reconstructible; the submission tracking layer is canonical. Different lifecycle, different schema evolution patterns.

### ADR-2: Plugin architecture vs. standalone configuration
**Decision needed.** Options:
- **(A) Full plugin**: `.claude-plugin/plugin.json`, `hooks/`, `commands/`, `agents/`, `scripts/` in a separate directory. Namespaced as `/math-forge:search`, etc. Portable, versioned, clean.
- **(B) Standalone in .claude/**: Add hooks to `.claude/settings.json`, commands to `.claude/commands/`, scripts to `scripts/`. No namespacing overhead. Tighter coupling to project.
- **(C) Hybrid**: Plugin for hooks and agents; extend existing `.claude/commands/` for workflow integration. Best of both worlds but more complex.
- **Recommendation**: (A) Full plugin. The mathematical knowledge infrastructure is a reusable, versioned system that should be cleanly separated from project-specific configuration. It also makes the architecture explicit and testable.

### ADR-3: Knowledge extraction approach
**Decision needed.** Options:
- **(A) Regex-based extraction**: Parse .lean files with grep/regex for theorem declarations, imports, sorry locations. Fast, simple, brittle.
- **(B) Python AST-like parsing**: Structured parser for Lean syntax. More robust, but Lean 4 parsing is non-trivial.
- **(C) LLM-assisted extraction**: Use a prompt hook or agent to read the .lean file and extract structured findings. Most accurate for strategy-level insights, but adds latency and cost.
- **Recommendation**: (A) for MVP with path to (C). Start with regex extraction for structural data (theorems, imports, sorry counts), which is sufficient for initial KB population. Add LLM-assisted extraction in a future iteration for strategy-level findings.

---

## Questions & Answers

### Q1: Separate knowledge.db or extend tracking.db?
**Answer**: (A) Separate knowledge.db — derived, reconstructible, independent schema evolution.
**Impact**: Plugin has its own data directory with knowledge.db. Migration script copies structured data from tracking.db at bootstrap.

### Q2: Full plugin or standalone .claude/ configuration?
**Answer**: (A) Full plugin with `.claude-plugin/plugin.json` at `math-forge/` in the project repo.
**Impact**: All components namespaced under `/math-forge:*`. Loaded via `--plugin-dir ./math-forge`.

### Q3: Where should the plugin directory live?
**Answer**: (A) Inside the project repo at `math-forge/`. Tight integration with tracking.db and submissions/.
**Impact**: Co-located, version-tracked together. `${CLAUDE_PLUGIN_ROOT}` resolves to `<project>/math-forge/`.

### Q4: SessionStart hook context injection level?
**Answer**: (B) Standard ~300 tokens. Queue status + top 3 actionable items + recent completions.
**Impact**: Enough to orient without consuming context. `mk` CLI for deeper queries on demand.

### Q5: Should SessionStart call Aristotle API live?
**Answer**: (C) Cached status from tracking.db with 5-min TTL. Near-instant startup. Staleness indicator if cache is old.
**Impact**: Hook reads cached status from a local file. `/status` command refreshes the cache.

### Q6: Bootstrap strategy for existing data?
**Answer**: (B) Partial migration. Copy structured tables (proven_theorems, false_lemmas, failed_approaches, candidate_problems) without parsing all 947 .lean files. ~500+ findings from day one.
**Impact**: Migration script runs once at bootstrap. Future .lean results extracted via the new pipeline.
