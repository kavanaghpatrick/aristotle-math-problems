# math-forge: Requirements

## Problem Statement

The math project has produced 1,063 submissions, 201 proven results, 114 proven theorems, 43 false lemmas, and 56 failed approaches. This knowledge exists as scattered artifacts across SQLite tables, .lean result files, .txt sketches, MEMORY.md notes, and CLAUDE.md rules. The knowledge compounds poorly:

1. **Session amnesia**: Each new session starts without awareness of queue state, proven results, or failed approaches. MEMORY.md is manually maintained and hitting context limits.
2. **Search friction**: Checking if a technique was tried requires manual SQL across 3+ tables. No unified search.
3. **Result extraction gap**: 947 .lean result files are opaque blobs with unextracted insights.
4. **No feedback loop**: Proven techniques do not automatically inform future sketches.
5. **Queue blindness**: No automatic briefing on session start about queue state.

## Users

- **Patrick (Researcher)**: Solo researcher using Claude Code. Needs fast orientation, unified search, knowledge accumulation.
- **Claude Code Agent**: AI agent that ideates, writes sketches, submits to Aristotle. Needs sub-second search, automatic context injection, prior knowledge during sketch writing.
- **Subagents (Debate, Research)**: Specialized subagents needing relevant KB context injection at spawn time.

## Scope (MVP)

1. **Knowledge DB with FTS5** -- `knowledge.db` with findings, strategies, problems tables. FTS5 full-text search with BM25 ranking.
2. **SessionStart hook** -- ~300-token briefing injected into Claude's context with queue status, ready-to-fetch results, KB stats, action items.
3. **PostToolUse hook** -- Validates .lean file writes/edits. Blocks sorry replacement, warns on false lemma references.
4. **KB CLI tool (`mk`)** -- Bash wrapper for sqlite3 queries. Subcommands: search, find, strategies, failed, stats, init, help.
5. **Result extraction pipeline** -- Python3 script parsing .lean result files into structured findings in knowledge.db.
6. **Sketch template enhancement** -- `/sketch` queries KB for relevant prior findings, auto-populates "Prior Knowledge" section.

## Out of Scope

- Replacing tracking.db (it remains source of truth for submissions)
- Lean code generation
- Vector embeddings / semantic search
- Web UI / dashboard
- Multi-user collaboration
- Aristotle API integration (existing scripts handle this)
- Automatic proof strategy generation

## Success Metrics

| Metric | Baseline | Target (30 days) |
|--------|----------|-------------------|
| Session orientation time | ~5-10 min manual | <10 sec automatic |
| Knowledge base size | 0 findings | 500+ findings |
| Duplicate submission rate | ~5-10% estimated | <2% |
| Result extraction coverage | 0% automated | 90%+ of new results |

## Key Decisions

1. **Separate knowledge.db** (not extending tracking.db) -- derived, reconstructible, independent evolution
2. **Full plugin at `math-forge/`** in project repo -- namespaced under `/math-forge:*`
3. **SessionStart hook**: ~300 tokens, cached status, no live API calls
4. **Partial migration bootstrap** -- copy structured tables, skip raw .lean parsing
5. **FTS5 external content table** with porter tokenizer, BM25 weights
6. **`mk` is bash wrapper** calling sqlite3 (~350 lines, ~50ms startup)
7. **PostToolUse**: tiered blocking (sorry=block, false lemma=warn)
8. **No `mk add` in MVP** -- ingestion via migration + extraction only

## Risks

| Risk | Mitigation |
|------|------------|
| FTS5 tokenizes math notation poorly | Supplement FTS5 with exact-match on structured fields |
| Automated extraction may miss findings | Start conservative (theorem names, imports, sorry counts); iterate |
| SessionStart hook latency | Target <2s; no network calls; cache queue status |
| Context window bloat | Progressive disclosure: hook <500 tokens; mk search top 5; details on demand |
