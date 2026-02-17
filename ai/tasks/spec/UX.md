# UX/UI Analysis: math-forge

## Research Findings

### CLI UX Design Principles

Research across major CLI design references ([Command Line Interface Guidelines](https://clig.dev/), [Atlassian's 10 CLI Design Principles](https://www.atlassian.com/blog/it-teams/10-design-principles-for-delightful-clis), [Evil Martians CLI UX](https://evilmartians.com/chronicles/cli-ux-best-practices-3-patterns-for-improving-progress-displays), [Thoughtworks CLI Guidelines](https://www.thoughtworks.com/en-us/insights/blog/engineering-effectiveness/elevate-developer-experiences-cli-design-guidelines)) converges on these key principles:

1. **Human-readable output is default; machine-readable on request.** Detect TTY vs pipe and adapt. Stdout for data, stderr for status/progress.
2. **Progressive disclosure.** Show the minimum needed at each layer. Summary first, details on demand. Running without args shows help. `-v`/`--verbose` for more.
3. **Suggest next steps.** After every output, tell the user what to do next. Reduces documentation dependency.
4. **Color with intention.** Highlight specific information; avoid coloring everything. Respect `NO_COLOR`, `TERM=dumb`, and non-TTY. Use color for semantics (red=error, green=success, yellow=warning), not decoration.
5. **One record per line for composability.** Output that pipes to `grep`, `wc`, `awk` without reformatting.
6. **Errors rewritten for humans.** Explain what happened, what the user can do, and suggest next steps. Group similar errors.
7. **Consistent verb/noun patterns.** Either verb-object (`mk search <query>`) or subject-verb (`mk findings search`). Pick one, use it everywhere.

### Claude Code Plugin-Specific Patterns

From [Claude Code Plugin Docs](https://code.claude.com/docs/en/plugins), [Hooks Reference](https://code.claude.com/docs/en/hooks), and [Plugin Architecture](https://github.com/anthropics/claude-code/blob/main/plugins/README.md):

1. **Hook output is consumed by Claude, not the human.** SessionStart `additionalContext` is injected into Claude's system prompt -- it must be optimized for LLM comprehension, not human scanning. Concise structured text > decorative boxes.
2. **PostToolUse hooks should prefer advisory warnings over hard blocks.** Blocking mid-task confuses the agent. Use `decision: "block"` only for genuinely destructive actions (sorry replacement). Use informational warnings for everything else.
3. **Progressive disclosure for skills/tools.** The Claude Code architecture uses lazy loading -- expose metadata first (name + description), load full context only when invoked. Apply the same principle to KB queries: return summary counts first, full findings on explicit request.
4. **Commands are user-invoked, skills are model-invoked.** The `mk` CLI should be usable as both: Patrick types it directly, and Claude invokes it via Bash during sketch writing. Output format must serve both audiences.

### Terminal Output Formatting

From [bat](https://github.com/sharkdp/bat), [eza](https://github.com/eza-community/eza), and modern CLI tools:

1. **Fixed-width column alignment** over ASCII art boxes for data tables. Boxes waste horizontal space and break copy-paste.
2. **Syntax-highlighted snippets** for code excerpts (Lean theorem statements).
3. **Line numbers** for orientation in code output.
4. **Truncation with indicators** ("... +12 more") rather than flooding the screen.
5. **Terminal width awareness** -- detect `$COLUMNS` and adapt layout. Default to 80 chars as safe minimum.

---

## Information Architecture

### Three-Layer Progressive Disclosure Model

The system has three distinct information delivery layers, each serving a different moment in the workflow:

```
Layer 0: HOOK INJECTION (~300 tokens)
  Automatic. No user action required.
  Injected at session start or after tool use.
  Optimized for LLM consumption.
  Answers: "What's the state of the world right now?"

Layer 1: COMMAND SUMMARY (~10-20 lines)
  User or Claude types `mk <subcommand>`.
  Returns ranked, truncated results with relevance scores.
  Answers: "What do we know about X?"

Layer 2: DETAIL DRILL-DOWN (~50-200 lines)
  Explicit request: `mk search --verbose <query>` or `mk find <id> --full`.
  Returns complete findings with code snippets, full context.
  Answers: "Tell me everything about this specific finding."
```

### Information Priority at Each Layer

**Layer 0 (SessionStart hook):**
Priority order for the ~300 token budget:
1. Results ready to fetch (highest urgency -- actionable RIGHT NOW)
2. In-flight submission count and slot availability
3. Recently proven results (last 48h) -- context for continuation
4. Top near-miss (1 sorry) -- quick win opportunity

**Layer 1 (mk commands):**
Priority order for the default view:
1. Exact problem ID matches (if querying a specific problem)
2. FTS5 BM25-ranked findings (most relevant first)
3. Failed approaches for the query (avoid repeating mistakes)
4. Related proven techniques (positive guidance)
5. Result count and "show more" hint

**Layer 2 (verbose/full output):**
All findings with full context, code snippets, submission links, timestamps, and confidence ratings.

---

## Command Design

### Tool Name: `mk` (math-knowledge)

Short, memorable, fast to type. Follows the pattern of `gh` (GitHub), `gp` (Gitpod), `wl` (Wolfram Language). Two characters is optimal for a frequently-used CLI tool.

### Subcommand Structure

The tool uses **verb-first** pattern (`mk search`, `mk find`), consistent with `gh`, `docker`, and the existing project's slash command style.

```
mk <subcommand> [arguments] [flags]
```

---

### `mk search <query>`

Full-text search across all findings in knowledge.db.

**Syntax:**
```
mk search <query> [--domain <domain>] [--type <type>] [--limit <n>] [--verbose]
```

**Arguments:**
- `<query>`: Free-text search query (passed to FTS5 MATCH). Required.

**Flags:**
- `--domain <d>`: Filter by domain (nt, algebra, combinatorics, analysis). Optional.
- `--type <t>`: Filter by finding type (theorem, technique, failure, false_lemma). Optional.
- `--limit <n>`: Max results. Default: 5 (Layer 1), 20 with `--verbose` (Layer 2).
- `--verbose` / `-v`: Show full finding text and code snippets (Layer 2).

**Output (Layer 1 -- default, ~10-15 lines):**
```
mk search "Erdos prime factors"

  SEARCH: "Erdos prime factors" — 7 results (showing top 5)

  #1  [PROVEN]  Erdos 850: prime factor triples (slot614)
      Technique: pigeonhole on omega(n) buckets + Ramsey
      Domain: number-theory | Score: 0.92

  #2  [PROVEN]  Erdos 370: smooth consecutive integers (slot616)
      Technique: Stormer + smooth number characterization
      Domain: number-theory | Score: 0.87

  #3  [FAILED]  Erdos 307: prime reciprocal existence (slot597)
      Approach: greedy decomposition of prime reciprocals
      Domain: number-theory | Score: 0.74

  #4  [FALSE]   Erdos 307: small witness existence
      Disproven: even 25 primes insufficient for P={2}
      Domain: number-theory | Score: 0.71

  #5  [PROVEN]  Erdos 350: Ryavec sum < 2 (slot620)
      Technique: reciprocal sum bound via density argument
      Domain: number-theory | Score: 0.68

  ... +2 more (use --limit 20 or --verbose for all)
```

**Output (Layer 2 -- with `--verbose`):**
```
mk search "Erdos prime factors" --verbose

  SEARCH: "Erdos prime factors" — 7 results

  ── #1 [PROVEN] Erdos 850: prime factor triples ──────────────
  Slot: 614 | Domain: number-theory | Proven: 2026-02-12
  Technique: pigeonhole on omega(n) buckets + Ramsey argument
  Statement: For any k, there exist n,n+1,n+2 sharing >= k prime factors
  Key Mathlib: Nat.Primes, Finset.card, Pigeonhole
  Lean snippet:
    theorem erdos_850_triple_factors (k : Nat) :
      exists n, (omega(n) >= k) ∧ (omega(n+1) >= k) ∧ (omega(n+2) >= k)
  ─────────────────────────────────────────────────────────────

  ── #2 [PROVEN] Erdos 370: smooth consecutive integers ──────
  ...
```

**Design rationale:**
- Default 5 results prevents flooding. Claude can always request more.
- BM25 score shown as normalized 0-1 relevance indicator.
- Status badges ([PROVEN], [FAILED], [FALSE]) give instant signal.
- Slot numbers link to the submission system -- user can `/project:fetch 614` directly.
- Verbose mode adds code snippets and full statements for Claude's sketch context.

---

### `mk find <problem-id>`

Retrieve ALL knowledge about a specific problem.

**Syntax:**
```
mk find <problem-id> [--full]
```

**Arguments:**
- `<problem-id>`: Matches against problem_id, filename patterns, Erdos numbers, etc. Examples: `erdos_364`, `slot614`, `kurepa`, `ft_p3`.

**Output (default):**
```
mk find erdos_364

  PROBLEM: Erdos 364 — Powerful number triples
  Status: IN_FLIGHT (slot622, submitted 2026-02-13)
  Domain: number-theory

  SUBMISSIONS (3):
    slot622  IN_FLIGHT  powerful triples (INFORMAL)       2026-02-13
    slot501  FAILED     direct construction                2026-02-08
    slot489  FAILED     brute force Fin 100                2026-02-06

  PROVEN RESULTS: none yet

  FAILED APPROACHES (2):
    - Direct construction of powerful triples via abc parametrization
      Why: parametrization space too large for bounded search
    - Brute force on Fin 100
      Why: no powerful triples in range, need larger search

  FALSE LEMMAS: none

  RELATED TECHNIQUES:
    - Smooth number characterization (used in Erdos 370, PROVEN)
    - Prime factor density arguments (used in Erdos 850, PROVEN)

  NEXT: Await slot622 result. If failed, try smooth+powerful intersection.
```

**Design rationale:**
- Single command gives the complete picture for a problem.
- Sections are always present (even if empty: "none yet") to confirm the check was done.
- NEXT section suggests action, reducing decision overhead.
- `--full` adds Lean snippets from proven results and detailed failure analysis.

---

### `mk strategies <domain>`

List successful proof strategies by domain.

**Syntax:**
```
mk strategies [<domain>] [--limit <n>]
```

**Arguments:**
- `<domain>`: Optional domain filter. Without it, shows all domains grouped.

**Output:**
```
mk strategies nt

  STRATEGIES: number-theory (23 proven, 8 failed)

  PROVEN TECHNIQUES (by success count):
    QR + Euler criterion ............ 4 proofs (slot590, 610, 612, ...)
    Pigeonhole principle ............ 3 proofs (slot614, 620, ...)
    Wilson's theorem modular ........ 2 proofs (slot594, 595)
    Smooth number theory ............ 2 proofs (slot616, 617)
    Direct computation (native_decide) 6 proofs (various)
    Inductive predicate construction  2 proofs (slot572, ...)

  COMMON FAILURE MODES:
    Greedy decomposition ............ 3 failures (Erdos 307, ...)
    Kummer symbol (circular) ........ 2 failures (FT p=3 q≡71)
    Pure group theory ............... 2 failures (FT p=3 q≡8mod9)

  Hint: mk search "<technique-name>" for details on any technique
```

**Design rationale:**
- Strategies are grouped by outcome (proven vs failed) and sorted by frequency.
- Dot leaders aid scanability in terminal (classic CLI pattern).
- Reference slot numbers for traceability.
- Footer hint teaches the next command to use.

---

### `mk failed [<keyword>]`

Query failed approaches and false lemmas.

**Syntax:**
```
mk failed [<keyword>] [--type false|approach|both]
```

**Output:**
```
mk failed "FT p=3"

  FAILED: "FT p=3" — 6 approaches, 0 false lemmas

  APPROACHES:
    1. QR of (1-q) — both sides equal +1, no contradiction
       Problem: FT p=3 q≡7mod8 | Attempts: 2

    2. Kummer symbol — circular: 3^(q+1)=3 iff 3^q=1
       Problem: FT p=3 q≡71mod72 | Attempts: 3

    3. Eisenstein reciprocity — equivalent to direct computation
       Problem: FT p=3 q≡71mod72 | Attempts: 1

    4. 9th power residue — insufficient character depth
       Problem: FT p=3 q≡8mod9 | Attempts: 2

    5. CM curves — curves exist but don't yield contradiction
       Problem: FT p=3 q≡8mod9 | Attempts: 1

    6. Pure group theory — all constraints satisfiable
       Problem: FT p=3 q≡8mod9 | Attempts: 1

  WARNING: Any approach matching these patterns should use a
  fundamentally different strategy. See CLAUDE.md kill list.
```

**Design rationale:**
- This is a SAFETY command. Its primary purpose is preventing duplicate failures.
- Attempt count provides intensity signal.
- WARNING footer reinforces the kill-list discipline from CLAUDE.md.
- Both Claude and Patrick can invoke this pre-sketch to check if an approach is dead.

---

### `mk stats`

Dashboard of KB size, coverage, and freshness.

**Syntax:**
```
mk stats [--full]
```

**Output:**
```
mk stats

  KNOWLEDGE BASE: math-forge
  ─────────────────────────────────────────
  Findings:        523  (+12 this week)
  Proven theorems: 114
  Failed approaches: 56
  False lemmas:     43
  Strategies:       31  (23 proven, 8 failed)
  ─────────────────────────────────────────
  Coverage by domain:
    number-theory   287 findings  (55%)  ████████████░░░░░░░░
    algebra          98 findings  (19%)  ████░░░░░░░░░░░░░░░░
    combinatorics    89 findings  (17%)  ███░░░░░░░░░░░░░░░░░
    analysis         49 findings  ( 9%)  ██░░░░░░░░░░░░░░░░░░
  ─────────────────────────────────────────
  Freshness:
    Last finding added: 2h ago (slot622 extraction)
    Oldest unprocessed result: slot619 (3 days)
  ─────────────────────────────────────────
  Pipeline:
    In flight:  6 submissions
    Slots open: 0 / 5
    Ready to fetch: 2 results
```

**Design rationale:**
- Single-screen dashboard using horizontal rules (not box-drawing for portability).
- Progress bars use block characters for domain coverage visualization.
- "This week" delta shows growth trajectory.
- Pipeline section mirrors SessionStart hook content for consistency.
- `--full` adds per-problem breakdown and extraction coverage metrics.

---

## Hook Message Design

### SessionStart Hook

**Audience:** Claude Code agent (LLM), not the human researcher. This is injected as `additionalContext` into Claude's system prompt.

**Token budget:** ~300 tokens (PM decision Q4).

**Format:** Structured plain text optimized for LLM parsing. No box-drawing, no color codes, no decorative elements. LLMs parse structured key-value pairs and lists more reliably than formatted tables.

**Output template:**
```
[math-forge] Session briefing (2026-02-13T14:30:00Z)

QUEUE: 6 in-flight, 0 slots open
READY TO FETCH: slot622, slot623 (completed in last 6h)
RECENT PROVEN: slot620 (Erdos 350 Ryavec, 228 lines), slot621 (Erdos 36, 193 lines)
TOP NEAR-MISS: slot619 (OddPerfect Euler, 1 sorry in sigma_bound lemma)
KB: 523 findings, last updated 2h ago

ACTION ITEMS:
1. Fetch slot622, slot623 — results ready
2. Close slot619 near-miss — 1 sorry in sigma_bound
3. Queue has space for 0 new submissions (wait for completions)

Use `mk search <query>` for KB queries. Use `mk find <problem>` for problem-level view.
```

**Design decisions:**
- **All-caps section headers** for LLM section parsing (proven to improve Claude's structured data comprehension).
- **Slot numbers as primary identifiers** -- consistent with existing project convention.
- **ACTION ITEMS numbered list** -- Claude processes ordered lists well and will act on item 1 first.
- **Footer with tool hints** -- teaches the agent to use `mk` during the session.
- **No emojis** -- per project CLAUDE.md preference ("avoid using emojis").
- **ISO timestamp** -- unambiguous for both human and LLM consumption.

### PostToolUse Hook (Lean Validation)

**Audience:** Claude Code agent, triggered after Write/Edit on `.lean` files.

**Trigger:** `tool_name in ["Write", "Edit"]` AND `tool_input.file_path ends with ".lean"`.

**Two modes:**

#### Advisory Warning (default -- non-blocking)

For detected issues that should be corrected but are not catastrophic:

```json
{
  "decision": "allow",
  "reason": "[math-forge] WARNING: File contains reference to false lemma 'apex_bridge_coverage' (disproven in slot534). Check `mk failed apex_bridge` for details."
}
```

The `reason` field is shown to Claude as feedback. Format:
```
[math-forge] WARNING: <what was detected>. <what to do about it>.
```

#### Hard Block (sorry replacement only)

For violations of the cardinal rule "NEVER replace existing proof code with sorry":

```json
{
  "decision": "block",
  "reason": "[math-forge] BLOCKED: Edit would replace proven code with sorry (line 47: `theorem foo` had proof, now has sorry). This violates project rule: never replace proof code with sorry. Restore the proof or use a different approach."
}
```

Format:
```
[math-forge] BLOCKED: <what was detected> (line N: <specifics>). <rule citation>. <what to do instead>.
```

**Design decisions:**
- `[math-forge]` prefix on all hook messages -- provides clear attribution so Claude knows where the message came from.
- Advisory for false-lemma references (Claude can proceed, but should reconsider).
- Hard block ONLY for sorry replacement (the most destructive action per CLAUDE.md rules).
- Self-contained messages -- each warning includes both the problem AND the remediation action.
- Line number references when available for precise location.

---

## Output Formatting Standards

### General Principles

1. **No box-drawing characters (double-line: ╔═╗, etc.) in `mk` output.** The existing `/sketch` and `/process-result` commands use box-drawing for their reports, and that is fine for those human-facing summaries. But `mk` output must be pipe-friendly and copy-paste clean. Use horizontal rules (`───`) and indentation instead.

2. **Two-space indentation** for nested content. Consistent, readable, minimal.

3. **Status badges in brackets:** `[PROVEN]`, `[FAILED]`, `[FALSE]`, `[IN_FLIGHT]`, `[NEAR_MISS]`. All-caps, bracketed. These are scannable and grep-able.

4. **Consistent column alignment** using fixed-width formatting. Slot numbers are always 3 digits (`slot614`), scores always 4 chars (`0.92`).

### Color Usage

Colors are used ONLY in interactive terminal output (TTY detected). All color is semantic:

| Color    | Meaning           | Used for                       |
|----------|-------------------|--------------------------------|
| Green    | Success/proven    | `[PROVEN]` badge, success counts |
| Red      | Failure/blocked   | `[FAILED]`, `[FALSE]`, `BLOCKED:` |
| Yellow   | Warning/in-flight | `[IN_FLIGHT]`, `WARNING:`, `[NEAR_MISS]` |
| Cyan     | Informational     | Section headers, hints          |
| No color | Default           | Body text, code snippets        |

Implementation: ANSI escape codes, gated on `[ -t 1 ]` (stdout is TTY) and `$NO_COLOR` not set.

### Truncation Rules

- **Default result limit:** 5 items per query (Layer 1).
- **Truncation indicator:** `... +N more (use --limit 20 or --verbose for all)`
- **Finding text truncation:** 120 chars in Layer 1, full text in Layer 2.
- **Code snippet truncation:** 5 lines max in Layer 1, 20 lines in Layer 2, full in `--full`.
- **Long lines:** Truncate at terminal width minus 4 chars, append `...`.

### Snippet Highlighting

When displaying Lean code snippets in verbose mode:

```
  Lean snippet:
  | theorem erdos_850_triple_factors (k : Nat) :
  |   exists n, (omega(n) >= k) /\ (omega(n+1) >= k) /\ (omega(n+2) >= k)
```

- Pipe character (`|`) as left margin for code blocks -- distinguishes code from prose.
- No syntax highlighting in snippets (adds complexity, low value for short excerpts; Claude reads raw text).

---

## Interaction Flows

### Flow 1: New Session Orientation

```
[Patrick opens Claude Code session]
  |
  v
SessionStart hook fires automatically
  |
  v
Hook queries: tracking.db (queue status), knowledge.db (recent findings)
  |
  v
~300 token briefing injected into Claude's context
  |
  v
Claude reads briefing, understands:
  - 2 results ready to fetch
  - 6 submissions in flight, 0 slots open
  - Top near-miss in slot619
  |
  v
Claude proactively says: "Two results are ready. Shall I fetch slot622 and slot623?"
  |
  v
Patrick: "yes"  -->  /project:fetch 622  -->  extraction pipeline  -->  KB grows
```

**Key UX principle:** Zero commands needed from Patrick to reach orientation. The hook does all the work. Patrick's first interaction is a decision, not a query.

### Flow 2: Writing a KB-Informed Sketch

```
Patrick: "/project:sketch Erdos 364"
  |
  v
Sketch command runs Step 1b (DB check)
  |-- EXISTING: manual SQL queries to tracking.db
  |-- NEW: `mk find erdos_364` for unified knowledge view
  |-- NEW: `mk search "powerful numbers"` for related techniques
  |
  v
Claude sees: prior submissions, failed approaches, related proven techniques
  |
  v
Claude writes sketch with "## Prior Knowledge" section auto-populated:
  - "Two prior attempts failed (direct construction, brute force)"
  - "Related success: Erdos 370 used smooth number characterization"
  - "No false lemmas for this problem"
  |
  v
Sketch saved  -->  /project:submit  -->  Aristotle
```

**Key UX principle:** The sketch command orchestrates KB queries transparently. Claude calls `mk` during sketch writing without Patrick needing to remember to check.

### Flow 3: Processing a Result into KB

```
/project:fetch 622
  |
  v
Result downloaded to slot622_result.lean
  |
  v
Existing audit runs (sorry count, axioms, etc.)
  |
  v
NEW: Extraction pipeline runs automatically
  |-- Extracts: theorem names, proof techniques, Mathlib imports
  |-- Inserts findings into knowledge.db
  |-- Prints: "Extracted 4 findings from slot622"
  |
  v
Knowledge base grows. Next session's hook includes new data.
Next sketch for related problems sees these findings automatically.
```

**Key UX principle:** Knowledge extraction is invisible. It happens as a side effect of the existing `/fetch` workflow. Zero additional commands for Patrick.

### Flow 4: Checking Before Retrying a Failed Approach

```
Claude considers retrying QR approach for FT p=3
  |
  v
Claude runs: mk failed "FT p=3 QR"
  |
  v
Output shows: "QR of (1-q) — both sides equal +1, no contradiction"
             "3 attempts, all failed"
  |
  v
Claude abandons the approach, tries a different strategy
```

**Key UX principle:** The failed-approaches check becomes a reflex because it's a single fast command. The output is definitive enough that Claude trusts it and moves on.

### Flow 5: Patrick Asks a Knowledge Question

```
Patrick: "What do we know about odd perfect numbers?"
  |
  v
Claude runs: mk search "odd perfect" --verbose
  |
  v
Output shows: slot619 (Euler form, PROVEN), slot625 (no p*q^2, IN_FLIGHT),
              2 related techniques, 0 false lemmas
  |
  v
Claude synthesizes: "We've proven the Euler form constraint.
  slot625 is testing whether odd perfects can have form p*q^2.
  No false lemmas in this area. The main proven technique is
  sigma multiplicativity + Euler's criterion."
```

**Key UX principle:** Patrick asks in natural language, Claude translates to `mk` queries, and synthesizes results in natural language. The CLI tool is invisible to Patrick -- it's infrastructure for Claude.

---

## Accessibility & Ergonomics

### Terminal Width

- **Design target:** 80 columns minimum, 120 columns optimal.
- **Adaptive layout:** `mk stats` progress bars scale with terminal width. Tables wrap gracefully at 80 cols.
- **No horizontal scrolling required** for any default (Layer 1) output.

### Copy-Paste Friendliness

- **No box-drawing in `mk` output** -- horizontal rules use `─` (U+2500) which copies cleanly, or plain `-` in non-TTY mode.
- **Slot numbers are always bare text** (`slot622`), not wrapped in formatting -- they can be copied directly into `/project:fetch slot622`.
- **Code snippets use pipe-margin** (`| code here`) -- easy to strip the margin with `sed 's/^  | //'`.
- **No trailing whitespace** on any output line.

### Screen Reader Compatibility

- **Status badges use text, not symbols:** `[PROVEN]` not checkmarks or emojis.
- **Section headers are plain text with consistent formatting** -- no ASCII art.
- **Structured output reads linearly** -- no column-dependent information.

### Speed

- **All `mk` commands target <500ms response time.** SQLite queries on a <10K row database are sub-millisecond. The bottleneck is shell startup + sqlite3 process spawn.
- **SessionStart hook targets <3 seconds.** No network calls (uses cached tracking.db state, not live Aristotle API).
- **PostToolUse hook targets <200ms.** Simple grep/diff operations on the written file.

### Error Messages

All errors follow the pattern: `[math-forge] ERROR: <what happened>. <how to fix>.`

Examples:
```
[math-forge] ERROR: knowledge.db not found. Run `mk init` to create it.
[math-forge] ERROR: No results for "quantum groups". Try broader terms or check `mk stats` for indexed domains.
[math-forge] ERROR: FTS5 query syntax error in "erdos AND OR prime". Remove adjacent operators.
```

---

## Questions & Answers

### Q1: Should `mk` output use box-drawing characters like the existing `/sketch` and `/process-result` reports?

**Answer: No.** The existing slash commands produce human-facing summary reports where box-drawing serves as visual emphasis. `mk` is infrastructure -- its output is consumed by Claude during sketch writing, piped to other commands, and needs to be copy-paste clean. Use horizontal rules (`───`) and indentation instead. This also avoids the terminal compatibility issues box-drawing creates in some environments.

### Q2: Should the SessionStart hook output be formatted for human reading or LLM reading?

**Answer: LLM reading.** The `additionalContext` field is injected into Claude's system prompt, not displayed to Patrick. Structured key-value pairs and numbered lists are more reliably parsed by LLMs than decorated tables. Patrick never sees this output directly -- he sees Claude's natural-language synthesis of the briefing. If Patrick wants to see the raw state, he uses `mk stats`.

### Q3: Should `mk search` default to 5 or 10 results?

**Answer: 5.** With a ~1000 finding corpus, 5 BM25-ranked results will almost always contain the relevant information. Showing 10 doubles the output without proportional value gain, and wastes Claude's context window during sketch writing. The `--limit` flag allows explicit expansion when needed.

### Q4: Should PostToolUse validation use `decision: "block"` or `decision: "allow"` with warnings?

**Answer: Tiered approach.** Only sorry-replacement (the single most destructive action per CLAUDE.md rules) gets a hard block. All other issues (false lemma references, suspicious patterns) use `allow` with warning in the `reason` field. Research on Claude Code hooks shows that blocking mid-task confuses the agent and produces worse results. Advisory warnings let Claude self-correct on the next turn.

### Q5: Should `mk` use colors in output?

**Answer: Yes, conditionally.** Colors are applied only when stdout is a TTY and `NO_COLOR` is not set. Semantic colors only: green for proven, red for failed/false, yellow for in-flight/warnings, cyan for headers. When piped or in non-TTY mode, status badges (`[PROVEN]`, `[FAILED]`) carry the same information textually. This follows the [Command Line Interface Guidelines](https://clig.dev/) recommendation.

### Q6: Should there be a `mk add` command for manually inserting findings?

**Answer: Not in MVP.** The primary ingestion paths are: (1) bootstrap migration from tracking.db, and (2) automated extraction from result files. Manual insertion creates a maintenance burden and data quality risk. If a finding needs to be manually recorded, it should go through the existing tracking.db tables (false_lemmas, failed_approaches) which will be mirrored to knowledge.db. Revisit for v2 if there's a clear need for ad-hoc findings.

### Q7: Should `mk find` accept fuzzy matching on problem IDs?

**Answer: Yes, with LIKE patterns.** `mk find erdos_364` should match `erdos_364`, `erdos364`, `Erdos 364`, `slot622_erdos364_*`. Implementation: normalize the input (strip spaces, underscores, case-fold), then search with LIKE '%normalized%' across problem_id, filename, and name fields. This matches how Patrick and Claude refer to problems (inconsistently).

### Q8: Should the extraction pipeline run as part of `/fetch` or as a separate step?

**Answer: Part of `/fetch`.** The goal is zero-effort knowledge accumulation. Adding a separate step means it will be forgotten. The extraction adds <1 second to the fetch workflow and the findings are immediately useful for the next session. The pipeline should be called at the end of Step 2 in `/fetch` (after audit). If extraction fails, it should log a warning and not block the fetch result.

### Q9: How should the SessionStart hook handle a stale cache (tracking.db not recently updated)?

**Answer: Display a staleness indicator.** If the most recent submission timestamp in tracking.db is >6 hours old, append a line: `NOTE: Last DB update was 14h ago. Run /project:status to refresh.` This is informational -- the hook still shows the cached state but signals that a refresh may be worthwhile. The 6-hour threshold avoids false alarms during normal overnight gaps.

### Q10: Should `mk` be a bash script or a Python script?

**Answer: Bash wrapper calling sqlite3.** Reasons: (1) fastest startup time (no Python interpreter overhead), (2) sqlite3 CLI is already available on macOS, (3) the queries are straightforward SQL with FTS5, (4) consistent with the project's existing bash-based tooling. The script will be ~200-300 lines of bash with embedded SQL queries. If extraction logic becomes complex, the extraction pipeline (`extract_findings.py`) remains Python -- but the query interface stays bash for speed.

### Q11: Should `mk` output include timestamps on findings?

**Answer: Yes, in relative format for Layer 1, ISO format for Layer 2.** Layer 1 shows "2d ago", "1w ago" for quick temporal orientation. Layer 2 (`--verbose`) shows full ISO timestamps for precision. This follows the pattern of `git log --relative-date` vs `git log --date=iso`.

### Q12: How should the sketch template's "Prior Knowledge" section be formatted?

**Answer: Bullet list under a markdown header, max 10 items.** Format:
```
## Prior Knowledge (auto-populated by math-forge)
- [PROVEN] Erdos 370 used smooth number characterization (slot616, 167 lines)
- [FAILED] Direct construction of powerful triples failed — parametrization too large (slot501)
- [FAILED] Brute force on Fin 100 — no witnesses in range (slot489)
- No false lemmas for this problem
- Related proven technique: pigeonhole on omega(n) buckets (Erdos 850)
```
This is injected into the sketch .txt file before Claude writes the proof strategy, ensuring Aristotle also benefits from the context. Max 10 items prevents bloat; items are ranked by relevance (BM25 score from `mk search`).
