---
spec: codex-proof-loop
phase: research
created: 2026-03-14T08:00:00Z
---

# Research: codex-proof-loop

## Executive Summary

The math-forge project currently uses Codex only for analysis (debate.py, codex_results/ markdown files). A "Codex proof loop" would add a new capability: Codex writes Lean 4 code, iterates against `lake build`, and produces compilable `.lean` files that feed into the existing Aristotle submission pipeline. The project already has a working Lean 4 project setup (lakefile.toml, Mathlib dependency, Lean v4.24.0), Codex CLI v0.107.0 installed with workspace-write sandbox support, and a rich pipeline infrastructure to build upon. Research from APOLLO and similar systems shows compile-fix loops raise proof success rates from ~12% to ~60%.

## External Research

### Best Practices: AI Proof Loop Architecture

- **APOLLO pattern** (arxiv 2505.05758): LLM generates proof -> Lean compiler checks -> error feedback -> LLM revises. Achieves 75% on miniF2F. Key insight: parse Lean error messages and feed them back as structured context.
  Source: [APOLLO paper](https://arxiv.org/html/2505.05758v1)

- **Agentic Proof Automation** (arxiv 2601.03768): "Agent generates proof script, invokes lean4check. If proof fails, agent reads error, interprets it, refines. Loop continues until success." Success rate: 12% -> 60%.
  Source: [Agentic Proof Automation](https://arxiv.org/pdf/2601.03768)

- **lean4-skills** (GitHub): Provides structured prove/review/golf loop, mathlib search, axiom checking, safety guardrails for AI agents working with Lean 4.
  Source: [lean4-skills](https://github.com/cameronfreer/lean4-skills)

### Codex CLI Capabilities (v0.107.0)

- `codex exec` runs non-interactively, outputs to stdout. Perfect for scripted loops.
  Source: [Codex CLI reference](https://developers.openai.com/codex/cli/reference)

- `--sandbox workspace-write` allows writes to working directory (needed for creating .lean files).
  Source: [Codex CLI features](https://developers.openai.com/codex/cli/features)

- `--full-auto` = workspace-write sandbox + on-request approvals. Suitable for automation.
  Source: [Codex flag guide](https://www.vincentschmalbach.com/how-codex-cli-flags-actually-work-full-auto-sandbox-and-bypass/)

- Model: `gpt-5.3-codex` (current) with reasoning effort settings (low/medium/high/xhigh).
  Source: [GPT-5.3-Codex docs](https://developers.openai.com/api/docs/models/gpt-5.3-codex)

- Network blocked by default in sandbox mode. Can override with config.
  Source: [Codex sandbox docs](https://developers.openai.com/codex/agent-approvals-security/)

- User config at `~/.codex/config.toml` shows model=gpt-5.2 with migration note to gpt-5.3-codex. Project `/Users/patrickkavanagh/math` already trusted.
  Source: `~/.codex/config.toml`

### Lake Build System

- Lake supports incremental builds -- only recompiles changed modules. Essential for fast iteration loops.
  Source: [Lake docs](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)

- `lake build` returns exit code 0 on success, non-zero on failure, with error messages on stderr.
  Source: [Lake README](https://github.com/leanprover/lean4/blob/master/src/lake/README.md)

- The project's lakefile.toml targets `Math` lib, depends on mathlib v4.24.0. Single source file at `Math/Slot145.lean`.
  Source: `/Users/patrickkavanagh/math/lakefile.toml`, `/Users/patrickkavanagh/math/Math/`

### Pitfalls to Avoid

- **Infinite loops**: LLMs can get stuck in cycles (same error, same fix attempt). Must cap iterations (3-5 max per proof).
- **Sorry inflation**: Codex might "fix" errors by adding `sorry`. Must count and reject sorry additions.
- **Import bloat**: Codex may add unnecessary Mathlib imports that slow compilation massively.
- **Wrong theorem statement**: Codex might change the theorem statement to make it trivially provable. Must lock the statement.
- **Build timeout**: Full Mathlib rebuild can take 30+ minutes. Incremental builds are seconds if only the target file changes.
- **Sandbox limitations**: Codex with `workspace-write` can only write to the working directory. The `Math/` directory is within workspace, so this works.

## Codebase Analysis

### Current Codex Integration (Analysis Only)

| Location | Usage | Pattern |
|----------|-------|---------|
| `scripts/debate.py:153-196` | `call_codex()` function | Writes prompt to temp file, runs `codex exec --full-auto --sandbox read-only`, captures stdout |
| `codex_results/` | Markdown analysis files | Codex writes analysis of math problems as `.md` files |
| `codex_results/v2/` | 15 solve files | `erdos*_solve.md` -- computational analysis |
| `codex_results/v3/` | 37 files (md + lean) | `*_math.md` analysis + `agoh_giuga_ge6_factors.lean` (one .lean!) |
| `~/.codex/config.toml` | Project trusted | `trust_level = "trusted"` for `/Users/patrickkavanagh/math` |

**Key finding**: `codex_results/v3/agoh_giuga_ge6_factors.lean` is the ONLY Lean file Codex has produced. It was created manually and has 1 sorry. The `*_sorry_math.md` files show Codex iterating on proofs in markdown, NOT actually compiling them. This is the gap the proof loop fills.

### Current Pipeline Flow

```
[Gap Identification] -> [Sketch (.txt, <=30 lines)] -> [safe_aristotle_submit.py]
    -> [Aristotle API] -> [result .lean] -> [aristotle_fetch.py] -> [audit + DB update]
```

The new Codex proof loop would add a parallel path:

```
[Problem + context] -> [Codex writes .lean] -> [lake build] -> [error feedback]
    -> [Codex revises] -> [loop until compiles or max iterations]
    -> [compilable .lean] -> [submit to Aristotle as context OR as formal submission]
```

### Lean Project Setup

| Component | Value | Source |
|-----------|-------|--------|
| Lean version | v4.24.0 | `lean-toolchain` |
| Build system | Lake (TOML config) | `lakefile.toml` |
| Dependencies | mathlib v4.24.0 | `lake-manifest.json` |
| Default target | `Math` lib | `lakefile.toml` |
| Source dir | `Math/` | `lakefile.toml` |
| Current source | `Math/Slot145.lean` (17KB) | ls output |
| `.lake/` present | Yes (packages downloaded) | `.lake/` exists |

**Build constraint**: The `Math/` directory is the only Lean source directory. Codex-generated files should go in `Math/` or a new sibling directory (e.g., `CodexProofs/`) registered in `lakefile.toml`.

### Submission Pipeline Integration Points

1. **safe_aristotle_submit.py**: Accepts `.txt` files (gap-targeting gate blocks `.lean`). To submit Codex .lean files, either:
   - Use `--force` flag (bypasses gap-targeting gate)
   - Use `Project.create_from_directory()` to submit the entire Lean project
   - Convert Codex output to context files attached to informal submissions

2. **gather_context()** (line 267-314): Auto-gathers prior `.lean` results from tracking.db. Codex output could be stored in results and auto-attached as context to future Aristotle submissions.

3. **aristotle_fetch.py**: Downloads results to `submissions/nu4_final/`. Codex output should go to a separate directory (e.g., `codex_proofs/`).

4. **Aristotle API**: Supports `Project.create_from_directory()` which tars up a Lean project directory. This is the natural integration point for submitting Codex-compiled proofs.

### Tracking Database Schema

Key tables for integration:
- `submissions`: UUID, status, sorry_count, output_file, gap_statement, submission_type
- `failed_approaches`: approach_name, why_failed, learned_insight
- `false_lemmas`: lemma_name, counterexample

New fields or table needed for Codex proof loop:
- Source of proof (codex vs aristotle vs manual)
- Iteration count
- Build log / error history
- Whether the Lean file was submitted to Aristotle as context

### Existing Skills/Commands

| Skill | File | Relevance to Codex Loop |
|-------|------|------------------------|
| `/submit` | `.claude/commands/submit.md` | Delegates to safe_aristotle_submit.py. Rejects .lean files. |
| `/fetch` | `.claude/commands/fetch.md` | Downloads Aristotle results. Could be extended for Codex results. |
| `/audit` | `.claude/commands/audit.md` | Full Lean file audit. Directly usable on Codex output. |
| `/process-result` | `.claude/commands/process-result.md` | Audit + DB update. Extendable for Codex results. |
| `/sketch` | `.claude/commands/sketch.md` | Writes .txt sketches. Not directly relevant. |
| `/debate` | `.claude/commands/debate.md` | Multi-AI debate. Codex already a participant. |
| `/optimize` | `.claude/commands/optimize.md` | Always says "state bare, submit INFORMAL". Needs updating. |

### Hooks

| Hook | File | Impact |
|------|------|--------|
| SessionStart | `context-loader.sh` | Injects gap-targeting reminder. No change needed. |
| PostToolUse | `lean-validator.sh` | Blocks sorry replacement in .lean edits. Important: Codex proof loop should bypass this (Codex iterates its own sorry removal). |

### Results Storage Patterns

- **Aristotle results**: `results_v07/<uuid>/output.lean` (tar.gz extracted)
- **Legacy outputs**: `*-output.lean` files in project root (80+ files, gitignored)
- **Codex analysis**: `codex_results/v{1,2,3}/*.md` (and one `.lean`)
- **Submissions**: `submissions/nu4_final/slot*_result.lean`

## Feasibility Assessment

| Aspect | Assessment | Notes |
|--------|------------|-------|
| Technical Viability | **High** | Codex CLI installed, Lean project configured, `lake build` works. All pieces exist. |
| Effort Estimate | **M** | Core loop script (~200 lines Python), new skill definition, lakefile update, DB migration. |
| Risk Level | **Medium** | Main risks: build times if Mathlib cache is cold; Codex may not produce useful Lean code for hard proofs. |
| Integration Complexity | **Low** | Clear attachment points in existing pipeline. |

### Key Technical Decisions Required

1. **Where do Codex .lean files live?**
   - Option A: `Math/Codex_<problem>.lean` (in main Lean project, compiled by default)
   - Option B: New `CodexProofs/` lean_lib in lakefile.toml (isolated compilation)
   - Option C: Temporary directory, only promoted if they compile

2. **How does Codex output reach Aristotle?**
   - Option A: As `.lean` context files via `--context` flag in safe_aristotle_submit.py
   - Option B: As a full Lean project via `Project.create_from_directory()`
   - Option C: Extracted theorems pasted into informal .txt sketch

3. **Codex sandbox mode?**
   - `workspace-write` (default for --full-auto): can write to project dir
   - `danger-full-access`: can run `lake build` with network (needed for first build)
   - Recommendation: Use `--full-auto` for writing files, then run `lake build` separately (outside sandbox)

4. **Max iterations per proof?**
   - APOLLO uses variable (until budget exhausted)
   - Recommendation: 5 iterations max, then save best attempt with sorries

## Related Specs

| Spec | Relevance | mayNeedUpdate |
|------|-----------|---------------|
| `fix-skill-infrastructure` | **High** -- submit.md skill definition needs update to handle Codex-to-Aristotle flow | true |
| `gap-targeting-pivot` | **High** -- current rules reject .lean submissions. Codex loop produces .lean files. Rules need a "Codex-verified formal" carve-out | true |
| `honest-tooling` | **Medium** -- audit/verdict logic applies to Codex output too | false |
| `math-forge` | **Medium** -- knowledge extraction should index Codex proofs | false |
| `erdos364` | **Low** -- potential test case for Codex proof loop | false |
| `erdos672-evaluation` | **Low** -- potential test case | false |

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| Lean Build | `lake build` | lakefile.toml |
| Lint | Not found | No package.json/Makefile |
| TypeCheck | N/A (Lean type-checks via `lake build`) | -- |
| Unit Test | Not found | No test runner configured |
| Python Scripts | `python3 scripts/<name>.py` | scripts/ directory |
| DB Query | `sqlite3 submissions/tracking.db` | submissions/tracking.db |
| KB Query | `mk search <query>` | math-forge/scripts/mk |

**Local CI**: `lake build` (Lean compilation is the primary quality gate)

## Recommendations for Requirements

1. **Create `scripts/codex_proof_loop.py`** -- Core script that:
   - Takes a problem description + optional context files
   - Prompts Codex to write a Lean 4 proof file
   - Writes the file to a temp directory with lakefile.toml + lean-toolchain
   - Runs `lake build` and captures errors
   - Feeds errors back to Codex for revision
   - Caps at N iterations (configurable, default 5)
   - Saves the best result (fewest sorries) even if not fully compiled

2. **Add `codex_proofs/` directory** for storing Codex-generated Lean files, organized by problem ID.

3. **Add `/codex-prove` skill** (`.claude/commands/codex-prove.md`) that orchestrates the loop and integrates with existing pipeline.

4. **Extend `safe_aristotle_submit.py`** to support `--codex-context <file.lean>` for attaching Codex proofs as context to informal submissions.

5. **Do NOT change the gap-targeting gate** for the Codex loop itself. Instead, the Codex proof loop is a pre-Aristotle step:
   - Codex produces a `.lean` file (may have sorries)
   - The `.lean` file becomes *context* for an informal Aristotle submission
   - Aristotle still receives a bare-gap `.txt` sketch + Codex `.lean` as supporting context
   - This preserves the gap-targeting philosophy while leveraging Codex's Lean output

6. **Track Codex iterations in DB** -- new `codex_iterations` table or extend `submissions` with `source='codex'` and `iteration_count`.

7. **Use isolated Lean project for Codex** -- don't pollute the main `Math/` dir. Create a temp Lean project per problem with:
   - Symlinked `lean-toolchain`
   - Fresh `lakefile.toml` pointing to Mathlib
   - Single `.lean` file for the proof
   - This avoids interfering with the main project and allows parallel runs

8. **Leverage existing Aristotle `Project.create_from_directory()`** for submitting Codex-verified Lean projects directly to Aristotle for sorry-filling.

## Open Questions

- What is the cold-start time for `lake build` with Mathlib on this machine? (Could be 30+ min if `.lake/` cache is missing)
- Does Codex (gpt-5.3-codex) have good Lean 4 + Mathlib training data? The one existing `.lean` file in codex_results suggests limited prior use.
- Should the Codex proof loop run in the main project directory or in isolated temp directories?
- How should Codex-generated proofs that compile clean be celebrated vs. Aristotle results? (The CLAUDE.md rule "compiled clean != resolved the gap" applies here too.)
- Should we use Codex Cloud tasks for longer-running proof attempts?

## Sources

- [Codex CLI reference](https://developers.openai.com/codex/cli/reference)
- [Codex CLI features](https://developers.openai.com/codex/cli/features)
- [GPT-5.3-Codex docs](https://developers.openai.com/api/docs/models/gpt-5.3-codex)
- [Codex CLI guide](https://blakecrosley.com/guides/codex)
- [Codex sandbox/approvals](https://developers.openai.com/codex/agent-approvals-security/)
- [APOLLO: Automated LLM and Lean Collaboration](https://arxiv.org/html/2505.05758v1)
- [Agentic Proof Automation](https://arxiv.org/pdf/2601.03768)
- [lean4-skills GitHub](https://github.com/cameronfreer/lean4-skills)
- [Lake Build System docs](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- `/Users/patrickkavanagh/math/lakefile.toml` -- project Lean config
- `/Users/patrickkavanagh/math/lean-toolchain` -- Lean v4.24.0
- `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` -- submission pipeline
- `/Users/patrickkavanagh/math/scripts/aristotle_fetch.py` -- result fetching
- `/Users/patrickkavanagh/math/scripts/debate.py` -- existing Codex integration
- `/Users/patrickkavanagh/math/.claude/commands/*.md` -- all skill definitions
- `/Users/patrickkavanagh/math/math-forge/` -- knowledge base CLI and hooks
- `/Users/patrickkavanagh/math/codex_results/` -- existing Codex output
- `/Users/patrickkavanagh/math/Aristotle Agent README.md` -- Aristotle API reference
- `/Users/patrickkavanagh/math/submissions/tracking.db` -- full schema
- `~/.codex/config.toml` -- Codex CLI configuration
