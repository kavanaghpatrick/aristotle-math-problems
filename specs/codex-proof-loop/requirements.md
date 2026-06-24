# Requirements: Codex Proof Loop

## Goal

Add a compile-fix loop where Codex (gpt-5.3-codex) writes Lean 4 proofs, iterates against `lake build` until compilation succeeds (or max iterations), and feeds results into the existing Aristotle pipeline as formal context. This creates a parallel proof path that leverages Codex's mathematical reasoning while preserving the gap-targeting philosophy.

## User Stories

### US-1: Run a Codex Proof Loop

**As a** mathematician using the pipeline
**I want to** give a problem description and get back a Lean 4 proof attempt that has been iterated against the compiler
**So that** I get machine-verified Lean code instead of uncompiled markdown analysis

**Acceptance Criteria:**
- [ ] AC-1.1: Script accepts a problem description (string or .txt file) and optional .lean context files
- [ ] AC-1.2: Codex generates a Lean 4 file targeting the problem
- [ ] AC-1.3: `lake build` runs against the generated file and captures stdout/stderr
- [ ] AC-1.4: On build failure, Lean error messages are fed back to Codex for revision
- [ ] AC-1.5: Loop terminates on successful compilation OR after max iterations (default 5)
- [ ] AC-1.6: Best result (fewest sorries) is saved even if no iteration fully compiles
- [ ] AC-1.7: Total wall-clock time is logged

### US-2: Isolated Build Environment

**As a** pipeline operator
**I want to** Codex proof attempts to build in isolation from the main `Math/` directory
**So that** failed experiments don't pollute the main Lean project or break other builds

**Acceptance Criteria:**
- [ ] AC-2.1: Each proof attempt uses a temporary Lean project directory
- [ ] AC-2.2: Temp project has its own `lakefile.toml` pointing to same Mathlib version (v4.24.0)
- [ ] AC-2.3: Temp project symlinks or copies `lean-toolchain` from main project
- [ ] AC-2.4: Temp project symlinks `.lake/packages/` from main project to avoid cold Mathlib rebuild
- [ ] AC-2.5: Multiple proof loops can run in parallel without interference
- [ ] AC-2.6: Temp directories are cleaned up after results are saved (configurable retain for debugging)

### US-3: Result Storage

**As a** mathematician
**I want to** Codex proof results stored persistently with metadata
**So that** I can review attempts, track progress, and reuse successful proofs

**Acceptance Criteria:**
- [ ] AC-3.1: Results saved to `codex_proofs/<problem_id>/` directory
- [ ] AC-3.2: Each attempt saves: final `.lean` file, metadata JSON, build log
- [ ] AC-3.3: Metadata includes: problem_id, iteration_count, sorry_count, compiled (bool), timestamp, codex_model, wall_time_seconds
- [ ] AC-3.4: Best attempt (fewest sorries, compiles) is symlinked as `best.lean`
- [ ] AC-3.5: Previous attempts are preserved, not overwritten

### US-4: Context Bridging to Aristotle

**As a** mathematician
**I want to** feed a Codex-compiled .lean file as context to an Aristotle informal submission
**So that** Aristotle can build on Codex's verified partial proofs to resolve remaining gaps

**Acceptance Criteria:**
- [ ] AC-4.1: Codex .lean output can be passed via `--context` flag to `safe_aristotle_submit.py`
- [ ] AC-4.2: The gap-targeting gate is NOT modified -- informal .txt sketch is still required
- [ ] AC-4.3: Codex .lean context is bundled into the tar.gz alongside auto-gathered prior results
- [ ] AC-4.4: A convenience flag (e.g., `--codex-context <problem_id>`) auto-locates the best Codex proof for a problem

### US-5: Tracking DB Integration

**As a** pipeline operator
**I want to** Codex proof attempts tracked in the database
**So that** I can query history, avoid duplicate work, and correlate Codex + Aristotle attempts

**Acceptance Criteria:**
- [ ] AC-5.1: New `codex_proofs` table: id, problem_id, created_at, iterations, sorry_count, compiled, model, wall_time_seconds, lean_file, build_log, promoted_to_aristotle
- [ ] AC-5.2: Each completed proof loop creates one DB row
- [ ] AC-5.3: `mk codex <problem_id>` queries Codex proof history for a problem
- [ ] AC-5.4: `mk codex-best <problem_id>` returns path to best compiled proof
- [ ] AC-5.5: When a Codex proof is submitted as Aristotle context, `promoted_to_aristotle` is set to the Aristotle submission UUID

### US-6: `/codex-prove` Skill

**As a** Claude Code user
**I want to** a `/codex-prove` slash command that orchestrates the full loop
**So that** I can trigger proof attempts conversationally without remembering script arguments

**Acceptance Criteria:**
- [ ] AC-6.1: `/codex-prove <problem_description>` runs the full loop
- [ ] AC-6.2: `/codex-prove <problem_description> --context <file.lean>` passes existing Lean as seed context
- [ ] AC-6.3: Skill reports progress: iteration number, build status, sorry count per iteration
- [ ] AC-6.4: On completion, displays: verdict (compiled/partial/failed), sorry count, file path, suggested next action
- [ ] AC-6.5: Suggested next action includes `/submit` command with `--context` pointing to the Codex result

### US-7: Audit Integration

**As a** mathematician
**I want to** audit Codex-produced .lean files with the existing `/audit` skill
**So that** I get the same rigorous verification (sorry, axiom, false-lemma checks) as Aristotle results

**Acceptance Criteria:**
- [ ] AC-7.1: `/audit <codex_proofs/problem_id/best.lean>` works with no changes to audit skill
- [ ] AC-7.2: Audit output identifies source as "codex" (vs "aristotle") if detectable from path
- [ ] AC-7.3: Audit verdict updates `codex_proofs` table (not `submissions` table) when file is from `codex_proofs/`

### US-8: Sorry-Targeting

**As a** mathematician
**I want to** extract remaining `sorry`s from a Codex proof as targeted sub-problems
**So that** I can submit each sorry as a focused gap for another Codex round or Aristotle

**Acceptance Criteria:**
- [ ] AC-8.1: Script extracts each `sorry` with its surrounding theorem/lemma context
- [ ] AC-8.2: Each sorry generates a standalone sub-problem file (Lean statement + sorry)
- [ ] AC-8.3: Sub-problems can be fed back into the proof loop (`--sorry-target` mode)
- [ ] AC-8.4: Sub-problems can be converted to informal .txt sketches for Aristotle submission
- [ ] AC-8.5: Parent-child relationship tracked in DB (parent_proof_id on sub-problem rows)

## Functional Requirements

| ID | Requirement | Priority | Acceptance Criteria |
|----|-------------|----------|---------------------|
| FR-1 | `scripts/codex_proof_loop.py` -- core loop script | High | Runs end-to-end: prompt -> Codex -> lake build -> error feedback -> iterate |
| FR-2 | Isolated temp Lean project per proof attempt | High | Symlinks `.lake/packages/`, independent `lakefile.toml`, no main project pollution |
| FR-3 | Structured error feedback to Codex | High | Lean compiler errors parsed, formatted, sent as revision prompt with prior code |
| FR-4 | Sorry counting on each iteration | High | Count `sorry` occurrences (excluding comments), reject iterations that increase sorry count vs prior best |
| FR-5 | `codex_proofs/` result directory | High | Organized by problem_id, preserves all attempts with metadata |
| FR-6 | `codex_proofs` DB table + migration | High | Schema as in AC-5.1, created via SQL migration script |
| FR-7 | `/codex-prove` skill definition | Medium | `.claude/commands/codex-prove.md` following existing skill patterns |
| FR-8 | `--codex-context` flag on `safe_aristotle_submit.py` | Medium | Auto-locates best Codex proof, adds to context bundle |
| FR-9 | Sorry extraction + sub-problem generation | Medium | Parse .lean, extract sorry blocks, generate standalone files |
| FR-10 | `mk codex` / `mk codex-best` CLI commands | Low | Query helpers for Codex proof history |
| FR-11 | Theorem statement locking | High | Codex prompt instructs: "Do NOT change the theorem statement. Only fill the proof." Validator checks statement unchanged between iterations |
| FR-12 | Configurable max iterations | Medium | Default 5, override via `--max-iterations N` flag |
| FR-13 | Build timeout per iteration | Medium | Default 300s per `lake build`, override via `--build-timeout N` |

## Non-Functional Requirements

| ID | Requirement | Metric | Target |
|----|-------------|--------|--------|
| NFR-1 | Incremental build time | Wall-clock per iteration | < 60s (assuming warm Mathlib cache) |
| NFR-2 | Codex API latency | Response time per call | < 120s (depends on model/reasoning effort) |
| NFR-3 | Disk usage | Per proof attempt | < 50MB (excluding shared .lake/ symlink) |
| NFR-4 | Parallelism | Concurrent proof loops | >= 2 independent loops without conflict |
| NFR-5 | Reliability | Script crash recovery | Partial results saved before exit; temp dirs cleaned on SIGINT |
| NFR-6 | Observability | Progress logging | Each iteration logs: iteration#, build result, sorry delta, wall time |

## Glossary

- **Proof Loop**: Cycle of [Codex generates .lean] -> [lake build] -> [error feedback] -> [Codex revises] repeated until success or max iterations
- **Sorry**: Lean 4 placeholder (`sorry`) marking an unproven obligation. Fewer sorries = more complete proof
- **Warm Cache**: `.lake/packages/` already contains compiled Mathlib. Incremental builds take seconds instead of 30+ minutes
- **Gap-Targeting Gate**: Existing validation in `safe_aristotle_submit.py` that rejects .lean files and proof-strategy-laden sketches. NOT modified by this feature
- **Context Bridging**: Using Codex .lean output as `--context` file for an Aristotle informal submission
- **Theorem Statement Locking**: Ensuring Codex doesn't change the theorem statement to make it trivially provable
- **Promoted**: A Codex proof that has been submitted to Aristotle as context (tracked via `promoted_to_aristotle` field)

## Out of Scope

- Modifying the gap-targeting gate to accept .lean files directly
- Building a UI/IDE integration for the proof loop
- Codex Cloud tasks (long-running remote execution) -- future enhancement
- Auto-submission to Aristotle (always requires explicit user action)
- Lean 4 LSP integration for richer error context
- Multi-file Lean proofs (one .lean file per proof loop)
- Custom Mathlib version per proof attempt
- Codex cost tracking / budget limits
- Replacing Aristotle with Codex -- this is a complementary path

## Dependencies

- **Codex CLI v0.107.0+**: Already installed. Must support `codex exec --full-auto`
- **Lean 4.24.0 + Mathlib**: Already configured. `.lake/packages/` must be warm (Mathlib compiled)
- **`safe_aristotle_submit.py`**: Existing script, extended with `--codex-context` flag
- **`submissions/tracking.db`**: Existing DB, extended with `codex_proofs` table
- **`math-forge` CLI (`mk`)**: Extended with `codex` / `codex-best` subcommands
- **OpenAI API key**: Must be configured for Codex CLI (already set up)

## Architecture Decision: Codex Invocation Model

The script runs `codex exec --full-auto` **for file generation only**, then runs `lake build` **separately outside the Codex sandbox**. This avoids sandbox permission issues with `lake build` (which needs network on first run) and gives the script full control over the build-feedback loop.

```
codex_proof_loop.py orchestrates:
  1. Build prompt (problem + context + prior errors)
  2. codex exec --full-auto --sandbox workspace-write "write proof to output.lean"
  3. Copy output.lean to temp Lean project
  4. lake build (outside sandbox, full system access)
  5. Parse errors -> go to step 1 (or save best result)
```

## Success Criteria

- A complete proof loop runs end-to-end: problem in, compiled .lean out (or best-effort with sorry count)
- At least one Codex-compiled proof is successfully used as Aristotle context (context bridging works)
- The loop correctly identifies and saves the best attempt across iterations
- Sorry count decreases (or stays equal) across iterations -- no sorry inflation
- Existing pipeline (informal .txt -> Aristotle) is completely unaffected

## Next Steps

1. Approve these requirements
2. Generate implementation plan (task breakdown)
3. Implement `scripts/codex_proof_loop.py` (FR-1, FR-2, FR-3, FR-4, FR-11)
4. Create `codex_proofs/` directory structure and DB migration (FR-5, FR-6)
5. Create `/codex-prove` skill (FR-7)
6. Extend `safe_aristotle_submit.py` with `--codex-context` (FR-8)
7. Implement sorry extraction (FR-9)
8. Extend `mk` CLI (FR-10)
