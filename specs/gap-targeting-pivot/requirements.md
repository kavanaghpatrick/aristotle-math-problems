# Requirements: Gap-Targeting Pivot

## Goal

Rewrite all project scaffolding (docs, skills, pipeline scripts, hooks, schema) to enforce gap-targeting ONLY. Every Aristotle submission must target the actual open gap of an unsolved problem -- bare conjecture statement, zero proof guidance, with accumulated prior Aristotle results as context. Hard-block anything else.

## Design Decisions (from interview + research)

| Question | Decision | Rationale |
|----------|----------|-----------|
| Sketch length enforcement | Pattern-based + 30-line cap | Bare conjecture = ~5-15 lines. 30 allows some slack for formal statement + status notes. Pattern detection catches "Proof Strategy" / "Key Lemma" sections regardless of length. |
| Falsification | Allowed as gap-targeting | "Is this gap real?" is a valid question about the gap. Tag as `submission_type=falsification`. |
| Bounded verification | NOT allowed unless bound IS the conjecture | "Prove for n < 10000" is infrastructure, not gap resolution. Exception: if the open conjecture itself is bounded (e.g., "verified to N"). |
| Context auto-attachment | Auto-detect from DB | `mk context <problem_id>` gathers all prior `_result.lean` files. Submit auto-attaches them. No manual `--context` needed. |
| Sub-cases | Only if the sub-case IS an open problem | "Grimm's conjecture for k=3" allowed only if k=3 is itself an open problem. "Full conjecture only" as default. |
| Override mechanism | None | No `--force`, no `--skip-gap-check`. Hard block is hard. |

## User Stories

### US-1: Bare Conjecture Submission
**As a** mathematician using the pipeline
**I want to** submit only the bare open gap statement to Aristotle
**So that** Aristotle finds its own proof path without being constrained by my (often wrong) strategy suggestions

**Acceptance Criteria:**
- [ ] AC-1.1: Sketch template produces files of <=30 lines containing only: problem name, conjecture statement (English + Lean), and open status
- [ ] AC-1.2: No "Proof Strategy", "Key Lemmas", "Proposed Approach", or "Main Proof Assembly" sections in generated sketches
- [ ] AC-1.3: Prior Aristotle results for the same problem are auto-attached as context files via `context_file_paths`
- [ ] AC-1.4: Sketch workflow completes in <5 minutes (identify gap, state it, submit)

### US-2: Hard Block on Non-Gap Submissions
**As a** project maintainer
**I want** the submit pipeline to refuse any submission not targeting an open gap
**So that** zero slots are wasted on infrastructure, known results, or bounded verification of known things

**Acceptance Criteria:**
- [ ] AC-2.1: `safe_aristotle_submit.py` rejects .txt files >30 lines with clear error message
- [ ] AC-2.2: `safe_aristotle_submit.py` rejects .txt files containing strategy keywords: "Proof Strategy", "Key Lemma", "APPROACH", "Main Proof", "Proposed Strategy"
- [ ] AC-2.3: `safe_aristotle_submit.py` rejects ALL .lean file submissions (gap-targeting = INFORMAL only)
- [ ] AC-2.4: No override flag exists -- rejection is final
- [ ] AC-2.5: Falsification submissions pass the gate (tagged `submission_type=falsification`)
- [ ] AC-2.6: Error messages explain WHY the submission was rejected and HOW to fix it

### US-3: Accumulated Context Passing
**As a** mathematician iterating on an open problem
**I want** prior Aristotle results to be automatically passed as context
**So that** Aristotle builds on its own prior work without me hand-curating proof strategies

**Acceptance Criteria:**
- [ ] AC-3.1: New `mk context <problem_id>` command lists all `_result.lean` files for a problem
- [ ] AC-3.2: Submit command auto-detects problem ID from sketch filename/content
- [ ] AC-3.3: All matching `_result.lean` files passed via `context_file_paths` parameter to `prove_from_file()`
- [ ] AC-3.4: Context attachment logged in submission DB record
- [ ] AC-3.5: Works when zero prior results exist (no context, no error)

### US-4: Gap-Targeting Philosophy in All Docs
**As a** new session of Claude starting work
**I want** every document and skill to reinforce gap-targeting philosophy
**So that** no session drifts into known-result formalization or proof-strategy hand-holding

**Acceptance Criteria:**
- [ ] AC-4.1: CLAUDE.md rewritten: single-phase pipeline (GAP -> SUBMIT), no Tracks B/C/D, no IDEATE phase, no case studies of known-result work
- [ ] AC-4.2: MEMORY.md simplified: gap-targeting mandate, remove old track record of known-math formalizations
- [ ] AC-4.3: All 11 command skills rewritten with gap-targeting philosophy; zero references to "Track D", "known result formalization", or "proof strategy development"
- [ ] AC-4.4: Session-start hook injects gap-targeting reminder into every session briefing
- [ ] AC-4.5: Lean-validator hook warns when .txt sketches contain proof-strategy patterns

### US-5: Gap Resolution Tracking
**As a** mathematician reviewing results
**I want** to see whether a result actually resolved the open gap (not just "compiled clean")
**So that** I can distinguish real progress from infrastructure

**Acceptance Criteria:**
- [ ] AC-5.1: `gap_statement TEXT` column added to tracking.db submissions table
- [ ] AC-5.2: `submission_type TEXT` column added (values: `gap_targeting`, `falsification`)
- [ ] AC-5.3: `targets_open_gap INTEGER DEFAULT 0` column added to knowledge.db findings table
- [ ] AC-5.4: Fetch/process-result commands assess whether result resolved the stated gap
- [ ] AC-5.5: `mk gaps` command lists all open gaps being targeted with status and prior results

### US-6: Skill Rewrites
**As a** user invoking pipeline commands
**I want** every skill to enforce gap-targeting behavior
**So that** the old IDEATE/multi-track workflow is impossible to accidentally use

**Acceptance Criteria:**
- [ ] AC-6.1: `sketch.md` generates bare-gap sketches only (no research phase, no strategy sections, no computational exploration)
- [ ] AC-6.2: `submit.md` runs gap-targeting gate before all other checks
- [ ] AC-6.3: `sweep.md` has single tier: open-gap candidates. No Tier B/C/D.
- [ ] AC-6.4: `screen.md` is binary: OPEN (submit) vs SKIP (not open). No scoring.
- [ ] AC-6.5: `screen-batch.md` is binary: OPEN vs SKIP. No tier system.
- [ ] AC-6.6: `optimize.md` always recommends: "State the gap bare, submit INFORMAL"
- [ ] AC-6.7: `audit.md` replaces "FIRST-EVER/EXTENSION/RE-PROOF" novelty with gap-resolution assessment
- [ ] AC-6.8: `fetch.md` and `process-result.md` add `target_resolved` assessment to audit
- [ ] AC-6.9: `debate.md` focuses debates on identifying the exact open gap, not proof strategies
- [ ] AC-6.10: `status.md` unchanged (pure status check)
- [ ] AC-6.11: Math-forge skills (`open-problems.md`, `number-theory.md`) query KB for prior results only, not strategies
- [ ] AC-6.12: `proof-strategies.md` removed or converted to "prior results" skill

## Functional Requirements

| ID | Requirement | Priority | Acceptance Criteria |
|----|-------------|----------|---------------------|
| FR-1 | `check_gap_targeting()` function in safe_aristotle_submit.py | High | Rejects >30 line .txt, strategy keywords, all .lean. No override. Unit-testable. |
| FR-2 | Bare-gap sketch template in sketch.md | High | <=30 lines: problem name, English statement, Lean statement, open status. Nothing else. |
| FR-3 | Auto-context attachment in submit pipeline | High | Queries DB for problem_id, finds `_result.lean` files, passes to `context_file_paths`. |
| FR-4 | `mk context <problem_id>` CLI command | High | Lists result files for a problem. Outputs paths suitable for context_file_paths. |
| FR-5 | `mk gaps` CLI command | Medium | Lists open gaps being targeted, with gap_statement, submission count, latest result status. |
| FR-6 | CLAUDE.md full rewrite | High | Single-phase pipeline. Gap-targeting only. ~100 lines (down from 273). |
| FR-7 | MEMORY.md simplification | High | Gap-targeting mandate. Remove historical known-math track record. ~50 lines. |
| FR-8 | All 11 command skills rewritten | High | Gap-targeting philosophy in every skill. Zero Track D references. |
| FR-9 | 3 math-forge skills rewritten/removed | Medium | `proof-strategies.md` removed. Others query KB for prior results only. |
| FR-10 | Session-start hook gap-targeting reminder | Medium | Inject reminder text into briefing. |
| FR-11 | Lean-validator hook sketch validation | Medium | Warn on strategy patterns in .txt writes. Requires hooks.json update for .txt. |
| FR-12 | tracking.db schema migration | Medium | Add `gap_statement TEXT`, `submission_type TEXT`. Non-breaking ALTER TABLE. |
| FR-13 | knowledge.db schema migration | Low | Add `targets_open_gap` column. finding_type CHECK constraint needs table recreation for `gap_progress` type. |
| FR-14 | Fetch/process-result gap assessment | Medium | target_resolved classification in result processing. |
| FR-15 | BATS tests updated | Medium | All 32 existing tests pass. New tests for gap-targeting gate, mk context, mk gaps. |

## Non-Functional Requirements

| ID | Requirement | Metric | Target |
|----|-------------|--------|--------|
| NFR-1 | Sketch generation speed | Wall clock time | <5 min per sketch (down from 15-30 min with research/IDEATE phase) |
| NFR-2 | Submit gate latency | Added time per submit | <2 sec for check_gap_targeting() |
| NFR-3 | No disruption to in-flight jobs | Existing slot646-650+ | Zero impact on fetching/processing existing results |
| NFR-4 | BATS test suite | Pass rate | 100% after all changes |
| NFR-5 | Context auto-attachment | Reliability | Works with 0, 1, or N prior results. No errors. |
| NFR-6 | Doc size reduction | CLAUDE.md line count | <=120 lines (from 273) |

## File Inventory (implementation scope)

### Tier 1: Philosophy Docs (2 files)
| File | Action | Priority |
|------|--------|----------|
| `/Users/patrickkavanagh/math/CLAUDE.md` | Full rewrite | High |
| `/Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md` | Simplify | High |

### Tier 2: Command Skills (11 files)
| File | Action | Priority |
|------|--------|----------|
| `/Users/patrickkavanagh/math/.claude/commands/sketch.md` | Major rewrite | High |
| `/Users/patrickkavanagh/math/.claude/commands/submit.md` | Add hard block | High |
| `/Users/patrickkavanagh/math/.claude/commands/sweep.md` | Major rewrite | High |
| `/Users/patrickkavanagh/math/.claude/commands/screen.md` | Simplify | Medium |
| `/Users/patrickkavanagh/math/.claude/commands/screen-batch.md` | Simplify | Medium |
| `/Users/patrickkavanagh/math/.claude/commands/fetch.md` | Add gap assessment | Medium |
| `/Users/patrickkavanagh/math/.claude/commands/audit.md` | Reframe novelty | Medium |
| `/Users/patrickkavanagh/math/.claude/commands/process-result.md` | Add gap assessment | Medium |
| `/Users/patrickkavanagh/math/.claude/commands/optimize.md` | Simplify | Low |
| `/Users/patrickkavanagh/math/.claude/commands/debate.md` | Minor update | Low |
| `/Users/patrickkavanagh/math/.claude/commands/status.md` | No change | -- |

### Tier 3: Math-Forge Skills (3 files)
| File | Action | Priority |
|------|--------|----------|
| `/Users/patrickkavanagh/math/math-forge/skills/open-problems.md` | Rewrite | Medium |
| `/Users/patrickkavanagh/math/math-forge/skills/number-theory.md` | Minor rewrite | Medium |
| `/Users/patrickkavanagh/math/math-forge/skills/proof-strategies.md` | Remove or gut | Medium |

### Tier 4: Hook Scripts (3 files)
| File | Action | Priority |
|------|--------|----------|
| `/Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh` | Add reminder | Medium |
| `/Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh` | Add sketch validation | Medium |
| `/Users/patrickkavanagh/math/math-forge/hooks/hooks.json` | Update triggers for .txt | Medium |

### Tier 5: Pipeline Scripts (3 files)
| File | Action | Priority |
|------|--------|----------|
| `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` | Add `check_gap_targeting()` | High |
| `/Users/patrickkavanagh/math/scripts/aristotle_fetch.py` | Add `target_resolved` | Medium |
| `/Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py` | Add `gap_progress` type | Low |

### Tier 6: CLI (1 file)
| File | Action | Priority |
|------|--------|----------|
| `/Users/patrickkavanagh/math/math-forge/scripts/mk` | Add `gaps`, `context` commands | Medium |

### Tier 7: DB Schema (2 files)
| File | Action | Priority |
|------|--------|----------|
| `submissions/tracking.db` | ALTER TABLE: add columns | Medium |
| `math-forge/data/schema.sql` | Add columns, recreate table for CHECK | Low |

## Glossary

- **Open gap**: The unsolved conjecture itself -- not a sub-lemma, not a bounded case, not a known reduction
- **Bare conjecture**: A sketch containing only the problem name, English statement, Lean formal statement, and open status. No proof strategy.
- **Gap-targeting**: Submitting work that directly targets closing an open gap
- **Accumulated context**: Prior Aristotle `_result.lean` files for the same problem, passed via `context_file_paths`
- **Hard block**: A submission gate with no override mechanism
- **Falsification**: Submitting to test whether a conjecture is false (valid gap-targeting: "is this gap real?")
- **Infrastructure**: Sub-lemmas, bounded cases, scaffolding that doesn't directly resolve the open gap
- **target_resolved**: Boolean flag on a result indicating whether it resolved the stated open gap

## Out of Scope

- Changing the Aristotle API or `aristotlelib` library
- Modifying the `submissions/tracking.db` submissions table structure beyond adding columns (no table recreation)
- Changing how Aristotle processes submissions (INFORMAL/FORMAL modes unchanged)
- Rewriting `debate.py`, `screen_formal_conjectures.py`, or other utility scripts (only the pipeline-critical scripts)
- Retroactively reclassifying past submissions
- Changing the math-forge plugin.json or settings.json
- CI/CD setup (no CI exists; BATS tests are the quality gate)

## Dependencies

- `honest-tooling` spec changes to `aristotle_fetch.py`, `safe_aristotle_submit.py`, and `mk` must be merged first (or changes must be compatible)
- `math-forge` spec wiring (hooks, KB integration) must be in place -- the gap-targeting pivot modifies WHAT flows through the pipeline, not the pipeline plumbing
- SQLite ALTER TABLE works for adding columns but cannot modify CHECK constraints -- knowledge.db `finding_type` expansion requires table recreation migration

## Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| BATS test failures from skill/hook rewrites | Medium | Run `bats math-forge/tests/` after each file change |
| In-flight submissions disrupted | High | Only apply new rules to future submissions. Fetch/process-result for existing slots unchanged. |
| Sketch validation false positives | Medium | Pattern matching + line count is heuristic. Tune keywords list during implementation. No override by design. |
| knowledge.db CHECK constraint migration | Low | Standard SQLite pattern: create new table, copy data, drop old, rename. Or defer to separate task. |
| Context auto-attachment picks wrong files | Low | Match on problem_id field. If ambiguous, attach nothing (safe default). |

## Success Criteria

- Zero submissions of known results or infrastructure after pivot is deployed
- Every sketch file is <=30 lines
- Every submission has a `gap_statement` recorded in DB
- `safe_aristotle_submit.py` blocks 100% of non-gap .lean and strategy-heavy .txt submissions
- All 32+ BATS tests pass
- Session-start briefing contains gap-targeting reminder
- `mk gaps` and `mk context` commands functional

## Unresolved Questions

- Exact keyword list for strategy detection in `check_gap_targeting()` -- needs tuning during implementation. Starting set: "Proof Strategy", "Key Lemma", "APPROACH", "Main Proof", "Proposed Strategy", "by induction", "by contradiction", "using CRT". May need expansion.
- Whether `context_file_paths` in aristotlelib accepts multiple files or a single file -- needs API verification before implementing auto-context.
- How to classify `target_resolved` automatically -- likely needs human review. Could add a prompt in `process-result` that asks the user.

## Implementation Order

1. **Philosophy docs** (CLAUDE.md, MEMORY.md) -- sets the frame for everything else
2. **Core skills** (sketch.md, submit.md, sweep.md) -- the main workflow
3. **Pipeline hard block** (safe_aristotle_submit.py `check_gap_targeting()`) -- enforcement
4. **Context commands** (mk context, mk gaps, auto-attachment in submit)
5. **Schema changes** (tracking.db columns, knowledge.db migration)
6. **Remaining skills** (screen, audit, fetch, process-result, optimize, debate, math-forge skills)
7. **Hooks** (context-loader.sh reminder, lean-validator.sh sketch check, hooks.json)
8. **Tests** (BATS updates, new tests for gap-targeting gate)
