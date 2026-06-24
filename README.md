# math-forge

An automated research harness for solving open mathematical problems. We identify unsolved conjectures, state them as bare targets, and submit them to [Aristotle](https://aristotle.harmonic.fun) (Harmonic AI's hybrid theorem prover) for autonomous proof construction — then feed results back as context for the next attempt.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4-purple)](https://lean-lang.org/)

**~1,265 submissions | 577 distinct problems | 0 genuine gap resolutions | 604 knowledge-base findings | ~18 months of operation (Dec 2024 – Jun 2026)**

---

## Honest Track Record (measured, June 2026)

This project's first principle is that **"compiled clean" is not "solved."** That principle is borne out by the live database, so we state the result plainly up front:

> **Of ~1,265 submissions, 0 have reached `compiled_advance` and 0 have `target_resolved=1`. No open gap has ever been closed by this harness.**

Outcome breakdown (from `submissions/tracking.db`, the source of truth):

| Status | Count | Meaning |
|--------|------:|---------|
| `compiled_no_advance` | 814 | Compiled clean, but the target conjecture was not resolved |
| `compile_failed` | 300 | Aristotle returned Lean that fails `lake build` |
| `compiled_partial` | 137 | Compiles but has residual `sorry`/`axiom` |
| `disproven` | 8 | Aristotle returned a verified counterexample (valid falsifications) |
| `submitted` | 6 | In-flight, not yet returned |
| `compiled_advance` | **0** | Genuinely advanced the target (opt-in, never awarded) |

This is consistent with the project's own ~0.8% calibrated hit rate on the hard Erdős long tail, and with Terence Tao's "lowest hanging fruit" framing: the AI sweet spot is the easy tail, and deep open problems should be expected to return 0%. The single most significant genuine *partial* result the project has produced — a machine-verified novel inequality/onset lemma on Erdős 124 ("Lemma A") — is documented honestly in [Notable Results](#notable-results--the-actual-math) and is **not** a conjecture resolution.

The codebase's strongest cultural asset is this honesty. The verification gauntlet, the audit downgrade pass, the cross-model adversary, and the canonical status enum all exist specifically to keep us from claiming a solve we don't have.

---

## The Idea

We don't write proofs. We don't develop proof strategies. We state the open gap and let Aristotle find the path.

The critical insight is **compounding context**: when Aristotle works on a problem and produces partial results (structural lemmas, bounds, reductions), those results are automatically attached as context on the next submission. Submission N+1 builds on everything Aristotle produced in submission N. Over repeated iterations, the prover accumulates a growing body of results to draw on.

### How Aristotle Actually Works

Aristotle is built by **Harmonic AI** (co-founded by Vlad Tenev), **not** Anthropic. Endpoint: `https://aristotle.harmonic.fun`; SDK: `aristotlelib` (currently 2.x). It is a **hybrid solver-formalizer**, not a pure formalizer, with three subsystems (per arXiv:2510.01346):

1. **Monte Carlo Graph Search (MCGS)** — a 200B+ parameter transformer used as policy + value function over Lean proof states. This is the formalizer that fires on **bare** submissions.
2. **Lemma-based informal reasoner** — natural-language proof generation, lemma decomposition, autoformalization, and a Lean REPL feedback loop. This subsystem fires only when given an **informal** prompt or paired with a strategy dossier (the FUSION / INFORMAL lanes).
3. **Yuclid geometry solver** — an AlphaGeometry-style plane-geometry engine.

Aristotle also performs **Test-Time Training (TTT)**: mid-attempt it retrains on search traces from failed attempts, so it can learn during a single submission.

**Honesty caveat (Igor Rivin):** Aristotle proves ~97.6% of the theorems it attempts, but only ~67% are *semantically correct* — it can "prove the wrong theorem a third of the time, fluently and confidently." This is the entire reason `scripts/audit_proven.py` and the verification gauntlet exist: every clean compile is treated as suspect until audited for what it actually proved.

> Documented external Aristotle results (not produced by this harness) include E124 (Alexeev, informal mode), E728 (paired with GPT-5.2 Pro, the first Erdős problem fully resolved by an AI system, per arXiv:2601.07421), and E481 (Barreto). Our own self-audit (`analysis/ai_math_solves_vs_our_process.md`) reclassifies several of these as retrieval/formalization rather than novel solves; read it before treating any of them as breakthroughs.

---

## Workflow

```
SCREEN  →  SKETCH  →  SUBMIT  →  FETCH  →  ITERATE
  │           │          │          │          │
  │           │          │          │          └─ Prior results become
  │           │          │          │             context for next run
  │           │          │          │
  │           │          │          └─ Download .lean result, audit for
  │           │          │             gap resolution (regex + gauntlet)
  │           │          │
  │           │          └─ Gap-targeting gate enforced, lane auto-routed,
  │           │             auto-context attached, submit INFORMAL
  │           │
  │           └─ State the conjecture in ≤30 lines,
  │              bare theorem statement + sorry
  │
  └─ Is this problem genuinely open?
     Check DB for prior attempts and false lemmas
```

### Screening

Before sketching, check whether the problem is genuinely open and whether we've already tried (and failed) approaches against it:

```bash
mk failed <keywords>     # Dead ends — what's been disproven
mk context <problem_id>  # What Aristotle has already produced
```

The `false_lemmas` and `failed_approaches` tables prevent re-submitting against known dead ends.

### Sketching

A sketch is a minimal informal statement of an open conjecture — nothing more:

```
OPEN GAP: [Problem Name]
Source: [reference]
Domain: [nt / algebra / combinatorics / analysis]

[1-3 sentence English statement of the unsolved conjecture]

theorem problem_name (vars : Types) : conclusion := by sorry

Status: OPEN. [One sentence on what's known]
```

No proof strategy. No key lemmas. No suggested approaches. The sketch states *what* to prove, never *how*. (Strategy, when we have it, lives in a companion JSON file — never in the `.txt`.)

---

## The Four Lanes

Every submission belongs to a lane. All four are **INFORMAL `.txt`** (no `.lean` is ever submitted); they differ in what companion metadata accompanies the bare sketch and which Aristotle subsystem they engage.

| Lane | Companion | Aristotle subsystem | CLI flag |
|------|-----------|---------------------|----------|
| **bare** (default) | none | MCGS formalizer only | *(auto)* |
| **closure** | `<stem>.closure.json` | MCGS + closure-axis gate | *(auto when companion present)* `--rubric-points` to override |
| **fusion** | `<stem>.fusion.json` (≤80 lines, airlocked) | informal reasoner | `--fusion-lane` `--paired-llm <name>` |
| **informal** | `<stem>.fusion.json` with an outline | informal reasoner | `--informal-mode` |

The `.txt` sketch itself stays ≤30 bare lines in **every** lane. Strategy belongs only in the `.fusion.json` companion (which is airlocked until human review).

**Lane auto-routing** (`decide_lane()` in `safe_aristotle_submit.py`, skipped entirely under `--force`):
`--bare-only` forces bare → explicit `--fusion-lane` → explicit `--informal-mode` → adjacent `.fusion.json` auto-detected → adjacent `.closure.json` triggers a banner → otherwise bare. The persisted DB `lane` value uses a separate precedence: informal > fusion > closure (`real_closure_candidate=true`) > bare.

**Lane decision tree** (from `CLAUDE.md`):

```
Is this an OPEN gap (not in Mathlib, not solved)?
├── NO → STOP. Don't submit.
└── YES → Submitted before?
    ├── NO → easy tail (combinatorics/NT/finite check)? ── YES → BARE
    │        known explicit closure mechanism?          ── YES → CLOSURE
    │        have a paired-LLM strategy dossier?        ── YES → FUSION
    │        else (novel)                               ──────→ INFORMAL
    └── YES → last verdict?
        ├── compile_failed       → BARE (or disprove)
        ├── compiled_partial     → BARE (narrow the residual)
        ├── compiled_no_advance  → FUSION or INFORMAL (bare exhausted)
        ├── compiled_advance     → don't resubmit; advance to the next sub-question
        └── disproven            → don't resubmit; the conjecture is dead
```

**Current lane distribution** (DB): `bare` 1174 · `informal` 73 · `closure` 12 · `fusion` 2 · *(null)* 4. The project remains ~93% bare-lane despite the May 30 2026 pivot toward the informal/fusion lanes — the FUSION lane (Method-1's lane) has produced only 2 rows, both `compiled_no_advance`.

---

## The Gate Stack

Every non-`--force` submission passes a stack of pre-submission gates before reaching Aristotle.

### Gap-targeting gate (`check_gap_targeting`)

Hard-blocks (no override except the global `--force`):

- **C1** rejects `.lean` files — INFORMAL `.txt` only.
- **C2** rejects empty files.
- **C3** rejects sketches > **30 non-blank lines** (`MAX_SKETCH_LINES=30`; `---` lines excluded).
- **C4** rejects proof-strategy keywords ("Proof Strategy", "Key Lemma", "Approach N", …) — **unless** the file is a falsification (falsification is valid gap-targeting and is exempt).
- **C5** rejects > 5 Lean-indicator lines in the sketch (`MAX_LEAN_LINES_IN_SKETCH=5`).
- **C6 (em-tautology guard)** rejects a theorem body of the shape `(P) ∨ ¬(P)`. Excluded middle is discharged by `exact em _` in one line and resolves nothing; state existence (`∃ x, P x`) or impossibility (`¬ ∃ x, P x`) separately. Root cause: `docs/research/PILOT_ERDOS850.md`.
- **C7** escalates an F1 undecidable-wrapper-with-no-finite-range to a hard reject.

### Closure-axis gate (`check_closure_axis`)

Reads `<stem>.closure.json` (required fields: CS / CM / CR / HM / `real_closure_candidate` / `rationale`), enforces internal coherence rules, and **rejects `real_closure_candidate=false` unless `--rubric-points` is passed** (which logs `RUBRIC_POINTS_OVERRIDE`). A missing companion warns and allows (transition period).

### Fusion-companion airlock (`check_fusion_companion`)

Runs only in the fusion lane. Validates the `.fusion.json` (9 required fields, ≤80 non-blank lines, `fit_score` in [0,1], outline ≤500 words, ≤10 candidate lemmas, stage-output paths) and runs an airlock that rejects strategy-term leakage into the bare `.txt`.

### The `--force` master bypass

`--force` skips auto-routing, **all** gates, the lockfile, the dedup check, and (with `--batch`) the capacity check. It is reserved for the orchestrator / Method-1 pipeline, which has its own admission gate.

---

## Submission

```bash
python3 scripts/safe_aristotle_submit.py <sketch.txt> [slot] --informal-mode [--context <file.lean>]
```

The slot is optional (auto-detected from a `slotNNN` filename). The default lane is auto-routed (bare unless a `.fusion.json` / `.closure.json` companion is present), so no lane flag is needed for the common case.

**Recognized boolean flags:** `--force`, `--batch`, `--rubric-points`, `--verbose-context`, `--fusion-lane`, `--informal-mode`, `--bare-only`, `--force-literature-stale`.
**Value-taking flags:** `--context <file>` (repeatable), `--codex-context <id>`, `--paired-llm <name>`, `--literature-ack "<note>"`.
*(Note: `--informal` alone is **not** recognized — only `--informal-mode`. Any unrecognized `--flag` is silently swallowed and ignored.)*

The submission script handles:

- **Lane auto-routing** and the full gate stack above.
- **Lockfile** (`.aristotle_submit.lock`, stale after 300 s) to prevent concurrent submissions.
- **Dedup** by SHA256(file)[:16] within a 10-minute window, scanned in the JSONL transaction log.
- **Capacity check** — default **25** concurrent slots (`DEFAULT_MAX_CONCURRENT=25`, env-overridable via `ARISTOTLE_MAX_CONCURRENT`; skipped under `--force`/`--batch`). This is a project-side guardrail; Harmonic publishes no hard server-side limit.
- **Auto-context** — attaches all prior result `.lean` files for the problem that exist on disk and were **not** `compile_failed` or audited-invalid (gated on artifact *presence*, not on a clean-compile status — this is the I1 fix to a pre-2026-05-30 bug that silently returned 0 rows for 1166 submissions). Prints a canary warning when 0 artifacts attach despite prior submissions existing. Attached files are tar.gz-bundled and passed to `Project.create(prompt, tar_file_path=...)`.
- **Transaction logging** to `aristotle_submission_log.jsonl` (append-only audit log), plus an idempotent upsert of lane/closure metadata into `submissions/tracking.db`.

The real submission is a single `aristotlelib` call — `Project.create(prompt, tar_file_path)`. "Informal mode" is purely a prompt-*shape* difference assembled by `aristotle_informal.build_informal_prompt()`; there is no separate informal endpoint.

> `scripts/submission_queue.py` is a separate, older queue manager (`MAX_CONCURRENT=15`, shells out to an `aristotle` CLI, scans `.lean` files) that **bypasses** the gate stack. Prefer `safe_aristotle_submit.py`.

---

## Fetching, Auditing, and the Verification Gauntlet

Results come back as `.lean` files. The fetch/audit layer is the honesty boundary between "Aristotle returned a file that compiles" and "the open gap was actually resolved."

### Fetch-time regex verdict

`scripts/aristotle_fetch.py` is the canonical tool (it writes `submissions/tracking.db` and `nu4_final/`). In `aristotlelib` 2.0, outcome lives on the latest `AgentTask`, not on `Project.status`. The fetch-time regex audit maps results into the canonical enum: a clean compile (0 sorry, 0 axiom) deliberately lands at **`compiled_no_advance`**, never at `compiled_advance`. The fetch path can **never** promote a row to an advance.

### Verification gauntlet (the only promoter)

`scripts/verification_gauntlet.py` is the **exclusive** writer of `compiled_advance` / `target_resolved=1`, via four ordered, fail-closed gates:

- **G1 — machine check:** real `lake build` against formal-conjectures Mathlib (rev v4.22.0) + `#print axioms` closure (`SAFE_AXIOMS = {propext, Classical.choice, Quot.sound}`) + inline failure-mode detection. The `lake build` runs **only when `GAUNTLET_BUILD=1`** (set by the Method-1 loop); in default skip-build mode the gauntlet cannot promote.
- **G2 — faithfulness:** `statement_diff.py` + the multi-agent cross-model adversary.
- **G3 — literature:** `biblio_gate.py`, fail-closed on UNKNOWN.
- **G4 — promotion:** `target_resolved=1` **iff** G1 clean **and** G2 faithful **and** G3 clear.

If the gauntlet (or `source_conjecture`/`problem_id`) is unavailable, fetch falls back to the regex verdict with `target_resolved=0` — it never promotes.

### Re-audit and downgrade

`scripts/audit_proven.py` is a **downgrade-only** re-audit pass (it never sets `compiled_advance`). It re-audits `compiled_no_advance`/`compiled_partial` rows and downgrades on critical issues (a `sorry` → `compiled_partial`; a new `axiom` → `compiled_no_advance`; self-loop → `compiled_partial`), setting `verified=0` and populating `axiom_count`/`axiomatizes_prior_work`.

### Failure-mode detectors

`detect_failure_modes()` flags the named shapes that compile clean but resolve nothing — F1/F8 `Iff.rfl` definitional tautology, F3 side-lemma proliferation, F4 `exact?/apply?` trails, F6 restate-with-`sorry`, F9 bounded `native_decide`, plus the em-tautology detector (added from PILOT_ERDOS850). These are *why* a clean build is treated with suspicion.

### Cross-model adversary

`scripts/multi_agent_audit.py` is the G2 cross-model node: Phase 1 local validation, Phase 2 **Claude** (critical Lean bugs: unrestricted `sInf`, `Finset.sym2` self-loops, missing `DecidableRel`, weakened statements), Phase 3 **Gemini** (semantic faithfulness), with **Codex** as fallback. The **Grok** node was removed 2026-06-01 (no live model reachable).

> Older parallel tools `aristotle_monitor.py` and `aristotle_queue.py` use JSON logs (`submitted_projects.json`, `analysis_log.json`) with a different "success/partial/negated" vocabulary that does **not** match the canonical DB enum. Don't mistake their "success" for a gap resolution; the canonical state is in `tracking.db` via `aristotle_fetch.py`.

---

## Autonomous Loops

There are **two** autonomous loops in the repo. They share the `proof_queue` table but use different state vocabularies and different Aristotle code paths.

### 1. Proof Orchestrator (older, Codex → Aristotle)

`scripts/proof_orchestrator.py` drives a Codex → Aristotle state machine:

```
QUEUED → CODEX_RUNNING
           │
   ┌───────┴────────┐
   │                │
 0 sorry = RESOLVED  has sorries
                    │
        re-run Codex with its own best.lean as context
        (decide_after_codex; partial proofs do NOT auto-hand-off)
                    │
   Aristotle leg (ARISTOTLE_PENDING → ARISTOTLE_SUBMITTED →
   ARISTOTLE_RUNNING → RESOLVED | QUEUED | STALLED) is reached
   only via recover_from_crash, not the normal Codex decision path
```

```bash
python3 scripts/proof_orchestrator.py enqueue "<problem>" --problem-id <id>
python3 scripts/proof_orchestrator.py run [--single-pass]
python3 scripts/proof_orchestrator.py status
python3 scripts/proof_orchestrator.py cancel <id>
python3 scripts/proof_orchestrator.py retry <id>
```

> **SDK staleness:** the orchestrator's Aristotle leg is stale against `aristotlelib` 2.0 (`get_solution()` no longer exists; `str(p.status)=='COMPLETE'` is wrong — `Project.status` is RUNNING/IDLE/UNKNOWN and outcome lives on the latest `AgentTask`). Use `method1_loop.py` for the Aristotle path.

**Honest baseline:** `proof_queue` has 29 rows (23 STALLED, 5 RESOLVED, 1 stuck SUBMITTED). All 5 RESOLVED reached 0 sorry via **Codex only** and are a smoke test plus decomposed sub-lemmas (`orch_smoke_test`, `zariski_cancellation`, `erdos672_sub2_d1_impossible`, `erdos672_sub3_assembly`, `erdos283_squares`) — **no full open-problem resolution.** The `codex_proofs` table holds 16 rows (15 compiled, 6 at 0 sorry; recorded model `gpt-5.3-codex`).

#### Codex proof engine

`scripts/codex_proof_loop.py` runs `codex exec --full-auto` against an isolated temp Lean project (symlinked `.lake/packages`, pinned `MATHLIB_REV`), locks the theorem statement after iteration 1, rejects sorry-inflation, picks the best iteration, decomposes each residual `sorry` into a standalone sub-problem, and records to `codex_proofs`.

```bash
/codex-prove <problem>
```

### 2. Method-1 / Recipe-B (author-adjudicate, current)

`scripts/method1_loop.py` is the project's stated pivot away from bare-spray. It is a **gated FUSION-lane conveyor**:

1. **`author_argument.py`** — a strong-LLM author (best-of-N / debate across Codex / Gemini / Claude) writes an informal-argument dossier and emits a bare `.txt` + a 9-field `.fusion.json`. It cross-checks with a different grader and runs a deterministic G2-L1 statement-diff pre-check. It does **not** submit.
2. **Admission gate** — refuses any row whose `.fusion.json` lacks a non-empty strategy outline ("no outline → no informal → never bare-spray"); a malformed dossier is terminal (`REJECTED`).
3. **Capacity-governed submit** — `asyncio.Semaphore` + daily $-cap + slot re-check, routed through the FUSION lane (informal reasoner).
4. **Verification gauntlet** (G1–G4) — the fail-closed adjudicator, the exclusive writer of `compiled_advance`.
5. **Self-repair** — `Project.ask` rounds, capped at `ASK_REPAIR_CAP=2`, with plateau detection.

**Default-safe:** Method-1 is **dry-run by default** (`LoopConfig.dry_run=True`); live submission requires explicit `--live`. There is intentionally no `--skip-gate` / bare-spray path. **It has never been run live** — its honest `compiled_advance` baseline is **0** (the gate working, not a regression). One dangling `SUBMITTED` row (`erdos_100_piepmeyer`, since 2026-06-01) is from a single live attempt that was never folded back in.

Supporting machinery on disk: `statement_diff.py`, `biblio_gate.py`, `advance_dashboard.py`, `migrate_method1.py`; the `v_method1_ready` DB view (12 rows) and `candidate_queue` table (593 rows).

### research_fusion/ — context assembly only

`research_fusion/` is a 3-stage dossier builder (Stage 1 literature → Stage 2 analogy → Stage 3 technique) under `research_fusion/runs/<problem_id>/` with a 7-day cache TTL. It **never** submits to Aristotle — it only assembles context that feeds the FUSION lane. ~23 problem dossiers exist (incl. ~10 "yolo" campaign dirs).

---

## Tooling

### Claude Code Skills

The harness is orchestrated through Claude Code. There are **12 project skills** (`/<name>`) in `.claude/commands/`:

| Skill | Purpose |
|-------|---------|
| `/screen` | Binary decision: is this problem open? |
| `/screen-batch` | Batch screen: OPEN vs SKIP |
| `/sketch` | Write a bare-gap sketch (≤30 lines) |
| `/submit` | Gate check → auto-context → submit INFORMAL |
| `/sweep` | Batch: scan for open gaps, sketch, submit |
| `/fetch` | Download result → audit → extract findings → update DB |
| `/status` | Queue and job status |
| `/audit` | 8-point strict Lean validity audit |
| `/process-result` | Extract + audit + DB update for one result file |
| `/codex-prove` | Codex proof loop: write Lean 4, iterate against lake build |
| `/debate` | Multi-AI debate (Grok + Gemini + Codex) to identify the exact gap |
| `/optimize` | Fixed recommendation: state the gap bare, submit INFORMAL |

Plus **4 plugin-namespaced commands** (`math-forge/commands/`), thin wrappers around the `mk` CLI: `/math-forge:search`, `/math-forge:knowledge`, `/math-forge:failed`, `/math-forge:stats`. The plugin also ships agents (`investigate`, `problem-researcher`) and skills (`number-theory`, `open-problems`, `prior-results`); a separate `proof-author` agent lives at `.claude/agents/proof-author.md`.

### math-forge CLI (`mk`)

A single 788-line bash script (`math-forge/scripts/mk`) dispatching over 17 subcommands. Knowledge commands hit `math-forge/data/knowledge.db`; pipeline commands hit `submissions/tracking.db`.

```bash
# Knowledge
mk search "<query>"          # FTS5 full-text search (BM25, title-weighted)
mk find "<problem_id>"       # All findings for a problem (+ false_lemmas)
mk failed [keyword]          # Failed approaches — check BEFORE sketching
mk strategies [domain]       # Verified theorem findings grouped by proof_technique
mk stats                     # KB dashboard: findings by type/domain, totals, problems tracked
mk init                      # Bootstrap knowledge.db

# Codex
mk codex [problem_id]        # Codex proof loop history
mk codex-best <problem_id>   # Best compiled Codex proof file path

# Research-fusion
mk fusion <problem_id>       # Run research_fusion Stages 1-3 (lit/analogy/technique)
mk debate <problem-id> <tpl> # Templated 3-AI cross-domain debate

# Pipeline
mk submit <file> [--yes]     # Lane pre-check + delegate to safe_aristotle_submit.py
mk status [uuid-or-slot]     # Aristotle queue status (via aristotle_fetch.py)
mk context <problem_id>      # Prior Aristotle results for auto-context
mk gaps                      # Open gaps currently being targeted + status
mk partials                  # Near-miss submissions (sorry=1)
mk resubmittable             # Resubmission candidates (1-3 sorries)
mk query "<sql>"             # Read-only SQL against tracking.db (SELECT/WITH/EXPLAIN/PRAGMA only)
```

*Note:* `mk stats` reports **knowledge-base** stats only (not submissions/clean rate/queue). The `strategies` and `queue_cache` tables are currently **empty**, so `mk find`'s "Strategies" section is always blank and `mk strategies` actually aggregates verified `findings` by `proof_technique`.

### Multi-Agent Support

When stuck on problem identification or gap analysis, the harness invokes multiple AI models in parallel:

- **Gemini** — deep analysis with a large context window; semantic-faithfulness audit (G2/Phase 3).
- **Claude** — synthesis, orchestration, sketch writing; critical Lean-bug audit (G2/Phase 2); Method-1 authoring.
- **Codex** — Lean 4 proof generation via the iterative compile-fix loop; audit fallback.
- **Grok** — live web/X search for `/debate` and screening (but **removed** from the audit ensemble 2026-06-01, no live model reachable).

These are used for *screening, gap identification, authoring (FUSION lane), and proof generation* — never to inject proof guidance into a bare submission.

---

## Database

State lives in two SQLite databases.

### `submissions/tracking.db` (4.3 MB, ~50 tables/views)

| Table / view | Purpose |
|--------------|---------|
| `submissions` | Every Aristotle job (1,265 rows; ~50 columns) |
| `submissions_audit` (view) | Read-only view exposing all audit axes in stable column order (1,265 rows) |
| `codex_proofs` | Codex proof-loop results (16 rows) |
| `proof_queue` | Autonomous orchestrator queue (29 rows) |
| `false_lemmas` | Claims that seemed plausible but are provably wrong — check before submitting |
| `failed_approaches` | Approaches tried and why they failed |
| `candidate_queue`, `v_method1_ready` | Method-1 staging |

### Canonical status enum (post-2026-05-28)

`submissions.status` takes exactly one of six values:

| Status | Meaning |
|--------|---------|
| `submitted` | Submitted, not yet returned |
| `compile_failed` | Returned Lean fails `lake build` |
| `compiled_partial` | Compiles but has residual `sorry`/`axiom` |
| `compiled_no_advance` | Compiles clean, but the target is not resolved |
| `compiled_advance` | Compiles clean **and** genuinely advances the target |
| `disproven` | Verified counterexample (conjecture was wrong) |

`compiled_advance` is **opt-in**: it requires `contribution_statement NOT NULL` **and** `axiomatizes_prior_work=0` **and** `target_resolved=1`, and is written **only** by the verification gauntlet. The pre-2026-05-28 messy labels (`compiled_clean`, `near_miss`, `error`, …) are preserved only in the `status_legacy` column.

### Key fields and lane columns

- `gap_statement` — what open gap this targets
- `target_resolved` — did this actually close the gap? (currently 0 across all rows)
- `output_file` — path to the `.lean` result (used for auto-context)
- Lane columns (I2 migration, May 30 2026): `lane` (default `bare`), `informal_mode_used`, `paired_llm`, `fusion_json`, `mathematical_content_score`, `closure_axis_json`
- Honesty columns: `axiom_count`, `axiomatizes_prior_work`, `cost_usd`

### `math-forge/data/knowledge.db` (680 KB)

604 findings (theorem 477, failure 56, false_lemma 43, technique 28) over a genuine FTS5 virtual table (`findings_fts`, `porter unicode61` tokenizer, BM25 ranking). Domains present: `nt` 505, unknown 56, `combinatorics` 43. *(The top-level `math-forge/knowledge.db` is a stale 0-byte stub — not the one used.)*

### Reproducing these stats

```bash
sqlite3 submissions/tracking.db "SELECT status, COUNT(*) FROM submissions GROUP BY status;"
sqlite3 submissions/tracking.db "SELECT COUNT(*) FROM submissions WHERE status='compiled_advance';"
sqlite3 submissions/tracking.db "SELECT COALESCE(lane,'(null)'), COUNT(*) FROM submissions GROUP BY lane;"
sqlite3 math-forge/data/knowledge.db "SELECT COUNT(*) FROM findings;"
```

---

## Notable Results — The Actual Math

The harness's deepest work lives in `analysis/` and `docs/`, not in the pipeline scripts. Everything below is scoped exactly as the project's own docs scope it — **partial results, not conjecture resolutions.**

- **Erdős 124 "Lemma A" (`erdos124_gap_onset`)** — the project's single genuine machine-verified *novel partial theorem*: sorry-free, standard axioms only (`propext`/`Classical.choice`/`Quot.sound`), 53 lines (`submissions/results_jun10/gap_onset_x/.../Main.lean`). It proves the elementary structural bound `S(X) ≥ m·β − C'` and the closed-form gap-condition onset `m₀=(C'−1)/σ` (the MW boundary at σ=0). It is a verified **inequality + onset**, **not** a proof of the conjecture; the all-k case is explicitly **open**, and the `124.lean` all-k tag is flagged as an over-claim.
- **Erdős 124 (3,4,7) k=2 cofiniteness** — a complete but tightly-scoped proof for the *fixed* triple at *fixed* k=2 (N₀=3,982,888), via symmetric-doubling + a per-atom gap lemma with a `native_decide` base case. All-k stays open.
- **Erdős 944 (Dirac k=4)** — proven structural lemmas (a degree-3 vertex forces 3 critical edges; any (4,1)-witness has min-degree ≥ 6) plus exhaustive computational **non-existence** of a (4,1)-witness on ≤12 vertices. No witness and no impossibility proof — honestly, "no resolution, a sharp map of why."

These campaigns were produced by a **flat multi-agent "team" methodology** (`analysis/e124q2/team/`, 189 files; `analysis/e944/team/`, 315 files) with a shared CLAIMS board (strict `[PROVEN]`/`[VERIFIED]`/`[CITED]`/`[OPEN]`/`[DEAD]` tags) and an adversarial verifier that independently recomputes load-bearing constants and catches errors in the team's own docs.

### What Aristotle can and cannot do

The self-audit `analysis/alignment_aristotle_ceiling_audit.md` finds a categorical ceiling: across the submissions studied, Aristotle never produced an unconditional new bound on an unbounded conjecture, never imported non-elementary machinery (modular forms, sieves, alg-geom), and never chained > 3 nontrivial lemmas without `native_decide`. Its observed ceiling is "what a sharp Mathlib contributor could do in a day, formalized." The strongest behavior observed is autonomously substituting an elementary proof when one exists.

---

## Hooks and Guardrails

Two SessionStart briefings fire every session (the second only because the `math-forge` plugin is enabled), plus one PostToolUse guard.

**Project-level** (`.claude/settings.json`):
- **SessionStart** → `scripts/session_start_hook.sh` — prints the orchestrator queue (active/resolved/stalled) and pending actions as plain stdout.

**Plugin-level** (`math-forge/hooks/hooks.json`, active only while the plugin is enabled):
- **SessionStart** → `context-loader.sh` — a DB-driven JSON briefing from `tracking.db` + `knowledge.db`; also appends the plugin's `scripts/` to PATH so `mk` resolves.
- **PostToolUse (Write|Edit)** → `lean-validator.sh`:
  - For `.txt` files whose path contains `sketch` or `slot`: **warns** (advisory only) on proof-strategy keywords or > 30 non-blank lines.
  - For `.lean` Edit calls: **hard-blocks** replacing real proof code with `sorry`.
  - For `.lean` files: **warns** on references to any lemma in the `false_lemmas` table.

Disabling the plugin removes the second briefing and the entire PostToolUse guard.

---

## Repository Structure

```
math/
├── submissions/
│   ├── sketches/                  # 476 bare-gap .txt sketches + 79 .fusion.json + 38 .closure.json companions
│   ├── nu4_final/                 # Aristotle result files (.lean) + _ID.txt receipts
│   ├── yolo_results/              # 84 result tarballs (yolo campaigns)
│   ├── method1/                   # Method-1 dossiers (.txt + .fusion.json + ID)
│   ├── results/, results_jun10/, results_jun11/, erdos/   # parallel result drop-zones
│   └── tracking.db                # Submission state (source of truth)
├── proven/                        # 58 .lean (44 sorry-free): re-formalized KNOWN results (Tuza ν≤3, Parker lemmas) — NOT novel solves
├── partial/                       # Near-miss / partial Lean (Erdős, Tuza ν=4 lemmas)
├── Math/                          # 4 curated Erdős targets (Erdos208/233/283Squares/Slot145; 3 still carry sorry or an external axiom)
├── analysis/                      # The actual math: e124q2/, e944/, e647_sieve/ campaigns + landscape/alignment self-audits
├── docs/                          # ~629 .md; docs/research/ holds referee-grade audits + methodology notes
├── agentic/                       # DORMANT/EXPERIMENTAL — see Legacy Subsystems
├── research_fusion/               # 3-stage dossier assembly (never submits)
├── scripts/
│   ├── safe_aristotle_submit.py   # Canonical submit: lanes, gate stack, auto-context
│   ├── aristotle_fetch.py         # Canonical fetch/audit → tracking.db
│   ├── verification_gauntlet.py   # G1-G4 fail-closed adjudicator (only writer of compiled_advance)
│   ├── audit_proven.py            # Downgrade-only re-audit + failure-mode detectors
│   ├── multi_agent_audit.py       # Cross-model adversary (Claude + Gemini, Codex fallback)
│   ├── method1_loop.py            # Method-1/Recipe-B author-adjudicate loop (dry-run by default)
│   ├── author_argument.py         # Strong-LLM dossier author (writes .fusion.json)
│   ├── statement_diff.py, biblio_gate.py, advance_dashboard.py
│   ├── proof_orchestrator.py      # Older Codex→Aristotle loop (Aristotle leg stale vs SDK 2.0)
│   ├── codex_proof_loop.py        # Codex Lean 4 proof iteration engine
│   ├── aristotle_monitor.py, aristotle_queue.py, submission_queue.py   # older JSON-log tools (bypass the gate stack)
│   └── debate.py, workflow.py
├── math-forge/
│   ├── data/knowledge.db          # FTS5 knowledge base (604 findings)
│   ├── hooks/                     # Plugin hooks (context-loader, lean-validator)
│   ├── commands/                  # 4 /math-forge:* mk wrappers
│   └── scripts/mk                 # math-forge CLI
├── results_v07/                   # 64 Aristotle result tarballs
├── lakefile.toml, lean-toolchain  # Lean 4 build configuration
├── .claude/
│   ├── commands/                  # 12 project skill definitions
│   ├── agents/proof-author.md
│   └── settings.json              # Hooks and session config
└── CLAUDE.md                      # Pipeline rules and methodology (source of truth for methodology)
```

---

## Legacy / Dormant Subsystems

- **`agentic/`** — a ~2,658-LOC multi-daemon harness for autonomously farming proofs of one problem (Tuza's conjecture, ν=4). It was seeded once (2026-01-01) and **never operated end-to-end**: all 15 Aristotle slots are empty, all 169 queue rows are `never_submitted`, the runtime tables and `logs/`/`pids/` are empty, and nothing outside `agentic/` imports it. Its design (submitting `.lean` files with embedded proof *strategy* via an `aristotle prove-from-file` CLI) directly **contradicts** the current bare-conjecture / INFORMAL-`.txt`-only methodology — it predates the Feb-17-2026 gap-targeting pivot and the May-30 4-lane model. Several files documented in `agentic/README.md` do not exist (the implementation was consolidated into `pool.py` / `pipeline.py`). Do not revive without a rewrite.

---

## Design Principles

**Honesty first.** "Compiled clean" is not "solved." A result that builds helper infrastructure without touching the core conjecture is not a resolution — only `target_resolved=1` (gauntlet-verified) counts, and that has happened 0 times. We state our zero-resolution record plainly rather than implying solves we don't have.

**Bare conjecture only (in the `.txt`).** No proof hints, no lemma suggestions, no strategy in the sketch. Strategy, when we have it, lives in an airlocked `.fusion.json` companion and engages Aristotle's informal reasoner — not the bare formalizer.

**Depth over breadth.** The project's own June 2026 audit (`analysis/ai_math_solves_vs_our_process.md`) identifies volume-spray as the rate-determining failure: bare-lane submission on deep-structural conjectures has a documented 0% genuine hit rate. The current direction is hand-screened easy-tail / construction problems with a strong informal reasoner *authoring* the math (Method-1) and the prover as verifier.

**Context compounds.** Even "failed" attempts that compile clean add to the auto-context pool for the next attempt.

**Falsification is valid.** "Is this gap actually real?" is a legitimate submission. The 8 `disproven` rows are real progress.

**Track everything.** Every submission, false lemma, and dead end goes in the database. The system's memory prevents repeating mistakes.

**Trust the gates, not the green checkmark.** Aristotle proves ~97.6% of what it attempts but only ~67% semantically correctly. The gate stack, the verification gauntlet, the downgrade-only re-audit, and the cross-model adversary exist precisely to catch the fluent-but-wrong third.

---

## License

MIT
