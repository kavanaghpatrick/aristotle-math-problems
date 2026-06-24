# Method-1 / Recipe-B Scale-Up — Build & Integration Report

**Date:** 2026-06-01
**Author:** integration agent (Phase-3 of 10-agent parallel build)
**Plan:** `analysis/method1_scaleup_plan.md` (build-ready; do NOT re-derive)
**Status:** BUILT + INTEGRATED + VALIDATED (non-paid). **Live Aristotle campaign NOT run — separate go decision.**

---

## 0. The boundary, stated first

This report covers a **BUILD + VALIDATE** pass only. **No live Aristotle submission was fired; no
campaign (plan P7) was run.** Verified at session end:

- `submissions` table: **0 rows** with a `2026-06-01` timestamp (`submitted_at`/`created_at`).
- `method1_loop.py run` is **dry-run by default** (`LoopConfig.dry_run=True`); live submit requires an
  explicit `--live` flag that was never exercised. `--dry-run` wins even if both flags are passed.
- The only `2026-06-01` line in `aristotle_submission_log.jsonl` is a `RUBRIC_POINTS_OVERRIDE`
  **gate-logging event from a pytest temp fixture** (`/private/tmp/.../pytest-*/fixture.txt`) — a logging
  side-effect of the existing test suite, NOT an Aristotle job (no uuid/project_id).
- `submissions/tracking.db` integrity_check = **ok**; counts unchanged end-to-end:
  `submissions=1252`, `proof_queue=28`, `candidate_queue=24`, `v_method1_ready=11`; rows 1254/1255 still
  `compiled_advance` (the baseline agent owns their reclassification, not this pass).

The first real run of the gated conveyor at scale is **P7 (Campaign)** and is a separate, explicit
go decision. It costs money and is outward-facing.

---

## 1. Components built (8 new scripts + 1 subagent)

The conveyor is a four-segment, DB-backed pipeline over a single SQLite source of truth
(`submissions/tracking.db`). All eight scripts follow repo style (`argparse` + `if __name__=='__main__'`,
`python3`). Total net-new code ≈ **6,722 lines**.

| Segment | Component | File | Lines | Role |
|---|---|---|---|---|
| Foundations | **DB migration** | `scripts/migrate_method1.py` | 420 | Additive schema: `candidate_queue`, `named_conjecture_status`, `v_method1_ready` view, `proof_queue.submission_uuid`, ensures `submissions.cost_usd`/`mathematical_content_score`. APPLIED to real DB. |
| Foundations | **Literature gate (fail-CLOSED)** | `scripts/biblio_gate.py` | 930 | `check_literature()` over zbMATH Open + Crossref + full-range arXiv + named-conjecture cards + 7-day cache. Any uncertainty → UNKNOWN, never CLEAR. |
| Foundations | **Statement-faithfulness (G2-L1)** | `scripts/statement_diff.py` | 790 | `compare_statements()` / `extract_theorem_statement()`. Deterministic structural diff: hypothesis-strip, quantifier-flip, weaker-conclusion, bound-injection, definition-swap. |
| Foundations | **Verification gauntlet (G1–G4)** | `scripts/verification_gauntlet.py` | 961 | `run_gauntlet()` — real `lake build` + `#print axioms` (G1), statement_diff (G2), biblio_gate (G3), promote (G4). EXCLUSIVE writer of `compiled_advance`/`target_resolved=1`. |
| 1 INTAKE | **Daily intake driver + S1–S8 tagger** | `scripts/source_screen_run.py` (+ edits to `screen_formal_conjectures.py`, `analysis/build_open_problems_registry.py`) | 610 | SOURCE → SCREEN (tier + snipe + deep_structural_exclude) → LITERATURE → RANK → write `candidate_queue`. Populated real DB (24 rows, 11 ready). |
| 2 AUTHORING | **Multi-LLM authoring unit** | `scripts/author_argument.py` (+ `.claude/agents/proof-author.md`) | 1222 | Strong-LLM authors informal argument → 9-field `.fusion.json` that passes `check_fusion_companion`. Best-of-N / debate. Does NOT submit. |
| 3 FORMALIZE+REPAIR | **Async state-machine loop** | `scripts/method1_loop.py` | 953 | `enqueue` / `run [--dry-run\|--live]` / `status`. Reads `v_method1_ready` → admission gate (no outline → no submit) → capacity-governed wave → fetch fold-in → `Project.ask` self-repair (cap 2). |
| 4 VERIFICATION+METRICS | **Throughput-governance dashboard** | `scripts/advance_dashboard.py` | 836 | Advance-rate / cost-per-advance per lane+author, faithfulness/literature reject breakdown, mislabeled-advance alarm, 3 self-enforcing invariants. Read-only. |
| 2 AUTHORING | **Claude Opus proof-author subagent** | `.claude/agents/proof-author.md` | (5.1 KB) | 3rd ensemble author; emits the dossier JSON schema `author_argument` expects. |

---

## 2. Validated vs. stubbed

### Validated by REAL execution (no mocks)

| Capability | Evidence |
|---|---|
| **All 8 modules import + py_compile** | `py_compile` clean on all 8; all 6 keyless modules import; `author_argument`/`method1_loop` import lazily without `ARISTOTLE_API_KEY` (entrypoints `run_author` / `check_admission` present). |
| **Cross-module contracts resolve together** | One process imports `verification_gauntlet` (+ its `run_g1/g2/g3`), `statement_diff.compare_statements` (keys `faithful/issue/severity`), `biblio_gate.check_literature` (keys `status/evidence/sources`, status ∈ enum), `method1_loop.check_admission`, `advance_dashboard.build_report` — **all resolve**. |
| **Migration idempotent + applied** | Re-run on temp copy: 0 tables created, 0 cards seeded, 24/11 preserved. Real DB integrity=ok. |
| **G1 real machine-check — refuses 1-sorry** | `erdos938_fusion` Main.lean (1 sorry): `build_ok=True`, `build_clean=False`, `#print axioms erdos_938` exposed **sorryAx** → refused. |
| **G1 — refuses native_decide** | `erdos319_sign_pattern` and Brocard `slot722`: `build_ok=True` but `#print axioms` exposed **Lean.ofReduceBool** + **F9** fired → refused. |
| **G1 — PASSES a genuinely clean artifact** | `yolo_d5_e364` (0 sorry, no native_decide): `build_ok=True`, `build_clean=True`, `axioms_clean=True`, `user_axioms=[]`, no failure modes. Proves G1 is not a blanket-reject. |
| **Full G1→G2→G3→G4 end-to-end** | `erdos319` with an unbounded source conjecture: **G1** Lean.ofReduceBool+F9, **G2** fatal bound-injection (`Finset.Icc 1 6`), **G3** CLEAR (live zbMATH/Crossref/arXiv, 2/3 reached), **G4** NOT promoted → `compiled_no_advance`, `target_resolved=0`. All four gates executed. |
| **§5 invariant — historical false positive downgraded** | Brocard `slot722` (`brocard_conjecture_bounded`, n∈[2,50] via native_decide) with the real unbounded Brocard source → **DOWNGRADED** to `compiled_no_advance`/`target_resolved=0` on **G1∧G2∧G3** simultaneously (G1 F9, G2 fatal bound-injection, G3 AMBIGUOUS). The gate rejects the project's own mislabeled advance. |
| **Authoring → fusion companion contract** | `author_argument --no-llm` produced `<pid>.txt` + `<pid>.fusion.json` (exactly the 9 fields), `fusion_companion_valid=True`. Independent `safe_aristotle_submit.check_fusion_companion(Path(...))` → `airlock_passed=True`. The exact gate `method1_loop` relies on accepts it. |
| **Method-1 loop full dry-run** | `run --dry-run --max 5`: REFILL pulled top-5 from `v_method1_ready` (tractability-ordered), ADMISSION denied 3 unauthored rows / admitted 2 authored (outline 342/344 chars), capacity governor sized wave to `slots_available=25`, both submits **SKIPPED (no --live)**. |
| **Safety precedence** | `run --dry-run --live` → "`--dry-run wins (no submit)`". No `--force`/`--skip-gate`/bare path exists. |
| **biblio_gate offline cards** | FLT/Catalan/etc. → `CLOSED` deterministically from `named_conjecture_status`; generic statement (no card, no network) → `UNKNOWN` (fail-closed, never CLEAR). |
| **Self-tests** | `statement_diff --self-test` PASS (em-tautology fatal, identical faithful); `advance_dashboard --self-test` PASS (synthetic invariants, I3 correctly flags mislabeled). |
| **Existing suites green** | `bats math-forge/tests/*.bats` → **40/40 pass**. `pytest` schema_consistency + failure_mode_detection → **35/35 pass**. auto_routing/lane_routing/gather_context/aristotle_fetch → pass. |

### Stubbed / NOT exercised (by design — safety boundary)

| Item | Why |
|---|---|
| **Live Aristotle submit / fetch / `Project.ask`** | Behind `--live`; never fired (HARD SAFETY BOUNDARY). Validated structurally: all reused primitives import and are callable; wave/admission/capacity/decision logic ran in dry-run; gauntlet-decision branches unit-tested with synthetic verdicts. |
| **A genuine `compiled_advance` (target_resolved=1)** | Unreachable without a real CLEAR-literature + faithful + axiom-clean artifact from a live run. That is P7, not this build. Today the honest count is **0** — the gate working, not a regression (plan §4/Risk 8). |
| **Paid LLM authoring (best-of-N live)** | Authoring agent made ONE real N=1 call during its own build; this integration pass used `--no-llm` only (zero paid calls). |
| **G2-L2 cross-model adversary (Gemini+Claude)** | Fires only on G2-L1 ambiguity at real run time; would burn paid LLM calls. Validated structurally. |
| **`cost_usd` population** | Aristotle has no SDK cost field (verified); cost is a directional wall-clock estimate written at fetch under `ARISTOTLE_USD_PER_HOUR`. Stays NULL until a live run books cost. |

---

## 3. EXACT run commands per stage

Prerequisite for ad-hoc invocation: `export PYTHONPATH="$(pwd)/scripts:$PYTHONPATH"` (the repo adds
`scripts/` to `sys.path`). All paths relative to repo root `/Users/patrickkavanagh/math`.

### Stage 0 — Foundations (one-time, idempotent)
```bash
# Apply / re-apply the additive schema (safe to re-run; CREATE IF NOT EXISTS / ALTER ADD COLUMN only)
python3 scripts/migrate_method1.py
# programmatic: from migrate_method1 import migrate; migrate('submissions/tracking.db')
```

### Stage 1 — INTAKE (daily, cron-able)
```bash
# Full live sweep of all open corpora -> candidate_queue (biblio_gate hits the network, 7-day cached)
python3 scripts/source_screen_run.py
# Bounded / offline variants:
python3 scripts/source_screen_run.py --dirs ErdosProblems --limit 20        # bounded live
python3 scripts/source_screen_run.py --skip-network                          # cards/kill-list only, fast
python3 scripts/source_screen_run.py --dry-run                               # screen+rank, no write
python3 scripts/source_screen_run.py --report                                # print v_method1_ready and exit
# Raw-intake (preserves enrichment on existing rows):
python3 analysis/build_open_problems_registry.py --to-db
```

### Stage 2 — AUTHORING (batchable, upstream of the prover)
```bash
# Author a dossier for one ready candidate -> DIR/<pid>.txt + DIR/<pid>.fusion.json
python3 scripts/author_argument.py --problem-id erdos_10 --mode best-of-N --n 3 \
        --out-dir submissions/method1/ --json
# Modes / engines:
python3 scripts/author_argument.py --problem-id erdos_10 --mode debate
python3 scripts/author_argument.py --problem-id erdos_10 --models codex,gemini,claude
python3 scripts/author_argument.py --problem-id erdos_10 --no-llm     # pipeline test, ZERO paid calls
```

### Stage 3 — FORMALIZE + REPAIR (the loop)
```bash
# DRY-RUN (default-safe; never submits) — the validated path
python3 scripts/method1_loop.py run --dry-run --max 5
python3 scripts/method1_loop.py status                  # read-only queue + cost-booked-today
python3 scripts/method1_loop.py enqueue --problem-id erdos_10
# LIVE (P7 ONLY — separate go decision; costs money; NOT run in this build):
#   ARISTOTLE_MAX_CONCURRENT=40 python3 scripts/method1_loop.py run --live --max 20 --loop
```

### Stage 4 — VERIFICATION + METRICS
```bash
# Run the gauntlet on a result artifact (G1 only, or full G1->G4 with a source)
python3 scripts/verification_gauntlet.py <Main.lean> --g1-only --json
python3 scripts/verification_gauntlet.py <Main.lean> --uuid <U> \
        --source-conjecture "<intended thm or FILE>" --problem-id <id> --json
# Throughput governance + invariant gate (exit 1 = a campaign should be blocked)
python3 scripts/advance_dashboard.py
python3 scripts/advance_dashboard.py --invariants-only      # CI/cron pre-gate
python3 scripts/advance_dashboard.py --json
```

The gauntlet is ALSO wired into `aristotle_fetch.update_db` (env `GAUNTLET_BUILD=1` enables the real
lake build inside the fetch path; default skip-build preserves the legacy cost profile and never promotes).

---

## 4. Dependency / run order

```
                              migrate_method1.py   (additive schema; run FIRST, idempotent)
                                      │
        ┌─────────────────┬──────────┼───────────────────┬──────────────────────┐
        ▼                 ▼          ▼                   ▼                      ▼
  biblio_gate.py   statement_diff.py │            named_conjecture_status   submissions.cost_usd
   (G3 authority)   (G2-L1 diff)     │              (cards, seeded)          + mcs (ensured)
        │                 │          │
        └────────┬────────┘          │
                 ▼                    │
        verification_gauntlet.py      │   (G1 lake build vs formal-conjectures/.lake = lean4 v4.22.0;
        (G1∧G2∧G3 ⇒ G4 promote)       │    G2 ← statement_diff; G3 ← biblio_gate; reuses audit_proven,
                 │                    │    codex_proof_loop symlink, multi_agent_audit for G2-L2)
                 │                    ▼
                 │            source_screen_run.py  ──writes──▶ candidate_queue ──▶ v_method1_ready (view)
                 │            (screen_formal_conjectures S1–S8 + deep_structural_exclude;                 │
                 │             build_open_problems_registry --to-db raw intake; biblio_gate literature)   │
                 │                                                                                        │
                 │                                              ┌─────────────────────────────────────────┘
                 │                                              ▼
                 │                                     author_argument.py  ──▶ submissions/method1/<pid>.{txt,fusion.json}
                 │                                     (gather_context, debate.py, build_informal_prompt,
                 │                                      statement_diff pre-check, check_fusion_companion,
                 │                                      proof-author.md subagent)
                 │                                              │
                 ▼                                              ▼
        ┌──────────────────────────── method1_loop.py ────────────────────────────────┐
        │ run: reads v_method1_ready → admission gate (needs .fusion.json outline)      │
        │      → safe_aristotle_submit.safe_submit(--fusion-lane)  [DRY-RUN SKIPS]      │
        │      → fetch_backlog fold-in → run_gauntlet → Project.ask self-repair (cap 2) │
        └──────────────────────────────────────────────────────────────────────────────┘
                 │
                 ▼
        advance_dashboard.py   (read-only over submissions/submissions_audit;
                                asserts I1/I2/I3; exit 1 gates the campaign)
```

**Strict ordering:**
1. `migrate_method1.py` (schema) — everything else assumes `candidate_queue`/`named_conjecture_status`/`v_method1_ready`/`proof_queue.submission_uuid` exist.
2. `biblio_gate.py`, `statement_diff.py` (leaf gates) before `verification_gauntlet.py` (composes them) and `source_screen_run.py` (uses biblio_gate).
3. `source_screen_run.py` populates `candidate_queue` → `author_argument.py` reads it and writes dossiers → `method1_loop.py` admits dossiers.
4. `verification_gauntlet.py` is the fetch-time gate `method1_loop` calls after fetch; `advance_dashboard.py` reads the resulting rows.

**Shared-resource notes for integrators:**
- `method1_loop` and `proof_orchestrator` SHARE `proof_queue` (both `CREATE TABLE IF NOT EXISTS`; `submission_uuid` added additively). Do not run them concurrently on the same `problem_id`s.
- The ONE capacity governor is `safe_aristotle_submit.check_rate_limit_and_capacity` (now env-driven `MAX_CONCURRENT=25`). `method1_loop._slots_available` = `min(server slots, MAX_CONCURRENT - local in-flight)`.
- G1 builds against `formal-conjectures/.lake` (**lean4 v4.22.0 / mathlib v4.22.0**), NOT `codex_proof_loop`'s root rev.

---

## 5. Integration bugs found & fixed (in NEW scripts only)

This pass found **no interface/import bugs** in the new scripts — they integrate as written. All eight
import together and the documented contracts resolve in one process. The earlier per-component build
reports already record the bugs each author found-and-fixed in their own files (biblio_gate
false-CLOSED title/named fixes; source_screen exact-card pre-check; method1_loop refill
duplicate-REJECTED fix). I edited **none** of the new scripts during integration (none needed it) and
**none** of another agent's existing-file edits.

`git status` confirms my footprint is exactly the 8 untracked `scripts/*.py` + this report. The three
modified existing files (`aristotle_fetch.py`, `multi_agent_audit.py`, `screen_formal_conjectures.py`)
are the Foundations/Intake agents' edits, pre-existing in the working tree — untouched by me.

---

## 6. Known pre-existing issue (NOT introduced by Method-1, NOT mine to fix)

`pytest tests/test_submit_capacity.py` → **6 failures**. Root cause: the Foundations agent's
working-tree edit to `scripts/safe_aristotle_submit.py` (a) raised the concurrency cap from a hardcoded
`5` to env-driven `MAX_CONCURRENT=25` (per plan §4 "run at 40–50"), (b) added a 5th return key
`max_concurrent` to `check_rate_limit_and_capacity`, and (c) widened the status query `limit` 20→30.
`test_submit_capacity.py` still asserts the OLD 4-key contract, `slots_available == 5 - in_progress`,
and `limit == 20`, so it fails with `slots_available == 22/23` and `Extra items: 'max_concurrent'`.

- This is **the intended new behavior**, not a regression — the capacity governor was deliberately made
  env-overridable to support the campaign cap.
- `safe_aristotle_submit.py` and `test_submit_capacity.py` are **not in my file-ownership set** (they
  belong to the capacity-governor change). Disjoint-ownership rule: I did not edit them.
- **`method1_loop` is unaffected** — it reads `slots_available` and `MAX_CONCURRENT`, both present and
  correct (the dry-run reported `slots_available=25`).
- **Recommended fix (for the capacity-governor agent):** update `test_submit_capacity.py` to assert the
  5-key dict, parameterize the expected cap on `MAX_CONCURRENT` instead of hardcoded `5`, and expect
  `limit == 30`. One test-file edit; no production change.

---

## 7. Bottom line

- **All four conveyor segments are built, import cleanly, and integrate** against each other's published
  contracts.
- **The fail-closed gauntlet works on real artifacts**: it refuses hidden-sorry (sorryAx) and
  native_decide (Lean.ofReduceBool/F9) proofs, passes a genuinely clean artifact, runs G1→G2→G3→G4
  end-to-end, and **downgrades the project's own historical mislabeled `compiled_advance` (Brocard)** —
  the plan's §5 acceptance invariant.
- **The loop's dry-run exercises the full path** (refill → admission gate → capacity governor → STOP
  before submit) with zero side effects on the real DB.
- **Existing tests green** (40/40 bats, 35/35 core pytest); the only failures are a pre-existing stale
  capacity test in another agent's file.
- **Live Aristotle campaign NOT run — separate go decision.** P7 is the first real, paid, outward-facing
  execution and must be authorized explicitly. The realistic near-term goal (plan §4) is the **first
  genuine `target_resolved=1` under the fail-closed gauntlet**, with the honest advance count expected to
  sit at 0 for a while — that is the gate working.
