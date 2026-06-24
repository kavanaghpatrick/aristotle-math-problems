# Method-1 / Recipe-B Scale-Up Plan

**Date:** 2026-06-01
**Author:** planning lead (synthesized from 4-agent inventory + 4 component designs)
**Status:** build-ready
**Verified against live repo/DB this session** (see "Ground-Truth Verification" footnotes).

---

## 0. The One-Sentence Mission

Run **hundreds of GATED Method-1 attempts per day** — strong-LLM-authored informal argument → fail-closed gates → Aristotle informal reasoner → fail-closed verification gauntlet — at high parallel throughput, where **the gates scale 1:1 with volume and there is no faster path that bypasses a gate**. Aggressive scale = parallel throughput of the *gated* method, **never** bare spray.

---

## 1. Architecture Summary

Method-1 is a **four-segment conveyor**, each segment a DB-backed stage that scales independently and is bounded by exactly one resource:

```
   ┌──────────────┐   ┌──────────────┐   ┌──────────────────┐   ┌──────────────────┐
   │ 1. INTAKE    │   │ 2. AUTHORING │   │ 3. FORMALIZE+    │   │ 4. VERIFICATION  │
   │ source+screen│──▶│ multi-LLM    │──▶│    REPAIR        │──▶│    GAUNTLET      │
   │ +lit-dedupe  │   │ argument     │   │ informal submit  │   │ +metrics         │
   │ (DB queue)   │   │ (.fusion.json│   │ +ask self-repair │   │ (promote/reject) │
   └──────────────┘   │  dossier)    │   │ (proof_queue)    │   └──────────────────┘
   bound: API/cache   └──────────────┘   bound: 25-slot     bound: local CPU
                      bound: per-LLM API  Aristotle budget   (lake build) + cache
```

**Single source of truth:** one SQLite DB (`submissions/tracking.db`). Two tables drive the conveyor — `candidate_queue` (new; extends the 32-row `candidate_problems`) holds class-tagged, literature-clean, ranked targets; `proof_queue` (existing, 28 rows) holds in-flight Method-1 attempts and gets linked to `submissions.uuid` via FK. The CSV intelligence (`long_tail_erdos_candidates.csv`, `open_problems_registry_may30.csv`) is migrated **into** the DB so the orchestrator polls a live `v_method1_ready` view, never a stale flat file.

**The decoupling that makes scale safe:** authoring (CPU/API-bound) runs *far ahead* of the Aristotle slot budget, so the prover is never fed garbage. The 25-slot server cap (`check_rate_limit_and_capacity`, `safe_aristotle_submit.py:247`) governs ONLY the submit handoff. The verification gauntlet's only heavy step (real `lake build`) is throttled by a *local* core-bound worker pool, separate from the API budget. Every gate is O(1)-per-artifact and runs inside an `asyncio.Semaphore` fan-out, so N candidates gate concurrently.

**The empirical baseline this is built on (verified live):** 1252 submissions, **target_resolved=1 on ZERO rows**, cost_usd populated on 0, mathematical_content_score on 8. The two `compiled_advance` rows (Brocard id1254, Feit-Thompson id1255) are BOTH lane=bare, informal=0, target_resolved=0 — bounded extensions mislabeled as advances. The 66-row informal lane produced 0 advances because those were informal-*shaped* prompts with no strong-LLM-authored argument behind them. **Method-1 as specified has never actually run.** This plan is the first real execution of it.

---

## 2. Pipeline Stages (the gated conveyor)

### Segment 1 — INTAKE (source + class-screen + literature-dedupe + rank)
**Mechanism.** Daily idempotent sweep: `build_open_problems_registry.py` pulls all ~471 `@[category research open]` files → `screen_formal_conjectures.py` 5-TIER classifier tags each with snipe-signature (S1–S8 from `advance_dna_may30.md`) and a `deep_structural_exclude` flag → **new** `biblio_gate.py` runs a fail-CLOSED literature check (full-range arXiv + zbMATH Open + Crossref + named-conjecture cards) → composite ranking (`snipe*0.45 + closure*0.35 + neglect*0.20`) writes `candidate_queue` rows. Orchestrator polls `v_method1_ready` (WHERE literature_status='CLEAR' AND deep_structural_exclude=0 AND NOT terminal ORDER BY tractability_score DESC LIMIT N).
**Gate.** (a) CLASS: easy-tail/construction/finite-verification only — infinite-universal-only + zero GOOD_SIGNALS → excluded (the codified "reject famous-structural conjecture" rule `screen.md` lacks). (b) LITERATURE: only `CLEAR` passes; `UNKNOWN`/`AMBIGUOUS` are HELD pending cited ack (flips today's fail-OPEN). (c) FAITHFULNESS (cheap proxies at intake): em-tautology regex + answer(sorry) penalty; canonical source statement stamped into the row for the downstream diff.
**Scale lever.** Daily sweep screens all ~805 statements in minutes (regex-only); biblio_gate is the rate-limiter but 7-day cached → steady-state a few dozen network calls/day. Volume scales by lowering the tractability cutoff and adding corpus sources.

### Segment 2 — AUTHORING (multi-LLM informal argument → `.fusion.json`)
**Mechanism.** `author_argument.py` (new) takes one `candidate_queue` row: assembles a context pack (`gather_context` + `mk failed`/`mk context`), runs best-of-N (default) or debate-mode authoring across Codex gpt-5.5@xhigh (default), Gemini (long-context), and a new Claude Opus `proof-author` subagent, cross-verifies each candidate with a *different* model than authored it, runs deterministic faithfulness pre-checks, picks the single best, and emits the 9-field `.fusion.json` dossier.
**Gate.** Four fail-closed, in order: (1) DETERMINISTIC — `_looks_like_em_tautology()` + `check_statement_locked()` (byte-identical Lean signature) + `detect_failure_modes()` (iff_rfl/F9-bounded); (2) STATEMENT-FAITHFULNESS — cross-model, grader≠author, rejects weaker/mis-stated/vacuous variants (Rivin 67%); (3) LITERATURE — cross-model + zbMATH, fail-closed on UNKNOWN; (4) SCHEMA — `check_fusion_companion()` 9 fields + airlock anti-leak. Only the highest-composite survivor is emitted; rest → `failed_approaches`.
**Scale lever.** Entirely upstream of the prover budget. `asyncio.Semaphore` pool over problem_ids, with a SEPARATE per-provider API rate limiter per engine. N candidates parallelize within a problem; pool width parallelizes across problems. No `--skip-gate` flag exists — only N and width move volume.

### Segment 3 — FORMALIZE + REPAIR (informal submit → ask self-repair loop)
**Mechanism.** `method1_loop.py` (new; replaces proof_orchestrator's broken Aristotle leg, keeps its state-machine skeleton). Admission refuses any row lacking a `strategy_outline`. Each tick reads `slots_available`, submits exactly that many `(sketch + .fusion.json)` pairs in one Semaphore-bounded `asyncio.gather` wave via `build_informal_prompt()` in-process (with context tarball), folds in `fetch_backlog`'s fetch/extract/audit, and on `COMPLETE_WITH_ERRORS` runs an **ask-based self-repair loop** (`Project.ask()` → `AgentTask.wait_for_completion()`, capped at ASK_REPAIR_CAP=2 with plateau detection via `proof_queue.stall_count`).
**Gate.** Admission gate (no strategy_outline → refuse, never bare-spray) + the I9 router's `has_outline` guard (informal mode requires a non-empty outline). Subsystem-engagement check at fetch (the informal reasoner must have fired).
**Scale lever.** Fill-to-capacity against ONE shared server budget (`ARISTOTLE_MAX_CONCURRENT`, run at 40–50 for a campaign), reconciling local pools with the live slot count. Raising the cap scales volume; gates scale linearly alongside.

### Segment 4 — VERIFICATION GAUNTLET (machine-check → faithfulness → literature → promote)
**Mechanism.** `verification_gauntlet.py` (new) is the SINGLE fetch-time entry point, wired into BOTH `aristotle_fetch.update_db` AND `fetch_backlog`, replacing the hardcoded `target_resolved=0` at `aristotle_fetch.py:185`. Four ordered fail-closed gates: **G1** real `lake build` in the formal-conjectures env (mathlib 79e94a093aff) + `#print axioms` closure check + inline `detect_failure_modes()`; **G2** statement-faithfulness — L1 structural diff (hypothesis-strip / quantifier-flip / weaker-conclusion / bound-injection / definition-swap), L2 cross-model adversary on ambiguity (Gemini + Claude, NOT Grok), L3 closure-axis self-declaration cross-check; **G3** fail-CLOSED literature (zbMATH + full-range arXiv + named-conjecture cards); **G4** metrics + promotion — the EXCLUSIVE writer of `compiled_advance` and `target_resolved=1`, populates `cost_usd` (wall-clock estimate) and mandatory `mathematical_content_score`.
**Gate.** `compiled_advance` becomes the exclusive output of `run_gauntlet`; every gate fails closed (error/UNKNOWN → row stays at pre-gauntlet ceiling). Promotion ⟺ passed G1∧G2∧G3.
**Scale lever.** Cheapest-deterministic-first (G1 regex + G2-L1 diff carry the bulk at near-zero marginal cost); expensive steps (G1 lake build, G2-L2 cross-model, G3 zbMATH) are cached and fire only on ambiguity. G1's build throttled by a local core-bound worker pool, decoupled from the API budget.

---

## 3. Reuse vs. Build

### REUSE AS-IS (do not rebuild — verified correct & live)
| Asset | Path | Role |
|---|---|---|
| `build_informal_prompt()` | `scripts/aristotle_informal.py:164` | The canonical Recipe-B prompt constructor. Call in-process. |
| `fetch_backlog.py` (Semaphore(3) + tar.gz extract + audit) | `scripts/fetch_backlog.py` | The fetch/extract/audit scaling primitive. Built this session, correct. |
| `check_status` / `fetch_result` (AgentTask.status) | `scripts/aristotle_fetch.py:219/235` | Correct COMPLETE + COMPLETE_WITH_ERRORS reads. |
| `cmd_ask` core (`Project.ask`) | `scripts/aristotle_fetch.py:489/516` | The unused self-repair lever — wrap, don't rewrite. |
| `check_rate_limit_and_capacity` / slots_available | `scripts/safe_aristotle_submit.py:210/247` | The ONE capacity governor. MAX_CONCURRENT=25 env-overridable. |
| I9 informal router + `has_outline` guard | `scripts/safe_aristotle_submit.py:1782+` | Hard downstream gate; "no outline → no informal". |
| `check_fusion_companion` + airlock | `scripts/safe_aristotle_submit.py` | 9-field schema + anti-leak. The Method-1 argument container. |
| `detect_failure_modes()` | `scripts/audit_proven.py` | F1/F3/F4/F6/F9 + em-tautology + self-loop regex library. |
| `screen_formal_conjectures.py` 5-TIER classifier | `scripts/screen_formal_conjectures.py` | Easy-tail HARD/GOOD signal scorer. |
| `advance_dna_may30.md` S1–S8 taxonomy | `analysis/advance_dna_may30.md` | The selection rubric (S7 needs supplied witness = Method-1 mandate). |
| `debate.py` harness | `scripts/debate.py` | ThreadPool + full-context + per-model error isolation. Add a Method-1 round preset. |
| `codex` gpt-5.5@xhigh / `gemini` CLIs | binaries | Live-tested. Default + long-context authors. |
| `false_lemmas` / `failed_approaches` tables | `submissions/tracking.db` | 45 + 56 rows; negative-knowledge store feeding author prompts. |
| `mk` CLI (`failed`/`context`/`gaps`) | `math-forge/scripts/mk` | KB/dedup lookups for the context pack. |

### BUILD (concrete net-new — ~30% of effort)
| Artifact | What it is | Reuses |
|---|---|---|
| `scripts/biblio_gate.py` | **Fail-CLOSED literature gate** closing the 40-yr blind spot: full-range arXiv (drop the 2024 floor at `literature_check.py:280`) + zbMATH Open REST (free, api.zbmath.org) + Crossref REST + deep-research escalation on AMBIGUOUS. | `literature_check.py` sources + 7-day cache |
| `candidate_queue` table + `v_method1_ready` view | Extends `candidate_problems` with snipe_signature, tier, deep_structural_exclude, literature_status, tractability_score, terminal, argument_authored. Replaces 3 stale CSVs. | `v_candidate_ranking` view pattern |
| S1–S8 snipe auto-tagger + deep-structural exclusion | Function in `screen_formal_conjectures.py` mapping TIER+signals → snipe-class, persisted; codifies the famous-structural reject. | screen signals |
| `scripts/source_screen_run.py` | Thin daily driver chaining Stage1→4 of intake, idempotent INSERT-OR-REPLACE, cron-able. | the four intake scripts |
| `scripts/author_argument.py` | **First-class batchable authoring unit.** `--problem-id --mode best-of-N\|debate --n --models`. Stages 0–4. Records sketch_model_primary/secondary, paired_llm, cost_usd. Chains to `safe_aristotle_submit --fusion-lane`. | debate.py, build_informal_prompt, check_statement_locked, gather_context |
| `.claude/agents/proof-author.md` | **New Claude Opus authoring subagent** (math-forge ships only Sonnet research bots). The always-available 3rd ensemble author. | — |
| `scripts/method1_loop.py` | **The async state-machine driver.** Replaces proof_orchestrator's broken Aristotle leg (`get_solution()` nonexistent at :532, `str(p.status)=='COMPLETE'` dead at :511, bare `--force` at :434). Admission guard + capacity-governed parallel submit + fetch fold-in + ask self-repair + cost capture. CLI mirrors proof_orchestrator. | proof_orchestrator skeleton, fetch_backlog, cmd_ask, capacity governor |
| `scripts/verification_gauntlet.py` | **The fail-closed fetch-time gate.** `run_gauntlet()` → G1→G2→G3→G4. EXCLUSIVE writer of compiled_advance / target_resolved=1. | audit_file, detect_failure_modes, multi_agent_audit, biblio_gate, formal-conjectures .lake |
| `statement_diff()` (G2-L1) | Deterministic faithfulness checker: hypothesis-strip, quantifier-flip, weaker-conclusion, bound-injection (extend F9), definition-swap (extend F10). | extract_theorem_statement, check_statement_locked |
| `NAMED_CONJECTURE_STATUS` table | ~60 named conjectures CLOSED/OPEN + citation; the cheap pre-2024 catch. Seeded from `literature_kill_list.csv` (29 rows). | kill-list schema |
| `scripts/advance_dashboard.py` | Throughput-governance surface: advance-rate per lane/author, cost-per-advance, faithfulness/literature reject breakdowns, mislabeled-advance alarm. | submissions_audit view |
| proof_queue migration | Add author_model, argument_path, lane, faithfulness_verdict, literature_status, repair_rounds; FK aristotle_uuid→submissions.uuid. | existing schema |
| Provenance/Grok fixes | Bump `grok_query.py:15` off dead grok-4 + gate on live x.ai access; correct stale `gpt-5.2`/`gpt-5.3-codex` DB labels to gpt-5.5; ensure debate.py runs with cwd=math dir. | — |

### REPLACE (cannot drive Method-1)
- `submission_queue.py` — vestigial, calls nonexistent `aristotle submit` CLI, BARE-only, stale MAX_CONCURRENT=15. → `method1_loop.py`.
- proof_orchestrator's Aristotle leg — 3 bugs (verified at :434/:511/:532), bare-only. Skeleton kept, leg replaced.
- `literature_check.py` fail-OPEN policy + arXiv-2024 floor — → `biblio_gate.py` fail-CLOSED.

---

## 4. Throughput Plan (how aggressive, concretely)

**Target: a continuously-refilled ready-queue of 50–150 gated candidates, feeding 40–50 concurrent Aristotle slots, sustaining ~100–200 GATED Method-1 attempts/day at steady state.**

**Parallelism budget per segment (one resource each):**
- **Intake:** ~805 statements screened/day in minutes (regex). biblio_gate cached 7-day → ~few-dozen network calls/day steady-state. Never the bottleneck.
- **Authoring:** `asyncio.Semaphore` pool over problem_ids; SEPARATE per-provider rate limiter (Codex / Gemini / Claude bill independent OAuth accounts). best-of-N default N=3. A dead engine (Grok) degrades gracefully. Author throughput runs FAR ahead of the prover — by design, no garbage reaches Aristotle.
- **Formalize:** the single hard ceiling = the shared Aristotle slot budget. Run `ARISTOTLE_MAX_CONCURRENT=40–50` (demonstrably already exceeded 25 → 36 in flight, so the server tolerates it). Each tick fills to `slots_available`. Ask self-repair capped at 2 rounds/job.
- **Verification:** G1 lake build is the only CPU-heavy step (300s cap, isolated scratch lib) → throttle with a local build-worker pool sized to cores (≈ N_cores), DECOUPLED from the API budget. G2-L1/G2-L2/G3 cached; common path (G1 regex + G2-L1 diff) is free.

**Why this is "aggressive" without being spray:** every one of those 40–50 concurrent slots is occupied by a strong-LLM-authored, literature-cleared, statement-faithful dossier that survived 4 author-side fail-closed gates. Admission to Segment 3 *requires* a strategy_outline. There is no code path that submits without authoring. Raising the cap raises gated attempts, not bare attempts.

**Cost envelope.** Today cost_usd is 0/1252 — totally uninstrumented, which is itself the risk. The plan makes cost first-class:
- Authoring cost = per-call token cost from Codex/Gemini/Claude OAuth accounts, written to `cost_usd` at author time (best-of-N × N candidates × ensemble = the dominant spend).
- Aristotle cost = wall-clock estimate (`last_updated_at - created_at`) × configurable RATE (no SDK cost field exists — verified; label it directional on the dashboard).
- **Daily $-budget governor:** env `$CAP` checked before each submit wave; campaign pauses when projected spend exceeds cap. `advance_dashboard.py` reports **cost-per-advance** per author/class so unproductive engines/classes get cut. Without this, "aggressive scale" degenerates into untracked spend.

**Honest expectation.** Project hit rate on the hard long tail is ~0.8%; target_resolved=1 is currently 0/1252. The realistic near-term goal is **the first genuine target_resolved=1 under a fail-closed gauntlet** + a measurable, attributable advance-rate per author/class — NOT a flood of advances. The gauntlet will likely hold honest advances at 0 for a while; that is the gate working, not a regression.

---

## 5. Quality Safeguards (NON-NEGOTIABLE, scale with volume)

These three gates are the entire point. Each is a per-row/per-artifact DB column or O(1) check inside an async fan-out, so **adding volume adds gate executions 1:1**. Dropping a gate = leaving a column NULL = the row never promotes. There is deliberately no faster path.

1. **EASY-TAIL SELECTION (intake, Segment 1).** Only the construction/finite-verification/witness class auto-passes. `deep_structural_exclude=1` for infinite-universal-only + zero GOOD_SIGNALS — the codified reject of famous-structural conjectures (~0% yield everywhere). Scales O(1)/candidate via the regex classifier. *Without it: slots burned on problems that never yield.*

2. **LITERATURE-DISENTANGLEMENT (intake + author + verify; fail-CLOSED).** Closes the verified ~40-yr pre-2024 blind spot: zbMATH Open + Crossref + full-range arXiv + named-conjecture cards replace the arXiv-2024-floored, MathSciNet/zbMATH-zero, fail-OPEN current gate. `UNKNOWN`/`AMBIGUOUS` are HELD, not passed. Run at THREE points (intake, author stage-2, verify G3) so a Le-2012-class already-solved problem is caught before a slot is spent AND before an advance is claimed. One cached bibliographic call/problem → scales trivially. *Without it: the Erdősgate trap — higher throughput = more false "open" advances.*

3. **STATEMENT-FAITHFULNESS (author + verify; fail-CLOSED).** The Rivin ~33%-wrong-theorem gate, which **does not exist today** (grep faithful/statement_match = 0). Author-side: cross-model grader≠author rejects weaker/vacuous variants. Verify-side G2: deterministic structural diff (hypothesis-strip / quantifier-flip / weaker-conclusion / bound-injection / definition-swap) + cross-model adversary on ambiguity. `compiled_advance` ⟺ passed this. One diff + one cached detect_failure_modes per artifact → O(1). *Without it: clean-compiling weaker theorems land silently as advances — exactly the 2 mislabeled rows today.*

**Self-enforcing invariants (asserted continuously by `advance_dashboard.py`):**
- `target_resolved=1` ⟺ row passed G1∧G2∧G3 (any violation = CRITICAL regression).
- `cost_usd` and `mathematical_content_score` non-NULL on 100% of compiled_* rows (today 0 and 8 — the completeness alarm).
- The 2 existing `compiled_advance` rows (Brocard, Feit-Thompson) are re-run through the gauntlet on first deploy and **will be downgraded** by G2's bound-injection check — proving the gate rejects the project's own historical false positives.

---

## 6. Phased Roadmap

| Phase | Deliverable | Effort | Depends on |
|---|---|---|---|
| **P0 — Unblock the verdict wire** | Replace hardcoded `target_resolved=0` (`aristotle_fetch.py:185`) with a `run_gauntlet` verdict stub; G1 real lake build against formal-conjectures env (mathlib 79e94a093aff) + `#print axioms`; promote `detect_failure_modes()` to mandatory inline. Re-run the 2 mislabeled advances. | M (~2d) | audit_file, detect_failure_modes, formal-conjectures .lake, codex_proof_loop symlink pattern |
| **P1 — Close the literature hole** | `biblio_gate.py` (zbMATH + Crossref + full-range arXiv, fail-CLOSED); NAMED_CONJECTURE_STATUS table seeded from kill-list. Highest priority — defeats Erdősgate. | M (~1.5–2d) | literature_check.py sources, deep-research skill |
| **P2 — Statement-faithfulness gate** | G2-L1 `statement_diff()` (deterministic) + G2-L2 cross-model adversary (Gemini+Claude, drop Grok); fix `multi_agent_audit.py` dead grok-4. The Rivin gate. | M (~2–3d) | extract_theorem_statement, check_statement_locked, multi_agent_audit |
| **P3 — DB-backed intake queue** | `candidate_queue` table + `v_method1_ready` view; redirect registry + screen outputs to DB; S1–S8 auto-tagger + deep-structural exclusion; `source_screen_run.py` daily driver; wire biblio_gate into screen/sweep. | M (~2d) | P1 (biblio_gate), build_open_problems_registry, screen_formal_conjectures |
| **P4 — Authoring engine** | `author_argument.py` (best-of-N + debate); `.claude/agents/proof-author.md`; cross-model verification rubric; fix stale model labels + Grok gating; chain to `safe_aristotle_submit --fusion-lane`. | M (~3d) | P2 (faithfulness rubric), debate.py, build_informal_prompt, gather_context |
| **P5 — Method-1 loop driver** | `method1_loop.py` (admission guard + capacity-governed parallel submit + fetch fold-in + ask self-repair + cost capture); proof_queue migration + FK; daily $-budget governor. | M (~3d) | P3 (queue), P4 (dossiers), fetch_backlog, cmd_ask, capacity governor |
| **P6 — Full gauntlet + dashboard** | Wire `verification_gauntlet.py` into BOTH fetch paths; G3 fail-closed at verify; G4 metrics (cost_usd + mandatory mcs); `advance_dashboard.py` with the 3 invariants. | M (~1.5d) | P0, P1, P2 |
| **P7 — Campaign** | Run a 50–150-candidate gated campaign at `ARISTOTLE_MAX_CONCURRENT=40`; measure advance-rate, cost-per-advance, gate-reject breakdown per author/class; tune. | — | all above |

**Total net-new build:** ~3 weeks of focused work (~70% reuse). The two genuinely hard algorithmic pieces are `statement_diff()` (P2) and `biblio_gate.py` recall (P1); everything else is composition/wiring over verified-live assets.

---

## 7. Risks & Mitigations

1. **Statement-faithfulness diffing is genuinely hard** (notation, implicit args, defeq). Too-strict → false-REJECTS faithful proofs (acceptable: fails-closed, costs an advance not a false positive); too-loose → weaker variants pass (UNacceptable). **Mitigation:** err strict at G2-L1, route ALL ambiguity to the L2 cross-model unanimity check, never auto-pass; keep compiled_advance opt-in so a miss yields compiled_no_advance.
2. **Literature gate recall** — zbMATH/Crossref keyword search can miss a closure under different terminology; famous-conjecture status is often folklore not a citable paper. **Mitigation:** fail-CLOSED-on-UNKNOWN (holding is safe, passing a closed problem is not) + NAMED_CONJECTURE_STATUS cards + deep-research escalation on AMBIGUOUS. Accept that many legitimately-open rows are HELD.
3. **Grok is dead** (re-confirmed: grok-4.3 "team … does not have access"; `grok_query.py:15` pins dead grok-4). **Mitigation:** ship Codex+Gemini+Claude default, substitute Gemini+WebSearch for live literature, isolate the dead node (debate.py already does). Restore x.ai team billing as a stretch.
4. **Concurrency runaway** — 36 already in flight vs 25 cap proves `--batch` can violate the cap. **Mitigation:** re-check `slots_available` before EVERY wave; single governor reconciling local pools with the one server budget.
5. **Cross-model collusion** — all LLMs share blind spots, can co-sign plausible-but-wrong arguments. **Mitigation:** deterministic G1/G2-L1 + zbMATH are the non-LLM backstop; compiled_advance requires the post-fetch gauntlet too.
6. **Cost is uninstrumented + estimated** — cost_usd 0/1252 today; no SDK cost field exists (verified). **Mitigation:** write authoring token cost at author time + Aristotle wall-clock estimate at fetch; daily $CAP governor; label cost-per-advance "directional" on the dashboard.
7. **Cold lake-build cache** can exceed the 300s G1 cap → fails-closed (under-counts). **Mitigation:** warm the mathlib cache; per-core build-worker pool decoupled from the API budget; build against the CORRECT rev (79e94a093aff), NOT codex_proof_loop's mismatched f897ebcf.
8. **Cultural: making compiled_advance fail-closed will hold the honest count at 0 for a while.** That is the gate working, not failing. **Mitigation:** the dashboard frames 0 honest advances as the truthful baseline the mission is built on, not a metric to tune away.
9. **Stale model labels** (gpt-5.2 / gpt-5.3-codex vs runtime gpt-5.5) corrupt the "which author produces advances?" audit query. **Mitigation:** fix labels before P7.

---

## 8. First Concrete Steps (in order)

1. **Wire the verdict (smallest, most load-bearing change).** Edit `scripts/aristotle_fetch.py:185` to call a new `verification_gauntlet.run_gauntlet()` instead of writing literal `0` for target_resolved. Start the gauntlet as a stub that returns the current audit verdict, then layer G1.
2. **Build G1 real lake build.** Reuse `codex_proof_loop.py`'s symlink pattern (`:177–198`) but repoint at `formal-conjectures/.lake` + `lean-toolchain` (mathlib **79e94a093aff** / lean4 v4.22.0). Add `#print axioms <main>` subset-check. Re-run the 2 mislabeled `compiled_advance` rows (id1254 Brocard, id1255 Feit-Thompson) — confirm G2's bound-injection check downgrades them.
3. **Build `biblio_gate.py`.** Add zbMATH Open REST + Crossref clients; remove the arXiv 2024 floor (`literature_check.py:280` → `[199101010000 TO 202612312359]`); flip fail-OPEN → fail-CLOSED on UNKNOWN. Seed NAMED_CONJECTURE_STATUS from `analysis/literature_kill_list.csv`.
4. **Build `statement_diff()` (G2-L1).** Reuse `codex_proof_loop.extract_theorem_statement` + `check_statement_locked`; extend `audit_proven.py`'s F9 (bound-injection, source-relative) and F10 (definition-swap). Route ambiguity to a G2-L2 wrapper over `multi_agent_audit.py` (Gemini + Claude — fix the dead grok-4 at `multi_agent_audit.py:69` first).
5. **Migrate intake to DB.** Create `candidate_queue` + `v_method1_ready`; redirect `build_open_problems_registry.py` output to DB rows; add the S1–S8 auto-tagger + deep_structural_exclude to `screen_formal_conjectures.py`; wire `biblio_gate` into `screen.md`/`sweep.md`.
6. **Build `author_argument.py`.** Compose the 5 stages over `debate.py` (add a Method-1 round preset), `build_informal_prompt` (in-process), `gather_context`, and `check_statement_locked`. Create `.claude/agents/proof-author.md` (Claude Opus). Default engine = Codex gpt-5.5@xhigh; ensemble = Codex+Gemini+Claude (Grok excluded). Record cost_usd + sketch_model_primary/secondary. Chain to `safe_aristotle_submit --fusion-lane`.
7. **Build `method1_loop.py`.** Fork proof_orchestrator's state-machine skeleton, DELETE its Aristotle leg (`get_solution()` at :532, `str(p.status)=='COMPLETE'` at :511, bare `--force` at :434), and replace with: admission guard (refuse no-outline rows) → capacity-governed parallel informal submit (Semaphore + `slots_available` re-check + `build_informal_prompt`) → `fetch_backlog` fold-in → `Project.ask()` self-repair loop (cap 2, plateau via `proof_queue.stall_count`) → cost capture. Add proof_queue migration + FK to submissions.uuid. Add the daily $CAP governor.
8. **Build `advance_dashboard.py`** and run a small smoke campaign: `ARISTOTLE_MAX_CONCURRENT=40 python3 scripts/method1_loop.py run` against the top ~20 `v_method1_ready` rows. Assert the 3 invariants; read cost-per-advance and gate-reject breakdowns; tune N and cap.
