# ATTACK_WORKFLOW.md — unified operational pipeline

**Updated:** 2026-05-28 (post-em-tautology fix + schema honesty + TARGETS_2026_05 debate)

This doc maps every available tool to its phase in the attack on open problems. Future sessions should treat this as the operational source of truth.

---

## Tool inventory

### Aristotle CLI 2.0 (verified `aristotle --version` = 2.0.0)
| Command | Use |
|---|---|
| `aristotle submit "<prompt>" [--project-dir DIR] [--wait]` | Fresh project submission (text or directory bundle) |
| `aristotle ask <project-id> "<prompt>"` | Follow-up AgentTask on existing project (no re-upload) |
| `aristotle formalize <file> [--wait]` | Submit a paper/file for formalization |
| `aristotle show <project-id> [--task TASK_ID]` | Stream event-level progress (THINKING, PROVING, RUNNING_LEAN…) |
| `aristotle tasks <project-id>` | List all tasks on a project (a project can have many) |
| `aristotle list [--limit N]` | Recent projects |
| `aristotle download <project-id>` | Pull result tarball |
| `aristotle cancel <project-id-or-task-id>` | Abort in-flight |

**SDK 2.0 highlights:** `TaskStatus` enum distinguishes `COMPLETE` / `COMPLETE_WITH_ERRORS` / `OUT_OF_BUDGET`. 14 `EventType` values stream live. `Project.ask()` is the bridge for COMPLETE_WITH_ERRORS recovery.

### Our scripts (`scripts/*.py`)
| Script | Purpose | Notes |
|---|---|---|
| `safe_aristotle_submit.py` | Gated submission with lockfile + rate-limit + duplicate guard | em-tautology gate active; `--force` for legit exceptions |
| `aristotle_fetch.py` | status / fetch / track / resub / **ask** | `ask <slot> "<prompt>"` is the SDK 2.0 follow-up entrypoint |
| `aristotle_queue.py` | Queue management (uses SDK Project.create directly now) | |
| `aristotle_monitor.py` | Live monitor with download_output via `get_files()` | |
| `audit_proven.py` | em-pattern + axiom_count + axiomatizes_prior_work | Only flags; never auto-promotes to compiled_advance |
| `codex_proof_loop.py` | Codex CLI iterates a Lean file against `lake build` | Output saved to `codex_proofs` table |
| `proof_orchestrator.py` | Autonomous Codex↔Aristotle queue (`enqueue/run/status/cancel/retry`) | State machine; long-running daemon |
| `migrations/run.py` | Generic SQL migration runner with auto-backup | |
| `screen_formal_conjectures.py` | Quick OPEN/SKIP binary screen | Used by `/screen` |

### `mk` (math-forge knowledge CLI)
| Command | Use |
|---|---|
| `mk search "<query>"` | FTS5+BM25 over knowledge.db |
| `mk find <problem_id>` | Problem-level report (lemmas, attempts, sketches) |
| `mk failed [keyword]` | Disproved/dead-end approaches — **check before sketching** |
| `mk context <problem_id>` | Prior Aristotle results for auto-context (note: currently returns empty for many; check `submissions` table directly as backup) |
| `mk gaps` | Open gaps being targeted + status |
| `mk codex [problem_id]` | Codex proof history |
| `mk codex-best <problem_id>` | Best compiled Codex proof path |
| `mk stats` | Dashboard |
| `mk query "<sql>"` | Read-only SQL on tracking.db |
| `mk partials` | Near-miss submissions (sorry=1) — resub candidates |
| `mk resubmittable` | Resubmission candidates |
| `mk strategies [domain]` | Proven techniques by frequency |

### Slash commands (`.claude/commands/*.md`)
| Command | Purpose |
|---|---|
| `/sketch <problem>` | Write bare-gap sketch ≤30 lines (now: existence OR impossibility, never disjunction) |
| `/submit <file> [slot]` | Gap-targeting gate → auto-context → submit INFORMAL |
| `/sweep [--domain nt]` | Scan for open gaps → state bare → submit |
| `/fetch <uuid-or-slot>` | Download → audit → gap-resolution assessment |
| `/status [uuid-or-slot]` | Aristotle queue & job status |
| `/screen <problem>` | Binary OPEN → submit / NOT_OPEN → skip |
| `/screen-batch <dir>` | Batch screen |
| `/audit <file.lean>` | Audit result for gap resolution (em + axiom checks) |
| `/process-result <file>` | Audit + DB update |
| `/optimize <file>` | Always: state gap bare, submit INFORMAL |
| `/codex-prove <problem>` | Codex proof loop |
| `/debate "<topic>" --context <file>` | Multi-AI debate (Grok+Gemini+Codex with full context accumulation) |

### External AI access (live state)
| Model | Status | Use via |
|---|---|---|
| Claude Opus 4.7 (this session) | ✅ Always | Direct + Agent tool |
| Codex CLI (defaults to GPT-5.5 now) | ✅ Working | `codex exec [-m gpt-5.5-pro]` or `codex_proof_loop.py` |
| Gemini 2.5 Flash | ✅ Working (but not for reasoning) | `gemini -m gemini-2.5-flash` |
| Gemini 3.1 Pro / 3 Deep Think / 3.5 Flash | ❌ 404 | Needs tier upgrade |
| GPT-5.5 Pro (named) | ⚠️ Reconnect | Same Codex CLI, intermittent |
| Grok via debate harness | ❌ SSL curl-35 | `grok-search` skill is a separate path that may work |

### Skills (`Skill` tool)
- `grok-search` — Grok with live X/Twitter + web search (separate from /debate path)
- `grok-ask` — Grok fast reasoning
- `grok-review` — Grok code review
- `gemini-analyze` — Gemini deep architecture/security analysis (1M context)
- `gemini-review` — Gemini code review
- `codex-task` — Delegate task to Codex CLI
- `codex-review` — Code review with Codex
- `multi-review` — Grok + Gemini in parallel
- `debate` — Full multi-AI debate harness

### DB tables (post schema-honesty)
| Table | Use |
|---|---|
| `submissions` | All Aristotle jobs; new vocab `{submitted, compile_failed, compiled_partial, compiled_no_advance, compiled_advance, disproven}` |
| `codex_proofs` | Codex proof loop results; `promoted_to_aristotle` flag |
| `proof_queue` | Autonomous orchestrator state machine |
| `false_lemmas` | Disproved claims — check before submitting |
| `failed_approaches` | Dead-end approaches per frontier |
| `erdos_problems` | 219-entry Erdős registry (`open=1` flag) |
| `erdos_formal` | 443-entry formalized Erdős (`has_sorry=1` flag) |
| `candidate_problems` | 32 scored candidates |
| `frontiers` | 10 research frontiers |

### formal-conjectures repo (`./formal-conjectures/`)
| Path | Use |
|---|---|
| `FormalConjectures/ErdosProblems/<N>.lean` | Per-Erdős-number Lean statement (many problems) |
| `FormalConjectures/Wikipedia/<Name>.lean` | Named conjectures (Brocard, Leinster, FeitThompson…) |
| `FormalConjectures/Arxiv/`, `Books/`, `Paper/`, etc. | Source-organized other conjectures |

---

## 7-phase pipeline (per target)

### PHASE 1 — Pre-flight
**Goal:** confirm target is real, untouched-with-new-tools, gate-acceptable.

```bash
# 1a. Find the Lean target
find formal-conjectures -name "*.lean" -ipath "*<keyword>*" | head
grep -rli "<concept>" formal-conjectures/ | head

# 1b. Check prior work (3 sources)
mk find <problem_id>                                # math-forge knowledge
mk failed <keyword>                                  # dead ends
mk query "SELECT id, status, contribution_statement FROM submissions WHERE problem_id='<id>' ORDER BY id DESC LIMIT 5"

# 1c. Decide form: existence-only / impossibility-only / split / ask-follow-up
#     - Both directions trivially decidable? skip (em-tautology)
#     - Strong prior partial under current key? ask-follow-up
#     - Strong prior partial under different key? fresh submission with --project-dir bundling the .lean
#     - Cold problem? existence-only first; impossibility-only later if existence compile_no_advance
```

### PHASE 2 — Sketch preparation
**Goal:** produce a `.txt` that passes the new gate and includes a contribution_statement.

Today Claude Opus 4.7 (this session) is the only reliable sketch writer (Gemini 3.x = 404, GPT-5.5 Pro = transport). When Gemini access lands, the recommended path is `informal_sketch.py --mode hybrid` per IMPLEMENTATION_PLAN.md.

```bash
# 2a. Draft sketch (Claude writes directly into submissions/sketches/<name>.txt)
#     Required structure:
#         OPEN GAP: <title>
#         Source: <formal-conjectures path>
#         Domain: <nt|algebra|combinatorics|analysis>
#         <1-3 sentence English statement>
#         theorem ... : <SINGLE direction, not disjunction> := by sorry
#         Status: OPEN. <one-sentence summary of what's known>
#         contribution_statement: <one sentence stating what target_resolved=1 would mean>

# 2b. Gate test BEFORE submission
python3 -c "
import sys; sys.path.insert(0, 'scripts')
from safe_aristotle_submit import check_gap_targeting
from pathlib import Path
print(check_gap_targeting(Path('submissions/sketches/<name>.txt')))
"
```

### PHASE 3 — Submission
**Goal:** get the project into Aristotle's queue with full provenance.

Two paths:

```bash
# 3a. FRESH submission (Aristotle has no prior state)
python3 scripts/safe_aristotle_submit.py submissions/sketches/<name>.txt <slot_num>
# OR with prior-result context bundled (when Project.ask is blocked by 403):
aristotle submit "$(cat submissions/sketches/<name>.txt)" \
    --project-dir prior_context_dir/

# 3b. ASK follow-up (existing project owned by current key)
python3 scripts/aristotle_fetch.py ask <slot> "<delta-only prompt>"

# 3c. DB tagging (the script doesn't auto-insert; SQL UPDATE after submission)
sqlite3 submissions/tracking.db "
  INSERT INTO submissions (filename, uuid, problem_id, pattern, status, frontier_id,
                           notes, submitted_at, experiment_arm, sketch_model_primary,
                           sketch_hash, prior_context_used)
  VALUES (...);"
```

### PHASE 4 — Monitoring
**Goal:** know what Aristotle is doing without waiting 9 hours blind.

```bash
# 4a. Cheap status check
python3 scripts/aristotle_fetch.py status

# 4b. Live event stream (SDK 2.0 new)
aristotle show <project-id> --limit 20      # shows latest 20 events

# 4c. Cancel if obviously stuck
aristotle cancel <project-id>
```

Live events to watch: `THINKING`, `PROVING`, `EDITING_FILE`, `RUNNING_LEAN`, `READING_FILES`, `SEARCHING_EXTERNAL`, `ERROR`, `FINISHED`. A long `THINKING` plateau without `EDITING_FILE` or `RUNNING_LEAN` is a stuck signal.

### PHASE 5 — Audit + classify
**Goal:** turn raw Lean output into one of the 6 honest statuses.

```bash
# 5a. Fetch (downloads tarball, extracts result file)
python3 scripts/aristotle_fetch.py fetch <slot>
# OR for batch:
python3 scripts/aristotle_fetch.py fetch    # all completed unfetched

# 5b. Audit (em-tautology + axiom + contribution check)
python3 scripts/audit_proven.py

# 5c. Manual gate-resolution check (REQUIRED before claiming target_resolved=1)
sqlite3 submissions/tracking.db "
  UPDATE submissions
  SET target_resolved=1, contribution_statement='<one-sentence what changed>'
  WHERE uuid='<uuid>' AND axiomatizes_prior_work=0 AND sorry_count=0;"
```

**Decision rule:**
- `em-tautology` flag → reject; rewrite sketch with new single-direction statement
- `axiomatizes_prior_work=1` → `compiled_no_advance`, refuse promotion
- Has `contribution_statement NOT NULL` AND `target_resolved` checked manually → `compiled_advance`
- Has non-trivial partial proven but didn't close → `compiled_partial`; pivot via Phase 6

### PHASE 6 — `ask` follow-up (the SDK 2.0 capability)
**Goal:** push a partial across the line without re-uploading the project.

```bash
# After Phase 5 returns compiled_partial or COMPLETE_WITH_ERRORS:
python3 scripts/aristotle_fetch.py ask <slot> "<delta prompt that EXCLUDES already-proven lemmas>"
# Example delta prompt:
#   "Using lemma_X and lemma_Y already proven in this project, derive the final
#    contradiction in case q≡71 mod 72. Do NOT re-derive lemma_X. State which
#    open conjecture this closes in the contribution_statement comment."
```

If `Project.from_id()` 403s (current key doesn't own the original UUID), fall back to a fresh `aristotle submit` with `--project-dir` containing the prior result.lean.

### PHASE 7 — Cross-AI verification (high-stakes decisions only)
**Goal:** when a result looks like a real `target_resolved=1`, validate before claiming.

```bash
# 7a. Multi-AI debate on whether the result actually resolves the gap
python3 scripts/debate.py --context <result-path> --topic "Does this Lean file resolve the open gap?" --rounds 3 --models grok,gemini,codex --output docs/research/verify_<slot>.md

# 7b. Independent grok-search for "has anyone published this since"
Skill grok-search "<problem name> resolved 2026 proof"

# 7c. Independent gemini-analyze on the full Lean file
Skill gemini-analyze submissions/nu4_final/slot<N>_result.lean
```

Only mark `target_resolved=1` AFTER at least one cross-AI signoff.

---

## Per-target dispatch (TARGETS_2026_05.md operationalized)

### Target 1 — `feit_thompson` (highest priority)
- **Form:** existence+impossibility split, but Phase-3a (fresh submission with `--project-dir`) because slot 613 = 403
- **Lean target:** `formal-conjectures/FormalConjectures/Wikipedia/FeitThompsonPrimeConjecture.lean` — `theorem feit_thompson_primes (p q hp hq h) : ¬ (q^p - 1)/(q-1) ∣ (p^q - 1)/(p-1)`. **Already an impossibility statement, single-direction. Gate-safe.**
- **Phase 1:** `mk find feit_thompson` + read `submissions/nu4_final/slot613_ft_p3_wieferich_kA2_result.lean` (381 lines, real Wieferich structure theory)
- **Phase 2 sketch:** bundles slot 613's .lean as context, asks Aristotle to extend the Wieferich theory to the final contradiction for p=3, q=71
- **Phase 3:** `aristotle submit "<prompt>" --project-dir /tmp/ft_context/` where `/tmp/ft_context/` contains slot 613 and 612 result files
- **Slot:** 720

### Target 2 — `Leinster: Nonabelian Leinster exists (S3×C5)`
- **Form:** existence-only
- **Lean target:** Custom — `formal-conjectures/FormalConjectures/Wikipedia/LeinsterGroup.lean` defines `LeinsterGroup.IsLeinster`; we need a new theorem witnessing it on S3×C5 (Equiv.Perm (Fin 3) × ZMod 5)
- **Approach:** `native_decide` on Fin 30 (group order is 6×5=30)
- **Phase 2 sketch:** existence-only statement asking Aristotle to prove `IsLeinster (Equiv.Perm (Fin 3) × ZMod 5)` and to use `native_decide` if possible
- **Slot:** 721

### Target 3 — `brocard`
- **Form:** impossibility-only first (per debate Round 3)
- **Lean target:** `formal-conjectures/FormalConjectures/Wikipedia/BrocardConjecture.lean` — `∀ n ≥ 1, 4 ≤ card primes in (p_n², p_{n+1}²)`. **Already universal-quantifier, single-direction. Gate-safe.**
- **Range pick:** start with `n ∈ [2, 50]` — small enough to be computational, large enough to be a non-trivial bound (Ferreira proved for sufficiently large n; the gap is small n)
- **Phase 2 sketch:** ask Aristotle to verify Brocard's conjecture for all `n ∈ [2, 50]` using a computational decide tactic
- **Slot:** 722

### Target 4 — `erdos_647`
- **Form:** existence-only
- **Lean target:** `formal-conjectures/FormalConjectures/ErdosProblems/647.lean` (62 lines — need to read to extract exact statement)
- **Phase 2 sketch:** must explicitly EXCLUDE the prior sub-results `tau_ge_two`, `exists_large_m_plus_tau`, `max_m_plus_tau_unbounded`
- **Slot:** 723

### Target 5 — `erdos_203`
- **Form:** existence-only
- **Lean target:** `formal-conjectures/FormalConjectures/ErdosProblems/203.lean` (37 lines)
- **Phase 2 sketch:** pick from the 8 staged variants in `submissions/sketches/erdos203_*.txt` (covering-systems domain) — read each, gate-test each, pick the cleanest
- **Slot:** 724

---

## Failure-mode dictionary (what each output means and what to do next)

| Output / status | What it means | Next move |
|---|---|---|
| Gate REJECTED (em-tautology) | Sketch is `(P) ∨ ¬ (P)` | Rewrite as existence-only OR impossibility-only |
| Gate REJECTED (>30 lines) | Sketch has too much prose | Trim to bare statement |
| Gate REJECTED (strategy keywords) | Sketch has "Proof Strategy" or "Key Lemma" | Strip strategy; let Aristotle find path |
| `compile_failed` | Lean didn't accept | Read error in result; if syntactic, rewrite; if dependency, add to `--project-dir` |
| `compiled_partial` (sorry > 0) | Aristotle proved some sub-lemmas | Phase 6 `ask` with delta prompt |
| `compiled_no_advance` + `axiom_count=0` | Compiles cleanly but no novel result | Check em-tautology; if not, rewrite to a stronger statement |
| `compiled_no_advance` + `axiomatizes_prior_work=1` | Axiomatized known lemmas | Resubmit without the axioms; require Aristotle to prove them |
| `COMPLETE_WITH_ERRORS` / `OUT_OF_BUDGET` | Ran out of budget | Phase 6 `ask` to continue from latest state |
| `compiled_advance` | Real advance — but verify | Phase 7 cross-AI; only then mark `target_resolved=1` |
| `disproven` | Aristotle found a counterexample | Add to `false_lemmas`; reformulate or skip |

---

## When to use what (cheat sheet)

| Situation | Tool |
|---|---|
| "What do we know about <problem>?" | `mk find <problem>` + `mk context <problem>` |
| "Has this approach failed before?" | `mk failed <keyword>` |
| "Find the Lean statement for <problem>" | `find formal-conjectures -name "*.lean" -ipath "*<keyword>*"` |
| "Is my sketch gate-safe?" | `python3 -c "from safe_aristotle_submit import check_gap_targeting; ..."` |
| "Submit a sketch" | `python3 scripts/safe_aristotle_submit.py <file> <slot>` |
| "Follow up on a partial" | `python3 scripts/aristotle_fetch.py ask <slot> "..."` |
| "What's in the queue?" | `python3 scripts/aristotle_fetch.py status` |
| "Stream live events" | `aristotle show <project-id>` |
| "Multi-AI 2nd opinion" | `python3 scripts/debate.py --topic "..." --context <file> --rounds 3` |
| "Autonomous Codex iteration on a Lean file" | `python3 scripts/codex_proof_loop.py <problem_id>` |
| "Autonomous Codex↔Aristotle loop" | `python3 scripts/proof_orchestrator.py enqueue <problem> && proof_orchestrator.py run` |
| "Read-only SQL on the DB" | `mk query "<SELECT...>"` |

---

## Hard constraints (the ALWAYS list)

1. **Never `(P) ∨ ¬ (P)`** — gate enforces, but as a writer never produce it
2. **Always include `contribution_statement` in the sketch** — auditor blocks `compiled_advance` without it
3. **Never axiomatize prior work** — `axiomatizes_prior_work=1` blocks `compiled_advance`
4. **Never `target_resolved=1` without Phase 7 cross-AI verification** — too costly to over-claim
5. **Never re-submit a previously-disproven approach** — check `false_lemmas` first
6. **Always tag `experiment_arm` + `pattern`** for new pilot rows
7. **Never bypass the gate without `--force` AND a documented reason** in the DB notes field
