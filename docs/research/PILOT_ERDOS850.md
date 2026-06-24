# PILOT_ERDOS850 — 1-problem 3-arm mini-pilot

**Launched:** 2026-05-28
**Completed:** 2026-05-28 (~9 hours wall-clock per arm)
**Target:** Erdős Problem 850 (do there exist distinct positive x, y with rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2)?)
**Purpose:** Smoke-test the new schema-honesty pipeline + Claude sketch arm + project.ask() integration end-to-end on a single open problem.

## ⚡ Headline finding

**All 3 arms returned identical pathological output:** `exact em _` (excluded middle).

The bare-conjecture template `(∃ x y, P(x,y)) ∨ ¬ (∃ x y, P(x,y))` is **structurally** the law of excluded middle. Aristotle discharged it in one line — without engaging the open problem. Even the Claude sketch arm (B) produced the same em proof, because the underlying theorem statement is already trivially provable; no sketch can override that.

Aristotle was explicit in every summary:
> "the formal statement as given is a disjunction trivially true by excluded middle and does not resolve the open problem in either direction."

**Root cause is at the THEOREM STATEMENT level, not the method level.** Sketches, hybrid models, and `project.ask()` follow-ups cannot fix a goal that's already a tautology.

## Why erdos850

- Open Erdős NT problem with clear formal-conjectures statement
- 5 prior Aristotle submissions for context (slots 614, 702, 705, 706 etc.)
- Pure number theory — Aristotle's strongest domain per arxiv 2510.01346
- NOT Tuza (avoids 317-attempt contamination)
- Existing bare sketch already written (`submissions/sketches/erdos850_bare.txt`)

## The 3 arms

| Arm | Slot | UUID | Submission | Provenance |
|---|---|---|---|---|
| **A — bare control** | 717 | 85d169be… | erdos850_bare.txt (15 lines) | experiment_arm='bare', pattern='bare_baseline_v1' |
| **B — sketch-first** | 718 | 9fe5b59c… | slot718_erdos850_claude_sketch.txt (71 lines, --force) | experiment_arm='sketch_first', sketch_model_primary='claude-opus-4-7' |
| **C — bare-then-ask** | 719 | f3337df8… | erdos850_bare.txt (15 lines, --force to bypass dup-guard) | experiment_arm='bare_then_ask', sketch_hash matches arm A |

## Results (audited 2026-05-28)

| Slot | Arm | Aristotle status | Audit verdict | axiom_count | Output |
|---|---|---|---|---|---|
| 717 | bare control | COMPLETE 100% | em-tautology | 0 | `exact em _` (21 lines incl. boilerplate) |
| 718 | Claude sketch-first | COMPLETE 100% | em-tautology | 0 | `exact em _` (24 lines; sketch ignored) |
| 719 | bare-then-ask seed | COMPLETE 100% | em-tautology | 0 | `exact em _` (40 lines; no error state to trigger ask) |

All 3 status fields in `submissions` table are `compiled_no_advance` with `target_resolved=0` and `contribution_statement='TAUTOLOGY: …'`. Result files at `submissions/nu4_final/slot71{7,8,9}_erdos850_pilot_result.lean`.

**Arm C's `project.ask()` mechanic never fired** because the bare submission completed without errors — there was no `COMPLETE_WITH_ERRORS` to trigger the follow-up. The mechanic remains untested; it'll only be exercised once we submit a sketch that genuinely fails.

## What the pilot revealed

The decision rule was: "succeeds if Arm B produces better than Arm A, or Arm C beats Arm A's terminal state, or at minimum the plumbing works."

**Plumbing:** ✅ all 3 schema columns populated correctly; new `project.ask()` CLI deployed; provenance JSON written; DB rows tagged.
**Method comparison:** ⛔ uninformative — every arm produced identical em-tautologies, so we can't distinguish sketch vs. bare from this data.
**Honest signal:** ⚠️ the failure mode itself is the most valuable finding — it reveals that the *theorem statement template* in `erdos850_bare.txt` (and likely many others) was structurally broken from the start. The PRIME DIRECTIVE was masking this for 1,157 prior submissions.

## Remediation applied (2026-05-28)

1. **`safe_aristotle_submit.py` gate** — `check_gap_targeting()` now rejects any theorem of the form `(P) ∨ ¬ (P)` at submission time with an actionable error message and a reference to this doc. See `_looks_like_em_tautology()`.
2. **`audit_proven.py` detector** — adds a CRITICAL issue when an output file's theorem body matches the em-tautology shape AND the proof uses `exact em _` / `Classical.em` / `Decidable.em`. Detects the goal-only shape too (in case Aristotle finds a non-em proof of the same trivial goal).
3. **Backlog scan** — 233 `compiled_no_advance` rows with output files were scanned. Only 3 em-pattern hits (our 3 pilot rows); the historical backlog was NOT polluted by em-tautologies. The dominant historical pathology was axiom-stuffing (135/211 per db-analyst), which the schema-honesty migration already addresses via `axiomatizes_prior_work`.
4. **New sketch templates** — `submissions/sketches/erdos850_existence.txt` and `submissions/sketches/erdos850_impossibility.txt` written. Each states only ONE side of the original disjunction, so Aristotle must commit to a direction. Both pass the new gate.
5. **CLAUDE.md** — Hard Rule added warning about the antipattern.

## Next pilot (proposed, awaiting user go-ahead)

Re-run the 3-arm experiment with the existence-form template:

| Slot (proposed) | Arm | File |
|---|---|---|
| 720 | bare control (existence) | `submissions/sketches/erdos850_existence.txt` |
| 721 | Claude sketch-first (existence) | new sketch grounded in the existence form |
| 722 | bare-then-ask seed (existence) | same as 720; fire `project.ask()` on error |

This time Aristotle cannot discharge the goal with `em` — it must either exhibit a witness or fail honestly with `compiled_partial` / `compile_failed`. THAT failure-mode distinction is what tells us whether sketches actually help.

Estimated cost: 3 Aristotle slots + ~9h wall-clock per arm.

## Honest caveats

1. **Single-source sketch.** Hybrid Gemini-Deep-Think + GPT-5.5-Pro mode was unavailable on pilot day (Gemini 3.x = 404; GPT-5.5-Pro = transport errors). Arm B used Claude Opus 4.7 alone. In retrospect this didn't matter — the goal was a tautology either way.
2. **Mini-pilot ≠ full pilot.** N=1 problem. The signal we got (em-tautology bug) is structural; it would have shown up on any problem using the same template, so the small N doesn't weaken this conclusion. But the *method comparison* (does sketch help?) remains untested.
3. **Gate was bypassed via --force.** Arms B and C used --force (B because the sketch exceeds the 30-line cap; C because the bare body is the same hash as A). Future sketches will not need --force once Proposal #1 fully ships.
4. **DB rows tagged manually.** safe_aristotle_submit.py doesn't yet write experiment_arm / sketch_model_primary; I patched the rows via a SQL UPDATE after submission. Proposal #1's informal_sketch.py will write these directly.

## Status checks

Quick one-liner to see all 3:
```bash
sqlite3 submissions/tracking.db "
SELECT id, filename, experiment_arm, sketch_model_primary, status, substr(uuid,1,12)
FROM submissions
WHERE uuid IN ('85d169be-8858-48c4-9b60-e2eb0fb68379',
               '9fe5b59c-0d6e-4a06-a13d-31656e644f49',
               'f3337df8-63ef-4882-afa3-aed678cb4f1b');
"
```

Or via the SDK:
```bash
python3 -c "
import asyncio, os, aristotlelib
from aristotlelib import Project
aristotlelib.set_api_key(os.environ['ARISTOTLE_API_KEY'])
async def t():
    for uuid in ['85d169be-8858-48c4-9b60-e2eb0fb68379',
                 '9fe5b59c-0d6e-4a06-a13d-31656e644f49',
                 'f3337df8-63ef-4882-afa3-aed678cb4f1b']:
        p = await Project.from_id(uuid)
        tasks, _ = await p.get_tasks(limit=1)
        t0 = tasks[0] if tasks else None
        print(f'{uuid[:8]} project={p.status.name} task={t0.status.name if t0 else None} pct={t0.percent_complete if t0 else None}')
asyncio.run(t())
"
```
