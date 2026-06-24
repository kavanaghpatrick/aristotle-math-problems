# tracking.db Evaluation — Deep Audit (1,157 submissions, Dec 2025 – Mar 2026)

**Headline:** Zero of 1,157 submissions have `target_resolved=1`. The 211 `compiled_clean` rows are overwhelmingly necessary-condition lemmas, tautological wrappers, or axiomatized re-statements of prior literature — not advances on the open problem. The pipeline currently has no mechanical distinction between "Lean accepted a file" and "we resolved math."

## The 5 process-change patterns

1. **`compiled_clean` ≠ "gap resolved" — and the schema reinforces the conflation.**
2. **tuza_nu4 absorbed 27% of all attempts, yielded zero resolution, but is the only frontier with disciplined falsification tracking.**
3. **Status labels are semantically incoherent — "disproven" is applied to non-counterexamples; "completed" is applied to budget-exhausted runs.**
4. **466 of 560 distinct problems are one-shot — no resubmission, no context iteration, no learning loop.**
5. **The Codex→Aristotle promotion pipeline is built but never used (0/6 sorry-free Codex proofs promoted).**

---

### Pattern 1 — `compiled_clean` is structurally meaningless

`SELECT SUM(target_resolved) FROM submissions` returns **0** across all 1,157 rows. Yet 211 are marked `compiled_clean` and the pipeline language treats these as "wins."

Spot audit of recent `compiled_clean` gap_targeting (Feb 2026):
- **slot699_result.lean** (id=1214, erdos251 "prime binary irrationality"): proves only `p_n ≤ 2^(n+1)` and `p_{n+1} < 2 p_n` — both immediate from Mathlib's Bertrand. Conjecture untouched.
- **slot700_result.lean** (id=1212, erdos252): the main theorem is literally `erdos_252_ge_5_conjecture ↔ ∀ k≥5, Irrational (…)` proved by `bound` — a **tautology** (`P ↔ P`). 48 lines, all wrapper.
- **slot706_result.lean** (id=1220, erdos850): proves parity-match, mod-6-match, |x−y|≥30 for hypothetical solutions. Existence (the open question) untouched.
- **slot695_result.lean** (id=1207, lehmer_totient, status=`disproven`!): proves "counterexample is odd & squarefree" — Lehmer 1932. Audit note honestly says "INFRASTRUCTURE_ONLY — known results."

**135 of 211 `compiled_clean` files in `submissions/nu4_final/` contain `axiom ` declarations** (e.g. slot13's `axiom alekseyev2019_erdos_283_squares` axiomatizes the entire 2019 result then "proves" the theorem in 3 lines). The 38 rows with a populated `contribution_statement` are the only ones with honest self-assessment — slot1139 reads `"Zero mathematical novelty, formalization only."` That field is non-NULL on **3% of submissions**.

**Action:** require `target_resolved` justification text before any submission can be marked `compiled_clean`; add a `axiomatizes_prior_work` boolean populated by the audit hook; promote `contribution_statement` to NOT NULL when status changes from `submitted` → terminal.

### Pattern 2 — tuza_nu4 is both the lesson and the warning

317 submissions on one problem (27% of all activity); 60 `compiled_clean`, 67 `near_miss`, 5 `failed`, 0 resolved. The `failed_approaches` and `false_lemmas` tables exist almost entirely *because* of tuza_nu4: **39 of 44 false_lemmas and 56 of 56 categorized failed_approaches are scoped `frontier_id='nu_4'`**. Examples:
- `local_cover_le_2` (false_lemmas id=1): Pattern 1, refuted by 3-AI debate Jan 1 2026 after >8 distinct approaches tried.
- `bridge_absorption` (id=3): aristotle-verified counterexample at V=Fin 5.
- 12 distinct named approaches recorded in `pattern` column: `scaffolded` (28), `boris_minimal` (5), `krivelevich_lp`, `explicit_8edge`, `debate_synthesis`, `multi_agent_optimized`, …

Concentration **did** generate real falsification knowledge — but that knowledge is **invisible to the 209 other problems** where 0 falsifications are recorded.

**Action:** generalize the false_lemmas/failed_approaches schema beyond `frontier_id='nu_4'`; require `/fetch` to populate one of {failed_approach, false_lemma, partial_progress_note} on every non-`compiled_clean` result.

### Pattern 3 — Status labels are arbitrary

`status` enum has 25 distinct values used across 1,157 rows. Examples of misuse:
- `disproven` (12 rows): slot695 "disproved Lehmer" actually proves a 1932 theorem; slot578 "disproved oeis_a67720" actually verifies k<3200. **At most 1–2 of 12 are real falsifications.**
- `completed` (468 rows, the modal label): row 5 (tuza_nu3) reads `"BREAKTHROUGH! 8 core Parker lemmas FULLY PROVEN … Budget exhausted"` — i.e., budget-exhausted IS the "completed" path.
- `near_miss` (78 rows): all have `target_resolved=0`; the label is purely lexical.
- `tainted`, `broken`, `incomplete`, `stale`, `historical` — overlapping intent; 30+ stale entries say `"Legacy entry - needs review"`.

**Action:** collapse to ≤6 statuses (`submitted`, `compile_failed`, `compiled_partial`, `compiled_no_advance`, `compiled_advance`, `disproven`) with a strict transition diagram; backfill via single audit pass.

### Pattern 4 — Submission distribution is bimodal, learning loop missing

```
attempts/problem:  1     2-5   6-20  100+
problems:          466   73    20    1   (= 560 distinct problems)
total subs:        466   173   155   317
```

466 problems (83%) have **one** attempt and stop. No resub, no context carry-forward — exactly the opposite of how the recent `Erdos 672 resub with slot698 Pell context` chain (ids 1213→1218→1243→1248) actually accumulates partial structure. The `/sweep` and bulk batch scripts produce most of the 466 singletons (the Feb spike: 334 distinct problems in one month, 14 of them singletons in gap_targeting alone — and that's BEFORE de-duping `_v2`, `_resub` variants).

The `mk codex-best` / `mk context` chain exists but `prior_work_checked=1` is true on only **18 of 1,157 rows**. The chain isn't being run.

**Action:** make `mk context <problem_id>` an automatic step in `/submit`; gate any second submission on a 1-line "what did the prior result establish" note; auto-archive problems with 1 submission and no resub within 14 days.

### Pattern 5 — Codex pipeline built, never connected

`codex_proofs` has 16 rows, **6 with `sorry_count=0 AND compiled=1`** (erdos283_squares, erdos672_sub2_d1_impossible, erdos672_sub3_assembly, zariski_cancellation, orch_smoke_test, smoke_test). Column `promoted_to_aristotle` is **NULL or empty on all 16 rows** — the promotion column exists, the proof_orchestrator code path exists (per CLAUDE.md), but it is never invoked. Spot-checking erdos283: the "proof" axiomatizes Alekseyev 2019 → so the gap is its `axiom`, which is exactly what Aristotle should be asked to discharge. The pipeline that would do this is the missing handoff.

`ai_consultations` shows similar leakage: 39 consults, only 13 produced a tracked `resulting_submission` (33% conversion). No `problem_id` column on this table at all — consultations cannot be queried per problem without joining through `frontier_id`, which is scoped only to nu_4.

**Action:** add `problem_id` to `ai_consultations`; wire `proof_orchestrator` to auto-submit any Codex `sorry=0` proof to Aristotle for axiom-discharge; surface NULL `promoted_to_aristotle` in `mk status`.

---

## Pipeline-gap inventory (data we'd need but don't have)

- No `execution_seconds` populated anywhere (0/1,157 rows) → cannot measure cost-per-attempt or cost-per-resolution.
- `prior_work_checked` populated on 1.5% (18/1,157) → cannot detect re-attempting disproved claims.
- `novelty_level` / `contribution_statement` populated on 4.5% / 3.3% → no signal on actual mathematical advance.
- `verified` is NULL on 751 rows (65%); the audit hook is not running on most results.
- `failed_approaches.problem_id` is NULL on 43 of 56 rows → cannot cross-reference failures to problems.
- No `output_file` SHA or size column → can't detect the axiom-stuffed wrapper pattern programmatically (the audit script could grep for `^axiom ` and `↔` self-statements).

## Bottom line

The DB tells a story of high-volume Lean compilation with very low mathematical signal. The infrastructure for tracking *what didn't work* exists but only on `nu_4`; the infrastructure for tracking *what would constitute a win* (target_resolved, contribution_statement) exists but is essentially never populated. Fix Pattern 1 (the compile≠resolve conflation) and Pattern 5 (the dangling Codex→Aristotle bridge), and the existing schema can carry honest signal.
