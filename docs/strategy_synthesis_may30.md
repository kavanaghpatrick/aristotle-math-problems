# Strategy Synthesis — Unified 30/60/90 Day Plan

**Author:** Agent S10 of 10 (synthesis)
**Date:** 2026-05-30
**Mission:** Cross-reference F-team audit + W-team research + I-team infrastructure + closure_taxonomy REAL-closure rule + S1–S9 deployment outputs into a single executable plan with metrics and exit criteria.

**Source citations:**
- F-team (audit): `analysis/math_research_audit_synthesis.md` (F10), `analysis/aristotle_math_vs_compute_audit.md` (F1), `analysis/failure_dna_may30.md`, `analysis/aristotle_capability_profile_may30.md`, `analysis/research_fusion_erdos938.md` (F5)
- W-team (research): `analysis/web_research_synthesis.md` (W8)
- I-team (infrastructure): `docs/infrastructure_changes_may30/{CHANGELOG.md,I1,I2,I4,I6,I7,I8,I9,I10}.md`
- Closure taxonomy: `docs/closure_taxonomy_may30.md` (C2 REAL-closure rule)
- S-team available at synthesis time: `docs/lane_routing_matrix.md` (S1), `docs/portfolio_sequence_jun.md` (S2), E938 artifacts in `submissions/sketches/erdos938_fusion.*` + `research_fusion/runs/erdos_938/`
- S-team not on disk at synthesis time (inferred from siblings): S3 (E938 fusion artifacts — partial via existing files), S4 inflight audit, S5 long-tail Erdős summary, S6 technique scouting round 1, S7 failure mode prevention, S8 cost optimization, S9 LLM pairing strategy

---

## TL;DR

We are pivoting from a **bare-gap-only computational verifier** (1166 submissions, ~0.6% real advance, 0 cross-domain fusions) to a **four-lane research-fusion pipeline** with measurable lane KPIs. The pivot is justified by W8's finding that Aristotle has a never-invoked informal-reasoner subsystem and by I10's STRONG PASS calibration (10/10 generous, 7/10 strict) on the technique-scout ensemble. The 30-day plan validates the FUSION lane through one cleanly-prepared E938 submission and a parallel BARE-lane multiplicativity sweep. The 60-day plan scales or rolls back. The 90-day plan is the post-validation maturity model.

**The single number that kills the FUSION lane: zero qualitatively-different artifacts (no NL-reasoning trace, no Bennett-Skinner citation, no `EllipticCurve.Jacobian` reach) across the first 3 FUSION submissions by Jul 15. The single experiment that validates the rebuild: E938 fusion + informal mode produces ANY non-trivial Frey-curve or cusp-form artifact by Jun 22.**

---

## 30-Day Plan (Jun 1 – Jun 30)

### Headline goal

Validate the FUSION+INFORMAL lane on E938 (the single best-prepared cross-domain target) while running a high-volume BARE lane on multiplicativity sweeps as the engineering baseline. Measure differential output.

### Week 1 (Jun 1 – Jun 7) — BARE workhorse + slot1258 readback

5 submissions, all BARE, total cost ≈ $8.50. (Matches S2 §3 Week 1.)

| Slot | Problem | Lane | Why | Expected |
|---|---|---|---|---|
| 747 | erdos_647 Cunningham residual 35 | BARE | Witness table precomputed; highest-confidence per S2 | compiled_advance (`journal_partial`) |
| 748 | odd multiperfect σ₀=11 extension | BARE+CLOSURE companion | Builds on slot1258 readback; σ-multiplicativity DNA | compiled_partial or advance |
| 749 | Brocard [1001, 2000] | BARE | Mechanical slot738 scale-up | compiled_advance (`journal_partial` — bounded_version_closure) |
| 750 | Erdős 672 k=4 ℓ=3 witness | BARE | Direct slot712 extension; witness data in `erdos672_k4_l3_search.json` | compiled_advance OR no_advance (route W2-5 contingent) |
| 751 | FT p=3 q=1583 diagnostic | BARE | Single-point break; cheap | compiled_advance |

**Concurrent dossier prep (Jun 1–7):**
- E938 fusion files already on disk (`submissions/sketches/erdos938_fusion.{txt,fusion.json,closure.json}`) — verify airlock passes locally
- E64 dossier authoring (for W2-3)
- E617 dossier authoring (for W3-4)

### Week 2 (Jun 8 – Jun 14) — FUSION debut

5 submissions, FUSION/BARE mix, total cost ≈ $26.

| Slot | Problem | Lane | Why |
|---|---|---|---|
| **752** | **E938 powerful 3-APs** | **FUSION+INFORMAL** (paired_llm=mixed) | THE pivot test. Frey-Hellegouarch + Ribet level-lowering dossier in place. |
| 753 | E203 12×12 disproof lift | BARE | Slot740 lift; either outcome informs whether E203 path stays open |
| 754 | E64 Erdős-Gyárfás 2^k cycles disproof | FUSION (paired_llm=codex) | SAT-search precedent; Cayley graph technique |
| 755 | Primitive weird ω(n)=6 | BARE+CLOSURE | Same multiplicativity DNA as W1-2 |
| 756 | Goormaghtigh (5,3) OR E672 FUSION retry | BARE OR FUSION | Conditional on W1-4 result |

### Week 3 (Jun 15 – Jun 21) — Contingent expansion

5 submissions; selection depends on W1+W2 results.

| Slot | Problem | Lane |
|---|---|---|
| 757 | Lehmer totient ω=7 odd sqfree | BARE+CLOSURE |
| 758 | E137 k=4 powerful disproof | BARE |
| 759 | E203 Sierpiński 1D benchmark | BARE |
| 760 | E617 r=4 K_17 disproof | FUSION (paired_llm=grok) |
| 761 | E672 retry next-k variant | BARE |

### Week 4 (Jun 22 – Jun 28) — Long-tail + one transformative bet

5 submissions, total cost ≈ $22.50.

| Slot | Problem | Lane |
|---|---|---|
| 762 | E307 finite prime sets reciprocal-product = 1 | BARE |
| 763 | E835 (k+1)-subset coloring | BARE |
| 764 | E283 squares family extension | BARE |
| 765 | LONG-SHOT Conway 99-graph existence | FUSION + external SAT (fires only if external SAT yields candidate by Jun 22) |
| 766 | E952 Gaussian moat dossier-backed | FUSION |

### 30-day budget

| Component | Cost |
|---|---|
| BARE compute (14 slots) | ≈ $24 |
| FUSION compute (5 slots × $2) | ≈ $10 |
| FUSION dossier prep (5 dossiers × $6) | ≈ $30 |
| Paired-LLM consultations (5 × $1) | ≈ $5 |
| Conway external SAT search | ≈ $10 |
| Reserve / retries | ≈ $20 |
| **Total** | **≈ $100** |

### 30-day expected outcomes

- **BARE lane (14 slots):** 4–6 `compiled_advance` (predominantly `journal_partial` per C2), 4–6 `compiled_partial`, 2–4 `compiled_no_advance`. Real-closure rate ≤ 10% per C2.
- **FUSION lane (5 slots):** 0–1 `compiled_advance`, 1–2 `compiled_partial`, 2–4 `compiled_no_advance`. Real-closure rate target ~15–20%; honest expectation lower.
- **The pivot signal:** at least 1 FUSION submission produces a qualitatively different result (NL proof trace, cross-domain Mathlib API reach, cusp-form computation attempt, or Bennett-Skinner citation in `ARISTOTLE_SUMMARY.md`).

---

## 60-Day Plan (Jul 1 – Jul 31)

### Branch on 30-day result

#### Branch A — FUSION validated (≥ 1 qualitatively-different artifact in Jun)

**Scale FUSION to 8–10 slots per month.** Build 4 more dossiers (top closure_list_may30 candidates not yet covered: Goormaghtigh (5,3), E938 retry with refined bridge, primitive weird ω=7 fusion, E835 subset coloring). Drop pure-BARE volume to 12 slots/month; reallocate budget to dossier prep ($60/month).

- Total submissions: 22/month (10 FUSION + 12 BARE)
- Budget: ≈ $170
- Real-closure rate target: 15–25% per C2 rubric (matches F10's day-31–60 forecast)
- Key metric: `mathematical_content_score` median across FUSION lane ≥ 3 (vs BARE median ≤ 2)

#### Branch B — FUSION fails to differentiate (no qualitatively-different artifact)

**Roll back. Halt FUSION at 1 slot/month minimum (for residual learning); restore BARE volume to 25–30 slots/month with the now-fixed `gather_context()` and the C2 honesty marker active.**

- Honest rebrand: pipeline is a computational-verification engine. Rule 12 finally hard-enforced: `compiled_no_advance_mechanical` is the default for bounded extensions; `journal_partial` is the optimistic ceiling.
- Continue the multiplicativity sweep aggressively (highest-yield lane per F10 + capability profile §1.4).
- Single FUSION experiment per quarter to refresh the W8 hypothesis test.

### 60-day exit criteria (pre-committed)

- **0 `compiled_advance` from FUSION lane in Jun → trigger Branch B regardless of "qualitative" assessment.** Discipline forbids hand-waving the absence of compiled output.
- **3 FUSION `compiled_advance` in Jun with `mathematical_content_score` ≥ 3 → Branch A, with one slot promoted to a "publication-class" attempt (E672 k=4 ℓ=3 Frey curve full proof attempt with explicit `EllipticCurve.Jacobian` usage).**
- **Real-closure-rate (C2 `real_closure_candidate=true ∧ target_resolved=1`) by Jul 31 < 5% across the whole pipeline → trigger Branch B with extended root-cause analysis.**

---

## 90-Day Plan (Aug 1 – Aug 31) — Maturity Model

### If everything has worked (Branch A persistence + at least one real closure by Jul 31)

The pipeline looks like:

- **3 lanes operating in steady state:** BARE (12/month, multiplicativity workhorse), CLOSURE (3–5/month, witness verifications with `.closure.json` companions), FUSION+INFORMAL (10/month, all dossier-backed, all paired_llm-tagged).
- **`mathematical_content_score` ≥ 3 on every public-claim submission.** `compiled_no_advance_mechanical` is recorded but never celebrated.
- **Calibration cadence:** every 90 days re-run the I10 calibration on 5 new historical problems; alert if strict-hit rate drops below 5/10.
- **Publication target:** 1 journal-clean closure submitted for peer review (E672 k=4 ℓ=3 if it advanced, OR primitive weird ω=6 with refined fusion). This is the public output the project was built for.
- **Cost stable at ≈ $200/month** at 25 slots + 8–10 dossiers.

### Pipeline architecture changes by Aug 31

1. **`.closure.json` REJECT (not WARN) for missing companions on CLOSURE-lane submissions.**
2. **`.fusion.json` REJECT for missing `informal_proof_outline` when `--fusion-lane` is passed AND fit_score ≥ 0.5.**
3. **`mathematical_content_score` populated as drafter input (not just audit), gated by gap-targeting check.**
4. **Auto-context (I1) extended: when a submission target shares mechanism (closure_axis CM) with a prior `compiled_advance`, the prior artifact is auto-attached. (Currently only same-`problem_id` prior artifacts are attached.)**
5. **`mk fusion <problem_id>` runs Stages 1–3 in one command (already shipped by I6); add `mk fusion-submit <problem_id>` that runs Stages 4–5 with one airlock check.**

### If Branch B (FUSION rolled back)

- Pipeline reduces to BARE + CLOSURE only.
- 25–30 slots/month, ~$60/month operational cost.
- F-team Honest output: "we run a computational-verification engine that occasionally surfaces structural micro-insights (slot737-class)." (F10's §4 rollback language.)
- No publication target. Project is engineering, not research.
- Single FUSION experiment per quarter to refresh the W8 hypothesis test ($30/quarter).

---

## Metrics Dashboard

### Tier 1 — Pivot validation KPIs (track weekly)

| KPI | Target Jun 30 | Target Jul 31 | Target Aug 31 |
|---|---|---|---|
| `compiled_advance` rate by lane (FUSION) | ≥ 10% | ≥ 15% | ≥ 20% |
| `compiled_advance` rate by lane (BARE) | ≥ 30% | ≥ 30% | ≥ 30% |
| `mathematical_content_score` median (FUSION) | ≥ 2.5 | ≥ 3 | ≥ 3.5 |
| `mathematical_content_score` median (BARE) | ≤ 2 | ≤ 2 | ≤ 2 |
| Real-closure rate (`real_closure_candidate=true ∧ target_resolved=1` / submissions) | 1+ events | 3+ events | 5+ events |
| Cost per advance (FUSION) | ≤ $50 | ≤ $35 | ≤ $25 |
| Cost per advance (BARE) | ≤ $5 | ≤ $4 | ≤ $4 |

### Tier 2 — Process health (track per submission)

| Metric | Definition | Alert |
|---|---|---|
| `gather_context` artifacts attached | I1 auto-context per submission | 0 attached when prior artifacts exist for problem_id → bug or stale verified flag |
| `closure_axis_json` completeness | All 4 axes (CS/CM/CR/HM) populated | NULL closure_axis_json on REAL-closure candidate → gate misconfiguration |
| Airlock pass rate (FUSION) | leak detections / fusion submissions | > 5% → bare-gap discipline slipping |
| Literature-check freshness | days since wiki snapshot | > 14 → manual refresh required |
| Informal-mode usage rate (FUSION) | informal_mode_used=1 / fusion lane | < 80% → I9 plumbing not engaging |

### Tier 3 — Cost (track monthly)

- API cost per slot, broken out by lane
- Wallclock per dossier (target ≤ 2 hours; alert > 6 hours)
- Reroll rate (resubmissions / submissions) per problem

### Storage queries

```sql
-- Lane × month × outcome
SELECT lane, strftime('%Y-%m', submitted_at) AS month, status, COUNT(*)
FROM submissions
WHERE submitted_at >= '2026-06-01'
GROUP BY lane, month, status
ORDER BY month, lane, status;

-- Real-closure events
SELECT id, problem_id, lane, submitted_at, mathematical_content_score
FROM submissions
WHERE json_extract(closure_axis_json, '$.real_closure_candidate') = 1
  AND target_resolved = 1
ORDER BY submitted_at DESC;

-- Mathematical content score distribution by lane
SELECT lane, mathematical_content_score, COUNT(*)
FROM submissions
WHERE submitted_at >= '2026-06-01' AND mathematical_content_score IS NOT NULL
GROUP BY lane, mathematical_content_score
ORDER BY lane, mathematical_content_score;
```

---

## Exit Criteria — Pre-committed Lane Kills

| Lane | Kill criterion (90 days) | Action |
|---|---|---|
| **FUSION** | 0 `compiled_advance` AND 0 qualitatively-different artifacts (no NL trace, no cross-domain Mathlib API reach) across first 3 submissions by Jul 15 | Demote to 1 slot/quarter; rebrand pipeline; halt dossier authoring |
| **FUSION** | Real-closure-rate < 5% across the lane by Aug 31 | Maintain at 3 slots/month max, no scaling |
| **BARE+multiplicativity** | < 3 `compiled_advance` from sigma-multiplicativity family across Jun (W1-2, W2-4, W3-1) | Drop multiplicativity attack permanently; reroute to disproof witness lane |
| **CLOSURE** | `real_closure_candidate=true` count remains 0 after Aug 31 | C2 rubric needs revision (likely too strict for our Aristotle profile) |
| **INFORMAL (I9)** | All informal-mode submissions produce MCGS-shaped failure signatures (same sorry/axiom shape as BARE) — i.e., I9 adapter isn't actually engaging subsystem #2 | Move informal mode behind feature flag; resume only if Harmonic exposes a dedicated API |

---

## Addressing the BIG questions

### Q1. Will Aristotle's informal mode (I9 adapter) actually engage subsystem #2?

**Test: slot 746 + Euclid smoke test result.**

The I9 smoke test (project `8d500201-0786-4bb2-8489-2f6aad91be91`, submitted May 30) verified that the SDK accepts a tarball-free natural-language prompt and creates a task with `has_input=False`, `file_name=None`. That confirms the API-shape routing on the client side. But it does NOT confirm server-side that subsystem #2 is the executor. **The only way to know is to read the eventual artifact:** if the output is a NL-reasoning trace + lemma decomposition + Lean autoformalization, subsystem #2 fired. If the output is a standard MCGS tree with a goal and `sorry`, it didn't.

**Decision rule:** The first 3 informal-mode artifacts (Euclid smoke test + slot 752 E938 FUSION + slot 754 E64 FUSION) are evaluated together. If at least 1 shows the NL-decomposition shape, subsystem #2 is engaged. If all 3 show MCGS shape, the adapter is a workaround that doesn't work, and Branch B applies regardless of `compiled_advance` count.

### Q2. Will fusion lane hit the calibrated 7/10 rate on OPEN problems?

**Almost certainly no.** I10's calibration was retrospective: the historical unlocks are known. On OPEN problems, the ensemble has to nominate a technique the field hasn't already converged on. F4's honest estimate: 25–30% of fusion breakthroughs are lit-search-derivable; 15–25% are LLM-suggestion-derivable; 5% are within Aristotle's tactic-level reach. **Expected first-pass real-closure rate on a fusion-amenable problem with a fresh dossier: 1–3% per F10 §4.** Caveat from S2 §7 ("treat first 5 fusion submissions as ARM 1") is correct: treat the Jun batch as a single experimental arm, not as the steady-state rate.

### Q3. Should we pursue GPT-5.2 Pro access (S9 recommendation)?

**Yes, with a budget cap.** W8 explicitly cites the canonical Aristotle workflow as "GPT-5.2 Pro generates informal proof → Aristotle formalizes" and Aristotle's own #728, #1090, #897 wins all pair with GPT-5.2 Pro. Our existing harness uses Codex (cheap, capable), Gemini (Deep Think), Grok (good for adjacent-analog discovery). None of those is GPT-5.2 Pro. **Provisional budget: $50 for a 2-week GPT-5.2 Pro trial run on E938 strategist role (Stage 4 outline refinement). Cancel if `mathematical_content_score` doesn't lift on the resulting FUSION submission.**

### Q4. The one experiment that, if it fails, kills the fusion lane

**E938 FUSION + INFORMAL submission (slot 752, Jun 8–14).** Conditions:

- The .txt sketch is bare (passes airlock)
- The .fusion.json companion declares `named_technique: "Frey-Hellegouarch curve + Ribet level-lowering with kernel control"`, `seminal_paper_arxiv: arXiv:math/0309108`, full `informal_proof_outline` (6-step Bennett-Skinner / Bombieri-Lang / Pila-Wilkie hybrid)
- Submitted via `--fusion-lane --paired-llm mixed`
- I9 routing fires (informal mode invoked because `informal_proof_outline` non-empty)

**Failure signature:** Aristotle returns standard MCGS goal-search output with `sorry` on the main theorem, no mention of Frey curves, Ribet, Bennett-Skinner, or cusp forms in `ARISTOTLE_SUMMARY.md` or any helper. `mathematical_content_score` ≤ 2.

**If this happens:** the entire FUSION lane is invalidated as currently architected. Either (a) Aristotle's informal-reasoner is not server-side engaged by our adapter (Q1 fails), or (b) Aristotle's reasoner cannot consume our dossier format. Branch B kicks in.

---

## The 3 Highest-Leverage Immediate Actions

### Action 1 — First submission to make

**Slot 747: Erdős 647 Cunningham residual 35 (BARE, Jun 1).** Lowest risk, highest confidence, validates that the post-I2 pipeline (with fixed `gather_context`, new audit columns) works end-to-end on the lane our DNA is best-fit for. If this doesn't `compiled_advance`, the infrastructure rewrite has a regression and the FUSION debut (Jun 8) must be delayed.

### Action 2 — First measurement to take

**Run `python3 scripts/safe_aristotle_submit.py <slot747_sketch> --verbose-context` and verify:**
- `gather_context()` attaches the slot737 + slot712 + slot722 prior artifacts to the auto-context.
- The lane resolution sets `lane='bare'` correctly.
- The post-submission DB row has `mathematical_content_score` written (or NULL with a clear audit-pending marker).

This is the load-bearing operational test for I1+I2. If the canary warning ("0 artifacts attached") fires, the F2 silent-context bug has regressed.

### Action 3 — First piece of infrastructure to harden

**Promote the `.closure.json` companion gate from WARN to REJECT for any submission claiming REAL closure.** Without this, the dashboards remain unreliable: any post-Jun submission could still slip through as "advance" without the four C2 axes populated, and we lose the ability to distinguish real closures from `bounded_version_closure` masquerade. Per CHANGELOG §"Known issues" #6, this is documented as "WARN-only transition" — promote it now, before the Jun batch starts producing data we cannot honestly categorize.

---

## Honest Failure Modes — What Does Failure Look Like

### Failure Mode A — "Bigger of the same thing"

By Jul 31, we have 8 BARE-lane `compiled_advance` rows (multiplicativity bumps, Brocard extensions, q-bumps). All are `bounded_version_closure` or `formalization_only` per C2. Zero `real_closure_candidate=true`. The FUSION lane is at 1/15 or 2/15 advance rate, no qualitatively-different artifacts.

**Rollback:** Branch B. CLAUDE.md Rule 12 finally enforced operationally — `compiled_no_advance_mechanical` is the default and `journal_partial` is the ceiling. Pipeline rebranded internally as engineering, not research. **This is the documented historical outcome; the 30/60/90 plan is designed to detect it within 60 days rather than 6 months.**

### Failure Mode B — "Fusion produces theater"

By Jul 31, FUSION lane has 4–5 `compiled_advance`, but `mathematical_content_score` ≤ 2 on all of them. The Aristotle outputs cite Bennett-Skinner in the prompt-context but the actual Lean proof is `native_decide` boilerplate — the strategy didn't translate to the formalization step.

**Rollback:** Branch B with a twist — keep FUSION at 3 slots/month for the dossier IP, but stop counting it as "research-fusion lane." Acknowledge per F10 §3.5 "Risk of theater" that a polished dossier can produce a polished but mathematically-empty Lean wrapper. The dossiers are still valuable institutional memory; the lane label is misleading.

### Failure Mode C — "Subsystem #2 isn't reachable"

By Jul 15, the I9 informal-mode output across 3 submissions is indistinguishable from MCGS output. Same sorry shape, same failure modes (F1 Iff.rfl, F3 infrastructure overgrowth, F4 axiomatize-the-hard).

**Rollback:** Disable I9 routing. Submit FUSION-tagged sketches with the .fusion.json companion as context, but skip the informal-mode prompt-shape switch. Re-evaluate when Harmonic ships an SDK with a documented `Project.solve_informal()` method. Until then, treat informal mode as wishful client-side framing.

### Failure Mode D — "Pipeline regression"

Jun 1 slot 747 fails to `compiled_advance` despite identical sketch shape to slot 720 / slot 722. The post-May-30 infrastructure has a bug.

**Rollback:** Halt all submissions. Run the I1+I2 test suite. Likely culprits: gate ordering change in `safe_aristotle_submit.py` after I8 wiring; auto-context attaching the wrong artifacts (verified flag mis-set); `--paired-llm` flag silently changing prompt assembly.

### Rollback procedure (any failure mode)

1. `mk submissions --since 2026-06-01 --status submitted` to identify in-flight slots; let them complete or cancel via `python3 scripts/aristotle_queue.py cancel <id>`.
2. Tag failed lane in DB: `UPDATE submissions SET notes = 'PIVOT_ROLLBACK_<date>_<reason>' WHERE submitted_at >= '<rollback-date>' AND lane = '<dead-lane>'`.
3. Revert lane-specific config:
   - FUSION rollback: `cp .claude/local-config-bare-gap-only.json .claude/active-config.json`; verify `/sketch` defaults to BARE-only.
   - I9 rollback: comment out the informal-routing block in `safe_aristotle_submit.py` (per I9 §4.1); preserve the adapter for future re-enable.
4. Update CLAUDE.md Hard Rules to remove FUSION mention if Branch B is invoked; restore the bare-gap discipline as canonical.
5. Postmortem doc: `docs/strategy_rollback_<date>.md` with which lane failed, what was tried, what the data shows, and what would need to be true for a re-attempt.

---

## The Single Number That Kills the FUSION Lane

**`mathematical_content_score` median on FUSION-lane submissions across Jun 1 – Jul 15.**

If this number is < 2.5 across at least 5 FUSION submissions (the minimum sample for the Jun + half-Jul window), the FUSION lane is dead per C2 honesty marker. The lane is supposed to produce substantive mathematical content (3 = visible structural reasoning; 5 = cross-domain bridge lemma). A median ≤ 2 means we are producing the same brute-force computational template as BARE, just at 4–6× the cost.

This is the **one number** that, once measured, settles the W8 hypothesis test for our infrastructure.

---

## The Single Experiment That Validates the Rebuild

**Slot 752 E938 FUSION+INFORMAL produces ANY of these by Jun 22:**

1. An `ARISTOTLE_SUMMARY.md` (or equivalent artifact) that cites Bennett-Skinner, Frey-Hellegouarch, or a specific arXiv paper from the dossier
2. A Lean proof attempt that imports `Mathlib.NumberTheory.ModularForms.*` or `Mathlib.AlgebraicGeometry.EllipticCurve.*` (currently unused by ALL 1166 prior submissions)
3. A natural-language reasoning trace in a `.md` or scratch artifact (not just the Lean source)
4. A non-trivial bridge lemma `frey_conductor_bound` or `ribet_kernel_lowering` partially proven (>50 lines of relevant content, not 1-line `sorry`)

**Any single one of these = pivot validated; even with no `compiled_advance`.** The W8 hypothesis (H2: latent reasoning unlocks with rich input) gets meaningful posterior weight. Branch A proceeds. The 60-day scaling is justified.

**Zero of these = pivot fails.** Branch B kicks in regardless of any `compiled_advance` from the BARE lane.

---

## Documentation Path

This file: `/Users/patrickkavanagh/math/docs/strategy_synthesis_may30.md`

**Hand-offs:**
- Mirror the metrics dashboard's SQL queries into a `make dashboard` target by Jun 5
- Update this file at Jun 30 (Branch A/B decision), Jul 31 (60-day checkpoint), Aug 31 (90-day decision)
- If Branch B fires, document in `docs/strategy_rollback_<date>.md` with the postmortem
- Per-slot artifacts continue to live in `submissions/sketches/*.{txt,fusion.json,closure.json,_ID.txt}` and `submissions/nu4_final/slot*_result.lean`

**Sibling S-agent outputs not yet on disk at synthesis time:** S3 (full E938 fusion artifacts beyond what's already on disk), S4 (inflight audit may30), S5 (long-tail Erdős summary), S6 (technique scouting round 1), S7 (failure mode prevention), S8 (cost optimization), S9 (LLM pairing strategy). If these land before Jun 1, re-validate Section 3 (30-day plan), Section 5 (metrics targets), and Q3 (GPT-5.2 Pro budget).

---

## Author note

This synthesis is operationally **honest about the empirical risk**: F10 estimates the FUSION lane's day-31–60 closure rate at 1–3% on well-chosen targets. The 30-day plan is calibrated to *detect* that rate quickly (5 FUSION submissions in Jun) rather than to *achieve* it on a single bet. The 60/90-day plan is the conditional response to whatever the data says.

The biggest single risk is the temptation to declare success on `compiled_advance` count without checking `mathematical_content_score` or `real_closure_candidate`. That's the failure mode CLAUDE.md Rule 12 polices, and it is the failure mode that 4 of 7 prior `compiled_advance` rows already exhibit per F1. The dashboards above are designed so that this temptation is mechanically blocked: an advance that is `bounded_version_closure` with `journal_partial` HM does not count toward the FUSION-lane KPIs.
