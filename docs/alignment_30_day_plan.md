# Alignment 30-Day Plan — Toward Truly-Novel Math Output

**Author:** A10 of 10 (final synthesis)
**Date:** 2026-05-30
**Synthesized from:** A1 (S5 long-tail), A2 (advance DNA / strategy), A4 (capability + Mathlib), A5 (literature gate), A8 (closure taxonomy), A9 (pairing options); V-team result audit (today's 22 artifacts); F4/F10 failure DNA; W3/W5/W6 external research.

---

## 0. Honest framing (read first)

- **Today's truly-novel count: 0 of 22 returned artifacts.** Zero. No paper a working number theorist would accept as new (V-team verdict; today_results_research_impact_synthesis.md).
- **Realistic AI ceiling: 1–3% novel per attempt** under *perfect* process, per W3/W5/W6 and F10. 6/6 novel in a day is not a real target; it implies 200–600 attempts even at the ceiling.
- **30-day honest target: 1–2 `journal_clean_novel` artifacts.** Six in 6 months is the upper-bound aspirational extrapolation, contingent on every upgrade landing.
- **The actual blocker is not compute or aggression. It is** (a) literature-gate (we routinely re-prove published results, e.g., R3 ⊂ Le 2012, R10 ⊂ McCranie 10¹⁰), (b) bare-gap prompting (subsystem #2 / informal-reasoner never engaged in production), and (c) Aristotle's own ceiling (it does not invent decreasing measures, density sieves, or cross-domain bridges — A4).

---

## 1. Day-by-day plan

### Week 1 — Foundation fixes (Jun 1 – Jun 7)
**Goal:** Stop wasting attempts on subsumed work. Make the closure taxonomy honest.

| Day | Owner | Task | Definition of done |
|-----|-------|------|---------------------|
| 1 | Infra | **zbMATH / MathSciNet literature gate (A5)**. Pre-submission `check_literature()` queries zbMATH for theorem-key tokens + Erdős# + technique words. Hard-block if (problem_id, technique_signature) already has a published result within last 25 yrs covering ≥ our claimed scope. | A test call against R3 (FT p=3 q≤2000) returns Le 2012 and BLOCKS. Asiryan-style false-negative test: R7 fusion now goes through (real arXiv paper) without bogus rejection. |
| 2 | Infra | **Update `closure_taxonomy`** (A8) to add `HM = journal_clean_novel`. This is strictly stronger than `journal_clean`: requires zbMATH gate pass AND citation gate AND no subsumption by published proof. Track in `submissions.closure_hm`. | Schema migration + back-fill of today's 22 results (all should land at `infrastructure_only`, `journal_partial`, or `journal_subclaim`; **zero** should land at `journal_clean_novel`). |
| 3 | Infra | **Tighten S5 long-tail selection (A1).** Add anti-criteria to `analysis/long_tail_erdos_candidates.csv`: drop any problem where (a) prior Aristotle prior_attempts ≥ 2 with no `journal_partial`, (b) closure mechanism is `bounded_to_infinite_lift` without a concrete lift lemma, (c) statement is `Tendsto`/`Irrational`/`IsEquivalent` wrapper (F1 iff_rfl risk). | New `long_tail_v2.csv` with ≤ 25 problems; each annotated with predicted HM ∈ {`journal_partial`,`journal_subclaim`,`journal_clean_novel`}. |
| 4–5 | Math | **One concrete Mathlib PR (A4).** Take the `unitarySigma` family from E1052 (8 lemmas) — rewrite from `simp_all +decide` style to idiomatic Mathlib (per Mathlib reviewer norms cited in `infrastructure_mathlib_audit.md`). Open as PR; chase reviewer. | PR open, CI green, at least one Mathlib reviewer assigned. Not "merged" — that takes longer. |
| 6 | Eng | **Citation verification gate.** Every Aristotle "this citation doesn't exist" critique triggers automated arXiv/MR check **before** acting. R7-style false-negatives must not propagate. Wire into `safe_aristotle_submit.py` post-process. | Replay R7/Asiryan → gate catches the false-negative; replay a known fake citation → gate confirms fake. |
| 7 | Audit | **Stop-list audit.** Remove all bounded-extension submissions from the queue (R3, R4, R5, R10-class). They are measurement instruments, not research (V-team verdict). | Queue snapshot before/after; ≥ 4 micro-extension slots cancelled. |

### Week 2 — Strategy upgrade (Jun 8 – Jun 14) **← single most important week**
**Goal:** Replace bare-gap prompts with frontier-incremental prompts; engage subsystem #2.

| Day | Owner | Task | Definition of done |
|-----|-------|------|---------------------|
| 8 | Math + LLM | **New sketch template: "incremental on published frontier" (A2).** Required fields: (i) explicit citation of SOTA, (ii) named gap between SOTA and our target with one-sentence justification of why it is open, (iii) closure mechanism from `closure_taxonomy` CM column, (iv) predicted HM. Bare conjecture still allowed but template is recommended for fusion lane. Replaces parts of `/sketch` for FUSION lane only — BARE lane unchanged. | Two reference sketches produced (E938 powerful 3-APs, E373 Surányi factorial). Both pass the new template + zbMATH gate + closure-axis gate. |
| 9 | Math | **Stop submitting bounded extensions of subsumed problems (V4 lesson).** Hard-block any submission whose `problem_id` already has a `journal_partial` row covering a strict superset of the claimed bound. Encoded in literature gate from Day 1. | R3-class submissions become a compile-time error in `safe_aristotle_submit.py`. |
| 10–11 | Pair | **Pair with human mathematician on 1 problem (A9 option E).** Choose E373 Surányi (S5 #1, 60-yr-old, no AI competition, S1/S5 structure) OR E944 Dirac k=4. Human writes the frontier-incremental sketch; we run it through fusion lane; human reviews the returned proof attempt before any `compiled_advance` claim. | Sketch authored, submitted, returned, human-reviewed within the week. Outcome recorded with HM verdict. |
| 12 | Eng | **Engage subsystem #2 (informal reasoner) — validate the lane.** Reproduce the I9 Euclid smoke-test signature (`Informal proof:` + `Formalization:` sections in `ARISTOTLE_SUMMARY.md`) on one production fusion submission. **No production submission today produced this signature** — this is the rate-determining step. | At least one fusion submission this week returns the informal-mode signature. If zero by end of week: roll back fusion lane, escalate to model vendor. |
| 13–14 | Eng | **Run 3 frontier-incremental sketches** through the new template + fusion + paired review. | 3 submissions in flight by end of week. |

### Week 3 — Quality push (Jun 15 – Jun 21)
**Goal:** Submit 5–10 carefully-curated novel-candidates. No volume play.

| Day | Owner | Task | Definition of done |
|-----|-------|------|---------------------|
| 15 | Math | **Curate 5–10 candidates.** Each must pass: (i) zbMATH gate (no published subsumption), (ii) frontier-incremental sketch template, (iii) closure-axis predicted HM ∈ {`journal_clean_novel`, `journal_subclaim`}, (iv) paired-human review of the sketch before submission. | Ordered queue with 5–10 entries; each entry carries the four gate decisions inline. |
| 16–18 | Eng | **Submit at staggered cadence (≤ 2 per day)** so each result returns before the next batch goes out. Aristotle review cycle is ~24 h. Process each `/fetch` immediately. | Submissions 1–5 land between Jun 16–18; results begin returning Jun 17. |
| 19–21 | Audit + Math | **Pairwise audit each return** for novelty (V-team protocol): literature check, folklore check, citation verification, contribution statement. Promote to `compiled_advance` only if `target_resolved=1` AND HM ≥ `journal_subclaim`. Promote to `journal_clean_novel` only with explicit V-team-style audit document. | Each returned artifact has a one-pager audit; promotions are explicit and signed. |

### Week 4 — Measure (Jun 22 – Jun 30)
**Goal:** Honest measurement and decision.

| Day | Owner | Task | Definition of done |
|-----|-------|------|---------------------|
| 22–24 | Audit | **Run the second wave (3–5 more)** through the same gate. Total month volume ~10–15 submissions, not 100. | Same audit discipline. |
| 25–27 | Audit | **Count `journal_clean_novel` rows.** SQL: `SELECT count(*) FROM submissions WHERE closure_hm = 'journal_clean_novel' AND date(submitted_at) BETWEEN '2026-06-01' AND '2026-06-30'`. | Number is the headline KPI. |
| 28 | Audit | **Honest comparison to teorth wiki section 1(a) (novel) vs 1(c) (new proof of known).** Map each compiled artifact to one of {1(a), 1(b), 1(c), 1(d), N/A}. | One-pager comparison. |
| 29–30 | Strategy | **Decide: scale or pivot.** Apply pre-committed exit criteria (next section). Write the 60-day plan accordingly. | Go/no-go decision document. |

---

## 2. Pre-committed exit criteria (decision rule, no wiggle room)

| 30-day `journal_clean_novel` count | Action |
|---|---|
| **0** | **Pivot to pure Mathlib-formalization output.** No more novelty claims. Pipeline rebrands as a Lean-formalization assistant. The 3 Mathlib PR candidates (`unitarySigma` family, `sq_powerful`+`powerful_infinite`, E373 Surányi bounds) become the Q3 output target. We accept that the current AI ceiling on novel math is below our pipeline's resolution. |
| **1** | **Scale the responsible process upgrade.** Identify which Week-2 change produced the hit (literature gate? frontier-incremental template? paired human review? informal-reasoner lane?) and double down on that one. Run a 60-day extension at 2× volume on the responsible lane only. |
| **2** | **Scale + add a second hit-class.** Strong signal that one process upgrade works. Run 60 more days targeting two upgrade vectors. |
| **≥ 3** | **We are at Tao long-tail bar.** Real research output. Publish the methodology as a workshop/blog post (per `strategy_critiques_value_audit.md`'s held-out-test-set recommendation). Begin venue-targeted writeup. |

---

## 3. Honest 30-day target

**1–2 `journal_clean_novel` artifacts.** Not 6. Not 6/6.

Rationale: 10–15 carefully-curated attempts × 1–3% AI novelty ceiling = expected value of 0.1–0.45 novel results. Realistic upside (everything working): 1–2. Realistic downside: 0. The exit criteria above match this distribution.

---

## 4. Single most important week

**Week 2: strategy upgrade.** Every other week is process polish. Week 2 is the only week where we actually change what we ask Aristotle to do. The literature gate (Week 1) prevents wasted effort; the curation/audit (Weeks 3–4) makes results legible; **Week 2 is the only place we touch the rate-determining step (subsystem #2 engagement + frontier-incremental prompting + paired human review).** If Week 2 fails, the rest of the month is measurement of an unchanged ceiling.

The single pass/fail check: **one fusion submission must return the informal-reasoner signature (`Informal proof:` + `Formalization:` sections) by Jun 14.** Today, zero did. If Jun 14 also returns zero, the fusion lane is rolled back and we operate as a computational verifier only.

---

## 5. What to STOP doing immediately

1. **Stop submitting bounded extensions of problems with published unconditional results.** R3 (FT p=3 q≤2000) is subsumed by Le 2012; R10 (E647 ≤ 10⁶) is subsumed by McCranie 10¹⁰. Hard-block in `safe_aristotle_submit.py`.
2. **Stop duplicate micro-extension submissions.** R4⊂L3 (E324 N=50/200), R5≈L10 (E319 N∈{7..10}). Dedup before submit.
3. **Stop celebrating "compiled clean" as gap resolution.** Reuse the `compiled_advance` discipline (`contribution_statement NOT NULL`, `target_resolved=1`); add `closure_hm` honest column.
4. **Stop trusting Aristotle's citation rejections.** The Asiryan false-negative would have caused permanent damage if V-CITE hadn't checked. Every rejection now goes through arXiv/MR verification (Week 1 Day 6).
5. **Stop using bare-gap prompts for fusion-lane submissions.** Bare-gap is correct for BARE lane (it's the prime directive of the pipeline); but FUSION needs frontier-incremental sketches with named SOTA + gap.
6. **Stop calling it "research-fusion" until subsystem #2 is reliably engaged.** Per F10: "We are at 2/10 on research-fusion. We are at 9/10 on computational-brute-force-via-bounded-native_decide." Honest rebrand pending validation.

---

## 6. Risk register

| Risk | Probability | Impact | Mitigation |
|---|---|---|---|
| **zbMATH integration takes longer than 1 day** | High (40%) | Slips Week 1 schedule | Fall back to manual MR search + Google Scholar with a 25-yr filter for first 5 candidates; ship the gate-as-checklist version Day 1, automated version Day 3. |
| **Frontier-strategy prompts still produce folklore** | High (50%) | Week 2 fails its primary check | Treat as a real signal — the bottleneck is then Aristotle's own ceiling, not our prompting. Pivot per exit criteria (0 → Mathlib-only). |
| **Aristotle ceiling IS the actual blocker** | Medium (35%) | Pipeline upgrade has no headroom | This is the discovery we are looking for. Honest acknowledgement; Mathlib pivot. No "throw more compute" hail-Mary. |
| **Subsystem #2 cannot be reliably engaged on production submissions** | High (60%) | Fusion lane stays at 0/n informal-signature | Escalate to vendor; in the meantime, run the lane as if it were bare-gap and accept zero novelty contribution from it. |
| **Mathlib community not progressing infrastructure** | Low (15%) | Week-1 PR sits unreviewed | Open the PR anyway; chase reviewers; this is a discovery cost, not a blocker. |
| **No time / depth (human reviewer unavailable for paired week)** | Medium (30%) | Week 2 paired step degrades to LLM-only | Reduce to 1 paired problem (not 3); accept lower novelty expectation; still ship the literature gate + closure-axis upgrade. |
| **Closure-axis `journal_clean_novel` gate is too strict / too loose** | Medium (25%) | Either 0 promotions even on a real win, or false promotions | Calibrate against today's 22 artifacts as the held-out test set; tune Day 2 before Week 3 begins. |
| **Aristotle-flagged citation false-positives leak through** | Low–Medium (20%) | One retraction destroys credibility | Day-6 gate + V-CITE-style audit on every promotion; one false promotion = revert and patch. |

---

## 7. Files this plan touches (load-bearing paths)

- `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` — Week 1 Day 1 (literature gate), Day 6 (citation gate), Week 2 Day 9 (subsumption hard-block).
- `/Users/patrickkavanagh/math/docs/closure_taxonomy_may30.md` — Week 1 Day 2 (`journal_clean_novel` axis value).
- `/Users/patrickkavanagh/math/submissions/tracking.db` — schema migration for `closure_hm`.
- `/Users/patrickkavanagh/math/analysis/long_tail_erdos_candidates.csv` → `long_tail_v2.csv` — Week 1 Day 3.
- `/Users/patrickkavanagh/math/Math/Erdos1052.lean` (or equivalent) → Mathlib PR branch — Week 1 Day 4–5.
- `/Users/patrickkavanagh/math/.claude/commands/sketch.md` — frontier-incremental template for fusion lane — Week 2 Day 8.

---

## 8. Sources

- V-team synthesis: `docs/research/today_results_research_impact_synthesis.md`
- Closure taxonomy: `docs/closure_taxonomy_may30.md`
- Long-tail candidates: `analysis/long_tail_erdos_summary.md` + CSV
- Strategy synthesis (S10): `docs/strategy_synthesis_may30.md`
- Per-result audits: `docs/research/{asiryan_citation,e324_h_zero,e1003_phi_n_trick,e267_badea_verification,e647_bounded_closure,ft_family_publishability,bounded_extensions_cluster,infrastructure_mathlib,strategy_critiques_value}_audit.md`
- F10 research-fusion synthesis: `analysis/math_research_audit_synthesis.md`
- Web research (W3/W5/W6): `analysis/web_research_{peer,academic,community,synthesis}*.md`
