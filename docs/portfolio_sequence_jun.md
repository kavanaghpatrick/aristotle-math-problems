# 30-Day Submission Portfolio Sequence — June 2026

**Author:** Agent S2 of 10 (sequencing & budgeting)
**Date drafted:** 2026-05-30
**Coverage window:** 2026-06-01 → 2026-06-28 (4 weeks)
**Inputs synthesized:**
- `analysis/closure_list_may30.md` (Agent C10 closure-axis ranking)
- `analysis/literature_kill_list.csv` (26 AI-closed / solved problems — DO NOT SUBMIT)
- `analysis/aristotle_capability_profile_may30.md` (Aristotle's demonstrated profile)
- `docs/infrastructure_changes_may30/I10_calibration_test.md` (fusion lane 7/10 strict)
- `docs/infrastructure_changes_may30/I8_fusion_lane.md` (FUSION gate spec)
- `docs/fusion_axis_companion_spec.md` (companion JSON requirements)
- `submissions/tracking.db` (inflight + historical state)

**S1 status:** `docs/lane_routing_matrix.md` not yet on disk at draft time. This sequence uses an inferred lane matrix from capability profile, fusion calibration, closure list, and CLAUDE.md "Pipeline (4 lanes)" guidance.

---

## 1. Inferred Lane Matrix (proxy for S1 output)

Four lanes per CLAUDE.md "Pipeline (4 lanes)":

| Lane | Best for | Cost/slot | Aristotle subsystem |
|---|---|---|---|
| **BARE** | Bounded computational closures, finite witness verifications, mechanical range extensions. Aristotle's MCGS shines here (slot 720 / 722 pattern). | $1-2 Aristotle compute | MCGS formalizer (subsystem #1) |
| **FUSION** | Open problems where named-technique strategy from cross-domain literature unlocks the path. 7/10 historical strict-hit on F4 calibration. Companion `.fusion.json` required. | $5-12 (Codex+Gemini+Grok for Stages 1-3) + $1-2 Aristotle | MCGS + informal-reasoner via outline |
| **CLOSURE** | When result must qualify as REAL closure per C2 rubric (CS∈{full/direction/disproof}, CM≠none, CR∈{clean_decidable, mitigable}, HM=journal_clean). Companion `_closure.json`. | $1-2 Aristotle | MCGS |
| **INFORMAL** | When informal-reasoner subsystem is explicitly invoked via Stage-3 outline; subset of FUSION. | $3-6 | informal-reasoner (subsystem #2) |

Per the I10 calibration (10/10 generous, 7/10 strict, $50-80 for 10 problems = ~$5-8/consultation), **FUSION debut is APPROVED for production on open problems**. Caveat: trust same-domain granularity over named-technique granularity.

### Lane-assignment heuristic

- Bounded universal / finite verification + supporting witness table → **BARE**
- Open conjecture with cross-domain named technique nominated by 2+ AIs → **FUSION**
- Mechanical extension of a compiled_advance precedent → **BARE**
- Disproof search with external candidate already in hand → **BARE** (witness pre-validated)
- Disproof search with NO candidate → **FUSION** (need search strategy)
- Closure-claim-grade per C2 rubric → also tag **CLOSURE** companion

---

## 2. Inflight & State Assumptions

**Inflight (slots 741-746):** 6 unresolved Aristotle submissions. Status assumed `submitted` through Week 1 start (June 1).
- These return ~Day 3-7 typical; gate Week 2/3 decisions on their outcomes.

**Recently-completed precedents (compiled_advance):**
- slot720 (FT p=3, q≡71 mod 72, q≤1000): mechanism = `native_decide` over `not_dvd_via_fermat_factor`
- slot722 / slot738 (Brocard [501,1000]): chunked precomputed-prime table + `interval_cases` + `native_decide`
- slot712 (Erdős 672 k=3 closed): direct precedent for k=4 extension
- slot737 (Erdős 647 sub-claim, σ₀ Cunningham): precedent for slot741+
- slot740 (Erdős 203 8×8 covering disproof): precedent for 12×12 lift

**Kill list (26 problems — DO NOT submit):** erdos_1051, erdos_1105, erdos_1148, erdos_125, erdos_152, erdos_258, erdos_26, erdos_283, erdos_326, erdos_330, erdos_347, erdos_351, erdos_38, erdos_397, erdos_42, erdos_457, erdos_694, erdos_728, erdos_741, erdos_846, erdos_848, erdos_851, erdos_888, erdos_897, erdos_90, erdos_942, erdos_996. **NONE appear in this portfolio.**

**Budget envelope:** 30 BARE submissions/month max; ≤20/month if mix is 50% fusion ($150-200 fusion budget cap).

---

## 3. Four-Week Schedule (20 slots planned across 4 weeks)

Each row: problem · lane · expected outcome · dependencies · exit criterion · cost.

### Week 1 (Jun 1-7) — 5 slots. Highest-confidence + lowest-risk.

| # | Slot | Problem | Lane | Expected outcome | Dependency | Exit if no advance | Cost |
|---|---|---|---|---|---|---|---|
| W1-1 | 747 | **erdos_647 Cunningham residual 35** (per `june01_batch_audit.md` #3) | BARE | compile + advance (slot738-style cascade). Highest-confidence of the slate; 35-row witness table well within slot738 headroom. | None (witnesses pre-computed in `erdos647_cunningham_witnesses.json`) | If no advance: re-examine `erdos647_cunningham_extended_table.json` for missed shape constraints, retry in W3 | $1.5 |
| W1-2 | 748 | **odd multiperfect σ₀(n)=11 non-existence** (slot1258 inflight is closure-axis precursor; if returned advance, this is the journal-clean extension) | BARE+CLOSURE | compile_partial → potentially advance; σ-multiplicativity case-split is Aristotle's strongest tool per capability profile §1.4 | Wait for slot1258 result (target Day 1-2) | If slot1258 no_advance: pivot W1-2 to FT q=1583 alternate (W1-5 below) | $2 |
| W1-3 | 749 | **brocard_nrange_1001_2000** (per `june01_batch_audit.md` #7) | BARE | compile + advance. Mechanical extension of slot738 with 2× sieve scaling. Calibration slot. | None | If runtime explodes: drop to [1001, 1500] in W3 retry | $2 |
| W1-4 | 750 | **erdos_672 k=4 l=3 AP-of-3-powerful witness** | BARE | compile + advance. Direct extension of slot712. Witness table in `erdos672_k4_l3_search.json` (1.8MB precomputed). | None | If no_advance: regroup as FUSION in W3 via `adjacent_analog.md` template | $1.5 |
| W1-5 | 751 | **FT_p3_q1583_alternate** (per `june01_batch_audit.md` #2) | BARE | compile + advance. Single-point diagnostic at canonical break q=1583. | None | If no_advance: drop FT family for 30 days; reroute compute | $1.5 |

**Week 1 total cost:** $8.5. **Week 1 expected outcomes:** 3-4 compiled_advance, 1-2 compiled_partial, 0-1 no_advance.

### Week 2 (Jun 8-14) — 5 slots. Fusion-lane debut.

**FUSION dossiers prepared:** Only `research_fusion/runs/erdos_938/` exists. W2 must commit dossier-prep work in parallel for E64, E203, E672 (if W1-4 missed), E952, E938.

| # | Slot | Problem | Lane | Expected outcome | Dependency | Exit if no advance | Cost |
|---|---|---|---|---|---|---|---|
| W2-1 | 752 | **erdos_938 powerful 3-APs** (Frey-Hellegouarch dossier ready) | FUSION (paired_llm=mixed) | compile_partial. Long-shot but ensemble nailed Frey on FLT calibration. The single best-prepared fusion debut. | Dossier exists; airlock check pre-clean | If no_advance: refine via `obstruction_diagnosis.md` template, retry W4 | $8 |
| W2-2 | 753 | **erdos_203 grid 12×12 B=1000** (per `june01_batch_audit.md` #5) | BARE | compile_partial or genuine no_advance. Either outcome informs slot740 lift question. | None | Move E203 off the active list; rebrand as long-tail | $2 |
| W2-3 | 754 | **erdos_64 Erdős-Gyárfás 2^k cycle disproof** | FUSION (paired_llm=codex) | compile_partial. SAT-search precedent in Codex C3 + dossier in `analysis/research_fusion_erdos64.md`. | Stage 1-3 dossier complete by Jun 8 | If no_advance: keep as W4 long-shot retry with `bias_flush` debate | $7 |
| W2-4 | 755 | **primitive weird ω=6 non-existence** | BARE+CLOSURE | compile_partial. σ-multiplicativity DNA shared with W1-2. | Wait for W1-2 outcome; if W1-2 advanced, run; if W1-2 failed, downgrade to W3. | If no_advance: hold for W4 | $2 |
| W2-5 | 756 | **erdos_672 k=4 l=3 FUSION retry** (only if W1-4 missed) OR **goormaghtigh (5,3) closure** if W1-4 advanced | FUSION or BARE+CLOSURE | depends on selector | Conditional on W1-4 | If both branches stall: roll to W4 | $7 |

**Week 2 total cost:** $26. **Week 2 expected outcomes:** 1-2 compiled_advance, 2-3 compiled_partial, 1-2 no_advance.

### Week 3 (Jun 15-21) — 5 slots. Contingent on W1/W2 results.

Branching logic. Default plan assumes baseline ~50% advance rate from W1/W2.

| # | Slot | Problem | Lane | Expected outcome | Dependency | Exit if no advance | Cost |
|---|---|---|---|---|---|---|---|
| W3-1 | 757 | **Lehmer totient ω=7 odd sqfree** | BARE+CLOSURE | compile_partial. Workhorse multiplicativity slot. | If W1-2 + W2-4 both no_advance: drop this slot — multiplicativity attack is exhausted | Move on permanently to other techniques | $2 |
| W3-2 | 758 | **erdos_137 k=4 powerful disproof** | BARE | compile_partial. Bounded existential. | None | Drop for the month | $2 |
| W3-3 | 759 | **erdos_203 sierpinski 1D benchmark** (audit #6) | BARE | compile_partial. Methodology probe. | None | Methodology validated either way | $1.5 |
| W3-4 | 760 | **erdos_617 Erdős-Gyárfás r=4 K_17 disproof** | FUSION (paired_llm=grok) | compile_partial. Search precedent in `erdos617_r5_search_may30.json`. | Stage 1-3 dossier by Jun 15 | Retry with `bridge_lemma` template if no_advance | $8 |
| W3-5 | 761 | **erdos_672 retry with NEXT k or NEXT precedent context** | BARE | compile_partial | Wait for W1-4 / W2-5 outcomes; submit only if neither advanced | Park E672 family for 30 days | $1.5 |

**Week 3 total cost:** $15. **Week 3 expected outcomes:** 1-2 advance, 2-3 partial, 1-2 no_advance.

### Week 4 (Jun 22-28) — 5 slots. Long-tail diversification (Tao sweet-spot).

Tao's sweet-spot framing: 1 long-shot per week is the rule (closure list §"Week 4"). Diversify domain coverage for the month.

| # | Slot | Problem | Lane | Expected outcome | Dependency | Exit if no advance | Cost |
|---|---|---|---|---|---|---|---|
| W4-1 | 762 | **erdos_307 finite prime sets with reciprocal-product = 1** | BARE | compile_partial. Pure existence search; Aristotle-friendly via small-prime enum. | None | One-shot; close out E307 for the quarter | $1.5 |
| W4-2 | 763 | **erdos_835 (k+1)-subset coloring witness** | BARE | compile_partial. Bounded combinatorial search. | None | Close out E835 for the quarter | $1.5 |
| W4-3 | 764 | **erdos_283 squares family extension** (NOT erdos_283 main; the W-team active variant per `Math/Erdos283Squares.lean`) | BARE | compile_partial. Local Lean precedent. | Verify NOT in kill list (kill list has erdos_283 base; the squares variant is open) | If conflicts with kill list: substitute erdos_938 RETRY with `obstruction_diagnosis` template | $1.5 |
| W4-4 | 765 | **LONG-SHOT — Conway 99-graph existence** | FUSION (paired_llm=mixed) + external SAT search | compile_partial OR transformative advance. Conway's $1000. | Only fire if external SAT search yields a candidate adjacency by Jun 22; otherwise sub for E938 second-pass | If no advance: log as scoping experiment | $10 |
| W4-5 | 766 | **erdos_952 Gaussian moat construction (FUSION)** | FUSION (paired_llm=codex+grok) | no_advance most likely; long-shot. F4 catalog has analytic-number-theory precedent. | Stage 1-3 dossier `analysis/research_fusion_erdos952.md` exists | Park E952 indefinitely | $8 |

**Week 4 total cost:** $22.5. **Week 4 expected outcomes:** 1 advance (lucky), 2 partial, 2 no_advance. **W4-4 is the single bet.**

---

## 4. Dependencies & Parallelization

### Hard dependencies (do-not-submit-before)

```
slot1258 (inflight, odd multiperfect σ₀=11 closure-axis precursor)
   └─→ W1-2 (slot748, σ₀=11 BARE+CLOSURE extension) — wait Day 1-2
       └─→ W2-4 (slot755, primitive weird ω=6) — same multiplicativity DNA
           └─→ W3-1 (slot757, Lehmer ω=7) — third in the multiplicativity chain

slot741-746 (inflight, unknown content) — block any submission that targets the SAME problem
   └─→ Cross-reference via `mk failed` before W1 day-of-submit

W1-4 (slot750, E672 k=4 BARE) — if advance, W2-5 becomes Goormaghtigh; if no_advance, W2-5 becomes E672 FUSION

W2-1 (slot752, E938 FUSION debut) — calibration data point
   └─→ W4-4 (slot765, Conway 99-graph FUSION) — gates whether the long-shot fusion shot is worth firing
```

### Parallel batches (submit same day, no inter-dependency)

- **Day 1 (Jun 1):** W1-1 + W1-3 + W1-5 (all BARE, all unrelated precedents)
- **Day 8 (Jun 8):** W2-2 + W2-3 (BARE + FUSION-E64 parallel; airlock independent)
- **Day 15 (Jun 15):** W3-2 + W3-3 (both light BARE)
- **Day 22 (Jun 22):** W4-1 + W4-2 (both bounded combinatorial)

### Dossier-prep work to schedule BEFORE submission

Each FUSION submission requires Stage 1-3 dossier + companion JSON authored before submit-day. Backfill schedule:

- **By Jun 5:** E64 dossier complete (for W2-3)
- **By Jun 5:** E938 dossier polished (already drafted; verify airlock passes)
- **By Jun 12:** E617 dossier complete (for W3-4)
- **By Jun 19:** Conway 99-graph dossier + external SAT search results (for W4-4)
- **By Jun 19:** E952 dossier (already partial in `analysis/research_fusion_erdos952.md`)

Dossier-prep cost: ~$5-8 per problem via `mk debate <id> technique_scout` (3 AIs × 1-3 rounds).

---

## 5. Budget Table

| Component | Per slot | Slots | Subtotal |
|---|---|---|---|
| BARE Aristotle compute (small) | $1.5 | 9 slots (W1-1, W1-3, W1-4, W1-5, W2-2, W3-1, W3-2, W3-3, W3-5) | $13.5 |
| BARE+CLOSURE Aristotle compute (mid) | $2.0 | 4 slots (W1-2, W2-4, W4-1, W4-2) | $8.0 |
| BARE (W4 long-tail) | $1.5 | 2 slots (W4-3, plus 1 reserve) | $3.0 |
| FUSION Aristotle compute (informal-mode + paired prompt) | $2.0 | 5 slots (W2-1, W2-3, W3-4, W4-4, W4-5) | $10.0 |
| FUSION dossier prep (Stages 1-3 via mk debate) | $6.0 | 5 dossiers (E64, E938, E617, Conway, E952) | $30.0 |
| FUSION paired-LLM consultation (per slot, on top of dossier) | $1.0 | 5 slots | $5.0 |
| Conway 99-graph external SAT search | $10.0 | 1 (compute-time provision) | $10.0 |
| **Total month** | | **20 slots + 5 dossiers** | **~$79.5** |

**Conservative buffer:** +$20 for retries, rescores, debate templates. **Working envelope: $100.**

Within budget ($30/month implicit ceiling at $1/slot, $300 if FUSION debut at full rate). **At ~$100, well under budget.**

---

## 6. Highest-Conviction & Long-Shot Picks

### Three highest-conviction Week 1 submissions

1. **W1-1 (slot747) erdos_647 Cunningham residual 35.** Witness table already computed (35 rows). Aristotle's `native_decide`-over-precomputed-table is the highest-yield template per capability profile §4. Expected outcome: **compiled_advance**.
2. **W1-3 (slot749) brocard_nrange_1001_2000.** Mechanical extension of slot738; encoding refactor headroom proven. Calibration slot for sieve-cost validation. Expected: **compiled_advance** (low-novelty but high-reliability).
3. **W1-4 (slot750) erdos_672 k=4 l=3.** Direct precedent in slot712 with witness data already mined (1.8MB). Aristotle's `native_decide` discharger fires on the AP-witness check. Expected: **compiled_advance**.

### Single Week 4 long-shot bet

**W4-4 (slot765) Conway 99-graph existence/non-existence.** This is the single most asymmetric bet of the month. Closure list §"Top-20 #4" prices it at 2/10 probability but flags as **transformative if hit** (Conway's $1000 prize, would settle a 50-year-open question). The fusion lane's 7/10 calibration says the technique-scout ensemble surfaces the right adjacency for structurally similar SRG existence questions (graph-theory adjacent_analog template). **Fire only if external SAT search yields a candidate adjacency by Jun 22** — pure verification is the BARE strong suit. The bet is: an LLM-paired strategy + external SAT seeder + Aristotle MCGS verifier MIGHT find the adjacency or prove non-existence in a way no individual approach has managed since 1969.

If the SAT seeder finds nothing, W4-4 becomes W4-4-alt: **erdos_938 retry with `obstruction_diagnosis` debate template** — same fusion infrastructure, less asymmetric but more likely to advance.

---

## 7. Risk Register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Multiplicativity chain (W1-2, W2-4, W3-1) all fail | 30% | Drop the chain after 2 misses; budget reroutes to W3 long-tail. |
| FUSION calibration overfit to historical problems (F4 calibration was retrospective) | 25% | Strict-hit 7/10 is FRAMEWORK confidence, not THIS-PROBLEM confidence. Treat first 5 fusion submissions as ARM 1; reassess. |
| Aristotle inflight slots 741-746 conflict with W1 targets | 15% | Mandatory `mk failed` + `mk context` check Day 1; bump conflicting slot to W2. |
| Conway SAT seeder produces no candidate by Jun 22 | 70% | Pre-staged W4-4-alt (E938 retry) ready to substitute. |
| Dossier-prep falls behind (need 5 dossiers by Jun 19) | 40% | Spawn dossier-prep tasks in parallel with W1 submissions; one per week minimum. |
| Closure-axis companion not yet enforced — false "closure" claims | 30% | Trust C2 rubric audit per submission, NOT submission counter. |

---

## 8. Exit Criteria for the Whole Month

If by Jun 28 the portfolio has:
- **0 compiled_advance:** stop, full retro on the lane matrix, suspend FUSION for July.
- **1-3 compiled_advance:** baseline. Proceed to July with refined lane matrix (S1's output if landed) and updated calibration.
- **4+ compiled_advance:** strong signal. Increase July to 25-30 slots; introduce 1 transformative-bet per fortnight instead of per month.
- **Any genuine closure (per C2 real_closure_candidate=true):** halt for 3 days, manual review, publish-grade write-up before continuing.

---

## 9. Notes & Hand-offs

- **S1's lane matrix not received:** This sequence used the implicit lane definitions from `CLAUDE.md`, `I8_fusion_lane.md`, and the closure list. If S1's matrix lands before Jun 1, re-validate lanes for slots 752, 754, 760, 765, 766 (the FUSION assignments).
- **`research_fusion/runs/` is bottleneck:** Only `erdos_938/` exists. The other 4 fusion dossiers (E64, E617, Conway, E952) need authoring before their submission week. Recommended: tag the dossier-prep work as P0 for the closure-team for Jun 2-19.
- **Kill list compliance:** All 26 kill-list problems are EXCLUDED. Verification was per-row against the portfolio at draft time.
- **Submission slots numbered sequentially 747-766:** assuming current slot counter is at 746 (per inflight assumption). If actual counter ≥ 747, adjust accordingly; numbering is not load-bearing.

---

## 10. Documentation path

This file: `/Users/patrickkavanagh/math/docs/portfolio_sequence_jun.md`

Hand-offs:
- Update `docs/portfolio_sequence_jun.md` Section 9 at end-of-Week-1 with W1 results
- Mirror compiled_advance / compiled_partial results to `submissions/tracking.db`
- Per-slot closure-axis JSON: `submissions/sketches/<name>_closure.json` (per X2 spec, when shipped)
- Per-slot fusion JSON: `submissions/sketches/<name>.fusion.json` (per I8 spec)
