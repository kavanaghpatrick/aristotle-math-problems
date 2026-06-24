# Bottleneck Analysis — What single upgrade most increases novel-output rate?

**Date:** 2026-05-30
**Agent:** A9 of 10
**Sibling reports received (5 of 8 by deadline):**
- **A1** `alignment_problem_selection_audit.md` — selection misses pre-2024 paywalled lit; perfect selection saves ~25-40% of slots but novelty still 0/6.
- **A2** `alignment_strategy_generation_audit.md` — LLMs retrieve, don't invent; 0/107 cross-domain analog prompts ever issued; the harness is general, the prompt convention is the limit.
- **A3** `alignment_aristotle_ceiling_audit.md` — Aristotle operates inside a closed "elementary universe"; categorical (not quantitative) gap to novel research math.
- **A4** `alignment_mathlib_gaps_audit.md` — Mordell-Weil rank highest-leverage gap; ~3 yrs community effort; necessary not sufficient.
- **A6** `alignment_output_patterns.md` — A+B = 83% mechanical, C = 17% structural, 0/6 novel today.
- **A7** `alignment_tao_calibration.md` — Below Tao long-tail bar (1(a)=0); we hit 1(c)/2(b); E728 Goldilocks-middle empty.

**Supporting evidence (F-team prior round):** F1 math-vs-compute (4/7 advances pure compute), F3 LLM consultations (87/13 META vs MATH), F10 math-research synthesis (research-fusion 2/10), E2 inflight audit (slots 741-746 all bounded sub-claims), V-team (0/22 novel), capability profile, advance DNA, AI-competition audit, infrastructure-Mathlib audit.

---

## 1. Per-hypothesis leverage estimate

| # | Hypothesis | Upper-bound novelty if ONLY this is fixed | Cost | Evidence FOR | Evidence AGAINST |
|---|---|---:|---|---|---|
| **A** | Problem selection | **~1–2%** diluted; saves ~25–40% of slots (A1 §4) but novelty count still ~0 | LOW — MathSciNet/zbMATH cross-check + named-conjecture card pack (A1 §3). ~1 week. | A1 §2: pre-2024 paywalled lit invisible to gate; Le 2012 missed despite being cited parenthetically. A1 §1: 18% LLM-pick SOLVED-SINCE rate. | A1 §4 explicit: "perfect selection does not convert a single submission into novel math. V-team 0/6 is a pipeline ceiling, not a selection failure." Selection is necessary, not sufficient. |
| **B** | Strategy generation | **~3–5%** on fusion-amenable problems; **~1–2%** diluted | LOW — `scripts/debate.py` already fully general (A2 §1). 4 prompt templates + dossier scaffold. Half-week + 2 weeks dossier work. | A2 §4: 0/107 cross-domain prompts. A2 §3 honest cap: "they retrieve and recombine, they do not invent." F10 §3 Upgrade #1: research-fusion dossier upstream of Aristotle. | A3 §4: even given a perfect cross-domain sketch with a bridge lemma, **Aristotle still substitutes elementary paths** (R9, E267, R7 h=0). The R9 evidence is brutal: Aristotle had S-unit theory + Tao entropy in the sketch and *chose* the rad-injection. Better prompts ≠ better outputs without a new lane. |
| **C** | Aristotle capability | **~1–3%** even with perfect inputs | EXTREME — vendor-dependent, months/years | A3 §2: never modular forms, sieve methods, AG objects, Galois reps. A3 §5: "It does NOT produce non-elementary novel theorems. Ceiling is what a sharp Mathlib contributor could do in a day." Capability profile: probability 0, category theory 0, quotients 0, custom Decidable 0. | Slot737 σ₀-multiplicativity, slot720 Fermat-divisor selection, R4 quintic algorithmic creativity — Aristotle DOES introduce non-obvious moves when the proof lives in the elementary universe. Capability ceiling is real but not zero. |
| **D** | Mathlib infrastructure | **~1.5–2%** marginal (per A4 §honest verdict) | EXTREME — Mordell-Weil ~3 years (Buzzard); BHV ~2 years; Subspace ~1 year; o-min ~2–3 years | A4 top-5: Mordell-Weil, Schmidt Subspace, BHV, o-minimal/Pila-Wilkie, Frostman all missing. A4: "5–10 year community effort." | A4 explicit: "Necessary, not sufficient. If Mathlib were complete tomorrow, hit rate would move from 0.8% to maybe 1.5–2%." A3 §2: Aristotle doesn't *import* novel machinery even when it exists — the binding constraint is strategic decomposition, not lemma availability. Infrastructure-Mathlib audit confirms: existing definitions are not being surfaced (`Nat.Powerful`, `SimpleGraph.IsCritical` duplicated locally). |
| **E** | Human pairing | **~5–10%** at the per-attempt level | HIGH — recruiting + sustained 1 FTE-equiv engagement of an NT/combinatorics researcher | F10 §1: 9/353 AlphaProof Nexus (all human-paired) vs 7/1166 ours (mostly bounded compute). 30× gap explained by pairing. A7 §6: E728 required Barreto's strategic insight; AI handled mechanics. F10 §2: Aristotle architecture wants informal sketches from a strategist (arxiv 2510.01346). | A7 §6 also notes E728 needed "Kummer + base-p carry analysis + dyadic existence" — pairing doesn't help if Aristotle can't formalize that. Operational ceiling on pairing is gated by Aristotle's elementary universe (A3 §5). Best estimate: pairing closes ~1/3 of the gap to Nexus, not the full 30×. |

---

## 2. Bottleneck ranking by leverage (novelty-gain / effort)

| Rank | Hypothesis | Leverage (gain ÷ cost) | Why |
|---|---|---|---|
| **#1** | **B — Strategy generation + dossier stage** | HIGH (3–5% gain at LOW cost) | Harness already general. Prompt templates + off-Lean dossier infrastructure. Zero new model capability required. Tests whether better strategy prompts actually move Aristotle's outputs (A3 §4 says no, but this is the cheapest experimental test). |
| #2 | A — Problem selection (MathSciNet gate) | MED (saves ~25–40% slots; novelty +0 directly, but cleans signal for #1 measurement) | A1 §3: MathSciNet card pack for ~60 named conjectures, <1 day. Critical scaffolding so we can *measure* if #1 worked. |
| #3 | E — Human pairing | HIGH gain (5–10%), HIGH cost | Best per-attempt leverage. Hard to land in 30 days. |
| #4 | D — Mathlib infrastructure | LOW gain (1.5–2% marginal), EXTREME cost | A4: 3+ year community effort. Worth supporting Buzzard's FLT work but not project-internal. |
| #5 | C — Aristotle base model | LOW gain (1–3%), EXTREME cost | Vendor-dependent, not actionable. |

---

## 3. The #1 bottleneck — **Strategy generation + dossier stage**

**Justification (the synthesis across siblings):**

1. **The cheapest test of capability vs sketch ceiling.** A3 §5 says Aristotle's ceiling is structural — won't help even with perfect sketches. A2 §4 says the bottleneck is prompt convention. These are testable head-to-head **only by sending better prompts and measuring**. The cost of running the test is ~$500 in API + 80 hours engineering; the information value is decisive for the next 6 months of pipeline direction.

2. **A2 + F3 + F10 converge unanimously:** 0/107 cross-domain analog prompts ever issued. The harness (`scripts/debate.py`) is fully free-form. The dossier stage (F10 Upgrade #1) is plumbing, not infrastructure. The wire submission still passes the gate — the dossier is institutional memory + selective `--context` attachment.

3. **A7 §6 identifies the "Goldilocks middle"**: E728-class problems (genuine combinatorial NT construction with a multi-step argument that is *not* novel deep machinery but *not* a bounded native_decide either). Our pipeline targets either deep open (correctly refused via P7 sorry) or finite verification (mechanical). The middle requires a strategist generating "non-textbook standard technique" prompts that Aristotle then formalizes — exactly what dossier-backed cross-domain debate produces.

4. **A1 confirms selection alone is insufficient.** Even perfect MathSciNet filtering produces 0 novel results (A1 §4). Selection only matters once strategy generation can produce something worth formalizing.

5. **A4 confirms Mathlib infrastructure is necessary-not-sufficient.** Mordell-Weil is 3 years out and would lift the rate from 0.8% to ~1.5–2%. Cheaper to extract those same percentage points from better strategy first.

6. **The crucial caveat from A3:** Even with perfect strategy prompts, Aristotle may still autonomously substitute elementary paths (R9 dropping S-units for rad-injection). If true, the ceiling is structural and #1 caps at +1–2% novelty. **But we have not actually run this test.** Every fusion-lane experiment so far has used closure-axis sketches that pre-strategized for Aristotle. The honest open question is what happens when a dossier-backed *rich* sketch with a cross-domain technique is submitted — and that is the one-month deliverable.

---

## 4. Realistic novelty rate ceiling

**Current observed rate:** 0 of 1166 mathematically-novel (per V-team 0/22 today; per F10 historical 0/7 advances aren't bounded compute; per A6 0/6 today).

| Configuration | Diluted overall novelty | On fusion-amenable subset |
|---|---|---|
| Current pipeline | ~0% | n/a (no fusion-amenable submitted) |
| + #1 fix (strategy + dossier) | **1–2%** | **3–5%** |
| + #1 + #2 (selection cleanup) | 2–3% | 5–8% |
| + #1 + #2 + #3 (human pairing) | 4–7% | 8–12% |
| + everything except #4 #5 | **5–10% peak; 3–5% sustainable** | **10–15%** |

**Hard ceiling without base-model upgrade or major Mathlib unblock: ~10%.** This matches AlphaProof Nexus's 2.5% × good problem selection × strong pairing = ~7–10%. A6 / A7 / A3 collectively rule out 20% — would require Aristotle to import non-elementary machinery (modular forms, Subspace, BHV) which A3 §2 catalogs as never-attempted across 33 today's submissions.

**Per F4 / F10 base rate stays ~1–3% on Tao long-tail even with all upgrades**, because the Tao long-tail itself is dominated by problems whose natural proof lives outside the elementary universe (E944 Dirac, E477 Sekanina, E1052 main, E938 powerful 3-AP). The "Goldilocks middle" of A7 §6 is genuinely small.

**Honest answer to "can we get to 10%?":** Yes, on a *fusion-amenable subset* with all tractable fixes including human pairing. **Honest answer to "can we get to 20%?":** No, not with current Aristotle architecture and Mathlib state. The categorical gap A3 §5 names is real.

---

## 5. One-month plan to address #1

### Week 1 (days 1–7) — Plumbing + prompt library
- **Fix `gather_context()` status filter** (`status IN ('compiled_advance','compiled_partial','disproven')`) — F10 Upgrade #2. **1 day.** This alone will reveal whether attaching priors changes Aristotle's behavior.
- **Add math-content scoring + brute-force tag** (`mathematical_content_score`, `compiled_no_advance_mechanical`) — F10 Upgrade #5 + A6 pattern A/B/C taxonomy. **1 day.** Required to *measure* whether #1 works.
- **Add MathSciNet/zbMATH named-conjecture card pack** (A1 §3) — ~60 named conjectures, JSON pack. **1 day.** Prevents the Le-2012-style misfires from contaminating the experiment.
- **Land 4 cross-domain debate prompt templates** in `scripts/debate.py` (A2 §4 + F3 §6):
  1. *Adjacent-analog discovery* — "Closest analog of {problem} in a different domain, and what cracked the analog?"
  2. *Named-mathematician transplant* — "What would Tao / Bhargava / Maynard / Scholze try? Specifically which technique from their published corpus?"
  3. *Cross-domain technique fusion* — "List 5 techniques from {algebraic geometry / representation theory / additive combinatorics / model theory / ergodic theory} that might apply, with adaptation paths."
  4. *Bias-flush* — "What technique are we systematically avoiding because it's outside our default toolkit?"

  **2 days.**

### Week 2 (days 8–14) — Dossier construction on 2 fusion-amenable problems
- Run all 4 prompt templates on **E#672 k=4 ℓ=3** (Frey + Chabauty per F5/F10 §6) and **E#938** (Bennett-Skinner Frey).
- ~$50 API spend per dossier. ~2 days per dossier wallclock. Output: 500–2000 word dossier + airlock sketch passing `check_gap_targeting()`.
- **NO submissions this week.** The dossier is the deliverable.

### Week 3 (days 15–21) — Controlled submissions
- **Critical experimental design:** for each of E#672 / E#938, submit BOTH a bare-control sketch AND a dossier-backed sketch (different slot, identical problem statement). Run F6 Experiment A pattern (bare vs rich Brocard [51,100]) on a known-closeable target as third arm.
- Total: 5 slots, ~$200 API, 9 hours wallclock each.
- This is the **first real test** of A3 §5's claim that Aristotle's ceiling is sketch-invariant.

### Week 4 (days 22–30) — Score, decide, document
- Score returned artifacts using new math-content rubric + A6 pattern taxonomy.
- Cross-arm comparison: did dossier-backed submissions produce a different *proof shape*? Did Aristotle cite the dossier's technique in `ARISTOTLE_SUMMARY.md`? Did pattern C (structural) frequency rise?
- **Decision rules:**
  - If dossier arm produces ≥1 of (a) proof structure differs from bare, (b) non-trivial bridge lemma compiled, (c) Aristotle cites cross-domain ingredient — **escalate to F10 days-31–60 plan**. Build 5 more dossiers from closure_list top-20.
  - If dossier arm produces none of the above — **A3 was right**, the ceiling is structural. Roll back to bare-only, document negative result publicly, refocus on selection + the closure-axis bounded-subclaim lane (which has its own value per A1 §4 / A7 §5).

### Milestone deliverables (end of month)
1. Cross-domain debate prompt templates in `scripts/debate.py`.
2. Dossier scaffold (`research_fusion/dossiers/{problem_id}/`) + 2 completed dossiers (E#672, E#938).
3. Math-content scoring column populated retroactively for the 240+ result archive.
4. MathSciNet card pack for ~60 named conjectures.
5. 5+ submissions through the new pipeline with audited deltas — first head-to-head A3 vs A2 test.
6. Honest go/no-go on dossier expansion for month 2.

**Budget:** ~$500 API, 80 engineering hours, 0 community-side asks. One operator, 30 days.

---

## Honest closing — three points the data refuses to let us avoid

1. **The 30× gap to AlphaProof Nexus (7/1166 vs 9/353) is not closeable by strategy prompts alone.** Their advantage is human pairing (E). Our cheapest unlock (#1) closes maybe one-third of that gap. The remainder requires bringing a mathematician into the loop — out of scope for a one-month engineering plan but the ultimate ceiling.

2. **A3 may be right.** The most important test in week 3 is whether dossier-backed sketches change Aristotle's behavior at all. If A3 §5 is correct that "the elementary universe is the ceiling," #1 caps at +1–2% novelty and the only further unlock is human pairing (#3) or vendor capability (#5). The dossier-backed experiment is **the cheapest decisive test we can run** to separate hypothesis B from hypothesis C.

3. **Even with all tractable fixes (#1 + #2 + #3), realistic ceiling is ~5–10% on a fusion-amenable subset, ~3–5% diluted.** Per F10 / A7, the Tao long-tail is dominated by problems whose natural proof lives outside Aristotle's elementary universe. 20% is not credible inside 2026 technology. The pipeline name says "math via Aristotle"; the honest pipeline behavior with #1 landed is "cross-domain literature scout + verifier with elementary-universe ceiling." That is still ~30× the current production rate of zero, and it is the highest-leverage upgrade we can land in 30 days.
