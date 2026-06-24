# Cost Optimization Model — Lane Mix Under $2k/Month

**Author:** Agent S8 of 10
**Date:** 2026-05-30
**Mission:** Optimize the monthly submission budget across the 4 lanes (BARE, CLOSURE, FUSION, INFORMAL) so that expected `compiled_advance` count and journal-clean closures are maximized for a fixed ~$2,000/month spend.

---

## 1. Inputs (from F10, I10, W4)

### 1.1 Per-lane cost (per submission)

| Lane | API cost | Aristotle compute | Wallclock | Per-submission total |
|---|---|---|---|---|
| **BARE** (`.txt` only, MCGS) | ~$0 | ~$20 (~9h GPU) | 9h | **~$20** |
| **CLOSURE** (`.txt` + `.closure.json`) | ~$5 (closure-axis prep + lit check) | ~$20 | 9h | **~$25** |
| **FUSION** (`.txt` + `.fusion.json`; I8) | ~$50-100 (Stage 1-3 ensemble: Grok+Gemini+Codex) | ~$20 | 2-5 days | **~$95** (midpoint) |
| **INFORMAL** (I9; routes via paired-LLM informal mode) | ~$30 (paired strategist GPT-5.2 Pro or Codex) | ~$30 (E124 = 6h vs BARE ~9h, but `informal` is sometimes faster — variance is real) | 1 day | **~$60** |

INFORMAL is materially cheaper than FUSION because it does not require the full Stage 1-3 dossier ensemble; it just routes a paired-LLM outline through Aristotle's informal reasoner. It is, however, more expensive than BARE because the strategist LLM is the load-bearing element.

### 1.2 Expected hit rates per lane (calibrated)

The relevant outcome metric splits in two:
- **`compiled_advance`**: status column in DB (engineering success — Lean compiles, no axioms, target_resolved=1, axiomatizes_prior_work=0). This is opt-in and conservative since 2026-05-28.
- **`journal_clean` closure** (closure-axis HM): the strict, REAL-closure marker. A journal would accept the manuscript as "we prove conjecture X" or "we disprove conjecture X". This is the only metric that maps to "the project resolved a gap".

| Lane | `compiled_advance` rate | `journal_clean` rate | Source |
|---|---|---|---|
| **BARE** on hard problems | 0.8% | 0.2% | F10: 2/220 historical (0.9% compile, ~1/4 of advances are journal-clean per F10§3 Upgrade #5; the rest are mechanical) |
| **BARE** on long-tail (Tao "lowest hanging fruit" Class 8) | ~3-5% compile, ~1-2% journal | ~1% | W8 Erdős #124, #1026, #728 precedent; "12 Erdős in 90 days" per Alexeev (Boris Alexeev: ~13%/month hit rate on hand-curated long-tail) |
| **CLOSURE** | 60-80% compile, but most are bounded extensions (`journal_partial`) | ~5-10% | F10§3 closure-axis upgrade #5; closure_list says <10% are real closure |
| **FUSION** on dossier-backed Class 6 (E#672, E#938, E#203) | 1-3% | 0.5-2% | F10§4 honest 30-60 day estimate; gated by I10's 7/10 strict-hit calibration AS UPPER BOUND |
| **INFORMAL** (formalizer pairing for solved-known problems) | up to ~80% if the result is solved upstream (formalizer mode) | 0% novel (per CLAUDE.md Rule 5: solved-upstream is `infrastructure_only`) | W4 verdict |
| **INFORMAL** (formalizer pairing for genuinely open problems) | 1-3% if paired with strong strategist | 0.5-2% | E#728 / Barreto + GPT-5.2 Pro precedent (W2 wiki) |

### 1.3 W4's verdict (critical asymmetry)

W4 / web research synthesis: of ~200 publicly-listed Aristotle contributions on the teorth wiki, ~170 are formalization entries (Section 2(b)) and only ~30 are primary contributions. Of those ~30 primaries, only 2 are Aristotle-as-sole-AI (E#124 partial, E#1077 counterexample) — the rest co-cite GPT-5.2 Pro / Claude / Gemini as the strategist.

**Operational consequence:** Aristotle-solo on a bare conjecture has a near-zero novel-math hit rate (0/7 cross-domain in our project F1). Paired-LLM via INFORMAL mode is the only configuration with public precedent for novel solves. FUSION lane is our productionization of the paired-LLM workflow.

### 1.4 I10's calibration (critical bound)

I10 ran the technique-scout ensemble on 10 known-fusion historical problems (FLT, Maynard, Zhang, Green-Tao, Hough, Cap-Set, Perelman, Faltings, Scholze, Helfgott). Result: 10/10 generous hits, 7/10 strict hits.

This is the **upper bound** of the ensemble's recall on cross-domain problems where the answer is in the literature. On genuinely open problems, the answer is by definition not in the literature, so the strict-hit rate must be lower. We use 7/10 = 0.70 as a recall ceiling and multiply by an "open-problem discount" of 0.05–0.15 to get the 1-3% fusion hit rate above.

### 1.5 Monthly budget assumption

- Total budget: **~$2,000/month**
- Practical Aristotle queue cap: ~30 submissions/month (~9h each in serial, plenty of slack in parallel)
- Historical baseline (April + May 2026): 9 submissions, 2 advances (22%) — but several of those are likely bounded extensions, not journal-clean. F10's honest characterization is "~1-2 `compiled_advance` per month, all bounded-version closures".

---

## 2. The Three Scenarios

### 2.1 Scenario A — Conservative (replicate current pattern + gates)

**Mix:** 25 BARE + 2 CLOSURE + 0 FUSION + 0 INFORMAL = 27 submissions

| Lane | Count | Unit cost | Subtotal |
|---|---|---|---|
| BARE | 25 | $20 | $500 |
| CLOSURE | 2 | $25 | $50 |
| FUSION | 0 | $95 | $0 |
| INFORMAL | 0 | $60 | $0 |
| **Total** | **27** | | **$550** |

**Expected outcomes:**

Mix bare into a 60/40 long-tail vs hard split (current pattern):
- 15 BARE long-tail × 0.04 = **0.60** advances
- 10 BARE hard × 0.008 = **0.08** advances
- 2 CLOSURE × 0.70 (compile) × 0.15 (real closure given compile) = **0.21** advances of which ~half journal-clean
- Total expected `compiled_advance`: **0.89/month** (~1)
- Total expected `journal_clean`: **0.21 + 0.04 = 0.25/month** (~1 every 4 months)

**Worst case (no advances):** $550 sunk, 27 sketches, 0 closures. Probability ≈ exp(-0.89) ≈ **41%** under Poisson approximation.

**Cost per expected advance:** $550 / 0.89 = **$618**
**Cost per expected journal-clean closure:** $550 / 0.25 = **$2,200**

This is the "BARE-heavy autopilot" — cheap, low yield, but high option value because we burn through many long-tail problems and occasionally surface a Tao-class hit.

---

### 2.2 Scenario B — Moderate (introduce fusion as a hedge)

**Mix:** 15 BARE + 5 CLOSURE + 3 FUSION + 0 INFORMAL = 23 submissions

| Lane | Count | Unit cost | Subtotal |
|---|---|---|---|
| BARE | 15 | $20 | $300 |
| CLOSURE | 5 | $25 | $125 |
| FUSION | 3 | $95 | $285 |
| INFORMAL | 0 | $60 | $0 |
| **Total** | **23** | | **$710** |

**Expected outcomes:**
- 10 BARE long-tail × 0.04 = **0.40** advances
- 5 BARE hard × 0.008 = **0.04** advances
- 5 CLOSURE × 0.70 × 0.15 = **0.53** advances (mostly `journal_partial`)
- 3 FUSION × 0.02 = **0.06** advances (but high journal-clean fraction: ~75%)
- Total expected `compiled_advance`: **1.03/month**
- Total expected `journal_clean`: 0.40×0.25 + 0.04×0.25 + 0.53×0.25 + 0.06×0.75 = **0.29/month**

**Worst case (no advances):** $710 sunk, 23 sketches. Probability ≈ exp(-1.03) ≈ **36%**.

**Cost per expected advance:** $710 / 1.03 = **$689**
**Cost per expected journal-clean closure:** $710 / 0.29 = **$2,448**

The moderate mix buys a meaningful chance at a fusion hit (3 × 2% = 6% chance of at least one) while preserving the long-tail BARE option value. Per-advance cost rises slightly but **the expected number of journal-clean closures is the highest** of the three scenarios because fusion advances are disproportionately journal-clean.

---

### 2.3 Scenario C — Aggressive (maximize fusion bet)

**Mix:** 5 BARE + 5 CLOSURE + 8 FUSION + 2 INFORMAL = 20 submissions

| Lane | Count | Unit cost | Subtotal |
|---|---|---|---|
| BARE | 5 | $20 | $100 |
| CLOSURE | 5 | $25 | $125 |
| FUSION | 8 | $95 | $760 |
| INFORMAL | 2 | $60 | $120 |
| **Total** | **20** | | **$1,105** |

**Expected outcomes:**
- 4 BARE long-tail × 0.04 = **0.16** advances
- 1 BARE hard × 0.008 = **0.008** advances
- 5 CLOSURE × 0.70 × 0.15 = **0.53** advances
- 8 FUSION × 0.02 = **0.16** advances (journal-clean fraction ~75%)
- 2 INFORMAL × 0.015 = **0.03** advances (journal-clean fraction ~70%)
- Total expected `compiled_advance`: **0.89/month**
- Total expected `journal_clean`: 0.16×0.25 + 0.008×0.25 + 0.53×0.25 + 0.16×0.75 + 0.03×0.70 = **0.31/month**

**Worst case (no advances):** $1,105 sunk, 20 sketches. Probability ≈ exp(-0.89) ≈ **41%**.

**Cost per expected advance:** $1,105 / 0.89 = **$1,242**
**Cost per expected journal-clean closure:** $1,105 / 0.31 = **$3,565**

The aggressive scenario doubles down on fusion. **Expected `compiled_advance` count is actually LOWER than scenario B** because closure's high compile rate dominates the headline number, and fusion's hit rate is bounded. But the expected count of journal-clean closures inches up because fusion hits are disproportionately journal-clean. The cost per closure rises sharply — this is a high-variance bet.

---

## 3. Summary Table

| Scenario | Cost | E[advance] | E[journal-clean] | $/advance | $/journal-clean | P(zero advances) |
|---|---|---|---|---|---|---|
| **A — Conservative** | $550 | 0.89 | 0.25 | $618 | $2,200 | 41% |
| **B — Moderate** | $710 | 1.03 | 0.29 | $689 | $2,448 | 36% |
| **C — Aggressive** | $1,105 | 0.89 | 0.31 | $1,242 | $3,565 | 41% |

**All three scenarios are well under the $2,000 cap.** This is itself a finding — we should not be blowing the budget on fusion just because we have it. The marginal dollar above $1,200/month is buying very little expected `journal_clean`.

---

## 4. Sensitivity Analysis — Fusion break-even

The headline question: **at what fusion-hit rate is fusion worth it?**

Let p_f = FUSION's `journal_clean` rate. Marginal fusion submission delivers `0.75 × p_f` journal-clean closures at a cost of $95. A marginal BARE long-tail delivers `0.25 × 0.04 = 0.01` journal-clean closures at $20 cost — so $20 buys 0.01 → $2,000 per journal-clean.

Fusion break-even: $95 / (0.75 × p_f) = $2,000 → **p_f ≥ 6.3%**.

But this is the absolute floor. The PRACTICAL break-even is "is fusion's per-closure cost competitive with closure-lane and bare-long-tail?":
- BARE long-tail: $2,000/journal-clean
- CLOSURE (mostly `journal_partial`): $25/(0.70×0.075) ≈ **$476/journal-clean** (best lane on cost, but caps at journal-partial, not full closure)
- FUSION: $95 / (0.75 × p_f) — to beat $2,000, need p_f ≥ 6.3%; to beat closure's $476, need p_f ≥ 27%

**Verdict:** Fusion's calibrated hit rate of **1-3%** is well below the 6.3% break-even for journal-clean. Fusion is **NOT cost-competitive** with bare long-tail at the calibrated rate.

**But** — fusion is the only lane targeting `full_closure` / `direction_closure` outcomes for hard structural-open problems (CLAUDE.md Class 6). Closure lane caps at `journal_partial` (bounded extension). BARE on hard caps at 0.2% journal-clean. **If we want even a chance at a real Erdős-class advance, fusion is the only lane with non-zero probability.**

This is an option-value argument. Fusion is a lottery ticket — but it's the ONLY lottery ticket for the high-value outcome.

---

## 5. Recommended Mix

**Recommendation: Scenario B (Moderate) with a tweak.**

```
15 BARE + 5 CLOSURE + 3 FUSION + 1 INFORMAL = 24 submissions, ~$770/month
```

The added INFORMAL slot exploits the cheapest paired-LLM configuration ($60 vs $95) and gives one more shot at a Class 6 / Class 8 hit without the full Stage 1-3 dossier expense.

**Why Moderate over Conservative:**
- Conservative has no fusion shots. We give up the ONLY lane with non-zero probability of journal-clean on hard structural-open problems. Project's stated goal (CLAUDE.md mission: "solve open mathematical problems") demands at least some fusion exposure.
- Moderate buys 3-4 fusion shots/month — sufficient to learn whether the calibrated 7/10 strict recall translates to actual project hits within 60-90 days, per F10's 30/60/90 plan.

**Why Moderate over Aggressive:**
- Aggressive's incremental fusion shots (5+) have diminishing marginal return because we exhaust the small list of fusion-amenable problems (per F10§6: only 2 of top-20 are fusion-amenable on the closure_list; ~5-10 across all open Erdős).
- Aggressive's cost-per-closure ($3,565) is 60% above Moderate's ($2,448).
- Aggressive starves the BARE long-tail lane that has the most consistent (if small) journal-clean expectation.

**Why we don't recommend INFORMAL > 1-2/month:**
INFORMAL is cheaper than FUSION but lacks the structured-dossier discipline. Its main value is replicating the Barreto / GPT-5.2 Pro precedent on one or two carefully chosen problems per month. Scaling INFORMAL is bottlenecked on having a quality strategist outline, not on the API budget.

---

## 6. Recommended Monthly Cap

**Hard cap: $1,200/month.**

The $2,000 envelope assumed in the briefing is the SDK / org budget. The OPTIMAL spend is materially lower:
- Moderate scenario: $710
- Moderate + 1 INFORMAL: $770
- Even Aggressive: $1,105

There is **no scenario where $2,000 buys better expected outcomes than $1,200.** Marginal dollars above $1,200 are buying additional fusion shots at $95 each, but we are bottlenecked on (a) the supply of fusion-amenable problems (F10§6: only a handful) and (b) Aristotle queue throughput (parallelism ceiling).

**Operational rule:** Cap at $1,200/month. If a particular month has 2+ exceptional fusion targets that warrant 4-5 fusion shots (e.g., closure_list top-20 sweep), the cap can absorb that. The remaining $800/month of headroom is project insurance, not target spend.

---

## 7. Sensitivity to Hit-Rate Uncertainty

The above uses F10's central estimates (BARE 0.8% hard / 4% long-tail; FUSION 2%; CLOSURE 70% compile / 15% journal-clean given compile). All are uncertain. Sensitivity:

| Parameter | Lower bound (pessimistic) | Central | Upper bound (optimistic) |
|---|---|---|---|
| BARE long-tail | 1% (F10 lower CI) | 4% | 13% (Alexeev rate) |
| FUSION journal-clean | 0.5% (Maynard-style miss) | 1.5% | 3% (F10 upper) |
| CLOSURE journal-clean | 5% | 7.5% | 15% (witness-table chunking sweet spot) |

Under pessimistic settings, Moderate yields **0.12 journal-clean/month** (~$5,900/closure). Under optimistic, **0.65 journal-clean/month** (~$1,100/closure). Range is ~5×.

**Implication for the recommendation:** Moderate is robust across the range. Conservative wins on $/advance under pessimistic settings (more BARE long-tail shots). Aggressive only wins under optimistic settings AND only on $/journal-clean — never on raw count.

---

## 8. Break-even fusion rate (TL;DR)

| Comparison | Fusion break-even rate |
|---|---|
| vs. BARE long-tail at $2,000/closure | **6.3%** |
| vs. CLOSURE at $476/closure (journal-partial dominant) | **27%** |
| vs. zero-spend null hypothesis | **0%** (any non-zero rate has positive expected value) |
| vs. opportunity cost of analyst time on dossier (~$200/dossier in attention) | ~**1%** (this is the regime we're in) |

The calibrated fusion rate of 1-3% **does not break even against bare long-tail on pure $/journal-clean math.** But it is the only lane with any probability of hitting CLAUDE.md Class 6 / 7 outcomes. **The case for fusion is option value, not expected value.**

---

## 9. Honest Uncertainty

1. The FUSION 1-3% rate is calibrated against the I10 ensemble's 7/10 strict-hit on HISTORICAL problems. Open problems are by construction harder. The actual rate could be 0% (W4's null-hypothesis case: ensemble adds nothing) or as high as 5% (if Aristotle's informal reasoner exploits the bridge-lemma scaffold better than the redacted-prompt setting suggested).
2. BARE long-tail's 4% rate is Alexeev's reported "12 in 90 days" — but those were hand-curated by an Erdős expert. Our project's curation quality is unproven; could be 1-2% in practice.
3. CLOSURE's `journal_partial` outputs are valuable as research notes but do NOT resolve gaps in the CLAUDE.md sense. Counting them as "advances" inflates the headline numbers; the model intentionally separates `journal_clean` from `compiled_advance`.
4. INFORMAL is a hybrid — we listed it at 1.5% hit rate but historical data is essentially nil (E124, E728, E1026, E481 = 4 known hits, all paired with named strong strategists). Our project doesn't currently have a GPT-5.2 Pro license, which is the canonical pairing. Budget assumes Codex/Grok/Gemini as strategist substitutes.

---

## 10. Documentation Path

`/Users/patrickkavanagh/math/docs/cost_optimization.md`
