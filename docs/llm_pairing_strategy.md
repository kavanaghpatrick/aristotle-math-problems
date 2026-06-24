# LLM Pairing Strategy

**Author:** Agent S9 of 10
**Date:** 2026-05-30
**Status:** Strategy document; not yet bound to gate
**Mission:** For each pipeline stage, name the LLM(s) to use, why, what the fallback chain is, and whether the GPT-5.2 Pro gap is worth closing.

**Source citations:**
- F3 LLM-consultation audit — `/Users/patrickkavanagh/math/analysis/llm_consultation_audit.md` (87% META-PROCESS, 13% math-content; never asked for cross-domain technique import)
- I10 calibration test — `/Users/patrickkavanagh/math/docs/infrastructure_changes_may30/I10_calibration_test.md` (Codex 7/10 strict, Gemini 6/10, Grok 4/10 — but Grok 10/10 generous = domain locator)
- W8 web-research synthesis — `/Users/patrickkavanagh/math/analysis/web_research_synthesis.md` (canonical pairing: GPT-5.2 Pro → Aristotle informal mode)
- LLM math landscape — `/Users/patrickkavanagh/math/docs/research/llm_math_landscape.md` (GPT-5.5 Pro best on FrontierMath; Codex CLI defaults to gpt-5.5)
- Lane routing matrix — `/Users/patrickkavanagh/math/docs/lane_routing_matrix.md` (Class 6 = FUSION+INFORMAL needs GPT-5.2 Pro)
- Grok closure candidates — `/Users/patrickkavanagh/math/analysis/grok_closure_candidates.md` (Grok added `KnownCliff` axis: Pollock=F9, FT q>1583=F5)

---

## TL;DR

| Stage | Primary LLM | Why | Cost/call | Fallback |
|---|---|---|---|---|
| Stage 1 Literature pull (arXiv/MathSciNet) | **Codex CLI (gpt-5.5)** | Codex has live web-search via `codex exec` + arxiv API integration; surfaced 20 results on closure_candidates sweep | $1–3 | Gemini CLI with `--google-search`, then Claude WebSearch |
| Stage 2 Analogy mining (CRITICAL) | **Ensemble: Codex + Gemini + Grok** | I10: 10/10 generous hit when union'd. None of the three alone exceeds 7/10. | $5–10 | Drop Grok if API broken; 2-LLM ensemble is 9/10 generous |
| Stage 3 Technique transfer (named cards) | **Codex (primary) + Gemini (critique)** | Codex 7/10 strict on naming exact technique (Faltings-Arakelov in 4 words). Gemini surfaces taxonomy gaps. | $3–5 | Codex alone passes the 4/10 gate |
| Stage 4 Informal proof outline | **GPT-5.2 Pro if available; else Codex via codex_proof_loop** | W4 canonical recipe: GPT-5.2 Pro is the mathematical author for #728, #205, #457, #635, #897. Codex CLI is gpt-5.5 = adjacent generation. | $5–20 | Codex+Aristotle pair = closest substitute; cost ~$50 |
| Stage 5 Aristotle response post-mortem | **Codex (Lean expert) + Claude (us, synthesis)** | Codex reads Lean fluently; Claude consolidates into DB updates and forwards lessons. | $1–2 | Claude alone (degrades but works) |
| Closure-axis classification | **Codex + Gemini ensemble** | F3 worked-example: Codex did the CS/CM/CR mapping cleanly. Gemini caught one mislabel. | $2 | Either alone is acceptable |
| Literature-check (Bloom-discipline) | **Codex with web-search (mandatory)** | Has the discipline to actually open arxiv/MathSciNet links. Gemini CLI sometimes hallucinates URL contents. | $1–2 | Gemini with `--google-search`, then human-in-loop |
| Debate templates per problem class | (see §3 below) | Class-specific routing | varies | varies |
| **Breakpoint-risk screen** | **Grok (specifically)** | W7 finding: Grok is the only LLM that added `KnownCliff = F9` to Pollock and `F5` to FT q>1583. Other LLMs missed both. | $1 | If Grok broken, ask Codex explicitly "what is the F-mode risk?" |

---

## 1. Per-stage rationale

### Stage 1 — Literature pull (arXiv abstract reading)

**Primary: Codex CLI.** Codex has the most disciplined web-search-and-read pipeline in our toolchain. The closure_candidates sweep (`/Users/patrickkavanagh/math/analysis/codex_closure_candidates.md`) opened 20 real arxiv URLs and quoted abstracts verbatim. Gemini CLI was slower and twice produced URL contents that did not match the actual abstract (hallucination). Claude WebFetch is reliable but Claude is more expensive per token than a dedicated codex call.

**Fallback chain:** Codex → Gemini CLI → Claude WebFetch → human-in-loop. Never skip literature-check (W2 directive after the GPT-5 Oct-2025 Bloom debacle).

**Failure mode to watch:** "5/10 with hallucinated references" (W8 #5 — 6/8 LLM-generated Hodge papers in Litt's review had fake citations). Always demand verbatim arxiv IDs and verify with `curl` once before trusting the abstract.

### Stage 2 — Analogy mining (the critical stage per I10)

**Primary: Ensemble Codex + Gemini + Grok.** I10 calibration is unambiguous: no single model exceeds 7/10 strict. Union (= ensemble best) reached 10/10 generous, 7/10 strict. The cost of running all three for ~$5–10 per consultation buys recall the team has never had.

**Specific roles inside the ensemble:**
- **Codex** is the headline-proposer (8/10 nailed the exact technique).
- **Gemini** is the buried-in-prose discoverer (Gemini-only buried "Shannon entropy bottleneck" in Hough; "entropy + W-functional" in Perelman).
- **Grok** is the domain locator + cliff-detector. 10/10 generous hits but only 4/10 strict; it nominates the right neighborhood. AND uniquely adds risk markers other models miss.

**Fallback chain:** If Grok API is broken (it currently is for `grok-4.3` per `scripts/debate.py` line 65; only `grok-4.20-0309-reasoning` works), run the 2-LLM Codex+Gemini ensemble. Expected loss: ~1 strict hit per 10 problems, but generous recall stays at 9/10.

**The single most important rule for Stage 2:** add **bias-flush** as a mandatory step (per F3 §6 #4). After the first round, prompt each model: *"Name 3 techniques you have NOT yet suggested for this problem that you would suggest if I told you this was a problem in {commutative algebra, p-adic analysis, finite model theory}."* This corrects the "stay in domain" failure of the strict-hit prompt — without it, the Maynard miss recurs.

### Stage 3 — Technique transfer (named cards with fit_score)

**Primary: Codex (proposer) + Gemini (critique).** A "named card" is a JSON object with `technique_name`, `domain_of_origin`, `adaptation_step`, `failure_mode`, `fit_score [0,1]`. Codex's strict-hit DNA (I10: 7 of 10 strict hits — including "Faltings-Arakelov height via arithmetic Riemann-Roch" in 4 words for a redacted Mordell prompt) makes it the proposer. Gemini's role is to assign fit_score and challenge weak proposals.

**Fallback chain:** Codex alone passes the I10 gate (4/10 threshold). If both Codex and Gemini are unavailable, Stage 3 should defer to Claude — but cards generated by Claude alone should be marked `provenance: claude_only` and flagged for re-validation on next ensemble run.

### Stage 4 — Informal proof outline drafting (THE GPT-5.2 PRO GAP)

**Primary (ideal): GPT-5.2 Pro.** Per W4 / W8: the canonical Aristotle solving workflow is *GPT-5.2 Pro generates informal proof → Aristotle formalizes*. This pairing produced Erdős #728, #205, #457, #635, #897. We do not have GPT-5.2 Pro in our toolchain.

**Primary (today): Codex CLI via `codex_proof_loop.py`.** Codex CLI defaults to gpt-5.5 (`scripts/codex_proof_loop.py:607` records `gpt-5.3-codex` but the CLI now resolves to gpt-5.5 per docs/research/ATTACK_WORKFLOW.md). Per the LLM math landscape, GPT-5.5 Pro scores 52.4% on FrontierMath T1-3 and 39.6% on T4 — the strongest published FrontierMath scores. **GPT-5.5 ≈ GPT-5.2 Pro is a defensible interpretation** as long as the FrontierMath benchmark is the metric we care about; the W4 paper's claim that "GPT-5.2 Pro is unambiguously the mathematical author" reflects publication-time pairing rather than a benchmark gap, since GPT-5.5 wasn't out yet for #728/#457/#635/#897/#1197.

**The pragmatic call:** Use Codex CLI (gpt-5.5) for Stage 4. Treat it as our GPT-5.2 Pro analog. Mark every Stage-4 outline with `paired_llm = codex-gpt-5.5-cli` for audit; do NOT silently log it as `gpt-5.2-pro`.

**Cost:** Codex per `codex_proof_loop` iteration ≈ $5–20 depending on token count.

### Stage 5 — Aristotle response post-mortem

**Primary: Codex + Claude (us).** Codex reads Lean fluently and can summarize a 1148-line slot result into 3 bullets. Claude's role is synthesis into DB (`submissions.cost_usd`, `axiomatizes_prior_work`, `target_resolved`) and the `failed_approaches` table.

**Fallback chain:** Claude alone, with longer manual scan. Costs more in our time but no LLM money.

### Closure-axis classification

**Primary: Codex + Gemini ensemble.** The 4-axis taxonomy (CS / CM / CR / HM per `docs/closure_axis_companion_spec.md`) is mechanical once a result is known; Codex executes it fastest. Gemini provides a sanity-check pass to catch HM mislabels (the dangerous one: marking a `bounded_version_closure` submission as `journal_clean`).

### Literature-check (Bloom-discipline)

**Primary: Codex with web-search, mandatory.** The Bloom debacle (W6: Kevin Weil claimed "10 Erdős solutions"; Bloom verified none were novel) is the cautionary tale our pipeline keeps re-deriving. Literature-check must be done by an LLM that actually opens URLs. Codex CLI's `codex exec` is the only tool in our chain with disciplined arxiv-fetching.

**Hard rule:** for any submission in Class 5 (solved-upstream-formalization risk), literature-check is REQUIRED and cannot be substituted by ensemble vote. Codex must actually return verifiable arxiv IDs.

### Debate templates per problem class

Implemented in `/Users/patrickkavanagh/math/research_fusion/prompts/debate_templates/`:

| Template | Primary LLM | Class |
|---|---|---|
| `technique_scout.md` | Ensemble (Codex+Gemini+Grok) | Class 2, 3, 6 (any with FUSION lane) |
| `adjacent_analog.md` | Codex + Gemini (Grok if available) | Class 6 cross-domain |
| `bridge_lemma.md` | Codex (proposes) + Gemini (critiques) | Class 6 specifically |
| `obstruction_diagnosis.md` | **Grok primary** + Codex | Stage 2 + Stage 4 — needs cliff-detector |
| `tao_simulator.md` | Codex (best at "what would Tao try") | Class 6 + Class 8 |
| `bias_flush.md` | Run after every Stage-2 ensemble | All FUSION classes |

---

## 2. The GPT-5.2 Pro question

**Should we pursue API access? My recommendation: NO, with one caveat.**

### Why not pursue

1. **Codex CLI is gpt-5.5**, which is GPT-5.2 Pro's successor on the FrontierMath benchmark (per `llm_math_landscape.md`: GPT-5.5 Pro 52.4%/39.6% on T1-3/T4). The W4 finding that "GPT-5.2 Pro is the mathematical author for #728" is a *publication-time* observation — those proofs were produced when GPT-5.5 did not yet exist. The architectural pattern (informal-author + Aristotle-formalizer) is what matters; the specific weights are interchangeable.

2. **OpenAI does not publicly differentiate GPT-5.2 Pro from gpt-5.5 in the API.** OpenAI's Responses API exposes `gpt-5.5-pro` and `gpt-5-codex` but the "5.2 Pro" SKU is a marketing label from late 2025 that has been folded into 5.5. Adding "GPT-5.2 Pro" to our toolchain via the OpenAI API would in practice mean adding `gpt-5.5-pro` — which Codex CLI already calls.

3. **Cost of an additional API integration ≈ 1–2 days of engineering time** for a marginal capability gain at best, and zero gain if codex CLI is already the same model.

### The one caveat

**If OpenAI publishes a "GPT-5.5 Pro Math Mode" variant** (rumored per `ofox.ai` Q2 2026 roadmap, cited in `llm_math_landscape.md`) — that would be worth integrating. Specifically: a long-context math mode with chain-of-thought baked in. Trigger condition: when the OpenAI Platform docs list a model explicitly with `math_mode = true` or a benchmark-leading FormalProofBench score. **Until then, treat Codex CLI as our Stage-4 author.**

### Substitute logic (today)

For every Class 6 problem (FUSION+INFORMAL lane), the canonical workflow is:

```
1. Codex CLI (gpt-5.5) drafts informal proof outline (Stage 4)
2. Submission to Aristotle in informal mode via aristotle_informal.py
3. paired_llm = "codex-gpt-5.5-cli"  (HONEST LABEL — not "gpt-5.2-pro")
```

This is the closest substitute we can build today.

---

## 3. Grok's specific value-add — the `KnownCliff` axis

Per W7 and the grok_closure_candidates output (`/Users/patrickkavanagh/math/analysis/grok_closure_candidates.md`):

- Grok was the ONLY LLM that flagged **Pollock tetrahedral verification as `KnownCliff = F9` (kernel timeout on heavy `native_decide`)** — Codex and Gemini both ranked it as "low-risk witness-table extension" without naming the failure mode.
- Grok was the ONLY LLM that flagged **FT p=3 for q > 1583 as `KnownCliff = F5` (residue-subfamily reduction collapses)** — Codex's Stage-4 outline did not name this until prompted in Round 2.

**Operational rule:** For every problem about to be drafted to a FUSION sketch, **Grok MUST be called specifically with the prompt:**

> *"For this problem, what `KnownCliff` mode (F1 Iff.rfl, F3 infrastructure overgrowth, F4 axiomatize-the-hard, F5 residue collapse, F6 restate-with-sorry, F7 bounded leak, F8 vacuous iff, F9 compute explosion, F10 definition mismatch) is most likely to fire? Cite the slot ID precedent."*

This is Grok's unique role. It is the breakpoint-risk screener; no other model in our toolchain does this consistently. The cost is ~$1 per call and it has caught two failure modes in the closure_candidates sweep that the other two models missed.

**If Grok API is broken** (currently true for `grok-4.3`; only `grok-4.20-0309-reasoning` works per debate.py): pass the prompt to Codex with explicit `KnownCliff` taxonomy attached. Codex's recall drops but the discipline of asking the question rescues some of the value.

---

## 4. The single highest-leverage LLM upgrade

**NOT** integrating GPT-5.2 Pro directly via OpenAI API (per §2).

**INSTEAD:** Adopt **Codex CLI (gpt-5.5) as the de facto Stage-4 author for every Class 6 submission**, paired with **Aristotle's informal mode** (per W8 §"The single most surprising finding"). The pipeline change is:

```diff
- safe_aristotle_submit.py (current: bare conjecture, ≤30 lines, .txt)
+ aristotle_informal.py    (new path for Class 6: 150–400 word informal outline
+                            authored by Codex CLI, submitted via informal API)
```

This is also what F10 recommended (§3 Upgrade #3, §6 caveat on E#672) and what W8 Experiments 2 and 3 are designed to test.

**Sub-leverage upgrade:** add Grok-`KnownCliff` as a MANDATORY pre-Stage-4 screen for every FUSION submission. ~$1 per call; would have caught the Pollock F9 risk before the sketch was drafted, saving an estimated 2 days of engineer attention per quarter.

---

## 5. Rate-limit and cost budgets

| LLM | Rate limit (today) | Cost per call (avg) | Daily cap recommendation |
|---|---|---|---|
| Codex CLI (gpt-5.5) | ~50 RPM via OpenAI subscription | $3–10 (varies by token count, agentic loops $20+) | 30 calls/day = ~$200/day |
| Gemini CLI | 5 RPM on Pro free tier; ~unlimited Flash | $0.50 (Flash); $3–5 (Pro, when available) | 100 calls/day Flash; 10 Pro |
| Gemini Pro (when available) | quota-limited | $5–8 | Reserve for Stage 2 critique only |
| Grok API (`grok-4.20-0309-reasoning`) | tied to XAI_API_KEY tier | $1–3 | 20 calls/day for KnownCliff screens |
| Claude (us) | session-bound | session token budget | Use sparingly; Claude is most expensive for raw math content |

**Sample daily budget for one Class 6 FUSION submission:**
- Stage 1 literature: 1 Codex call = $2
- Stage 2 analogy mining (ensemble x 1 round): $5–8
- Stage 3 technique cards: 1 Codex + 1 Gemini = $4
- Stage 4 informal outline: Codex `codex_proof_loop` 5–10 iterations = $30–60
- Stage 5 post-mortem: 1 Codex + Claude = $2
- KnownCliff screen (Grok): $1
- **Total per Class 6 submission: $44–77 in LLM costs** (plus Aristotle slot, ~$50–100)

**Weekly budget at 5 Class 6 submissions: ~$300–400 LLM + ~$300–500 Aristotle.**

---

## 6. Fallback chains (consolidated)

| Stage | Primary down → Fallback 1 → Fallback 2 |
|---|---|
| 1 Literature | Codex → Gemini CLI `--google-search` → Claude WebFetch |
| 2 Analogy | Codex+Gemini+Grok → Codex+Gemini (drop Grok if broken; lose KnownCliff axis) → Codex alone |
| 3 Technique cards | Codex+Gemini → Codex alone → Claude (mark as `provenance: claude_only`) |
| 4 Informal outline | Codex CLI → Claude (degraded) |
| 5 Post-mortem | Codex+Claude → Claude alone |
| Closure-axis | Codex+Gemini → Codex alone |
| Literature-check | Codex (mandatory web-search) → Gemini CLI → human |
| KnownCliff screen | Grok → Codex with explicit `KnownCliff` taxonomy → skip with WARN logged |

**If Codex is down:** All math-content stages degrade to Gemini Pro (if quota) + Claude. Lose ~3 points of strict-hit recall on Stage 2. Pause submissions until Codex returns.

**If only Claude is up:** Pause submissions. Claude is not the optimal raw math author and we should not pretend otherwise.

---

## 7. The single most important pairing pattern

**Class 6 (cross-domain FUSION):** `Codex CLI (gpt-5.5) writes 150–400 word informal proof outline → Aristotle informal mode formalizes → Grok screens for KnownCliff before submission`.

This is the closest substitute we have to the W4 canonical GPT-5.2 Pro → Aristotle workflow, plus the Grok cliff-screen catches breakpoints the others miss.

For Class 1/2/3/4/8 (CLOSURE / BARE / disproof / long-tail), the LLM stack is lighter: Codex for literature, Codex+Gemini for technique cards, Aristotle direct submission, no informal mode needed. The expensive pairing is reserved for Class 6.

---

## 8. Documentation path

`/Users/patrickkavanagh/math/docs/llm_pairing_strategy.md` (this file).

Related:
- `docs/lane_routing_matrix.md` (S1) — which lane each problem goes to.
- `docs/closure_axis_companion_spec.md` — companion-file format the gate reads.
- `docs/research/llm_math_landscape.md` — benchmark survey backing the GPT-5.5 ≈ GPT-5.2 Pro substitution argument.
- `research_fusion/calibration/` — I10's calibration test infra (re-run after any major LLM upgrade).
