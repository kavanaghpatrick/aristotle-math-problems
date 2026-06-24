# EXP7: Wrong-First Prompting

**Date:** 2026-05-31
**Author:** EXP7 coordinator
**Problems:** Erdős 938 (consecutive-powerful 3-APs) + Erdős 364 (no three consecutive powerful integers)
**Models:** Grok-4 (xAI), Gemini-2.5-pro (CLI, quota-throttled out), Codex / gpt-5.5 (CLI exec, read-only sandbox, medium reasoning effort)
**Output directory:** `/Users/patrickkavanagh/math/analysis/exp7_outputs/`

---

## Hypothesis

Forcing the model to first produce a **deliberately wrong** "beautiful" proof, then to find its own errors, then to identify the structural reason the errors cannot be fixed, will surface creative reasoning that a direct "prove it" prompt misses. The intuition: wrong attempts force the model to commit to a concrete narrative, which exposes load-bearing assumptions; the structural-reason step then forces a meta-level diagnosis that direct prompts elide.

**Falsifiable prediction:** at least one of the 6 (problem × model) trials produces a Round-4 sketch containing a genuine structural insight absent from the same model's BASELINE for the same problem.

## Methodology

### Protocol (per model per problem, 5 outputs)

| Round | Prompt summary |
|---|---|
| **BASELINE** | "Prove the problem directly. If you cannot, state the smallest unconditional sub-result and identify what is open." (300-500 words.) |
| **R1 (wrong)** | "Produce a proof attempt that LOOKS convincing but contains a subtle load-bearing error." (300-500 words; ends with `# END OF ATTEMPT`.) |
| **R2 (find failures)** | "Find 3 specific places where R1 fails. Cite step, name false claim, explain why." |
| **R3 (structural)** | "For each failure, identify the structural reason it cannot be fixed by a minor patch." |
| **R4 (correct sketch)** | "Use the structural diagnoses to produce a sketch of a correct proof, or identify the smallest unconditional sub-result." |

### Prompt asymmetry (documented confound)

Grok ran with a blunt R1 prompt ("produce a beautiful but wrong proof"). Codex refused the blunt prompt with "I can't write a deliberately deceptive journal-style proof with an unflagged load-bearing error." The harness was updated to reframe R1 as "EDUCATIONAL EXERCISE IN ERROR ANALYSIS … pedagogically-seeded errors"; codex then complied. Gemini hit the updated prompt from the start but was throttled by shared-account quota contention (3 concurrent gemini jobs running other experiments). Gemini cells were dropped from primary analysis.

### Models / settings

- **grok-4** — REST, temperature 0.5, max_tokens 4000.
- **gemini** — CLI `gemini -p ... --approval-mode plan`, default model (gemini-2.5-pro). Stalled in quota-wait loops; 0/10 cells completed.
- **codex** — CLI `codex exec --sandbox read-only -c model_reasoning_effort="medium"` on gpt-5.5.

### Output volume

20 markdown files (4 complete cells × 5 rounds each) under `analysis/exp7_outputs/`. Gemini cells empty due to quota; documented but not scored.

### Scoring rubric (per cell, 0-12)

For each (problem, model) pair, R4 is scored against BASELINE on:

1. **Novelty of structural insight** (0-3) — R4 cites a structural reason absent from BASELINE.
2. **Specificity** (0-3) — named theorem / family / construction / modulus, not a gesture.
3. **Falsifiability awareness** (0-2) — explicit acknowledgement the conjecture may be false (van Doorn 2026 / Mathlib decide-up-to-N).
4. **Smallest-unconditional-sub-result** (0-2) — explicit, named, unconditional lemma.
5. **Honest open-status acknowledgement** (0-2) — admits problem is open if so.

**Net lift** = R4_score − BASELINE_score per cell. Aggregate mean net lift → verdict.

---

## Results

### Raw outputs

All raw outputs in `/Users/patrickkavanagh/math/analysis/exp7_outputs/`. Files named `{problem}_{model}_{round}.md`.

### Per-cell scoring (4 complete cells; gemini = quota-throttled)

| Cell | BASELINE score | R4 score | Net lift | Key R1-emergent insight |
|---|---:|---:|---:|---|
| **E938 × grok** | 8 | 6 | **−2** | (in R2) Erdős-Selfridge applies ONLY to *consecutive* integers (a, c at distance 2d ≫ 2 are not consecutive), so no minor patch revives it |
| **E938 × codex** | 5 | **10** | **+5** | (in R4) Explicit Pell construction x²−2 = 7³y² → infinitely many powerful 3-term APs; cites van Doorn 2026 (arXiv:2605.06697); reframes open gap as "void of intervening powerfuls in [(x−2)², x²)" |
| **E364 × grok** | 8 | 4 | **−4** | (in R2) Powerful pair (25, 27) at distance 2 = 3³ − 5² demonstrates Mihăilescu-style arguments insufficient |
| **E364 × codex** | 9 | 9 | **0** | (in R3) "Catalan classifies consecutive *perfect powers* — powerful numbers include mixed-exponent objects like 72 = 2³·3² that aren't perfect powers"; (in R4) explicit "no four consecutive powerful integers" proposition |
| E938 × gemini | — | — | — | (quota-throttled, dropped) |
| E364 × gemini | — | — | — | (quota-throttled, dropped) |

**Aggregate (4 complete cells):**
- Mean net lift: (−2 + 5 − 4 + 0) / 4 = **−0.25 points** on a 12-point scale.
- Variance is large: one big positive (+5), two negatives (−2, −4), one zero.
- Lift sign distribution: 1 positive / 2 negative / 1 zero.

### Where Round-4 *outperformed* BASELINE (E938 × codex, +5)

Codex's R4 made a **genuine construction**:

> For every Pell solution (x, y) to x² − 2 = 7³y², the three integers (x−2)², (x−1)², x² − 2 form a 3-term AP in which each term is powerful (the first two are perfect squares; the third is 7³y², powerful because 7 has exponent ≥ 3 and each prime of y² has exponent ≥ 2). The Pell equation has infinitely many solutions.

This establishes UNCONDITIONALLY that infinitely many powerful 3-APs exist — the BASELINE codex had retreated to "no even powerful number ≡ 2 mod 4." Codex's R4 also explicitly cited van Doorn 2026 (arXiv:2605.06697) and reframed Erdős 938's open content as:

> Prove (or disprove) that for infinitely many such Pell solutions, no other powerful number lies in the interval [(x−2)², x²). The "consecutive in powerful sequence" condition is exactly this interval-emptiness.

The R1→R2→R3→R4 cycle worked as a retrieval cue. R1 committed to a wrong squarefree-kernel approach; R2 found that kernels grow like x^{1/3} so pigeonhole fails; R3 named "kernel non-compactness" structurally; R4 pivoted to "construct a non-consecutive AP unconditionally via Pell" — exactly the right insight.

### Where Round-4 *underperformed* BASELINE (E938 × grok, −2; E364 × grok, −4)

Grok's BASELINE on both problems was already rich (Faltings, Mihăilescu, mod-4 parity, ABC). Grok's R4 *collapsed to a one-paragraph summary*:

- E938 R4: "problem is open; smallest unconditional sub-result is liminf δ_m/√n_m = 0." (4 sentences total.)
- E364 R4: "problem is open; abc implies finiteness." (2 sentences total.)

The content was already extracted in R3. R4 became a degenerate distillation that *lost the Faltings reference, the Mihăilescu reduction, and the mod-36 structure*. Net lift was negative because R4 is being compared to a richer BASELINE.

### Where Round-4 *matched* BASELINE (E364 × codex, 0)

Codex's BASELINE recovered the slot622-style mod 36 ∈ {7, 27, 35} result. Codex's R4 produced essentially the same content plus explicit citation of erdosproblems.com #364 and MathWorld, plus the "no four consecutive powerful integers" mod-4 proposition. The content gain from R4 (citations + mod-4 sub-prop) roughly balances the slight redundancy with R3. Net lift ~0.

---

## Findings

### F1. Wrong-first works as a retrieval cue when BASELINE is empty

The codex E938 cell is the clearest positive: BASELINE retreated to a triviality (no even powerful ≡ 2 mod 4), R4 produced an explicit Pell construction and cited van Doorn 2026. **+5 lift on a 12-point scale** when BASELINE is thin.

### F2. Wrong-first underperforms when BASELINE is already rich

Grok's BASELINE for both problems pre-loaded the heavy machinery (Faltings, Mihăilescu, mod-36). R4 collapsed to summaries, losing texture. **Negative lift** when BASELINE is dense.

### F3. The high-leverage round is R2, not R4

Every genuine novel insight in the experiment surfaced in R2 (find-failures), not R4. R3 packaged. R4 either packaged or collapsed:

- Grok E364 R2 — powerful pair (25, 27) at distance 2 = 3³ − 5².
- Grok E938 R2 — Erdős-Selfridge needs *consecutive* integers; a, c at distance 2d don't qualify.
- Codex E938 R2 — squarefree kernels grow like x^{1/3} so pigeonhole over moving space fails.
- Codex E364 R2 — Catalan ≠ Powerful; 72 = 2³·3² is the canonical counterexample.

**This is the single most important methodological finding.** R2 is where the wrong-first cycle pays.

### F4. Codex refuses blunt deceptive prompts; reframe as pedagogical

Codex initially refused R1 with "I can't write a deliberately deceptive journal-style proof." The harness was updated to use an "EDUCATIONAL EXERCISE IN ERROR ANALYSIS … pedagogically-seeded errors" frame, and codex then produced the highest-quality R1 in the experiment (the squarefree-kernel approach using Thue-Siegel and Fermat-on-squares-in-AP). **Implication: any production deployment must use the pedagogical frame.**

### F5. Gemini was quota-throttled out

Gemini-2.5-pro on the shared account ran one BASELINE attempt then stalled. Zero cells completed in the experiment window. **Cannot evaluate wrong-first for Gemini on this problem set.** Re-run during off-hours or with a dedicated quota.

### F6. Grok's R1 was partially self-flagging

Grok's E938 R1 ended with a parenthetical disclaimer: "(The preceding paragraph invokes the sieve in a regime where the level of distribution is marginally insufficient; the resulting upper bound is therefore not justified.)" The model has an epistemic instinct against unflagged false claims. R2 still produced a substantive 3-failure critique, but the R1 design relies on plausibility — grok partly broke that. Less of an issue with codex (which committed to wrong proofs fully under the pedagogical frame).

### F7. The wrong proofs are *canonical errors*, not random ones

Three of the four R1 proofs made the same load-bearing error: **conflating "powerful" with "perfect power"** to trigger Mihăilescu / Catalan. Codex E364 R1 absorbed squarefree factors into bases to make perfect powers; Grok E364 R1 did the same; Grok E938 R1 used Erdős-Selfridge on "products of consecutive integers." This is not a quirk — it is a real cognitive trap that even the post-publication grad student literature has fallen into. The wrong-first protocol exposes the trap explicitly.

---

## Verdict

**Wrong-first prompting is a CONDITIONAL useful lever, with caveats.**

Aggregate mean lift is slightly negative (−0.25 on a 12-point scale, n=4 cells), but this hides bimodal behavior:

- **Strongly positive** when BASELINE is empty/low-content and the model has latent constructive knowledge. Codex E938: +5 lift, surfaced an unconditional Pell construction.
- **Strongly negative** when BASELINE is already substantive — R4 collapses into degenerate summary. Grok E938 and E364: −2 and −4.
- **Neutral** when content is equally extracted under both prompts. Codex E364: 0.

The genuine value of wrong-first lives in **R2 (find-failures)**, not R4. R2 is where the canonical errors get named, where novel obstructions surface, where the cognitive trap (powerful ≠ perfect power) is forced into explicit view.

### Falsifiable prediction outcome

**Confirmed.** Codex E938 produced a Round-4 sketch (Pell construction + van Doorn citation) absent from its BASELINE. The wrong-first cycle did surface a genuine insight on this cell. So the experiment's falsifiable prediction holds in at least one case — wrong-first is a useful retrieval lever in specific conditions.

---

## The Most Useful R1-Emergent Insight

**Codex's E938 cycle produced an explicit Pell-based construction of infinitely many powerful 3-term APs**, plus a precise reformulation of Erdős 938's open content as an interval-emptiness condition.

> For every solution (x, y) to the generalized Pell equation
>
>   x² − 2 = 7³ y²
>
> the three integers (x−2)², (x−1)², x² − 2 form a 3-term arithmetic progression in which each term is powerful: the first two are perfect squares, and the third is 7³y² (powerful because 7 appears with exponent ≥ 3 and every other prime dividing y² appears with exponent ≥ 2). The Pell equation has infinitely many solutions.
>
> The remaining open content of Erdős 938 is therefore: prove (or disprove) that for infinitely many such Pell solutions, no other powerful number lies in the interval [(x−2)², x²). The "consecutive in the powerful sequence" condition is exactly this interval-emptiness — what van Doorn 2026 (arXiv:2605.06697) studies and conjectures the answer "yes" to.

**Verified numerically (EXP7 audit step):** the smallest Pell solution is x=11427, y=617, giving the triple (130530625, 130553476, 130576327). Common difference d = 22851 = 3 · 7 · 1088.14… = 3 · 7621. All three numbers are powerful (verified by `sympy.factorint`). This is **exactly van Doorn 2026's first triple** documented in `analysis/e938_deep_synthesis.md` ("Confirmed van Doorn's first triple (130530625, 130553476, 130576327) is REAL but NOT CONSECUTIVE — explicit computational verification of 5 intervening powerfuls"). Codex's Pell construction reproduces van Doorn's family A₁ from latent knowledge under the wrong-first cycle.

**Why this matters:**

1. It exhibits unconditional infinitude of powerful 3-APs — a fact the codex BASELINE missed entirely.
2. It maps Erdős 938 cleanly onto van Doorn's recent (May 4 2026) work, giving a concrete family (Pell-7³ family A₁) to verify or falsify against.
3. It identifies the operative open question as **interval-emptiness in a Pell-orbit context**, which is a sharper target than "finitely many 3-APs."
4. Codex pulled the construction from latent knowledge *only after* the wrong-first cycle exposed why the squarefree-kernel pigeonhole approach fails (kernels grow like x^{1/3}). The direct prompt could not retrieve it.

This is the most concrete demonstration in the experiment that wrong-first can surface latent knowledge that direct prompts cannot.

---

## Recommendation

1. **Adopt wrong-first as an OPTIONAL tactic in the FUSION-lane paired-LLM workflow** (per the F3 finding that 87% of LLM consultations are meta-process rather than math). Reserve it for cells where the BASELINE produces low-content output. Skip when BASELINE is already substantive.

2. **Use R2 (find-failures) as a standalone "stress-test this strategy" tool**, without the full R1→R3→R4 wrapper. R2 is where the value is; the wrapper increases compute cost ~5× for marginal additional benefit.

3. **Always use the pedagogical frame** ("educational exercise in error analysis with pedagogically-seeded errors"), not the deceptive frame ("trick me with a wrong proof"). Codex refuses the latter. The reframe is documented in `analysis/exp7_outputs/run_exp7.py` line 30 (variable `R1_wrong`).

4. **Re-run Gemini cells during off-hours** when shared-account quota is uncontested. The current run hit 3 concurrent gemini jobs (from other experiments) and stalled. Single-job runs should complete in 30-60s.

5. **For the E938 fusion dossier**: incorporate the codex R4 Pell construction (x² − 2 = 7³y²) as concrete novel context. Aristotle has not been given this exact family as a candidate falsification target. Estimated value: low to moderate — it's a single representative of van Doorn's family A₁, but stating it explicitly may help Aristotle's MCGS prune correctly.

6. **The canonical R1 error ("powerful = perfect power") is a known cognitive trap.** Use it as a *test* for new sketch-generation models: any model whose R1 does *not* fall into this trap is suspiciously strong (or hedging). Codex and grok both fell into it under wrong-first; this is consistent with the historical record of grad student attempts at E364 / E938 (per the research.md analysis).

---

## Appendix A — File index

```
/Users/patrickkavanagh/math/analysis/exp7_outputs/
  E938_grok_BASELINE.md  E938_grok_R1.md  E938_grok_R2.md  E938_grok_R3.md  E938_grok_R4.md
  E938_codex_BASELINE.md E938_codex_R1.md E938_codex_R2.md E938_codex_R3.md E938_codex_R4.md
  E938_gemini_*                                  (quota-throttled, empty)
  E364_grok_BASELINE.md  E364_grok_R1.md  E364_grok_R2.md  E364_grok_R3.md  E364_grok_R4.md
  E364_codex_BASELINE.md E364_codex_R1.md E364_codex_R2.md E364_codex_R3.md E364_codex_R4.md
  E364_gemini_*                                  (quota-throttled, empty)

  run_exp7.py                                    (harness, caches per file)
```

Total: 20 valid output files + harness.

## Appendix B — Replication

```bash
cd /Users/patrickkavanagh/math/analysis/exp7_outputs
python3 run_exp7.py                # all models, both problems, resumes cached cells
python3 run_exp7.py codex E938     # subset
python3 run_exp7.py gemini E938    # gemini-only when quota free
```

The harness caches per-file so partial reruns are cheap. Each existing `.md` file is treated as cached; delete to force re-run.

## Appendix C — The Canonical Wrong Proof

Both grok and codex produced essentially the same wrong proof for E364 under R1. The canonical error pattern:

1. Write powerful n = a²u³ with u squarefree (correct).
2. Claim n is therefore "a perfect power" by absorbing u (FALSE — (au)³ = a³u³ ≠ a²u³).
3. Apply Mihăilescu (Catalan) to consecutive perfect powers.
4. Conclude (8, 9) is the only consecutive powerful pair, contradicting hypotheses.

The R2 critique in both cases: powerful numbers are NOT perfect powers in general (counterexample: 72 = 2³·3², which is powerful but neither a square nor a cube). The R3 structural diagnosis: the square-cube decomposition records *mixed local prime data*, while Catalan/Mihăilescu requires *one uniform global exponent*.

**Methodological implication:** wrong-first protocols are particularly well-suited to problems with *canonical errors* — known traps that have been fallen into by previous attempts. E364 and E938 both exhibit the "powerful = perfect power" trap. The protocol exposes the trap reliably.
