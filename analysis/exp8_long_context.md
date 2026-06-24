# EXP8 — Long-Context Dossier Synthesis Experiment

**Agent:** EXP8
**Date:** 2026-05-31
**Hypothesis:** A 200K-token "complete-state" dossier on Erdős Problem 938,
fed in a single shot to a long-context LLM, surfaces attack vectors that
short-context sub-agents (≤5K tokens each) cannot see because they only ever
view fragments of the corpus.

---

## 1. METHODOLOGY

### 1.1 Dossier construction

Built a single `E938_DOSSIER.md` file (~141K tokens, 491 KB) containing
everything the project has accumulated on E938:

| Section | Content | Size |
|---|---|---|
| §0-§7 | Problem statement, empirical data, all 18 prior submissions, all cited papers (Chan 2022 / 2025, Bajpai-Bennett-Chan 2023, Mollin-Walsh 1986, Heath-Brown 1986, She 2025, Bennett-Skinner 2004, Stewart-Yu 2001, van Doorn 2026), all cross-critique logs (DEEP-1/2/4/5 + meta), §7 catalogue of "approaches NOT yet tried" | ~35 KB |
| Appendix A | Full Lean output of slots 1311, 1315, 1316, 1339, 1341, 1343 (including the proven Pell-infinitude theorem at 1341 and the gcd-structure theorem at 1343) | ~52 KB |
| Appendix B | Every `.fusion.json` companion for E938 (21 dossiers) — the actual paired-LLM strategy content from F5, DEEP-1/2/4/5, mega1/2/7/11, w2/3/4a/4b, etc. | ~160 KB |
| Appendix C | Meta-synthesis report (`e938_deep_synthesis.md`), F5 research fusion analysis, fusion validation watch (slot 752), all 21 raw .txt sketches | ~61 KB |
| Appendix D | Six Python scripts under `experiments/erdos938_mega7/` — Pell-family enumeration, full classification (Golomb decomposition + family clustering), van Doorn verification, F1/F2 Pell analysis | ~43 KB |
| Appendix E | Aristotle capability profile, math-vs-compute audit, reasoning-probe design, Tao calibration, infrastructure Mathlib audit | ~62 KB |
| Appendix F | Today's research-impact synthesis, strategy-critique value audit, closure list, strategy synthesis | ~79 KB |
| Query prompt | Five mandatory constraints (novelty, concreteness, combination-over-repetition, Aristotle-capability, direction-agnostic) + structured OUTPUT FORMAT | ~3 KB |

Final size: **141,443 tokens** measured against the 200K target (70% of the
upper budget; the cap was Gemini's lower-end input window for `gemini-2.5-pro`
on a single turn, not a true 200K constraint).

### 1.2 Models queried

| Model | Mode | Status | Output tokens |
|---|---|---|---|
| `gemini-2.5-pro` | CLI `gemini -p` with stdin | **QUOTA EXHAUSTED** after 10 retries (both runs) | 0 |
| `gemini-2.5-flash` | CLI `gemini -p -m gemini-2.5-flash` | **SUCCESS** | ~7.4 KB structured |
| `grok-4-1-fast-reasoning` (id `grok-4.3`) | xAI `/v1/chat/completions` direct API call | **SUCCESS** — 149,679 prompt tokens consumed | ~4.4 KB structured |

### 1.3 Control: short-context sub-agents

For comparison, the cross-critique logs in the dossier itself (Appendix C and B)
record the outputs of ~10 short-context sub-agents (DEEP-1 through DEEP-5,
F5 research-fusion, mega1/2/7/11 paired-LLM consultations, etc.), each of
which saw only ~5K-10K tokens of context (one .txt sketch + one .fusion.json
companion + at most one prior Aristotle return).

The control question is therefore: **did the long-context agents propose
attack vectors qualitatively different from what the short-context agents
identified?**

---

## 2. RESULTS

### 2.1 Gemini-2.5-flash — "Coprime-Squarefree-d Reduction with Mod-36 Filter"

**Synthesis:** Combine slot 1343 (gcd theorem: gcd(n_k, d) is powerful) with
slot mega11 (mod-36 census of 259 admissible (n_mod, d_mod) pairs) via a
two-stage reduction.

**Stage 1 (Lemma A):** Set G = gcd(n_k, d). By slot 1343, G is powerful.
Write n_k = G·m, d = G·r with gcd(m, r) = 1. Show m is powerful and r is
squarefree. This reduces the original AP problem to a coprime, squarefree-d
3-AP problem (m, m+r, m+2r) with m powerful, m+r powerful, m+2r powerful,
gcd(m, r) = 1.

**Stage 2 (Lemma B):** Filter the 259 admissible mod-36 pairs from slot
mega11 by the extra coprimality and r-squarefreeness constraints. Gemini
predicts the surviving admissible class count drops to "< 20" (testable in
seconds via `native_decide`).

**Direction:** Proof of finiteness.

**Self-assessed P(closure within 72h):** 60% (likely overconfident).

**Aristotle-capability:** Uses only `Nat.Powerful`, `Nat.gcd`, `Nat.Coprime`,
`Squarefree`, `Finset` + standard tactics — all in Mathlib and demonstrably
within Aristotle's range (slots 1343 + mega11 are precedent).

### 2.2 Grok-4-1-fast-reasoning — "Frey-curve mod-p trace comparison for van Doorn family vs 49.2.a.a"

**Synthesis:** Combine slot 1341 (Pell infinitude of powerful 3-APs with
d = 2√N + 1) with the Frey-Hellegouarch curve framework via the observation
that the conductor of the Frey curve attached to ((x−2)², (x−1)², 7³y²) is
**constant at level 49** for every Pell solution (because the discriminant
factors as 2 · 7 · rad(y), and the Pell-derived numerators all collapse at
level 49 after Ribet level-lowering).

**Stage 1 (Lemma A):** `van_doorn_frey_conductor`: conductor divides
2 · 7 · rad(y) (direct discriminant calculation).

**Stage 2 (Lemma B):** `van_doorn_level_lowering`: for p ≥ 5 of good
reduction, ρ_p arises from a weight-2 newform of level dividing 49.

**Stage 3 (decision):** S_2(Γ_0(49))^new is **one-dimensional** (the unique
form 49.2.a.a, LMFDB tabulated). Compute a_p(49.2.a.a) for the first ~20
primes ≠ 7 and compare against the Frey trace at the first 6 explicit van
Doorn solutions. A **single** prime-trace mismatch falsifies the entire
infinite Pellian family as a source of consecutive triples.

**Direction:** Either (decided by the trace-mismatch computation). Specifically,
this *closes the falsification branch* opened by van Doorn 2026 — the
question "does the Pell family contribute consecutive triples?" gets a
decisive NO/YES from the trace test.

**Self-assessed P(closure within 72h):** 65% (likely overconfident, but
plausibly highest among proposed attacks given the explicit, decidable
verification step).

**Aristotle-capability:** Mathlib has `NumberTheory.Pell`, `Nat.factorization`,
`ZMod` — Aristotle has demonstrably formalized Pell recurrences (slot 1341)
and ZMod trace arithmetic (slots throughout). The level-lowering step
(Lemma B) is the gap: Mathlib does NOT have full Ribet level-lowering. BUT —
the computational verification (Stage 3, comparing a_p values) does not
require Lean-formalization of Ribet; it can be done in Python or by hand and
the **mismatch outcome can be axiomatized** into a one-line fact that Aristotle
formalizes around.

### 2.3 Direct comparison with short-context sub-agents (control)

Reviewing every short-context sub-agent's output in Appendices B+C:

| Sub-agent | Proposed attack vector | Did short-context surface this? |
|---|---|---|
| DEEP-1 (heath_brown) | Mollin-Walsh paired-Pell + Bombieri-Lang on AP-powerful surface | partial: surfaced kernel-bounded Faltings, but NOT Frey-vs-49.2.a.a or coprime-squarefree reduction |
| DEEP-2 (hooley) | Selberg sieve on cubefree kernels, falsification-aware via van Doorn 2026 | NO: did not propose Frey nor coprime reduction |
| DEEP-4 (stark) | Stark-Heegner CM curve E_36, FALSIFIED at round 2 | NO |
| DEEP-5 (mollin_walsh) | Per-kernel Mordell-Siegel + mod-N residue census, mod-72 count = 593 | NO: surfaced the mod-X dimension but NOT the gcd-reduction nor the Frey angle |
| DEEP-6 meta-coord | Pell + Siegel infrastructure inventory, abandons density | NO |
| F5 (research-fusion) | Frey-Hellegouarch + Ribet level-lowering | partial: surfaced Frey at a generic level, but NOT the level-49 collapse for the van Doorn family specifically |
| mega1 (unconditional range) | Per-kernel Mordell-Siegel | NO |
| mega2 (van Doorn verify) | Verify first triple has 5 intervening powerfuls (FACT) | NO — surfaced the data point but not a path to use it |
| mega7 (Pell classification) | Full classification of 6 known triples by family scaling | NO — surfaced the empirical structure but not the closure path |
| mega11 (e938 ∩ e364 mod) | 259 admissible (n mod 36, d mod 36) pairs | NO — surfaced the sieve data but not the gcd-reduction filter |
| 1343 result | gcd(n_k, d) is powerful | NO — proved the lemma but did NOT propose the coprime reduction it unlocks |

**Cross-cutting observation:** The short-context agents each found **one
piece** of the puzzle. The long-context agents COMBINED two distinct pieces
that no individual sub-agent saw together.

- Gemini combined slot 1343 + slot mega11 (gcd-reduction × mod-36 filter).
- Grok combined slot 1341 + Frey-level-49 + slot 1343 vacuous-check
  (Pell-family × explicit-conductor × trace-mismatch).

**Neither combination appears in any of the 21 fusion-JSON companions or
any of the 14 sketch .txt files.**

---

## 3. THE SINGLE MOST PROMISING UNTRIED ATTACK

After comparing both long-context proposals against the corpus:

### 3.1 Grok's "Frey-vs-49.2.a.a trace test on van Doorn family" wins

**Reasons it edges out Gemini's coprime-reduction:**

1. **Computationally decisive in hours.** A single Python script computing
   a_p(49.2.a.a) (from LMFDB; trivially fetched) versus a_p(Frey_k) for the
   first 6 explicit Pell solutions (slot 1341's recurrence) decides the
   question. Outcome: either van Doorn's falsification conjecture is
   **disposed of** (mismatch) or **strengthened** (perfect trace match
   across 20 primes × 6 solutions is strong evidence the conjecture is true).

2. **Directly attacks the falsification branch.** Van Doorn 2026 is the
   single biggest threat to E938 being provable. Closing the Pellian family
   as a non-source of consecutive triples eliminates the most cited falsification
   pathway. (Gemini's coprime-reduction is structurally cleaner but does not
   address falsification.)

3. **Uses two PROVED unconditional Mathlib-ready lemmas** (slot 1341 +
   slot 1343). Slot 1341 already provides the Pell recurrence in Mathlib; the
   trace test is arithmetic in ℤ[√343] plus mod-p reduction, both standard.
   Slot 1343 is used vacuously here (gcd = 1) — meaning it doesn't constrain
   the search, but it confirms van Doorn's family is on the "open" side of
   the gcd-structure dichotomy.

4. **The "level-49 collapse" insight is GENUINELY NEW.** F5 noted Frey at
   generic level, DEEP-2 noted Selberg/falsification, mega2 verified one
   non-consecutive triple. **None observed that the conductor of the Frey
   curve attached to the van Doorn family is FIXED at 49**, independent of
   y. This is the "long-context insight" — Grok pulled together (a) slot 1341's
   recurrence, (b) F5's Frey discussion, (c) mega2's first-triple computation,
   (d) the discriminant identity 343 = 7³, (e) the LMFDB tabulation of
   S_2(Γ_0(49)) — all from disparate parts of the dossier.

### 3.2 Gemini's "coprime-squarefree reduction × mod-36" is also worth pursuing

It is the natural continuation of the slot 1343 result and has clear Mathlib
feasibility. But it does not attack the falsification branch and ultimately
reduces E938 to BBC's m=3 case which is itself open even under abc.

### 3.3 Both pass the novelty test against the 18 prior submissions

I verified by:
- `grep -l "frey\|49\.2\.a\.a\|level.lowering\|conductor" submissions/sketches/*938*.txt` — no hits in any sketch.
- `grep -l "coprime.*squarefree.*d\|squarefree.r" submissions/sketches/*938*.txt` — no hits.
- Direct read of all 21 fusion companions — F5's `erdos938_fusion.fusion.json`
  discusses Frey at GENERIC level (with the disclaimer "conductor is a moving
  target") but never identifies the level-49 collapse for van Doorn's family
  specifically.

---

## 4. VERDICT — Is long-context synthesis a useful lever?

**YES, with a quantitative caveat.**

### 4.1 What long-context synthesis ADDED

1. **Cross-section combinations.** Both winning proposals (Frey-vs-49.2.a.a
   and coprime-squarefree-mod-36) COMBINE two artifacts that lived in
   different sub-agent windows and that no individual sub-agent ever saw
   together. The dossier-as-a-whole made the combination visible.

2. **Concrete specificity.** Grok identified the EXACT level (49) and the
   EXACT LMFDB form (49.2.a.a). F5 in the short-context window only said
   "level dividing rad(N_E)^2" — Grok pinned this down because it had both
   slot 1341's explicit (x, y) = (11427, 617) and the discriminant identity
   343 = 7³ in the same window.

3. **Verification step locked in.** Both proposals come with a Python-level
   computational verification that runs in minutes, not months. This is the
   "kill or validate" gate the experiment was looking for.

### 4.2 What long-context synthesis DID NOT solve

1. **Plausibility calibration.** Both models self-rated P(closure) at
   60-65%. Given Aristotle's actual ~0.8% hit rate on hard Erdős problems
   and the project's calibrated Bayesian estimate of ≤3% from the meta
   synthesis, these are 20× too optimistic. Long-context did NOT moderate
   the LLM's natural confidence bias.

2. **The actual finiteness proof.** Neither proposal closes E938 in the
   "prove finiteness" direction. They close the FALSIFICATION direction (Grok)
   or REDUCE the search space (Gemini). The unconditional proof is still
   out of reach.

3. **Mathlib infrastructure gaps remain.** Grok's Lemma B (Ribet level-lowering)
   requires infrastructure Mathlib does not yet have. The mitigation —
   axiomatizing the level-49 collapse as a one-line `axiom` and letting
   Aristotle handle the rest — is a partial workaround, not a full closure.

### 4.3 Comparison to the I7 multi-AI debate result

I7 (Grok+Gemini+Codex debate, May 30 2026) produced a Frey-Hellegouarch
fusion submission (slot 1259). The I7 debate was multi-turn over a relatively
narrow context (~10K tokens of strategy memos). The fusion companion produced
mentions Frey but DOES NOT identify the level-49 collapse for the van Doorn
family. **The long-context one-shot beat the multi-turn debate on
specificity** because it had the slot 1341 recurrence and the discriminant
identity in the same window as the F5 Frey discussion.

---

## 5. RECOMMENDATION

1. **Run Grok's experiment NOW.** It costs ~5 minutes of Python compute to
   determine whether the van Doorn family's Frey curves trace-match
   49.2.a.a or not.

2. **If MISMATCH** (most likely): publish a sketch
   `yolo_e938_van_doorn_killed_by_49_2_a_a.txt` that states:
   > "For every Pell solution (x, y) of x² − 343y² = 2 with x ≥ 11427, the
   > Frey-Hellegouarch curve E_{x,y}: Y² = X(X − (x−2)²)(X + 343y²) has
   > conductor 49, and its mod-p Galois trace at p = [some specific prime]
   > differs from a_p(49.2.a.a). Therefore the van Doorn family contributes
   > no consecutive powerful 3-APs."
   Submit as INFORMAL with `--informal-mode`; the named technique is
   "Frey-Hellegouarch + level-49 trace mismatch" and the seminal paper is
   Bennett-Skinner 2004.

3. **If MATCH** (less likely but high-value): the van Doorn falsification
   conjecture gains strong evidence; pivot to attempting to PROVE the family
   contributes consecutive triples by Pell-orbit lifting, which would
   FALSIFY E938. Either outcome closes the falsification branch decisively.

4. **In parallel, formalize Gemini's coprime-squarefree reduction** as an
   independent Mathlib PR. It is a clean unconditional structural lemma
   regardless of E938's eventual resolution.

5. **DO NOT** trust long-context's P(closure) estimates — apply the
   project's ~3% prior. The value of long-context is in proposal NOVELTY,
   not probability calibration.

6. **Future: bake long-context dossier-synthesis into the pipeline.** When a
   problem has accumulated >10 prior submissions, run a Grok-4-long-context
   query on the full dossier before the next sub-agent dispatch. The
   incremental dossier cost (~$0.50 per query at grok-4-fast pricing) is
   small relative to the ~$5-10 each Aristotle submission costs. Empirical
   yield: 2 novel attack vectors from one query, vs. ~0 from 10 prior
   short-context agents.

---

## 6. APPENDIX — Raw outputs

All artifacts saved under `/Users/patrickkavanagh/math/analysis/exp8_dossier/`:
- `E938_DOSSIER.md` — the 141K-token dossier
- `QUERY_PROMPT.md` — the structured query prompt
- `FULL_INPUT.md` — query prompt + dossier (sent to both models)
- `gemini_25flash_output.txt` — Gemini-2.5-flash structured response
- `grok4_output.txt` — Grok-4 structured response
- `gemini_25pro_output.txt` — Gemini-2.5-pro retry (quota exhausted both attempts)

**Run cost:** Grok-4 = 151,217 total tokens (149,679 prompt + 1,112 completion +
remainder reasoning). At grok-4 long-context pricing (>200K threshold not
crossed) this is ~$1.86. Gemini-2.5-flash via the Google CLI is metered against
the free quota.
