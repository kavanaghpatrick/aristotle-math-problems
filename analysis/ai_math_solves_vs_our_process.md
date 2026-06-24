# AI Open-Math Solves vs. Our Process — A Decision-Grade, Hype-Free Comparison

**Date:** 2026-06-01
**Author:** Synthesis lead (over 9 research-team findings + live DB audit)
**Scope:** Every documented AI system credited with solving/advancing an OPEN math problem, 2023–2026, classified GENUINE_NEW / FORMALIZATION / RETRIEVAL / HYPE, then compared against this project's actual track record (sqlite3 on `submissions/tracking.db`, verified 2026-06-01).

---

## 0. Verification of the internal numbers (done first, not assumed)

Re-ran the queries the internal-audit finding cites, against the live DB. **Every number matches.**

| Metric | Finding claims | Live DB (2026-06-01) | Match |
|---|---|---|---|
| Total rows | 1252 | 1252 | ✅ |
| compiled_no_advance | 802 | 802 | ✅ |
| compile_failed | 262 | 262 | ✅ |
| compiled_partial | 133 | 133 | ✅ |
| submitted / disproven / compiled_advance | 36 / 17 / 2 | 36 / 17 / 2 | ✅ |
| **`target_resolved=1` rows** | **0** | **0** | ✅ |
| Lane: bare | 1168 (93.3%) | 1168 | ✅ |
| Lane: informal / closure / fusion | 66 / 12 / 2 | 66 / 12 / 2 | ✅ |
| paired_llm='none' | 1190 | 1190 | ✅ |
| mathematical_content_score populated | 8 | 8 | ✅ |
| informal_mode_used | 68 | 68 | ✅ |
| Date span | 2024-12-14 → 2026-05-30 | identical | ✅ |

The two `compiled_advance` rows, inspected directly:
- **id 1254** `slot722_brocard_bounded_n2_50` — lane=bare, mcs=3, **target_resolved=0**, contribution: "brocard…proved for n ∈ [2,500] via a custom computable nth-prime function" (a finite computation).
- **id 1255** `slot720_feit_thompson_p3q71_close` — lane=bare, mcs=5, **target_resolved=0**, contribution: "FT_p3_q71_family proved for ALL primes q ≡ 71 mod 72 with q ≤ 1000" (a bounded family).

Both violate the project's own `compiled_advance` definition (which requires `target_resolved=1`). The honest genuine-resolution count is **0/1252 = 0.0%**.

---

## 1. The verified landscape — full case table

Classification key: **GENUINE_NEW** = result not previously in the literature, machine- or expert-verified; **FORMALIZATION** = Lean/symbolic proof of a known-answer (benchmark/competition) or known-result statement; **RETRIEVAL** = AI surfaced an already-published solution to a problem only nominally "open"; **HYPE** = announced/overclaimed, not verified or walked back.

| Case | System | Difficulty | Classification | Verification | The honest one-liner |
|---|---|---|---|---|---|
| **OpenAI unit-distance disproof (Erdős #90/1946)** | OpenAI internal generalist reasoning model | deep-famous | **GENUINE_NEW** (conf 0.8) | 9-mathematician human-verified note (Alon/Gowers/Bloom/Sawin/Tsimerman/Wood…); NOT Lean | The single most credible AI math result of the period — a *construction/counterexample*, not a structural proof. Bubeck: "executed like an amazing mathematician," did not "invent something fundamentally new." Verified by the same people who debunked OpenAI's 2025 overclaims. No matching upper bound; problem not closed. |
| **FunSearch — cap-set lower bound 2.2180→2.2202** | DeepMind FunSearch (LLM mutation + evaluator + GP loop) | moderate | **GENUINE_NEW** (conf 0.85–0.95) | Exact finite object, machine-checkable; corroborated in peer-reviewed *Discrete Analysis* | "Largest improvement in 20 years." Evolutionary *program search* against a fast exact scorer. Reviewer Davis judged broader excitement "unwarranted." |
| **AlphaEvolve — ~20 of 67 curated bounds improved** (kissing-11D 592→593, Erdős min-overlap, autocorrelation, hexagon packing, 4×4 complex matmul 48) | DeepMind AlphaEvolve (Gemini + evaluators, evolutionary) | moderate | **GENUINE_NEW / MIXED** (conf 0.7–0.9) | Constructions exactly/numerically checkable; deeper claims proven *by Tao by hand* | Authors' own caveat: most improvements "could likely also have been matched by more traditional…methods." Kissing-11D later **matched/beaten by a human** (Ganzhinov) whose method generalizes; AI's "lacks clear geometric structure." 48-mult result is *complex* arithmetic (≈up to 144 real); humans later rederived over ℚ. |
| **Equational Theories Project (22M magma implications, Asterix/Obelix structures)** | Tao crowd + classical ATPs (Vampire) + Lean | moderate | **GENUINE_NEW / MIXED** (conf 0.8–0.95) | Fully Lean-formalized end-to-end | New math came from **classical ATPs + human ingenuity on the hard ~700**, NOT frontier LLMs (Claude/Copilot "did not play a major role"). |
| **Cosmic-strings gravitational radiation (analytic power spectrum)** | Gemini Deep Think + Tree Search + numeric harness | moderate | **GENUINE_NEW** (cross-domain, conf 0.7) | Numerical only; not formal, not yet refereed | Paper's own words: "synergistic human-AI handoff rather than a fully autonomous pipeline." |
| **Erdős #1196 (Erdős–Sárközy–Szemerédi primitive sets, 60-yr)** | GPT-5.4 Pro (human-prompted by Price) | moderate→deep | **GENUINE_NEW (provisional)** (conf 0.5–0.72) | Lean-verified; Tao + Lichtman endorse novelty | Strongest GPT-5.x candidate. BUT post-dates reliable cutoff, **refereeing "underway,"** and the erdosproblems forum itself demanded contamination-controlled, internet-OFF replication. Do NOT treat as settled. |
| **Erdős #728 (factorial-divisibility log-gap)** | GPT-5.2 Pro (math author) + Aristotle (Lean) | easy-tail / moderate | **MIXED** (conf 0.75–0.85) | Lean-verified; Tao vouched | "First Erdős fully resolved autonomously by AI" — with qualifiers: statement was **misformulated**, community reconstructed the intended version (which is *why* no prior literature), human re-prompted, method "similar to Pomerance." Math author = **GPT-5.2 Pro, not Aristotle alone**. |
| **Erdős #650 (matching integers to multiples)** | ChatGPT (strategy) + Aristotle (Lean) + 3 human authors | moderate | **GENUINE_NEW** (conf 0.82) | Lean + 3 named human authors wrote the prose | Paper verbatim: "strategy first proposed by ChatGPT… formally verified in Lean by Aristotle… **final proofs presented here are entirely human-written**." Most human-heavy genuine case. |
| **Erdős #729, #401, #397** | GPT-5.2 Pro + Aristotle | easy-tail / moderate | **MIXED** (conf 0.7–0.88) | Lean-verified | Derivatives of the #728 argument. #401 includes a counterexample to one reading. #397 surfaced a related 2013 Elkies post. |
| **DeepMind AlphaProof Nexus — 9/353 Erdős + 44/492 OEIS + 15-yr alg-geom + optimization bound** | Gemini 3.1 Pro in "Ralph loops" + Lean (4 agent variants) | easy-tail | **MIXED** (conf 0.85) | Lean 4.27 end-to-end, SafeVerify, sandboxed | Mostly GENUINE_NEW on the easy tail. **Striking: simplest agent (Gemini 3.1 Pro + Lean loop) replicated all 9 — specialized search not needed.** Humans formalized statements & caught misformalizations. Some overlap literature. |
| **Gemini Deep Think / Aletheia sweep (Erdős #1051 + 18 CS/physics)** | Gemini Deep Think + NL self-verifier | moderate | **MIXED** (conf 0.78–0.88) | Informal human grading (mostly NOT Lean); non-unanimous | Honesty exemplar: count **shrank 9→4 novel** under literature-disentanglement; 31.5% "technically correct" vs only **6.5% "meaningfully correct"** on intended reading; #1051 graded 4-of-5. DeepMind explicitly claims **no Level 3/4** results. |
| **Erdős #124 (Brown's-criterion variant)** | Aristotle, informal mode, Alexeev | easy-tail | **MIXED / FORMALIZATION** (conf 0.85–0.9) | Lean kernel + human review (Alexeev, Tao) | The best "Aristotle-alone" evidence — yet **RETRIEVAL in substance**: Erdős omitted a hypothesis → collapses to Brown's criterion (1980s). Solved the **weaker variant** (Tao wiki: yellow/partial). Used the **informal NL interface, not bare Lean**. |
| **Aristotle "new proofs of known results" cluster (#43, #264, #966, #1007, #1026, #1043, #1047, #1048, #1095…)** | Aristotle alone, formal statement | easy-tail | **FORMALIZATION / RETRIEVAL** (conf 0.85) | Lean-verified (plby/lean-proofs) | Genuine from-scratch Lean proofs, but **every theorem is already in the literature** (Pommerenke 1961, Goodman 1966, Seidenberg 1959, Tidor-Wang-Yang 2016…). Cleanest evidence of autonomy; zero new theorems. |
| **Erdős #481** | Aristotle alone, Barreto | easy-tail | **RETRIEVAL** (conf 0.85–0.9) | Lean-verified; matched Klarner 1982 *after the fact* | Tao lists it among "solved autonomously, then found already solved years ago." **Our CLAUDE.md miscredits this as a novel solve — it is retrieval.** |
| **Aristotle ~95+ "pure formalizations" (Tao wiki §2b)** | Aristotle, often paired | easy-tail | **FORMALIZATION** (conf 0.9) | Lean-verified | Column header literally "Proof to formalize." Formalizations of known proofs (Ahlswede-Khachatrian 1995, de Bruijn 1951…). |
| **AlphaProof + AlphaGeometry 2 — IMO 2024 (28/42 silver)** | AlphaProof (RL+Lean) + AG2 | benchmark | **FORMALIZATION** (conf 0.9–0.95) | Lean kernel + Gowers/Myers grading | Known-answer competition problems. Humans **manually formalized every statement**. Both *combinatorics* problems FAILED. Not open math. |
| **AlphaGeometry 1 & 2 — Olympiad geometry** | Neuro-symbolic (Gemini + DDAR) | benchmark | **FORMALIZATION** (conf 0.9) | Symbolic deduction engine | Competition benchmark; geometry is "chess-like" (bounded branching, synthetic data). |
| **OpenAI / DeepMind IMO 2025 gold (5/6)** | OpenAI experimental LLM; Aristotle (Lean) | benchmark | **FORMALIZATION** (conf 0.9–0.92) | OpenAI: **self-graded** (3 paid ex-medalists, no official mark scheme) — CONTESTED; Aristotle: Lean-verified | "Graded by people we paid" ≈ "compiled clean." DeepMind got official IMO certification; Aristotle's was Lean-verified ("nobody has to look at it"). 2025 was an unusually easy set. |
| **AlphaTensor — 4×4 mod-2 matmul (47 mults)** | AlphaZero-style RL | moderate | **MIXED** (conf 0.8) | Exactly verifiable | **Reproduced by humans (Kauers-Moosbauer) within a week** once told it existed; V. Williams "a little overhyped"; DeepMind later "conceded a dead end." Characteristic-2 only. |
| **DeepSeek-Prover-V2 / DeepSeekMath-V2 / Goedel-Prover / Kimina / Numina / Leanstral / BFS-Prover** | Open-source Lean provers (class) | benchmark | **FORMALIZATION** (conf 0.9–0.95) | Lean compilers | **ZERO open problems advanced.** April-2026 survey: "autonomous, creative theorem discovery remains UNPROVEN" for these. Real value = Mathlib expansion, benchmark hygiene. |
| **GPT-5 "solved ~10 Erdős problems" (Erdősgate, Oct 2025)** | GPT-5 as literature-search tool | easy-tail | **RETRIEVAL → HYPE** (conf 0.97) | Refuted by Bloom in ~24h; tweets deleted | The **archetype**. "Open" only meant uncatalogued. Hassabis: "embarrassing." Recht: "Lore Laundering Machines." |
| **Aristotle methodology paper (arXiv:2510.01346)** | Harmonic | benchmark | (FORMALIZATION) (conf 0.95) | IMO 2025 Lean-verified | **PRIMARY-SOURCE CORRECTION:** 0 mentions of "Erdős"/"ProofBench"/"open problem"/"novel result." Makes ONLY the IMO 2025 claim. **"ProofBench #1 at 71%" and "Polya-Szegő 100/100" in our CLAUDE.md are NOT in the paper — treat as HYPE_UNVERIFIED marketing.** |
| **Riemann / Goldbach / twin-prime / Erdős #3** | All systems | deep-famous | **(none) HYPE if claimed** (conf 0.95) | N/A | **Zero genuine advance, ever.** Consensus: AI combines existing knowledge, cannot create new concepts. |
| **Igor Rivin Polya-Szegő audit of Aristotle** | Audit, not a solve | benchmark | (MIXED, evidence) (conf 0.9) | External semantic check | **97.6% compile, only 67.3% semantically correct.** ~1/3 prove the *wrong/weaker* theorem fluently — "worse than sorry." Harmonic's own paper concedes this (built a "faithfulness judge"). |
| **THIS PROJECT (1252 submissions)** | LLM sketch → Aristotle (93% bare-MCGS) | mixed (often deep-famous) | **FORMALIZATION / no-advance** (conf 0.9) | Self-audit | 0/1252 `target_resolved`; 2 mislabeled bounded-computation "advances"; fusion layer 0 advances; this session's flagship E938/Mordell result was an oversold relabel of folklore (Golomb 1970 / Chan 2022) refuted by a published counterexample. |

### Count of truly-new open-problem results by AI (verified, 2023–2026)

- **Deep-famous, GENUINE_NEW:** essentially **ONE** — the OpenAI unit-distance disproof (May 2026), and even it is a *construction* (no upper bound, problem not closed) with heavy human verification. Erdős #1196 is a *candidate* still in refereeing.
- **Moderate, GENUINE_NEW (all construction/bound/finite-casework):** ~4 distinct lines — FunSearch cap-set, AlphaEvolve's ~20 improved bounds, the Equational Theories casework, the cosmic-strings analytic solution. Every one is *score-optimizable construction* or *exhaustive verification*, not a structural theorem, and the deepest pieces were **human-completed** (Tao wrote the Nikodym/Kakeya proofs).
- **Easy-tail, MIXED/GENUINE_NEW:** a few dozen Erdős results (Aristotle-Nexus 9, #728/#729/#650/#1051…), but these cluster on obscure problems, frequently overlap literature, and *every* genuine one used a **strong informal reasoner (GPT-5.x / Gemini) to author the math, with Lean/Aristotle only as downstream verifier.**
- **Net:** The number of confirmed genuinely-new open-problem results authored **by a formalizer running bare statements** (our default mode) is **zero**.

---

## 2. Winning recipes (the pipelines actually behind genuine solves)

**Recipe A — Score-optimizable construction + fast exact evaluator + evolutionary loop.**
Problem must reduce to "find a configuration/algorithm beating a checkable numeric bound." LLM/RL proposes *code*; a deterministic evaluator scores; selection iterates over thousands-to-millions of candidates.
*Evidence:* FunSearch (cap-set, Nature + Discrete Analysis), AlphaEvolve (~20/67 bounds, kissing-11D, matmul). **The only paradigm with a deep-famous-adjacent GENUINE_NEW that self-verifies (no faithfulness gap).** Human role: pick the problem, write the evaluator.

**Recipe B — Strong external informal reasoner authors the math; formal prover verifies; named human curates & verifies.**
A frontier *generalist* model (GPT-5.x / Gemini Deep Think) produces the natural-language argument; Aristotle/Lean formalizes and self-repairs; a named human selects the problem, disambiguates the statement, re-prompts, and vouches.
*Evidence:* Erdős #728, #729, #650, #1051, #1196, AlphaProof-Nexus. This is exactly the project's **FUSION / INFORMAL lane**. **Every credible AI-Erdős advance used this; none used bare-formalizer-only.**

**Recipe C — Exhaustive finite casework + classical ATPs + Lean.**
For problems decomposable into millions of decidable sub-cases, classical theorem provers (Vampire) beat LLMs; humans handle the hard residual.
*Evidence:* Equational Theories Project (22M implications, Asterix/Obelix).

**Recipe D — Human-formalize-statement → AI-prove → machine-check → human-grade (benchmark template).**
*Evidence:* AlphaProof IMO 2024, Aristotle IMO 2025. Gold-standard verification but **zero open-problem content** — included only to show the verification bar.

**What is common to ALL genuine cases:** (1) a human hand-picks a *specific* problem; (2) the *creative/strategic step* comes from a strong reasoner (human, frontier LLM, or evolutionary search over a scorer) — **never from a bare statement handed to a formalizer**; (3) the target is *construction/bound/finite-verification* or *easy-tail obscure*, never deep-structural; (4) a **named human verifies faithfulness and clears the literature** before the result counts.

**The verification bar a claim must clear (distilled across all cases):**
1. **Machine-checked** (Lean, sorry/axiom-audited) OR self-verifying computational artifact.
2. **Faithful** — solved statement provably matches the *intended* conjecture, checked by an *independent* verifier/expert (not the prover). [Rivin: 67% semantic; E124/E850 wrong-theorem.]
3. **Novel** — survives explicit literature-disentanglement. [The step that shrank Gemini 9→4 and demolished GPT-5's 10.]
4. **Honestly attributed** about autonomy (AI-proved vs human-picked/strategized/prompted/interpreted).
5. **Survives external scrutiny** before the count is final.

---

## 3. Our process & track record (DB-grounded)

**What we are (one sentence):** a high-volume, single-vendor, bare-conjecture **submission-and-audit shop** — we forward open gaps to Harmonic's Aristotle and grade what returns; we do not generate mathematics.

**Pipeline:** 4 lanes (BARE default → MCGS formalizer only; CLOSURE; FUSION = paired-LLM dossier; INFORMAL = the reasoner subsystem). Gate `check_gap_targeting()` enforces ≤30-line bare sketches, blocks strategy keywords/.lean/em-tautologies. Audit layer + `audit_proven.py` catch over-claiming.

**Track record (live DB, 2026-06-01):**
- 1252 submissions over ~18 months. **`target_resolved=1`: 0 rows. Genuine resolution rate = 0.0%** (not the self-stated 0.8%; the DB doesn't support even that).
- 802 (64%) compiled_no_advance, 262 (21%) compile_failed, 133 (11%) compiled_partial.
- 2 `compiled_advance` — **both violate our own definition** (target_resolved=0); both are bounded brute-force computations (Brocard n≤500; FT for 7 small primes). Lenient "advance" rate = 2/1252 = 0.16%.
- **93.3% of volume is BARE** — the lane the doctrine says fails >99% on structural problems. The reasoner-engaging lanes (informal 66 + fusion 2 + closure 12) total ~6.7%, almost all created in the final 48 hours. INFORMAL: 0 advances. FUSION: 0 advances.
- **Paired-LLM layer:** 1190 rows have no pair; the ~60 grok/gemini/codex/gpt5.5 "fusion"/"mega-team" rows produced **0 advances, 0 resolutions**, and almost all have NULL mcs (no math was even scored). [F3's "87% of LLM consultations were meta-process" made concrete.]
- `mathematical_content_score` populated on 8/1252 rows (0.6%) — the audit-quality column is essentially empty; `cost_usd` populated on 0 rows.
- 17 disproven are predominantly own-lemma negations / misclassifications, not counterexamples to famous conjectures.
- This session: E938/Mordell (18 submissions, 0 advances) — headline "reduce E938 to Mordell" rated OVERSOLD across 9 verdicts (folklore: Golomb 1970, Walker 1976, Chan 2022; converse refuted by a published counterexample; van Doorn 2026 conjectures E938 *false*). Verdict: DO_NOT_SUBMIT.

---

## 4. Gap analysis — where we diverge from what works (unflinching)

1. **Wrong instrument for genuine novelty.** Every GENUINE_NEW open-problem result is either (A) construction-search over a fast exact scorer or (B) a strong informal reasoner authoring the math with a prover verifying. We run **neither** at scale: 93% of our volume is bare-statement → MCGS formalizer, the one mode with **zero documented genuine open-problem solves anywhere in the public record**. Our own audits already say "the pipeline change is the rate-determining step," and the DB (0/1252) confirms it.

2. **Volume-spray vs. focused depth.** 1252 single-shot submissions, 87 on one day. The genuine wins are the *opposite*: one hand-picked problem, a frontier model writes the argument, a prover formalizes, a named human verifies. Depth + a strong upstream reasoner + named verification beats breadth. Our "HAVE FAITH IN ARISTOTLE, submit aggressively, fear nothing" posture is in direct tension with Tao's "scattered successes among a big sea of unreported failures" — and is not how any 2026 solve happened.

3. **The doctrine inverts the evidence.** Our BARE "zero guidance, let the formalizer find the path" doctrine corresponds to **no documented genuine solve**. Even E124 (the closest "Aristotle-alone" case) used the *informal NL interface*, solved the *easier mis-stated variant*, and is RETRIEVAL in substance. The productive lever (informal reasoner / paired strategy) was historically unused (68 informal rows, all last-48-hours) and the fusion layer has 0 advances. We switched on the right lane too late and too thinly.

4. **Problem-selection blind spot = the RETRIEVAL trap.** Erdősgate is our exact risk externalized: "open" means *uncatalogued*, not unsolved. Our gate checks teorth wiki + erdosproblems.com + arXiv-2024+ + local DB but **no MathSciNet/zbMATH** — a ~40-year pre-2024 blind spot that already swallowed FT-p3 (Le 2012), weird-ω6 (Amato 2019), Lehmer-ω7 (Cohen-Hagis 1980). F2 found **0/220 sketches had literature attached**. We are structurally set up to "solve" things already in the literature and call them new.

5. **Target mismatch.** Our flagship targets (E938, Feit-Thompson, Brocard, Lehmer, Casas-Alvero, Tuza) are deep-structural conjectures — the regime where *every* system scores ~0% and where AI "cannot create new concepts." We are not targeting the construction/bound/finite-verification problems where genuine AI wins actually occur.

6. **Faithfulness gap unguarded.** Rivin's 67% (and Harmonic's own faithfulness judge) prove "compiled clean" ≠ "right theorem." Our gate enforces *sketch hygiene* but has no *independent statement-faithfulness review* — exactly how E124/E850 wrong-theorem/em-tautology failures slip through. The audit layer catching our over-claims is the only part of the pipeline reliably working.

7. **Self-honesty drift in our own facts.** CLAUDE.md credits "E481 (Barreto, Aristotle alone)" and "E124 (informal mode)" as *documented novel solves*. Both need correction: **E481 is RETRIEVAL** (Klarner 1982); **E124 is a partial solve of a weaker statement-flaw variant**. And the "ProofBench 71% / Polya-Szegő 100/100" benchmarks are unsourced marketing, not in the Aristotle paper.

---

## 5. Prioritized recommendations

| # | Recommendation | Rationale (evidence) | Effort | Expected impact |
|---|---|---|---|---|
| **1** | **Stop bare-lane submission on deep-structural conjectures. Make FUSION/INFORMAL the default; gate BARE behind "construction/finite-verification only."** | 0/1252 bare resolutions; bare = the one mode with zero documented genuine solves; every credible advance used Recipe A or B. | Low (config/gate change) | **Highest.** Removes the rate-determining bottleneck. Stops spending on a mode that has never worked. |
| **2** | **Add a hard literature-disentanglement gate: MathSciNet/zbMATH + teorth-AI-wiki + GPT/Gemini deep-research, pre-submission, mandatory.** | Erdősgate; our 40-yr pre-2024 blind spot (Le 2012 etc.); F2's 0/220; the step that shrank Gemini 9→4. | Medium | **High.** Converts our dominant failure (RETRIEVAL-as-solve) into a pre-filter. Cheapest way to avoid the next E938. |
| **3** | **Build/adopt an evolutionary construction harness (OpenEvolve/AlphaEvolve-style) and re-aim targets at score-optimizable construction/bound/finite-verification problems (cap-set/packing/Erdős-extremal class).** | Recipe A is the ONLY paradigm with deep-adjacent GENUINE_NEW that self-verifies; our MCGS pipeline is structurally mismatched to where wins occur. | High | **High (for genuine novelty).** This is the proven instrument for new constructions; bare Lean is the wrong tool. |
| **4** | **Adopt Recipe B as the named workflow: frontier reasoner authors NL argument → Aristotle formalizes → independent human/agent faithfulness review → literature clear → only then audit as advance.** | Every credible AI-Erdős solve (#728/#650/#1196/#1051) did exactly this; our fusion layer has 0 advances because strategy never reached the math. | Medium | **High.** Aligns us with the one pipeline that demonstrably produces easy-tail novelty. |
| **5** | **Add an independent statement-faithfulness check to the audit gate (does the compiled theorem match the intended conjecture? reject weaker/em-tautology/hypothesis-stripped variants).** | Rivin 67%; Harmonic's own faithfulness judge; E124/E850. "Compiled clean" ≠ "right theorem." | Medium | **Medium-High.** Closes the orthogonal-verification gap; prevents the next "advance" that proves the wrong thing. |
| **6** | **Adopt DeepMind's Level 0–4 ladder and Tao's wiki taxonomy (standalone / alongside-lit / building-on-lit / human-collab; green/yellow/red) as the reporting schema; pre-commit to reporting failures and expecting 24–48h downgrades.** | Gemini paper's shrinking-count discipline is the best-practice exemplar; our enum needs an explicit "already-in-literature" axis. | Low | **Medium.** Institutionalizes honesty; makes "advance" claims survivable under scrutiny. |
| **7** | **Correct the internal record now: down-grade E481 (RETRIEVAL/Klarner-1982) and E124 (partial/weaker-variant) in CLAUDE.md/MEMORY; flag "ProofBench 71% / Polya-Szegő 100/100" as unsourced; relabel the 2 compiled_advance rows as bounded-computation (not advances).** | Primary-source corrections; the 2 rows violate our own enum. | Low | **Medium.** Restores calibration; the audit layer is our most valuable asset — keep it accurate. |
| **8** | **Concentrate on ≤5 hand-screened easy-tail problems with full Recipe-B treatment instead of high-volume sprays; populate cost_usd and mcs so productivity is measurable.** | depth-over-breadth feedback; 0.8% hit rate demands concentration; 8/1252 mcs and 0 cost rows mean we can't even measure ourselves. | Medium | **Medium.** Matches the depth pattern of every real win; makes ROI legible. |

---

## 6. Honest bottom line

Across every verified case from 2023–2026, the number of genuinely-new open-problem results authored by an AI **formalizer running bare conjecture statements — our default mode — is exactly zero**; the lone deep-famous GENUINE_NEW result (OpenAI's unit-distance disproof) and the handful of moderate ones (FunSearch, AlphaEvolve) were all *constructions over a checkable scorer* or *strong-reasoner-authored arguments with a prover as downstream verifier*, and the deepest pieces were finished by human mathematicians. Our own database confirms the mismatch without ambiguity: 1252 submissions, `target_resolved=1` on **0** of them, the two recorded "advances" are bounded brute-force computations that violate our own criterion, and the multi-AI fusion layer that was supposed to be the lever has produced 0 advances. We are not a discovery shop; we are a submission-and-audit shop whose audit gate is the only component doing reliable work — chiefly by catching our own over-claims, most recently the oversold E938/Mordell "reduction" that is folklore refuted by a published counterexample. The realistic path to ever producing genuine new mathematics is to abandon high-volume bare-formalizer spraying on deep conjectures and adopt what actually works: hand-screened easy-tail or construction-class problems, a strong informal reasoner (or an evolutionary search over an exact evaluator) authoring the math, a prover for verification, a mandatory literature/faithfulness clearance, and named human review before anything is called an advance. A skeptic should read this as: the instrument is mismatched to the goal, the honest hit rate is 0%, and the only credible upgrades are the ones the evidence — not optimism — points to.
