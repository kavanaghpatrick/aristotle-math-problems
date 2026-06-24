# Web Research: AlphaProof, AlphaGeometry, DeepSeek-Prover and Peers — Novel Math vs. Benchmark

Research date: 2026-05-30. Agent: W3.

## Executive summary

The question: have peer LLM+Lean systems demonstrated **genuine novel math discovery** (not just benchmark wins or competition solving)? Answer is now **YES, but narrowly and recently** — the bar shifted between October 2025 (Weil/Bloom debacle) and May 2026 (OpenAI unit-distance disproof verified by 9 mathematicians including Gowers, Bloom, Alon). The single highest-quality novel-math result by an AI system to date is the **disproof of Erdős's planar unit-distance conjecture (1946)** by an internal OpenAI reasoning model, announced May 20, 2026, with companion proof by Lijie Chen and human-verified remarks signed by Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, and Wood.

For the LLM+Lean stack specifically (Aristotle, DeepSeek-Prover, Goedel-Prover, AlphaProof) the genuine novel-math story is much weaker: **Erdős #728 (Jan 2026)** — proved by GPT-5.2 Pro reasoning + Aristotle formalization — is the strongest legitimate claim, with Tao acknowledging it but noting techniques were "similar to" prior Erdős/Pomerance work. Erdős #124 (Nov 2025) turned out to be the *weaker variant* of the problem.

---

## System-by-system classification

### AlphaProof (Google DeepMind)

- **Highest result**: IMO 2024 silver medal (P1, P2, P6 — P6 the hardest, solved by only 5 of 609 humans). Published in Nature Nov 12 2025.
- **Method**: AlphaZero-style RL on Lean, auto-formalized ~80M training statements, test-time RL with variant generation.
- **Classification**: **MATH-COMPETITION SOLVING.** AlphaProof has *not* independently produced a novel research result. Its post-IMO role in the AlphaEvolve/Deep Think Kakeya pipeline is **FORMALIZATION** — it took a human-readable proof from Deep Think and converted it to Lean.
- **Caveat**: Problems were hand-translated into Lean by experts; 2–3 days of compute per problem.

Sources:
- https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/
- https://www.nature.com/articles/s41586-025-09833-y
- https://terrytao.wordpress.com/2025/11/05/mathematical-exploration-and-discovery-at-scale/

### AlphaGeometry / AlphaGeometry 2

- **Highest result**: 88% coverage of IMO geometry 2000–2024; solved IMO 2024 P4; gold-medalist average performance.
- **Method**: Gemini LLM + symbolic deduction engine; trained on synthetic geometry problems.
- **Classification**: **MATH-COMPETITION SOLVING.** Zero documented novel geometry research results. Geometry as a field has not seen an AlphaGeometry-discovered open conjecture resolution.

Sources:
- https://arxiv.org/abs/2502.03544
- https://deepmind.google/blog/alphageometry-an-olympiad-level-ai-system-for-geometry/

### DeepSeek-Prover (V1, V1.5, V2)

- **Highest result**: 88.9% on MiniF2F-test; 49/658 on PutnamBench; 6/15 on AIME 2024–25 (ProverBench).
- **DeepSeek Math V2 successor**: gold-medal-level on IMO 2025; Seed-Prover solved 5/6 IMO 2025 problems.
- **Classification**: **BENCHMARK SOLVING + MATH-COMPETITION SOLVING.** Zero documented novel research results. Authors themselves frame it as future aspirational: "could assist mathematicians in solving difficult theorems."

Sources:
- https://arxiv.org/abs/2504.21801
- https://arxiv.org/abs/2511.22570

### Goedel-Prover V1/V2 (Princeton)

- **Highest result**: 32B model outperforming DeepSeek-Prover-V2 671B on MiniF2F (1/20th parameters). Best open-source ATP.
- **Classification**: **BENCHMARK SOLVING.** No novel-math claims at all. Pure infrastructure paper.

Sources:
- https://arxiv.org/abs/2502.07640
- https://arxiv.org/abs/2508.03613

### Lean Copilot / LeanDojo (Caltech / LeanProver community)

- **Highest result**: 74.2% proof-step automation on Mathematics-in-Lean textbook (vs 40% AESOP).
- **Classification**: **FORMALIZATION assistant.** Explicit framing in the paper: "current LLMs fall short [on novel theorems]... AI should act as a copilot." No claim of novel math.

Sources:
- https://arxiv.org/abs/2404.12534
- https://leandojo.org/

### Aristotle (Harmonic) — the project's own peer

- **IMO 2025**: gold-medal equivalent.
- **Erdős #124 (Nov 2025)**: Solved autonomously in 6 hours in Lean. **CAVEAT (Tao):** Erdős omitted a key hypothesis; the problem as stated is a consequence of Brown's criterion (a known result). Aristotle solved the *weaker variant*. Bloom confirmed: comparable difficulty to competition math.
- **Erdős #728 (Jan 4–6 2026)**: GPT-5.2 Pro reasoning + Aristotle formalization. **First Erdős problem "regarded as fully resolved autonomously by AI" with no prior literature found.** Writeup by Sothanaphan; arxiv:2601.07421. Tao acknowledged. **CAVEAT:** the strategy is "similar to results regarding divisors of binom(2n,n) studied earlier by Erdős and by Pomerance." Also resolved #729 and #401 by argument modifications.
- **Classification**: **NOVEL MATH (modest)** — at the level of "lowest hanging fruit" per Tao. Real but not deep.

Sources:
- https://arxiv.org/abs/2601.07421
- https://www.erdosproblems.com/forum/thread/124
- https://magazine.mindplex.ai/post/harmonics-ai-aristotle-claims-solution-to-historic-math-puzzle

### OpenAI reasoning models (GPT-5, GPT-5.2 Pro, GPT-5.4 Pro)

#### THE DEFINITIVE COUNTEREXAMPLE: Kevin Weil tweet, Oct 2025

Then-VP Kevin Weil tweeted that GPT-5 had "solved 10 previously unsolved Erdős problems and made progress on 11 others." Thomas Bloom (erdosproblems.com maintainer): **"a dramatic misrepresentation."** GPT-5 had merely re-surfaced existing literature for problems Bloom had personally marked open. LeCun and Hassabis publicly mocked OpenAI. Weil deleted the post and left OpenAI by April 2026.

This is the canonical AI-math hallucination incident. It established the verification bar.

Sources:
- https://techcrunch.com/2025/10/19/openais-embarrassing-math/
- https://futurism.com/artificial-intelligence/openai-researcher-deletes-tweet

#### THE REDEMPTION: Erdős unit-distance disproof, May 20 2026

Internal OpenAI reasoning model disproved Erdős's 1946 planar unit-distance conjecture. The square-grid arrangement was *not* optimal: an infinite family of constructions yields n^(1+δ) with δ = 0.014, later improved by Sawin to 0.014 then n^1.0318. Model's 100+ page chain-of-thought tried to *disprove* (not prove) — the direction most humans hadn't taken — and connected the geometry problem to **algebraic number theory** (Ellenberg-Venkatesh, Golod-Shafarevich, Hajir-Maire-Ramakrishna ideas).

**Verification**: 19-page companion paper (arxiv:2605.20695, "Remarks on the disproof of the unit distance conjecture") signed by 9 mathematicians: **Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, Matchett Wood**. The same Bloom who debunked Weil now endorses. Lijie Chen authored the primary counterexample paper with model computational support.

Gil Kalai compared it to the 1976 four-color theorem computer-assisted proof as a scientific landmark.

OpenAI called it "the first time AI has autonomously solved a prominent open problem central to a field of mathematics."

Sources:
- https://openai.com/index/model-disproves-discrete-geometry-conjecture/
- https://arxiv.org/abs/2605.20695
- https://gilkalai.wordpress.com/2026/05/21/amazing-erdos-unit-distance-problem-was-disproved-it-was-achieved-by-ai/
- https://techcrunch.com/2026/05/20/openai-claims-it-solved-an-80-year-old-math-problem-for-real-this-time/

#### Other recent OpenAI/Tao-verified Erdős resolutions (Jan 2026)

- **Erdős #397, #728, #729**: GPT-5.2 Pro → Aristotle formalization → Tao verification. "Lowest hanging fruit" per Tao but legitimate.
- **Erdős #1196**: GPT-5.4 Pro found solution in ~80 min. Tao noted the AI used a Markov-chain technique "human mathematicians had overlooked despite years of work" — a "previously undescribed connection between the anatomy of integers and Markov process theory."

Sources:
- https://medium.com/@cognidownunder/three-erd%C5%91s-problems-fell-in-seven-days-and-terence-tao-verified-every-proof-himself-1a1ff4399bc6
- https://the-decoder.com/openais-gpt-5-4-pro-reportedly-solves-a-longstanding-open-erdos-math-problem-in-under-two-hours/

---

## Tao's blog: primary-source position

Tao's blog "What's New" posts on AI, 2024–2026:

1. **April 2024** — AI Mathematical Olympiad announcement. Leading model: 4/50 problems.
2. **April 2024** — erdosproblems.com promotion.
3. **September 2024** — "A pilot project in universal algebra" — Equational Theories Project. Explicit warning: AI "can 'hallucinate' plausible-looking, but nonsensical arguments."
4. **December 2024** — AI for Math fund ($9.2M Renaissance Philanthropy + XTX).
5. **November 5 2025** — "Mathematical exploration and discovery at scale" — 67-problem AlphaEvolve study.
6. **November 12 2025** — "New Nikodym set constructions over finite fields" — direct collaboration writeup.

### Tao's exact position (synthesized from blog posts)

- AlphaEvolve "did not locate any stronger counterexamples" for the open conjectures he tested — only "modest new observations."
- For the Nikodym set result he co-discovered with AlphaEvolve + DeepThink + AlphaProof: **Tao himself wrote the rigorous proof**; the AI tools' arguments were "non-rigorous" and "none of the AI tools could overcome a key obstacle"; Tao resolved it by "adding back a small random portion of the removed quadratic surfaces."
- Strong warning: **"I would caution against using AI tools without the ability to independently verify their output. Relying on these tools to compensate for their own mistakes is quite risky."**
- Timeline shift: target date moved from ~2029 to **2026 for "superhuman AI mathematician,"** with caveat "while a stretch, even 2025 is possible." (Quote attributed via Silicon Reckoner; not on Tao's blog directly.)
- Three-stage proof process (Mathstodon): generate → verify → **digest.** "AI is getting very good at the first two aspects, but the third (arguably most important) remains a question."

Sources:
- https://terrytao.wordpress.com/tag/artificial-intelligence/
- https://terrytao.wordpress.com/2025/11/05/mathematical-exploration-and-discovery-at-scale/
- https://terrytao.wordpress.com/2025/11/12/new-nikodym-set-constructions-over-finite-fields/
- https://siliconreckoner.substack.com/p/terence-tao-on-machine-assisted-proofs

---

## Counter-evidence: First Proof challenge (Feb 2026)

11 mathematicians (Abouzaid, Blumberg, Hairer (Fields Medal), Kileel, Kolda, Nelson, Spielman, Srivastava, Ward, Weinberger, Williams) contributed 10 research-lemma problems. **Result: only 2 of 10 problems solved correctly by any publicly available LLM**, and even those were partially contaminated (Hairer's website had a proof sketch archived to Wayback Machine).

Abouzaid: AI proofs have "the flavor of 19th-century mathematics, but we're trying to build the mathematics of the 21st century."

Daniel Litt (predicted "maybe 2–3 correct"): on Hodge conjecture arXiv contamination, June 15–Feb 2026, of 8 papers with "Hodge conjecture" in title/abstract, **6 (75%) are LLM-generated nonsense with hallucinated references.**

Sources:
- https://www.scientificamerican.com/article/first-proof-is-ais-toughest-math-test-yet-the-results-are-mixed/
- https://arxiv.org/abs/2602.05192
- https://x.com/littmath/status/1970841807371305277

---

## Final classification table

| System | Best Result | Classification |
|---|---|---|
| AlphaProof | IMO 2024 P6 silver | MATH-COMPETITION |
| AlphaGeometry 2 | 88% IMO geometry coverage | MATH-COMPETITION |
| DeepSeek-Prover V2 | 88.9% MiniF2F, 49/658 Putnam | BENCHMARK + COMPETITION |
| DeepSeek Math V2 / Seed-Prover | 5/6 IMO 2025 | COMPETITION |
| Goedel-Prover V2 | 32B beats DeepSeek 671B on MiniF2F | BENCHMARK |
| Lean Copilot | 74.2% proof-step automation | FORMALIZATION assist |
| LeanDojo | Premise retrieval infrastructure | FORMALIZATION assist |
| AlphaEvolve + Deep Think + AlphaProof | Nikodym set improved construction (Tao co-author) | **NOVEL MATH (modest, human-mediated)** |
| Aristotle (Harmonic) | Erdős #124 (weaker variant), #728, #729 | **NOVEL MATH (modest)** |
| GPT-5.2 Pro + Aristotle | Erdős #397, #728, #729, #1196 | **NOVEL MATH (lowest hanging fruit per Tao)** |
| OpenAI reasoning model (May 2026) | **Erdős unit-distance disproof, n^1.014** | **NOVEL MATH (landmark)** |
| OpenAI GPT-5 (Oct 2025) | "10 Erdős problems" | **HALLUCINATION (retracted)** |
| LLMs on First Proof | 2/10, both contaminated | **DOES NOT GENERALIZE** |

---

## Bottom line for the Aristotle audit

1. **Genuine novel-math capability EXISTS in principle** — the May 2026 unit-distance disproof is the proof of existence.
2. **But it required**: OpenAI's internal reasoning model + Lijie Chen as human author + 9 mathematicians for verification + algebraic number theory connections beyond standard prover training.
3. **For LLM+Lean stack specifically** (Aristotle's peer group): genuine novel results are limited to "lowest hanging fruit" Erdős problems (Tao's exact phrase). Real, but they are problems Erdős labeled with low difficulty.
4. **The bar HAS shifted from "benchmark + formalize" to "novel + verified"** — but only since Jan 2026, and only for a handful of problems.
5. **75% LLM hallucination rate on Hodge conjecture arXiv papers** (Litt) is the corrective baseline. The First Proof 2/10 result is the realistic ceiling for autonomous LLM research math today.

If Aristotle's claimed advances are at the **Erdős #728 level** (logarithmic gap factorial divisibility, technique close to known Pomerance/Erdős work), that is consistent with peer state-of-the-art. If they are at the **First Proof / Hodge conjecture level** (research lemmas in active fields), the project's audit is correct to be skeptical — peer systems also fail there.
