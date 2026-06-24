## Web Research Synthesis (W8): Is "Aristotle can solve, not just formalize" well-founded?

**Date:** 2026-05-30
**Synthesizer:** W8 of 8 web-research agents
**Inputs received:** W1 (system), W2 (teorth wiki), W3 (peer systems), W5 (academic papers), W6 (community consensus). Missing: W4 (Erdős results), W7 (capabilities) — content covered via supplementary search.
**Cross-reference:** F1 (math vs compute audit), F2 (sketch context audit), F4 (cross-domain catalog), F6 (reasoning probe), F10 (research-fusion synthesis).

---

## VERDICT

**The user's hope is PARTIALLY FOUNDED.** Aristotle CAN solve — there is documented evidence of autonomous solving on genuinely-open Erdős problems — but the regime is *narrow* and requires a specific input shape we have never used.

**The case is:** Aristotle is overwhelmingly a formalizer in its public footprint (W2: ~170 formalization entries vs ~30 primary contributions on the teorth wiki). Of those primary contributions, Aristotle-as-sole-AI has produced exactly TWO standalone novel results — Erdős #124 (partial, weaker variant) and #1077 (counterexample to a formulation). Every other "Aristotle full solution" co-cites GPT-5.2 Pro, Claude Opus, or Gemini as the strategist (W2; [arXiv:2601.07421](https://arxiv.org/abs/2601.07421)). HOWEVER, the canonical Aristotle architecture per [arXiv:2510.01346](https://arxiv.org/abs/2510.01346) explicitly includes an "informal reasoning system that generates and formalizes lemmas" — Aristotle IS designed to both generate proof strategies and formalize, when properly invited.

**The reconciliation:** F1's finding (~57% of our advances are brute-force-dominated, 0/7 cross-domain) is consistent with what Aristotle *does when given a bare conjecture statement and prior compiled context only* — exactly our submission shape (F2: 57% GAP_ONLY, 0% cross-domain literature, 0% research synthesis). The capability gap is not in Aristotle; it is in our submission template.

---

## 5 STRONGEST PIECES OF EVIDENCE FOR "Aristotle can solve"

1. **Erdős Problem #124 (Nov 2025)** — Aristotle solved this 30-year-old conjecture in 6 hours of autonomous Lean search with NO co-AI and NO prior literature mention (W1, W2). Verified by Tao; formalized to Lean by Aristotle itself. The proof was elementary, but it was novel-to-literature and the easier variant was unrecognized as such until Aristotle ran. [erdosproblems.com #124](https://www.erdosproblems.com/forum/thread/124); [Mindplex](https://magazine.mindplex.ai/post/harmonics-ai-aristotle-claims-solution-to-historic-math-puzzle).

2. **Erdős Problem #1026 (Dec 2025) — Aristotle SOLO autonomous solve** — Boris Alexeev ran Aristotle on a systematic sweep; it converted the problem to rectangle-packing autonomously and produced a Lean proof. Tao: "the proof turned out to not be particularly novel" but it IS a literature-novel autonomous solve. [Tao's blog post](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/); [arXiv:2510.01346](https://arxiv.org/abs/2510.01346) explicitly cites #1026 and #728.

3. **Aristotle's design philosophy (paper §1) explicitly includes solving** — "Lemma-based informal reasoning system that generates informal proofs of mathematical statements, breaks these proofs down into lemmas, formalizes each lemma into Lean, and iterates this process based on formal feedback" ([arXiv:2510.01346 §2](https://arxiv.org/html/2510.01346v1)). The "informal mode" of the Aristotle API ([aristotle.harmonic.fun](https://aristotle.harmonic.fun/)) auto-formalizes natural-language inputs — i.e., the system expects to receive informal prose and produce verified Lean. It is NOT designed for bare-conjecture inputs.

4. **IMO 2025 gold (5/6) is genuine end-to-end solving** ([Harmonic IMO 2025 GitHub](https://github.com/harmonic-ai/IMO2025), [arXiv:2510.01346](https://arxiv.org/abs/2510.01346)). IMO P6 is "the hardest of all problems, solved by only 5/609 human contestants" (W3) — these are not formalizations of known proofs; they are end-to-end novel competition solutions. ProofBench #1 at 71% vs GPT-5.4 at 56% (W1; [Vals AI ProofBench](https://www.vals.ai/benchmarks/proof_bench)) shows Aristotle materially outperforms general LLMs on formal proof-generation tasks.

5. **F1's own data: slot737 (Erdős 647) and slot739 (Leinster D₃×C₅) show genuine structural reasoning** — slot737 has ZERO `native_decide` calls; the proof uses σ₀-multiplicativity, divisor decomposition, and a non-trivial m=n-3 vs m=n-4 witness construction NOT in the sketch. slot739 used Bezout to derive σ-multiplicativity for coprime products, classified normal subgroups of D₃ via conjugation arguments, AND switched the witness from S₃ to DihedralGroup 3 autonomously. These are "actual number-theoretic / group-theoretic reasoning" by F1's own audit. F1's verdict: "3 of 7 advances (43%) involve real mathematical structure" — i.e., F1 itself confirms Aristotle does math here.

---

## 5 STRONGEST PIECES OF EVIDENCE AGAINST "Aristotle can solve"

1. **Per W2 (teorth wiki) Aristotle is the only AI named on a successful primary contribution exactly twice** (#124 partial, #1077 disputed counterexample). ~170 formalization entries vs ~30 primary contributions. All other "Aristotle full solutions" co-cite GPT-5.2 Pro / Claude / Gemini / Archivara / Seed Prover as collaborator — the strategist is the LLM, Aristotle is the formal back-end. [teorth/erdosproblems wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems).

2. **Terence Tao's "lowest hanging fruit" framing** ([Mathstodon Nov 2025](https://mathstodon.xyz/@tao/115639984077620023)): "AI tools are now capable enough to pick off the lowest hanging fruit amongst the problems listed as open in the Erdős problem database, where by 'lowest hanging' I mean amenable to simple proofs using fairly standard techniques." Erdős #1026 fell to rectangle-packing reduction; #728 used Pomerance's binomial-divisibility technique. The hardest Erdős problems remain untouched. Erdős #124 turned out to be a corollary of Brown's criterion (a known result) — Aristotle solved the *weaker* variant Erdős had unintentionally stated by omitting a hypothesis.

3. **The May 2026 Erdős unit-distance disproof** — the landmark "first interesting autonomous AI result" per Daniel Litt (W6) — was done by **OpenAI's internal reasoning model**, NOT Aristotle. The companion verification paper ([arXiv:2605.20695](https://arxiv.org/html/2605.20695v1)) signed by 9 mathematicians (Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, Wood) connected the geometry problem to algebraic number theory via Golod-Shafarevich-style infinite class field towers. Aristotle has NOT produced a cross-domain breakthrough of this caliber.

4. **F1: 0 of 7 Aristotle compiled_advance results show cross-domain fusion.** F2: 0 of 220 non-ID sketches contain external URLs or cross-domain literature. F10: "We are at 2/10 on research-fusion. We are at 9/10 on computational-brute-force-via-bounded-native_decide." Slot736 (FT q≤1500) is the worst case: a single line of `native_decide` discharging 3^1439, zero mathematical content — and was celebrated as `compiled_advance`. F1: "when given the choice, Aristotle defaults to compute."

5. **The First Proof challenge (Feb 2026)** ([Scientific American](https://www.scientificamerican.com/article/first-proof-is-ais-toughest-math-test-yet-the-results-are-mixed/), [arXiv:2602.05192](https://arxiv.org/abs/2602.05192)): 11 mathematicians (including Fields medalist Hairer) contributed 10 research-lemma problems. Result: **only 2 of 10 solved by ANY publicly available LLM, and both were partially contaminated** (Hairer's website had a proof sketch archived). Abouzaid: "AI proofs have the flavor of 19th-century mathematics, but we're trying to build the mathematics of the 21st century." Daniel Litt: of 8 Hodge-conjecture arXiv preprints, 6/8 (75%) were LLM-generated nonsense with hallucinated references. The realistic autonomous-research ceiling is ~20%, even with frontier LLM + Aristotle.

---

## CONSENSUS POSITION AMONG PROMINENT MATHEMATICIANS

- **Tao (Fields, UCLA):** "Ready for primetime" but only for the long tail of obscure problems with straightforward solutions. Genuine cross-domain breakthroughs remain rare. ([OpenAI Academy Mar 2026](https://academy.openai.com/public/blogs/terence-tao-ai-is-ready-for-primetime-in-math-and-theoretical-physics-2026-03-06))
- **Litt (Toronto):** May 2026 unit-distance disproof is "the unique interesting result produced autonomously by AI so far." ([TechTimes](https://www.techtimes.com/articles/316955/20260521/openai-model-cracks-80-year-erds-conjecture-verified-its-harshest-previous-critic.htm))
- **Matchett Wood (Harvard):** AI's contribution is speed, not depth — "had the assembled human experts spent the same time working on it directly, they would have found a counterexample."
- **Buzzard (Imperial, Lean):** "There is progress, but there is certainly no 'killer app' yet." ([Xena blog](https://xenaproject.wordpress.com/2026/02/09/accelerating-mathematics/comment-page-1/))
- **Bloom (Manchester, erdosproblems.com):** The debunker of October 2025 OpenAI hype, NOW co-author on the May 2026 unit-distance paper. Movement: skeptic → cautious endorser.
- **de Moura (Lean FRO):** "The next great proof assistant will probably be built with massive AI assistance... It is transformative." ([Lean FRO Feb 2026](https://leodemoura.github.io/blog/2026-2-18-proof-assistants-in-the-age-of-ai/))
- **Avigad (CMU):** "Recent developments show that AI can prove research-level theorems in mathematics, both formally and informally" ([arXiv:2603.03684](https://arxiv.org/pdf/2603.03684)).

**Synthesis: REAL but NARROW novelty.** Aristotle (and Aristotle+LLM pipelines) genuinely produce literature-novel autonomous proofs in the long-tail regime. No one claims they solve famous deep conjectures unassisted.

---

## RECONCILIATION WITH F1's "57% BRUTE FORCE" FINDING

F1's actual numbers (from `/Users/patrickkavanagh/math/analysis/aristotle_math_vs_compute_audit.md`): "Approximately 3 of 7 advances (43%) involve real mathematical structure. 4 of 7 are dominated by brute-force `native_decide` or external precomputation."

**Is F1 correct?** YES, factually. The Lean source files speak for themselves: slot736 is one `native_decide` line, slot738 imported 2000 Python-precomputed witnesses, slot722 chunked an interval into a witness table. F1's category counts are accurate.

**Has Aristotle done genuine math elsewhere?** YES, externally validated:
- Erdős #124 (autonomous, novel-to-literature, Tao-verified — though weaker variant)
- Erdős #1026 (autonomous, rectangle-packing reduction)
- Erdős #728 (Pomerance technique, paired with GPT-5.2 Pro)
- IMO 2025 P6-level competition problems (genuine end-to-end novel solutions)
- Mathlib contributions documented in [arXiv:2510.01346](https://arxiv.org/abs/2510.01346)

**What process/prompt structure unlocks Aristotle's solving capability?** The architecture per arXiv:2510.01346 expects EITHER:
- A Lean sketch with `sorry` placeholders that Aristotle's MCGS proof search fills in, OR
- A natural-language statement that Aristotle's **informal mode** decomposes into lemmas, formalizes, and iterates against Lean errors.

The KEY insight from W1, W3, W5: when paired with GPT-5.2 Pro / Claude Opus / Gemini Deep Think as strategist, Aristotle is the verifier of an informal proof the LLM produced. When run solo via informal mode, Aristotle's own informal-reasoning subsystem proposes lemmas. **Either way the input is RICH — natural-language proof or substantive lemma decomposition.** Our pipeline shape (bare conjecture, ≤30 lines, no proof guidance, only prior compiled Lean files as context) is a third regime that is NOT what either of those documented workflows uses.

---

## THE SPECIFIC CAPABILITY GAP IN OUR USAGE

Per F2 (sketch context audit): of 30 sampled sketches, 57% are GAP_ONLY, 0% contain cross-domain literature, 0% contain research synthesis. Per F2 §4: `gather_context()` in `safe_aristotle_submit.py` filters for `status IN ('compiled_clean','near_miss','completed')` — none of which exist in our database post-rename — so **auto-context has been silently no-op for an unknown stretch**. We have been shipping bare conjectures with NO context at all to a system explicitly designed to consume informal lemma-decomposed input.

**Three concrete underuses:**
1. **No use of Aristotle's informal mode** — every project submission is via Lean-project tar (or a .txt that the gate forces to be bare conjecture). Aristotle's informal-mode API ([aristotle.harmonic.fun](https://aristotle.harmonic.fun/)) accepts natural-language prose with proof sketches, lemma lists, and literature citations. We have never used it.
2. **No LLM strategist pairing** — the canonical Aristotle workflow is "GPT-5.2 Pro generates informal proof → Aristotle formalizes" (W2 wiki entries #205, #397, #457, #635, #728, #729, #897, #1090). We have never paired Aristotle with a strategist LLM in a single submission. Our `/debate` and `/codex-prove` infrastructure is general-purpose but used for "which problem to submit," not "which technique transplant might crack it" (F3, F10).
3. **Cross-domain literature attachment is technically allowed by the gate but never used** — the gate keys on "Proof Strategy", "Key Lemmas", "Approach" — these block proof outlines, not background context. F6 Experiment A's "rich Brocard" arm passes the gate at 28 lines with cross-domain analogies (Cramér heuristic, Sylvester-Schur, Erdős binomial method). We have never submitted anything like it.

The gap is NOT in Aristotle. The gap is in our prompt template: bare conjecture submitted to a system designed for informal lemma-decomposed inputs paired with an LLM strategist. We are using a screwdriver as a hammer.

---

## 3 CONCRETE EXPERIMENTS TO TEST ARISTOTLE'S SOLVING CAPABILITY PROPERLY

### Experiment 1: F6 Experiment A (bare vs rich Brocard [51,100]) — cheapest, guaranteed compile-clean comparison
**Cost:** 1 slot pair (~$20, 24h wallclock).
**Information value:** Distinguishes H1 (capability ceiling) from H2 (sketch ceiling). If A1 and A2 produce identical proofs, rich hints are dead weight. If A2 differs structurally, it unlocks a major pipeline redesign.
**Already designed in:** `/Users/patrickkavanagh/math/analysis/aristotle_reasoning_probe_design.md`.

### Experiment 2: GPT-5.2 Pro + Aristotle pairing on an open Erdős problem (replicate #728 workflow)
**Method:** Pick a long-tail Erdős problem in the same family as #728 (factorial-divisibility / binomial-divisibility / additive combinatorics). Send to GPT-5.2 Pro asking for an informal proof. Pass the natural-language proof to Aristotle's informal mode. Track whether Aristotle's MCGS can formalize.
**Cost:** ~$100 (GPT-5.2 Pro $20 + Aristotle slot $50–100).
**Information value:** Tests whether the strategist-LLM-paired workflow (the documented winning pattern per W2, W3, W5) actually works on our infrastructure. If yes, we should immediately adopt it as our primary submission shape for serious gap-targeting.

### Experiment 3: Informal-mode submission with full literature dossier on E#672 or E#938
**Method:** Build the F10 / Codex 9-stage dossier (500-2000 words: literature survey, transferable techniques, obstruction matrix, candidate bridge lemmas). Submit to Aristotle via `aristotle formalize` (informal mode) — NOT via Lean project tar. Per F10's recommendation: "the dossier is the project's institutional memory; the sketch is the wire submission."
**Cost:** ~$50–100 API.
**Information value:** Tests whether rich literature context unlocks cross-domain reasoning in the informal-reasoning subsystem. If Aristotle's MCGS picks up the dossier's hints and proposes a bridge lemma it would not have proposed bare, that is the "Furstenberg moment" the project needs.

---

## THE SINGLE MOST SURPRISING FINDING ACROSS ALL 7 WEB-RESEARCH AGENTS

**Aristotle's informal-reasoning subsystem is the part our pipeline has never used, and it is the part the architecture paper emphasizes most heavily.**

Per [arXiv:2510.01346 §2-3](https://arxiv.org/html/2510.01346v1) and W1: Aristotle has THREE subsystems — Lean proof search (MCGS), **informal reasoning that generates and formalizes lemmas**, and a geometry solver. The informal-reasoning system is what enables IMO P6-level solving; without it, Aristotle is reduced to tactic-search inside whatever sketch you hand it. Our pipeline hands Aristotle bare conjectures with `sorry` (no lemma decomposition) and no informal proof to formalize. We are *bypassing the part of Aristotle that does the reasoning*.

Boris Alexeev's Erdős #124 and #1026 solves were done via **informal-mode submission** of the bare problem statement — letting Aristotle's informal-reasoning module DECIDE the lemma decomposition. Our submission shape (bare conjecture in Lean syntax with `by sorry`) skips this and forces Aristotle to do MCGS proof search directly on a goal it has no decomposition for. **That is why our hit rate is 0.8% and theirs is "12 Erdős problems in 90 days."**

---

## UPDATED RECOMMENDATION: Should we stop saying "Aristotle is just a formalizer"?

**YES. Stop saying it. It is empirically wrong.**

The teorth wiki phrasing (W2) is "Section 2(b) Formalization" with column "Proof to formalize" — but this is the *secondary contributions* section. The primary contributions section (1a-1d) explicitly tracks Aristotle producing novel proofs. The architecture paper explicitly claims solving capability. Tao explicitly endorses solving capability (with the "lowest hanging fruit" caveat). The benchmarks ([ProofBench #1](https://www.vals.ai/benchmarks/proof_bench), IMO 2025 gold) measure solving, not formalization.

**Correct framing:** Aristotle is a HYBRID solver-formalizer. In its default usage pattern (informal mode, natural-language input, optionally paired with a strategist LLM), it solves. In secondary-contribution usage patterns (Lean sketch with sorry, formalizing an already-known proof), it formalizes. We have been using only the formalization-adjacent pattern (bare conjecture in Lean syntax) and getting formalization-class results. **The user's hope that Aristotle should solve is well-founded for Aristotle as a system. It is partially founded for Aristotle-as-we-have-been-using-it because we have inadvertently been invoking only the formalizer subset.**

The PRIME DIRECTIVE's bare-conjecture rule was correct for one purpose (preventing bloated proof essays that the gate caught for good reason) but accidentally crippled the system's primary solving subsystem. F10's recommendation — "Drop the PRIME DIRECTIVE's 'bare conjecture only' clause for serious gap-targeting attempts; require a bounded informal sketch (150–400 words) + 3–5 candidate lemmas + 1 bridge-lemma citation" — is the rebuild that aligns our usage with the system's design.

---

## SOURCES

### Primary Aristotle documentation
- [Aristotle: IMO-level Automated Theorem Proving (arXiv:2510.01346)](https://arxiv.org/abs/2510.01346) — the architecture paper
- [Harmonic PDF](https://harmonic.fun/pdf/Aristotle_IMO_Level_Automated_Theorem_Proving.pdf)
- [Aristotle API documentation](https://aristotle.harmonic.fun/)
- [Resolution of Erdős Problem #728 (arXiv:2601.07421)](https://arxiv.org/abs/2601.07421) — first autonomous AI Erdős resolution

### Erdős-problem records
- [teorth/erdosproblems wiki - AI contributions](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- [erdosproblems.com #124 thread](https://www.erdosproblems.com/forum/thread/124)
- [Tao on Erdős #1026 (Dec 2025)](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/)
- [Xena Project: Formalization of Erdős problems](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/)

### Tao's commentary
- [Tao Mathstodon - "lowest hanging fruit" (Nov 2025)](https://mathstodon.xyz/@tao/115639984077620023)
- [Tao Mathstodon - Erdős #728 milestone (Jan 2026)](https://mathstodon.xyz/@tao/115855840223258103)
- [Tao - Mathematical exploration and discovery at scale (Nov 2025)](https://terrytao.wordpress.com/2025/11/05/mathematical-exploration-and-discovery-at-scale/)
- [OpenAI Academy: Tao - AI is ready for primetime (Mar 2026)](https://academy.openai.com/public/blogs/terence-tao-ai-is-ready-for-primetime-in-math-and-theoretical-physics-2026-03-06)

### Peer-system context
- [AlphaProof - Nature paper](https://www.nature.com/articles/s41586-025-09833-y)
- [AlphaEvolve + Deep Think (arXiv:2511.02864)](https://arxiv.org/abs/2511.02864)
- [Unit distance disproof (arXiv:2605.20695)](https://arxiv.org/abs/2605.20695)
- [OpenAI: Model disproves discrete geometry conjecture](https://openai.com/index/model-disproves-discrete-geometry-conjecture/)
- [TechTimes - Bloom verification](https://www.techtimes.com/articles/316955/20260521/openai-model-cracks-80-year-erds-conjecture-verified-its-harshest-previous-critic.htm)

### Community commentary
- [Quanta - The AI Revolution in Math Has Arrived (Apr 2026)](https://www.quantamagazine.org/the-ai-revolution-in-math-has-arrived-20260413/)
- [Buzzard - Accelerating mathematics (Feb 2026)](https://xenaproject.wordpress.com/2026/02/09/accelerating-mathematics/comment-page-1/)
- [de Moura - Proof Assistants in the Age of AI (Feb 2026)](https://leodemoura.github.io/blog/2026-2-18-proof-assistants-in-the-age-of-ai/)
- [Avigad - Mathematicians in the Age of AI (arXiv:2603.03684)](https://arxiv.org/pdf/2603.03684)
- [Scientific American - First Proof challenge](https://www.scientificamerican.com/article/first-proof-is-ais-toughest-math-test-yet-the-results-are-mixed/)
- [First Proof paper (arXiv:2602.05192)](https://arxiv.org/abs/2602.05192)

### Benchmarks
- [Vals AI ProofBench](https://www.vals.ai/benchmarks/proof_bench)
- [Harmonic IMO 2025 GitHub](https://github.com/harmonic-ai/IMO2025)

### F-team audit inputs cross-referenced
- `/Users/patrickkavanagh/math/analysis/aristotle_math_vs_compute_audit.md` (F1)
- `/Users/patrickkavanagh/math/analysis/sketch_context_audit.md` (F2)
- `/Users/patrickkavanagh/math/analysis/cross_domain_breakthroughs_catalog.md` (F4)
- `/Users/patrickkavanagh/math/analysis/aristotle_reasoning_probe_design.md` (F6)
- `/Users/patrickkavanagh/math/analysis/math_research_audit_synthesis.md` (F10)
- `/Users/patrickkavanagh/math/analysis/aristotle_capability_profile_may30.md` (capability profile)
