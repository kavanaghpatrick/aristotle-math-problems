# Web Research W6: Math Community Consensus on LLM-Driven Mathematical Discovery

**Date compiled:** 2026-05-30
**Scope:** X/Twitter, Mathstodon, prominent mathematician blogs, Quanta Magazine, arXiv preprints, 2025-2026 coverage.

---

## 1. THE OVERALL CONSENSUS (Q1 2026 -> Q2 2026)

The community has moved from "AI is a fast tutor / mediocre grad student" (Tao, Sep 2024) to "AI is ready for primetime" (Tao, March 2026). The dominant view as of May 30, 2026:

- **Real but narrow novelty.** AI systems are now producing genuinely *novel* proofs of *open but tractable* problems, almost exclusively via Lean-verified pipelines.
- **Hallucination remains the central failure mode.** Informal LLM proofs alone are not trusted. Formal verification (Lean 4) is treated as the load-bearing trust layer.
- **The bar of "novelty" is contested.** "Lowest-hanging fruit," "not in literature but uses standard techniques," "deep insight" are three different bars and most 2026 wins clear only the first two.
- **Overclaiming has had real reputational cost.** OpenAI/Weil's October 2025 episode is the cautionary tale that every mathematician cites; Bloom's debunking is the implicit gatekeeper now.

---

## 2. KEY TIMELINE OF VERIFIED + DEBUNKED EVENTS

### Genuine novel-AI-math (endorsed by named mathematicians)

| Date | Event | Endorser | URL |
|------|-------|----------|-----|
| Jan 8, 2026 | **Erdős #728** resolved autonomously by GPT-5.2 Pro + Aristotle (Harmonic), Lean-verified | Terence Tao explicitly: "first Erdős problem solved largely autonomously... not documented in existing literature" | https://mathstodon.xyz/@tao/115855840223258103 ; arXiv:2601.07421 |
| Jan 11, 2026 | **Erdős #397** (DISPROVED via Lean) plus #729 within same week | Tao verified within 24 hours | https://www.erdosproblems.com/forum/thread/728 |
| Jan 12, 2026 | **Vakil + Manners + Salafatinos** prove a theorem using Gemini DeepThink + FullProof: "elegant, correct, beautifully written" | Vakil (Stanford) on the record | https://www.quantamagazine.org/the-ai-revolution-in-math-has-arrived-20260413/ |
| May 20, 2026 | **Erdős Unit Distance Conjecture disproved** by internal OpenAI reasoning model; counterexample via Golod-Shafarevich infinite class field towers | Companion paper authors: Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, V. Wang, Matchett Wood | https://arxiv.org/html/2605.20695v1 |
| May 21-22, 2026 | **AlphaProof Nexus** (DeepMind) solves 9/353 open Erdős problems + 44/492 open OEIS conjectures + a 15-year Hilbert function question, all Lean-verified | DeepMind preprint; Hassabis caveats "not AGI" | https://arxiv.org/html/2605.22763v1 ; https://winbuzzer.com/2026/05/26/google-deepmind-says-alphaproof-nexus-is-still-not-agi-xcxwbn/ |

### Overclaimed / debunked (cautionary cases)

| Date | Event | Debunker | URL |
|------|-------|----------|-----|
| Oct 2025 | Kevin Weil (OpenAI VP): "GPT-5 found solutions to 10 previously unsolved Erdős problems" — post got 100k views, deleted within days | **Thomas Bloom** (erdosproblems.com maintainer): GPT-5 had just run a literature search and surfaced already-published papers Bloom hadn't catalogued | https://nerdleveltech.com/openai-erdos-unit-distance-conjecture (recap); https://www.theneuron.ai/explainer-articles/from-erdos-to-axiom-the-open-problems-ai-has-actually-solved/ |
| Aug 2025 | Bubeck (OpenAI) claim that GPT-5 solved a convex optimization open problem | Malliavin-Stein researchers later showed the model could not in fact extend the qualitative fourth-moment theorem to a quantitative one | https://arxiv.org/abs/2509.03065 |
| Several 2025-26 cases | Erdős problems briefly marked "solved" via AI-powered lit search, then reclassified as "literature retrieval, not novel" (Tao's Mathstodon thread Nov 2025) | Tao + Bloom community moderation | https://mathstodon.xyz/@tao/115639984077620023 |

---

## 3. WHAT PROMINENT MATHEMATICIANS ARE SAYING

### Terence Tao (Fields Medal, UCLA)

- Tao's central frame on Mathstodon (Nov 2025): "AI tools are now capable enough to pick off the *lowest hanging fruit* amongst the problems listed as open in the Erdős problem database, where by 'lowest hanging' I mean 'amenable to simple proofs using fairly standard techniques.'" https://mathstodon.xyz/@tao/115639984077620023
- On #728 (Jan 8, 2026): "first Erdős problem solved largely autonomously by AI... not replicated in existing literature." https://mathstodon.xyz/@tao/115855840223258103
- OpenAI Academy interview (Mar 2026): AI is "ready for primetime" because it now "saves more time than it wastes." https://academy.openai.com/public/blogs/terence-tao-ai-is-ready-for-primetime-in-math-and-theoretical-physics-2026-03-06
- Klowden+Tao essay (Mar 29, 2026): "vanilla extract, not the cake" -- AI improves workflow, but pure AI-generated proofs risk being "odorless" (technically valid, devoid of insight). https://terrytao.wordpress.com/2026/03/29/mathematical-methods-and-human-thought-in-the-age-of-ai/ ; arXiv:2603.26524
- His view that AI is currently a "trustworthy co-author" (his 2023 prediction, now arriving on schedule per multiple May 2026 commentaries).

### Kevin Buzzard (Imperial, Xena / formal-math advocate)

- Feb 2026 blog "Accelerating mathematics": "Right now there seem to be two relevant technologies poised to help disrupt mathematics: the LLM and the ITP. There is progress, but there is certainly no 'killer app' yet." https://xenaproject.wordpress.com/2026/02/09/accelerating-mathematics/comment-page-1/
- On hallucinations: "One hallucination can break an entire mathematical argument because that's the nature of mathematics."
- His framing: pros use LLM+Lean for intermediate undergrad/PhD-level steps; amateurs and cranks aim higher and "do not survive 5 minutes of expert scrutiny."

### Richard Borcherds (Fields Medal, Berkeley)

- Epoch AI roundtable: ~10 years until AI surpasses humans in research math, "with substantial uncertainty." Expects a transitional phase of human+AI collaboration, then a phase where "human intervention just makes it worse." https://epoch.ai/frontiermath/expert-perspectives
- On formalization: "AI is pretty close to being able to formalize an awful lot of human mathematics."

### Thomas Bloom (Manchester / erdosproblems.com)

- The debunker of October 2025 OpenAI claim; now a co-author on the May 20, 2026 unit-distance disproof paper.
- Bloom in companion paper (May 2026): "the human still plays a vital role in discussing, digesting, and improving this proof, and exploring its consequences." Says the proof "doesn't deliver any fundamentally new geometric tools" but expects "many algebraic number theorists will be taking a close look at other open problems in discrete geometry."

### Daniel Litt (Toronto)

- On the May 20 OpenAI unit-distance disproof: **"This is the unique interesting result produced autonomously by AI so far."** https://www.techtimes.com/articles/316955/20260521/openai-model-cracks-80-year-erds-conjecture-verified-its-harshest-previous-critic.htm

### Melanie Matchett Wood (Harvard)

- On the same paper, sobering: had the assembled human experts spent the same time as they did verifying the AI's answer working on it directly, "the mathematicians would have found a counterexample." The AI's contribution was speed, not depth.

### Frank Calegari (Persiflage, UChicago)

- Historically skeptical of formal math investment in his subfield (number theory): "I don't really know what I am talking about or indeed have any idea what 'Lean' actually is." Persiflage 2026 posts focus on classical number theory rather than AI; he has not (publicly) flipped to AI-positive. https://galoisrepresentations.org/about/

### Leonardo de Moura (Lean FRO creator)

- "Proof Assistants in the Age of AI" (Feb 18, 2026): "The next great proof assistant will probably be built with massive AI assistance. At the Lean FRO, we have already embraced AI as part of our development process. It is transformative." https://leodemoura.github.io/blog/2026-2-18-proof-assistants-in-the-age-of-ai/
- "When AI Writes the World's Software, Who Verifies It?" (Feb 28, 2026): notes every IMO-medal AI system (AlphaProof, Aristotle, SEED Prover, Axiom, Aleph, Mistral) builds on Lean. https://leodemoura.github.io/blog/2026/02/28/when-ai-writes-the-worlds-software.html

### Jeremy Avigad (CMU)

- "Mathematicians in the Age of AI" (Mar 2026, arXiv:2603.03684): "Recent developments show that AI can prove research-level theorems in mathematics, both formally and informally. The essay urges mathematicians to stay up-to-date... Although the technologies are still niche and have seen only a handful of notable successes, the advances make it clear that they are bound to have a significant impact."

---

## 4. THE ARISTOTLE-SPECIFIC STORY (Harmonic, NOT Anthropic)

Aristotle is by **Harmonic** (Vlad Tenev cofounder), not Anthropic. Its public record:
- IMO 2025 gold-medal performance (arXiv:2510.01346).
- Erdős #124: autonomously generated a Lean proof in 6 hours. Caveat from Tao: "Erdős omitted a key hypothesis which made the problem a consequence of a known result (Brown's criterion)... not noticed until Boris Alexeev applied the Aristotle tool to this problem." So Aristotle solved the *weaker* version actually stated.
- Erdős #728 (Jan 2026): GPT-5.2 Pro + Aristotle pipeline; Aristotle formalized in Lean. This is the canonical "first."
- Erdős #729, #397: same pipeline week.

Aristotle's value-add is **formalization**: it takes an informal LLM proof and produces a Lean 4 artifact that's compiler-checked. The novelty itself usually comes from a frontier LLM (GPT-5.2 Pro most often, also Gemini DeepThink).

---

## 5. POLYMATH-STYLE HUMAN+AI COLLABORATIONS

- **Aletheia (DeepMind, Mar 2026, arXiv from Feng Tian's group)**: Gemini DeepThink + intensive tool use, used with mathematicians at UC Berkeley, Brown, Yonsei, Concordia, KIAS, UCSD, Caltech to produce a "wave of mathematical research papers."
- **AI Co-Mathematician (arXiv:2605.06651)**: scored 48% on FrontierMath Tier 4, framed as agentic-AI collaboration.
- **Vakil-Manners-Salafatinos** (Stanford + DeepMind, Jan 12, 2026 preprint): humans sketched, Gemini filled in details for a general case.
- **Gauss agent**: formalized strong Prime Number Theorem in 3 weeks with expert scaffolding.
- **Numina-Lean-Agent**: formalized a research paper on Brascamp-Lieb inequalities via mathematician-in-the-loop blueprint refinement.
- **Tao's PNT+ / Explicit Analytic Number Theory project**: AI use is permitted but must be disclosed and human-edited; CI rejects non-typechecking Lean.

The pattern: **humans pick the problem and steer; AI fills in routine derivations; Lean verifies**. Pure-autonomous wins exist (Erdős #728, AlphaProof Nexus's 9) but are still the exception.

---

## 6. THE SINGLE MOST CREDIBLE POSITION ON "CAN CURRENT AI PROVE NEW THEOREMS?"

**Terence Tao on Mathstodon, Nov 2025 + Jan 2026:**

> Yes -- but only the lowest hanging fruit, where "lowest hanging" means "amenable to simple proofs using fairly standard techniques." The capability is genuine and accelerating; #728 is the first autonomous case where no prior literature exists. But these wins say more about speed than difficulty. The Erdős problems span a range; the hardest remain untouched.

Daniel Litt's complement (May 2026): "This is the unique interesting result produced autonomously by AI so far" — and that was the unit-distance counterexample requiring nine senior mathematicians to verify and reshape.

---

## 7. IMPLICATIONS FOR OUR PROJECT (math-forge / Aristotle queue)

1. **Our pipeline matches the dominant 2026 paradigm.** GPT-5.2 Pro / Codex generates strategy; Aristotle formalizes; Lean verifies. This is exactly what Sothanaphan/Barreto did for #728.

2. **The "novelty bar" is now triple-gated:**
   - Compiles in Lean (sorry-free, no axioms beyond Mathlib).
   - Statement matches an open gap (per Bloom's curated registry).
   - No prior literature contains the same/similar result.
   The community now expects all three. Our "compiled_advance" status (contribution_statement + axiomatizes_prior_work=0 + target_resolved=1) maps to this — keep enforcing it.

3. **Falsification works.** OpenAI's May 2026 win was a *disproof* (unit distance), not a constructive proof. Validates our policy that "is this gap real?" is valid gap-targeting.

4. **Overclaiming carries severe cost.** Weil's deleted X post is the cautionary tale. Bloom's debunking method is now the implicit standard — always run literature search before claiming novelty. Our `mk failed` + `false_lemmas` discipline is the correct posture.

5. **"Compiled clean != resolved the gap"** (our rule #12) aligns precisely with Tao's "odorless proofs" caveat and Wood's observation that AI speed != AI insight.

6. **Bare-gap submission to formalization-first systems is the empirically winning workflow.** Vakil's protocol (sketch the case, let AI fill details), Sothanaphan's #728 (informal LLM strategy -> Aristotle Lean), and AlphaProof Nexus all follow it. Our `/submit` + auto-context model is in the same shape.

7. **What's missing from our project vs. SOTA:**
   - **External mathematician verification.** Bloom-style debunking is a service we don't have in-loop. Consider adding a `/literature-check` skill that searches arXiv/MathSciNet pre-submission.
   - **DeepMind-scale parallelism.** AlphaProof Nexus brute-forced 9 wins over 353 attempts (~2.5% hit rate) at "a few hundred dollars per problem." Our 0.8% hit rate is consistent with their selectivity baseline; concentrating on fewer problems (per Memory directive #3) is the rational response.
   - **Public registry signaling.** Tao maintains a GitHub Wiki cataloguing AI-solved Erdős problems. If we get a `compiled_advance`, surfacing it there (via erdosproblems.com forum) is the canonical credibility move.

---

## SOURCES CITED

- [Tao, Mathstodon, Nov 2025: "lowest hanging fruit"](https://mathstodon.xyz/@tao/115639984077620023)
- [Tao, Mathstodon, Jan 2026: Erdős #728 milestone](https://mathstodon.xyz/@tao/115855840223258103)
- [Tao, "Mathematical methods and human thought in the age of AI" (Mar 29, 2026)](https://terrytao.wordpress.com/2026/03/29/mathematical-methods-and-human-thought-in-the-age-of-ai/)
- [OpenAI Academy: "Tao: AI is ready for primetime" (Mar 6, 2026)](https://academy.openai.com/public/blogs/terence-tao-ai-is-ready-for-primetime-in-math-and-theoretical-physics-2026-03-06)
- [Resolution of Erdős Problem #728, arXiv:2601.07421](https://arxiv.org/abs/2601.07421)
- [Aristotle: IMO-level Theorem Proving, arXiv:2510.01346](https://arxiv.org/abs/2510.01346)
- [AlphaProof Nexus paper, arXiv:2605.22763](https://arxiv.org/html/2605.22763v1)
- [Unit distance disproof, arXiv:2605.20695](https://arxiv.org/html/2605.20695v1)
- [Quanta: "The AI Revolution in Math Has Arrived" (Apr 13, 2026)](https://www.quantamagazine.org/the-ai-revolution-in-math-has-arrived-20260413/)
- [Buzzard, "Accelerating mathematics" (Feb 9, 2026)](https://xenaproject.wordpress.com/2026/02/09/accelerating-mathematics/comment-page-1/)
- [De Moura, "Proof Assistants in the Age of AI"](https://leodemoura.github.io/blog/2026-2-18-proof-assistants-in-the-age-of-ai/)
- [Borcherds + others on Epoch AI](https://epoch.ai/frontiermath/expert-perspectives)
- [Persiflage (Calegari) blog](https://galoisrepresentations.org/about/)
- [TechTimes: OpenAI unit distance + Bloom verification](https://www.techtimes.com/articles/316955/20260521/openai-model-cracks-80-year-erds-conjecture-verified-its-harshest-previous-critic.htm)
- [Avigad, "Mathematicians in the Age of AI", arXiv:2603.03684](https://arxiv.org/pdf/2603.03684)
- [Aletheia, Towards Autonomous Mathematics Research (Mar 2026)](https://math.berkeley.edu/~fengt/Aletheia.pdf)
- [The Neuron: AI cracks Erdős](https://www.theneurondaily.com/p/ai-cracks-legendary-erdos-problems)
