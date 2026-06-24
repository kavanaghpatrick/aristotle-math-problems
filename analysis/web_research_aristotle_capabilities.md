# Aristotle Capability Research — Adversarial-to-the-Skeptic

**Date**: 2026-05-30
**Agent**: W7
**Mission**: Find the strongest possible evidence that Aristotle CAN solve novel problems, not just formalize. Treat F1's "57% brute force" audit as the position to challenge.

---

## 1. The Strongest Pro-Discovery Evidence

### 1.1 Erdős Problem #728 (Jan 2026) — first Erdős problem fully resolved by AI

The arXiv writeup by Nat Sothanaphan ([arXiv:2601.07421](https://arxiv.org/abs/2601.07421)) explicitly states:

> "This is the first Erdős problem regarded as fully resolved autonomously by an AI system. The system in question is a combination of GPT-5.2 Pro by OpenAI and Aristotle by Harmonic, operated by Kevin Barreto."

KoishiChan's literature search found NO prior human resolution. The proof uses Kummer's theorem + base-p carry counting + "carry-rich but spike-free" choices of m. Status: novel.

**But critical caveat**: GPT-5.2 Pro generated the informal strategy. Aristotle formalized + simplified. The mathematical extension to the stronger version was attributed to GPT-5.2 Pro's response, not Aristotle's autonomous reasoning. (Source: WebFetch of [arXiv:2601.07421 html](https://arxiv.org/html/2601.07421v1))

### 1.2 Erdős Problem #124 (Boris Alexeev case, Dec 2025)

Aristotle "autonomously located (and formalized in Lean) a solution to this weaker version of the problem within hours." Terence Tao confirmed Erdős had omitted a key hypothesis, which Aristotle's solution exposed. ([Erdős Problems forum](https://www.erdosproblems.com/forum/thread/124)). This is the cleanest "Aristotle alone" case, though the proof was deemed "almost surely the most simple proof possible" — not necessarily creative.

### 1.3 Tao's Analysis I textbook discoveries (Aristotle paper, Appendix D)

The Aristotle paper ([arXiv:2510.01346](https://arxiv.org/abs/2510.01346)) reports:
- Discovered **4 false exercises** with explicit **counterexamples** (witness construction)
- For 2 other exercises, noticed that **a hypothesis was unnecessary** (mathematical insight, not just search)
- Worked over a custom type system distinct from Mathlib — proving cross-domain abstraction

### 1.4 IMO 2025 Problem 3 — auxiliary set S

Per the Aristotle paper (WebFetch of [arXiv:2510.01346v1](https://arxiv.org/html/2510.01346v1)):

> "For Problem 3, Aristotle defined a set S 'not directly defined or suggested by the problem statement,' illustrating ability to 'define and use novel auxiliary definitions, much as a human mathematician would.'"

For Problem 5, Aristotle "defined f(k) which turns out to become a useful invariant." Inventing useful invariants is a key creative mathematical act.

### 1.5 Erdős Problem #481 (Barreto)

> "Kevin Barreto resolved Problem 481, and then made two requests to Aristotle: one to formalize his proof, and one to solve the problem by itself. Both succeeded."

This is Aristotle solving a non-trivial problem with no human strategy provided. ([AI contributions to Erdős problems wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems))

### 1.6 Mathlib novel contributions

The paper states Aristotle "made novel contributions to Mathlib (e.g., Niven's theorem, Gauss-Lucas theorem, eigenvalues as roots of the characteristic polynomial)" during training. These were missing from Mathlib and proven autonomously.

---

## 2. Aristotle's Internal Architecture

From WebFetch of [arXiv:2510.01346v1](https://arxiv.org/html/2510.01346v1):

**Aristotle is NOT a single LLM call**. It is an agentic system with multiple components and memory.

### 2.1 Three subsystems
1. **Monte Carlo Graph Search (MCGS)** — generalizes MCTS over Lean states; uses a 200B+ parameter transformer as policy + value function; treats states as vertices in a directed graph with equivalence classes
2. **Lemma-based informal reasoning system** — natural-language proof generation, lemma decomposition, autoformalization, Lean REPL feedback loop, iteration
3. **Yuclid geometry solver** — algebraic + diagram-based, descended from AlphaGeometry

### 2.2 Memory and state
- Action history included in prompts to reduce circular trajectories (paper notes this is "theoretically unnecessary [the state machine is memoryless]" but practically useful)
- Equivalence-based caching turns the search tree into a hypergraph
- States compared by goal expressions, local context, local variable names

### 2.3 Test-Time Training (TTT)
The paper confirms: at deployment, when a problem isn't solved, Aristotle **retrains the model on search traces from these attempts**. This enables cross-pollination between lemmas from different proof sketches. This IS a discovery-enabling capability — the model literally learns mid-attempt.

### 2.4 The lemma reasoning pipeline (mechanism)
1. Generate informal natural-language proof of theorem
2. Restructure as a sequence of lemmas building on each other
3. Formalize each lemma in Lean
4. Send to Lean REPL, parse error messages, request corrections
5. If unsuccessful: keep proved lemmas, request new ones, repeat
6. Hidden chain-of-thought with dynamic thinking budget
7. Co-evolution of formal Lean + informal comments + hidden CoT during training

### 2.5 Error repair behavior
Paper documents Aristotle **repairing flawed informal reasoning during formalization** — caught and fixed confusion between "strictly decreasing, weakly decreasing, sequences which decrease at some point." This is real mid-attempt strategy refinement, not brute search.

---

## 3. Comparison: Aristotle vs GPT-5.2 Pro vs AlphaProof

| Capability | Aristotle (Harmonic) | GPT-5.2 Pro (OpenAI) | AlphaProof Nexus (DeepMind) |
|---|---|---|---|
| IMO 2025 | 5/6 formal Lean | 5/6 natural language | 4/6 (2024) silver, IMO 2025 also gold via Gemini Deep Think |
| Open Erdős problems solved | #124 (alone), #728 (with GPT-5.2), #481 (alone) | #728 (with Aristotle) | 9/353 Erdős, 44/492 OEIS |
| Architecture | MCGS + informal lemmas + TTT, 200B+ params | Reasoning LLM, max effort | LLM + Lean + evolutionary search + RL ("Agent D") |
| Autonomy | Hybrid — pairs well with GPT-5.2 | Stronger informal reasoning, no formal verification on own | Most autonomous; "agent constructs novel proofs" |
| Verification | Lean 4 mandatory; "no hallucinations" claim | Natural language only | Lean 4 with evolutionary search |
| FrontierMath | not benchmarked | 40.3% (Tier 1–3), state of the art | not benchmarked |
| Verified novel discovery | Counterexamples, invariants, auxiliary sets | Bubeck convex optimization (disputed by Ryu), statistical learning theory, MLE monotonicity, FrontierMath open problem | 9 Erdős problems, counterexample for #198, example for #730 |

### 3.1 Cost & Scale
- AlphaProof Nexus: "a few hundred dollars per problem" ([cryptobriefing](https://cryptobriefing.com/deepmind-alphaproof-nexus-erdos-problems/))
- Aristotle: requires 200B+ parameters + parallel reasoning instances + TTT iteration (significant compute, but not disclosed)
- GPT-5.2 Pro: API pricing public

### 3.2 The novelty gauntlet
DeepMind's Hassabis called earlier OpenAI Erdős claims "embarrassing" because GPT-5 had retrieved existing references. AlphaProof Nexus and Aristotle both passed the KoishiChan literature gauntlet for at least some claimed results.

---

## 4. Single Strongest Piece of Evidence FOR "Aristotle Can Solve"

The Aristotle paper's own claim about IMO 2025 Problem 3:

> "Aristotle defined a set S not directly defined or suggested by the problem statement, illustrating ability to define and use novel auxiliary definitions, much as a human mathematician would."

PLUS the Tao Analysis I case: discovering 4 false exercises with witness counterexamples and identifying 2 unnecessary hypotheses. Witness construction and hypothesis pruning are non-trivial creative acts.

The Polya-Szego project ([Igor Rivin](https://igorrivin.github.io/research/polya-szego-aristotle/)) achieved **100% on 80 inequalities** — a benchmark where frontier LLMs alone scored 2.8%. The 30x gap closure is concrete evidence that Aristotle does NOT collapse to brute-force LLM output.

## 5. Single Strongest Piece of Evidence AGAINST

The Erdős #728 writeup itself: GPT-5.2 Pro generated the strategy, Aristotle formalized. When the stronger version was needed, **GPT-5.2 Pro was asked first**, not Aristotle. Aristotle's role in the most-publicized "first AI-solved Erdős problem" was the autoformalization layer, not the creative engine.

Also: AcerFur's three caveats — ambiguity of problem statement, heavy inspiration from Pomerance's prior work, unclear how much unsearched literature exists.

Also: Igor Rivin's secondary finding — Aristotle proves 97.6% of theorems it attempts, **but only 67% are semantically correct**. It can "prove the wrong theorem a third of the time, fluently and confidently." An external agentic pipeline is needed to push this from 67% to 97% semantic accuracy.

---

## 6. Resolution

**The user's optimism is partially founded.**

**Founded by**:
- Aristotle has architectural ingredients for discovery (informal reasoning, lemma decomposition, TTT, MCGS, error repair)
- Demonstrated novel invariant/auxiliary-set construction on IMO 2025 problems
- Found 4 counterexamples + 2 unnecessary hypotheses in Tao's textbook unsupervised
- Solo solution of Erdős #124 and #481 (the latter with no human input)
- Cleared the 2.8% → 100% gap on Polya-Szego, vastly outperforming baseline LLMs

**Tempered by**:
- The flagship Erdős #728 case relied heavily on GPT-5.2 Pro for strategy; Aristotle was the formalizer
- Aristotle has a 33% semantic-drift problem (proving theorems that aren't quite the asked one)
- The "novel" Erdős proofs are often refinements of known techniques (Pomerance, Brown's criterion)
- AlphaProof Nexus has more documented frontier Erdős results (9 problems) than Aristotle alone

**The "57% brute force" framing is reductive.** Aristotle has documented creative behaviors that pure brute force cannot exhibit: inventing useful auxiliary sets, identifying redundant hypotheses, repairing flawed strategy mid-attempt, finding witness counterexamples. The TTT loop literally makes it learn during deployment.

**However, Aristotle alone has not yet demonstrated solving a previously open research-level problem entirely without informal-reasoning collaboration.** The strongest results — Erdős #728, Polya-Szego — used GPT-5.2 Pro or DeepSeek as a co-pilot. The Tao counterexamples, Erdős #124, Erdős #481, and Mathlib contributions are the cleanest "Aristotle alone" cases, and these are mostly competition-style problems or false-statement detection rather than open research conjectures.

**Bottom line for the project**: Aristotle CAN solve novel problems, especially when paired with a strong informal reasoner. The gap-targeting strategy in this codebase (state bare gap, let Aristotle find path) is asking Aristotle to do BOTH the informal reasoning AND the formal proof. The evidence suggests Aristotle benefits enormously from having an informal strategy provided. The current pipeline may be under-utilizing the system by withholding strategy hints that Aristotle is documented to use successfully.

---

## Cited URLs

1. [arXiv:2510.01346 — Aristotle: IMO-level Automated Theorem Proving (paper)](https://arxiv.org/abs/2510.01346)
2. [arXiv:2510.01346 HTML — same paper](https://arxiv.org/html/2510.01346v1)
3. [arXiv:2601.07421 — Resolution of Erdős Problem #728](https://arxiv.org/abs/2601.07421)
4. [arXiv:2601.07421 HTML](https://arxiv.org/html/2601.07421v1)
5. [Erdős Problems thread on #124](https://www.erdosproblems.com/forum/thread/124)
6. [Erdős Problems thread on #728](https://www.erdosproblems.com/forum/thread/728)
7. [Polya-Szego + Aristotle by Igor Rivin](https://igorrivin.github.io/research/polya-szego-aristotle/)
8. [Mindplex on Erdős #124 claim](https://magazine.mindplex.ai/post/harmonics-ai-aristotle-claims-solution-to-historic-math-puzzle)
9. [OpenAI on GPT-5 mathematical discovery (Ryu)](https://openai.com/index/gpt-5-mathematical-discovery/)
10. [OpenAI on GPT-5.2 for science and math](https://openai.com/index/gpt-5-2-for-science-and-math/)
11. [Mathematical research with GPT-5: Malliavin-Stein](https://arxiv.org/abs/2509.03065)
12. [GPT-5.4 FrontierMath open problem](https://www.remio.ai/post/gpt-5-4-solves-its-first-open-math-problem-from-frontiermath-benchmark)
13. [AlphaProof Nexus 9 Erdős problems](https://officechai.com/ai/google-deepminds-alphaproof-nexus-agent-has-solved-9-open-erdos-problems-at-a-cost-of-a-few-hundred-dollars-each/)
14. [DeepMind AlphaProof IMO 2024 silver](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
15. [AI contributions to Erdős problems wiki (Tao)](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
16. [Mindplex/Implicator on Harmonic $1.45B valuation](https://www.implicator.ai/ai-cracked-research-math-harmonic-just-priced-the-consequence-at-1-45-billion/)
17. [Xena Project — Formalization of Erdős problems](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/)
18. [Emergent Mind on Aristotle](https://www.emergentmind.com/topics/aristotle-imo-level-automated-theorem-proving)
19. [Cambridge CS seminar — Aristotle](https://www.cst.cam.ac.uk/seminars/list/243277)
20. [SiliconAngle on Harmonic $100M raise](https://siliconangle.com/2025/07/10/harmonic-raises-100m-nearly-900m-valuation-scale-ai-model-formal-mathematical-reasoning/)
21. [Endroid on Aristotle hallucination-free claim](https://endroid.com/2025/harmonic-launches-aristotle-app-claiming-hallucination-free-ai-math-answers/)
22. [Crypto Briefing — AlphaProof Nexus](https://cryptobriefing.com/deepmind-alphaproof-nexus-erdos-problems/)
23. [VentureBeat on Lean4 as AI competitive edge](https://venturebeat.com/technology/lean4-how-the-theorem-prover-works-and-why-its-the-new-competitive-edge-in)
