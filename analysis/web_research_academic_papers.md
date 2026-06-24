# Web Research: Academic Papers on Lean+LLM Producing Novel Mathematics (2024-2026)

Research agent W5 -- compiled May 30, 2026.

---

## 1. Foundational Papers

### Polu and Sutskever 2020 -- "Generative Language Modeling for Automated Theorem Proving" (arXiv:2009.03393)
- Introduced GPT-f for Metamath.
- KEY ACHIEVEMENT: GPT-f found new short proofs accepted into the Metamath library -- "the first time a deep learning based system has contributed proofs that were adopted by a formal mathematics community."
- Scope: short proof shortenings, not open conjectures.
- URL: https://arxiv.org/abs/2009.03393

### Yang et al 2023 -- LeanDojo (arXiv:2306.15626, NeurIPS 2023)
- Open-source Lean toolkit + ReProver (retrieval-augmented prover).
- ReProver: ~51% solve rate Pass@1 on LeanDojo Benchmark random split, drops on novel_premises split.
- Built for benchmark performance, not novel-result generation.
- URL: https://arxiv.org/abs/2306.15626 ; https://leandojo.org

---

## 2. 2025 LLM-based Lean Provers (Benchmark-Focused)

### DeepSeek-Prover-V2 (arXiv:2504.21801, April 2025)
- 671B param, 88.9% on MiniF2F-test, 49/658 on PutnamBench.
- Recursive subgoal decomposition via DeepSeek-V3.
- Introduces ProverBench (325 problems incl. 15 AIME 2024-25).
- Did NOT produce novel published mathematics. Solved competition problems.
- URL: https://arxiv.org/abs/2504.21801

### Kimina-Prover Preview (arXiv:2504.11354, April 2025)
- 72B, Qwen2.5 backbone, 80.7% on MiniF2F pass@8192.
- Reasoning-driven exploration. First to show clear scaling with model size in neural theorem proving.
- Benchmark-only.
- URL: https://arxiv.org/abs/2504.11354

### Goedel-Prover-V2 (arXiv:2508.03613, August 2025)
- Strongest open-source prover at release. Scaffolded data synthesis + self-correction.
- Iterates against Lean compiler feedback (similar architecture to our `/codex-prove`).
- Benchmark-only.
- URL: https://arxiv.org/abs/2508.03613

### LeanConjecturer (arXiv:2506.22005, June 2025)
- Auto-generates university-level conjectures in Lean 4. 12,289 conjectures from 40 Mathlib seed files; 3,776 non-trivial.
- Generates training data, not novel theorems.
- URL: https://arxiv.org/abs/2506.22005

### "Discovering New Theorems via LLMs with In-Context Proof Learning in Lean" -- CPL (arXiv:2509.14274, September 2025)
- Conjecturing-Proving Loop: iteratively conjecture + prove in Lean, condition on prior proofs.
- Most directly relevant prior work: explicitly targets "novel theorems."
- Claims experimental evidence that CPL increases discovery rate of hard-to-prove theorems via self-generated in-context learning.
- Caveat: "novel" here means theorems the LLM hasn't seen, not novel research mathematics.
- URL: https://arxiv.org/abs/2509.14274

### Self-play Theorem Prover (STP) -- Dong & Ma 2025
- LLM as both "conjecturer" and "prover." Dual-role dynamic curriculum.
- Architectural template for combined sketch/prove pipelines.

---

## 3. Systems With Documented NOVEL Research Math Output (Lean-verified)

### Aristotle (Harmonic) -- arXiv:2510.01346, October 2025
- Achieved gold-medal-level IMO 2025 with FORMAL Lean proofs (5/6 problems). Google DeepMind and OpenAI also got gold but with natural-language proofs only.
- Combines: (1) Lean proof search via Monte Carlo Graph Search with transformer policy, (2) informal reasoning that generates and formalizes lemmas, (3) geometry solver.
- 200B+ params. Dynamic test-time training.
- CLAIMS NOVEL CONTRIBUTIONS: "novel contributions to Mathlib, formalized proofs for long-standing open conjectures including Erdős Problems 1026 and 728, and identified subtle logical errors within established academic textbooks."
- URL: https://arxiv.org/abs/2510.01346 ; https://github.com/harmonic-ai/IMO2025

### Erdős Problem #728 Resolution -- arXiv:2601.07421
- "First Erdős problem regarded as fully resolved autonomously by an AI system."
- System: GPT-5.2 Pro (OpenAI) + Aristotle (Harmonic), operated by Kevin Barreto.
- Final result is a formal Lean proof. Human role: operator + translator to informal write-up (Nat Sothanaphan).
- Uses Kummer's theorem + carry-counting in base-p expansions. Method "resembles results regarding divisors of (2n choose n) studied earlier by Erdős and by Pomerance."
- URL: https://arxiv.org/abs/2601.07421

### Erdős Problem #124 -- Aristotle solo, November 2025
- Aristotle solved problem #124 (or "124.1," the easier of two variants) AUTONOMOUSLY from the formal statement. 6 hours search, 1 minute verification.
- Thomas Bloom (Erdős problems site maintainer): solution is "elementary," comparable to a competition problem.
- "The proof Aristotle found for 124 ... is not a 'proof from the Book'."
- 30-year-old conjecture (Burr, Erdős, Graham, Li 1995).
- URL: https://www.erdosproblems.com/forum/thread/124

### AlphaEvolve + AlphaProof + Deep Think -- Georgiev, Gómez-Serrano, Tao, Wagner (arXiv:2511.02864, November 2025)
- "Mathematical exploration and discovery at scale."
- 67 problems across analysis, combinatorics, geometry, NT. Rediscovered SOTA in ~75% of cases; IMPROVED in ~20%.
- End-to-end verified pipeline: AlphaEvolve discovers -> Deep Think formalizes informal proof -> AlphaProof produces verified Lean.
- Specific verified novelty: finite-field Kakeya conjecture improved bounds; Nikodym set construction (inspired Tao's separate paper).
- URL: https://arxiv.org/abs/2511.02864

### Donald Knuth + Claude Opus 4.6, March 2026
- Claude solved an open graph theory problem Knuth had worked on for weeks.
- Solution was natural-language. Kim Morrison (Lean community) formalized the construction in Lean shortly after.
- URL referenced: https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf

---

## 4. Terence Tao's Position (Critical Authority)

### Direct Quotes

**On Erdős Problem 613 (Tao's own vibe-coded Lean formalization), October 21, 2025 (Mastodon):**
> "Inspired by the recent successful 'vibe coding' in Lean of a solution to an Erdős problem"
> -- Tao formalized Pikhurko's 2001 disproof: a 44-edge graph on 15 vertices. ~1 week of work. 1125 lines of Lean. ChatGPT Pro acted as "translator/assistant" to convert informal proof to Lean.
> NOTE: This is FORMALIZATION of an existing proof, not novel discovery.
> URL: https://mathstodon.xyz/@tao/115493667607261044

**On AI in the long tail (November 30, 2025):**
> "the class of open problems in mathematics has a 'long tail' -- a large number of problems which would be relatively easy to prove or disprove, but which have not received significant attention from the (limited) number of expert mathematicians available."
> "the scalable nature of AI systems makes them 'better suited for being systematically applied to the long tail of obscure Erdős problems, many of which actually have straightforward solutions.'"
> "many of these easier Erdős problems are now more likely to be solved by purely AI-based methods than by human or hybrid means."
> Empirical example: Equational Theories Project resolved 22 million implications in universal algebra "within days."
> URL: https://mathstodon.xyz/@tao/115639983683442577

**On the difficulty boundary (from arXiv:2511.02864 blog):**
> "We believe that tools like AlphaEvolve will be most effective on the 'long tail' of the large number of less well known, but perhaps not extremely difficult, problems in a field, as the number of such problems often exceeds the number of human experts who are willing to devote time to such problems, even when the techniques needed to solve these problems are likely somewhere in the literature for related problems already."

**On limitations for famous open conjectures (AlphaEvolve paper):**
> For Sidorenko's and Sendov's conjectures: "AlphaEvolve generally was able to locate the previously known candidates for optimizers... but did not locate any stronger counterexamples"
> For analytic number theory: "it struggled to take advantage of the number theoretic structure in the problem, even when given suitable expert hints"

**On AGI skepticism (Mastodon, late 2025):**
> "I doubt that anything resembling genuine 'artificial general cleverness'..." (post mathstodon.xyz/@tao/115722360006034040 -- exact quote requires direct fetch)

### Tao's Position Summary
1. AI + Lean is REAL and productive RIGHT NOW for the long tail.
2. "AI is beginning to find success in the 'long tail' of open mathematical problems" (Nov 30, 2025).
3. Tao verifies these proofs himself ("Three Erdős Problems Fell in Seven Days, and Terence Tao Verified Every Proof Himself" -- Medium, March 2026).
4. AI struggles with deep famous conjectures requiring genuinely new techniques.
5. The "easy long tail" is exactly the regime where AI works: problems where the technique is in the literature but no human has bothered to apply it.

---

## 5. Mainstream Press / Community Tracking

- Quanta Magazine, April 2026: "The AI Revolution in Math Has Arrived" (https://www.quantamagazine.org/the-ai-revolution-in-math-has-arrived-20260413/)
- Erdős Problems site AI Contributions wiki: tracks every AI-credited solution (https://www.erdosproblems.com/forum/thread/AI%20Contributions)
- TechCrunch Jan 2026: "AI models are starting to crack high-level math problems"
- Per Tao: since late 2025, "over a dozen previously open mathematical problems have been moved to 'solved' status with AI models credited in the solutions."
- Tao accepted GPT-5.2 proof for Erdős Problem #397 (verified via Lean).

---

## 6. Does the literature support "Aristotle should solve, not just formalize"?

**YES, strongly.** Evidence:

1. The Aristotle paper (arXiv:2510.01346) IS Harmonic explicitly positioning their system as solving, not just formalizing. They state Aristotle made "novel contributions to Mathlib, formalized proofs for long-standing open conjectures including Erdős Problems 1026 and 728."
2. Erdős #124 was solved by Aristotle "all by itself, working only from the formal statement" -- exactly our pipeline ("bare gap, Aristotle finds the path").
3. Erdős #728 (arXiv:2601.07421) explicitly documents the first autonomous AI solution to an Erdős problem -- using Aristotle + GPT-5.2 Pro.
4. Tao's own position: long-tail Erdős problems are EXACTLY where AI-from-bare-statement works.
5. AlphaEvolve paper (arXiv:2511.02864) demonstrates the same paradigm at scale: 20% of 67 open problems improved.

The literature DIRECTLY validates the math-forge pipeline thesis.

**Anti-evidence / caveats:**
- Aristotle's #124 proof was elementary; Bloom: "not a proof from the Book."
- Most "novel" results are in the long tail, not deep conjectures.
- The Conjecturing-Proving Loop paper (2509.14274) defines "novel" weakly (LLM-new, not literature-new).
- Tao: AlphaEvolve doesn't crack famous conjectures, just variants and long-tail.

---

## 7. Single Most Important Paper For This Project

**arXiv:2510.01346 -- "Aristotle: IMO-level Automated Theorem Proving" (Harmonic Team, October 2025)**

This is the paper documenting the exact system we are submitting to. It explicitly states the design philosophy:
- "A problem is only considered solved if the system produces a complete proof using the Lean 4 proof language and its mathematical library Mathlib, without gaps or unsound axioms like sorryAx."
- It explicitly claims novel contributions on Erdős #1026 and #728.
- Architecture description (MCGS + informal reasoner + Lean proof search) tells us exactly what context to attach in INFORMAL submissions.

**Companion paper**: arXiv:2601.07421 (Erdős #728 writeup) -- this is the concrete proof-of-concept that the pipeline works on the same problem class we are targeting.

---

## Sources

- Aristotle (Harmonic): https://arxiv.org/abs/2510.01346
- Erdős #728 Resolution: https://arxiv.org/abs/2601.07421
- AlphaEvolve / Tao et al (Mathematical Exploration at Scale): https://arxiv.org/abs/2511.02864
- DeepSeek-Prover-V2: https://arxiv.org/abs/2504.21801
- Kimina-Prover: https://arxiv.org/abs/2504.11354
- Goedel-Prover-V2: https://arxiv.org/abs/2508.03613
- LeanConjecturer: https://arxiv.org/abs/2506.22005
- CPL (Discovering New Theorems): https://arxiv.org/abs/2509.14274
- LeanDojo: https://arxiv.org/abs/2306.15626
- Polu+Sutskever GPT-f: https://arxiv.org/abs/2009.03393
- Tao's Mastodon (long tail): https://mathstodon.xyz/@tao/115639983683442577
- Tao's Mastodon (vibe coding Erdős 613): https://mathstodon.xyz/@tao/115493667607261044
- Tao's Mastodon archive: https://terrytao.wordpress.com/mastodon-posts/
- Tao's AlphaEvolve blog: https://terrytao.wordpress.com/2025/11/05/mathematical-exploration-and-discovery-at-scale/
- Quanta "AI Revolution in Math": https://www.quantamagazine.org/the-ai-revolution-in-math-has-arrived-20260413/
- Erdős Problems #124 thread: https://www.erdosproblems.com/forum/thread/124
- Erdős Problems AI Contributions wiki: https://www.erdosproblems.com/forum/thread/AI%20Contributions
- Knuth's "Claude's Cycles": https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf
- AlphaProof Nature paper: https://www.nature.com/articles/s41586-025-09833-y
