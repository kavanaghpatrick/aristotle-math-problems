# Forensic Web Research: Aristotle-credited Erdős Results

Agent W4, dated 2026-05-30. Investigates the actual proof content, role-split, and novelty of every Aristotle-credited Erdős solution we could find evidence for.

## TL;DR

- **The flagship "GPT-5.2 Pro + Aristotle" pipeline is a strict math/formalization split.** GPT-5.2 Pro (or GPT-5.5 Pro, Claude Opus 4.7, Gemini 3 Flash, etc.) produces the *mathematical argument* (informal proof in LaTeX/English). Aristotle's job is to *autoformalize* that argument into Lean 4 + close the residual gaps. Aristotle is not the mathematical author.
- **Aristotle *does* have a separate "autonomous" mode** where it works from the formal Lean statement alone. The flagship example is **Erdős #124**, where Aristotle independently rediscovered that the (loosely-stated) problem is a corollary of Brown's criterion. Plus a *small constellation* of others (#264, #488, #679, #958, #966, #1007, #1026, #1043, #1047, #1048, #1095) — these are mostly *new proofs of already-known results*, formalized from scratch.
- **Aletheia (Google DeepMind) is a separate system** based on Gemini Deep Think. Erdős #1051 is its flagship autonomous result; Aletheia is *not* Aristotle. Conflating them is a category error.
- **The actual Lean code is public and substantial.** `plby/lean-proofs` on GitHub. Erdős #728b is 1422 lines; #1026 is 3658 lines; #124b is 407 lines; #1043 is 225 lines. Brown's criterion in #124 is *reproven from scratch*, not imported.

---

## Per-problem forensic file

### Erdős #728 — "first AI-solved Erdős problem"

- **Date:** Jan 4-6, 2026 (formal verification); Jan 8, 2026 (Tao's endorsement).
- **Role split:** Kevin Barreto prompts GPT-5.2 Pro → GPT-5.2 Pro generates *informal proof* (probabilistic-method argument using Kummer's theorem + carry counts on `C(2m,m)` mod prime powers) → Aristotle *autoformalizes* into Lean (with errors auto-corrected). Boris Alexeev re-ran Aristotle on Jan 6 to *simplify* the proof.
- **Mathematical author:** GPT-5.2 Pro (the proof strategy is GPT-5.2 Pro's). Aristotle does formalization-with-gap-filling, not mathematical invention.
- **Novelty:** *Marginal.* The overall strategy is "similar to results regarding divisors of `C(2n,n)` studied earlier by Erdős and by Pomerance" — Tao said the proof was "inspired by Pomerance" but the specific theorem is not literally in the literature. KoishiChan (community literature hunter) failed to find a direct prior reference.
- **Depth:** Real probabilistic-method argument with explicit carry-rich/spike-free Diophantine construction. Lean proof is 1422 lines. Genuine combinatorial number theory.
- **Caveats:** Erdős' original 1975 statement was *ambiguous* and admitted trivial solutions; the version Aristotle solved is the "intended" reformulation after community clarification.
- **Sources:**
  - [arXiv 2601.07421](https://arxiv.org/abs/2601.07421) — official writeup by Nat Sothanaphan, Jan 12, 2026.
  - [erdosproblems.com forum thread 728](https://www.erdosproblems.com/forum/thread/728)
  - [the-decoder.com](https://the-decoder.com/terence-tao-says-gpt-5-2-pro-cracked-an-erdos-problem-but-warns-the-win-says-more-about-speed-than-difficulty/) — Tao's "speed not difficulty" comment.
  - Lean code: `https://raw.githubusercontent.com/plby/lean-proofs/main/src/v4.24.0/ErdosProblems/Erdos728b.lean` (1422 lines)

### Erdős #457 — q(n,log n) bound

- **Date:** March 2, 2026.
- **Role split:** GPT-5.2 Pro spots a tightening (only need `n` within `k/2` of being divisible by primes in `[k, Ak]`, achievable via Dirichlet approximation) → Aristotle autoformalizes.
- **Mathematical author:** GPT-5.2 Pro.
- **Novelty:** Moderate — Bloom flagged that the problem as stated is "very easy" and that Erdős' actual intent (in [Er79d]) was likely the *opposite-direction* inequality. So Aristotle solved a possibly-mis-stated problem.
- **Depth:** Improves the bound from `O(A)^{O(k)}` to `O(A)^{O(Ak/log k)}` using Dirichlet approximation — a clean elementary improvement, not deep.
- **Sources:**
  - [erdosproblems.com forum thread 457](https://www.erdosproblems.com/forum/thread/457)
  - [GitHub AI-contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)

### Erdős #1051 — irrationality of `Σ 1/(a_n a_{n+1})`

- **CRITICAL: This is NOT Aristotle.** Solved by **Aletheia** (Google DeepMind, built on Gemini Deep Think), then formalized in Lean 4 by Barreto.
- **Date:** Jan 2026 initial discovery; published Mar 2026 in arXiv 2602.10177 + 2601.22401.
- **Role split:** Aletheia autonomously produced the proof from prose statement; consensus from 5 mathematicians was 4-1 acceptable; the one rejected step ("standard comparison theorems for linear recurrences imply…") was patched in an ablation re-run.
- **Mathematical author:** Aletheia (Gemini Deep Think backbone).
- **Novelty:** *Genuine.* The DeepMind team rates this as one of only 4 "autonomous resolutions" (vs ~700 problems screened). Solution not directly inspired by prior arguments though uses classical idea (Mahler's criterion on series tail).
- **Depth:** Real analytic number theory. Proof by contradiction assuming `S' = p/q`, recurrence `b_{n+1} K_n = q P_{n-1} + K_{n+1}`, growth bound `P_{n+1} ≤ C P_n^2`, conclude `Π ≥ L^3` contradicting `L > 1`. Followed up by a real research paper (BKKKZ26 = Barreto/Kang/Kim/Kovač/Zhang generalization).
- **Sources:**
  - [arXiv 2601.22401](https://arxiv.org/html/2601.22401v3) — DeepMind "Semi-Autonomous Mathematics Discovery with Gemini" paper.
  - [math.berkeley.edu Aletheia.pdf](https://math.berkeley.edu/~fengt/Aletheia.pdf) — Tony Feng talk slides.
  - [DeepMind superhuman/aletheia GitHub](https://github.com/google-deepmind/superhuman/blob/main/aletheia/README.md)

### Erdős #729 — sibling of #728

- **Date:** Jan 2026.
- **Role split:** Same as #728. GPT-5.2 Pro produces "adapted" argument; Aristotle struggles to formalize a key lemma (`exists_good_m_medium_primes`), threshold `t_p` is taken twice as large as in informal proof. Eventually corrected.
- **Novelty:** Same family as #728. Tao describes the entire family as "lowest hanging fruit."

### Erdős #397 — central binomial coefficient equation

- **Date:** Jan 2026.
- **Role split:** Neel Somani prompts GPT-5.2 Pro → proof → Aristotle formalizes.
- **Novelty:** *Matched China TST 2012* — i.e., the proof was a known competition problem result. Not novel mathematics, but novel formalization.

### Erdős #635 — Elliott (1979) restatement

- **Date:** Jan 2026.
- **Role split:** GPT-5.2 Pro thinks for 50 minutes → informal proof in LaTeX → Aristotle formalizes (Acer Fur cleaned up Lean).
- **Novelty:** *Largely matched Elliott (1979).* So: rediscovery, not breakthrough.

### Erdős #694 — Carmichael totient bound

- **Date:** May 1, 2026.
- **Role split:** Liam Price prompts **GPT-5.5 Pro** (note: not Aristotle).
- **Result:** Asymptotic `max f_max/f_min ~ (e^γ + o(1)) log log x`.
- **Caveat:** Lower bound uses Linnik's theorem nonexplicitly — community noted you cannot exhibit a concrete pair without fixing Linnik's constants.

### Erdős #741

- **Date:** March 31, 2026 (partial); April 16, 2026 (full).
- **Role split:** DeepMind prover agent + OpenAI internal model. **No Aristotle involvement.**

### Erdős #1026 — c(k²) = 1/k, rectangle packing

- **Date:** Dec 7, 2025.
- **Role split:** Boris Alexeev runs Aristotle "alone" (only formal statement input) → autonomous Lean proof. *But also* Desmond Weisenberg/Stijn Cambie/Wouter van Doorn formulated the problem, KoishiChan/AlphaEvolve/literature search provided complementary parts.
- **Novelty:** *Not novel.* Tao explicitly: "the proof turned out to not be particularly novel." Already in Tidor/Wang/Yang (2016 paper) and reduces to a Seidenberg 1959 packing argument that Aristotle was "likely aware of through training data."
- **Depth:** Lean proof is 3658 lines, real combinatorial geometry. Strong formalization.

### Erdős #124 — Brown's criterion variant (BEST AUTONOMOUS EVIDENCE)

- **Date:** Late 2025.
- **Role split:** **Aristotle alone**, working only from the formal statement. No external LLM strategy provider. 6 hours of MCTS proof search.
- **Mathematical author:** Aristotle (genuinely).
- **Novelty:** *None* — Aristotle's contribution was to *notice* that Erdős' restated 1996/1997 hypothesis omits a key assumption, reducing the problem to Brown's criterion (known since the 1980s). Boris Alexeev/Tao note this was the actual scientific contribution: spotting that the stated problem is *not* the original hard one.
- **Depth:** Lean proof is 407 lines. Brown's criterion is *reproven from scratch* inside the file (not imported from Mathlib). Genuine inductive argument with constructive `u_seq` greedy sequence + base-`d` digit decomposition for subset-sum representation. Mix of real math + heavy automation (`aesop`, `nlinarith`, `grind`, `set_option maxHeartbeats 0`).
- **Sources:**
  - [plby/lean-proofs Erdos124b.lean](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos124b.lean)
  - [Xena Project blog by Alexeev](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/)
  - [eu.36kr.com](https://eu.36kr.com/en/p/3576638922980231) — Tao's commentary on the "weaker variant" caveat.

### Other "Aristotle alone" problems (all on plby/lean-proofs)

Per the wiki, the following are credited "Aristotle alone" (no co-LLM):
- **#43**: new partial-result proof, building on Barreto (2025)
- **#264**: new partial proof
- **#488**: solution to variant (Stijn Cambie also independently found counterexample)
- **#481**: autonomous (also solved independently by Klarner 1982)
- **#679**: improved proof
- **#958**: new proof
- **#966**: full solution (matched Spencer, unpublished)
- **#1007**: new proof (matched House 2013, Chaffee/Noble 2016)
- **#1026**: see above (matched Tidor/Wang/Yang 2016)
- **#1043**: new proof (matched Pommerenke 1961) — Lean proof is 225 lines, very compact
- **#1047**: new proof (matched Goodman 1966)
- **#1048**: special case of Pommerenke 1961
- **#1077**: trivial counterexample to a faulty formulation
- **#1095**: new partial proof
- Plus ~95 *formalizations* of existing proofs (sections 2(a)/2(b) of the wiki) where Aristotle is auto-formalizing already-known arguments.

**Pattern:** Almost all of these are *new Lean proofs of known mathematical results.* The "math is novel" arm is essentially empty for Aristotle-alone runs. Aristotle's autonomous mode produces **strong formalizations**, not mathematical discoveries.

### Other AI systems active in same space (not Aristotle)

- **AlphaProof / DeepMind prover agent**: Solved #198, #730, #741 (and 9 out of 353 in May 2026 [AlphaProof Nexus, arXiv 2605.22763](https://arxiv.org/html/2605.22763v1)).
- **Aletheia (DeepMind)**: 4 autonomous resolutions, including #652, #654, #1040, #1051.
- **AlphaEvolve**: Contributed upper-bound constructions on #1026.
- **OpenAI internal model**: Partial result on #741 (March 2026).

---

## Specific to "GPT-5.2 Pro + Aristotle": who did what?

**Authoritative answer from arXiv 2601.07421 + Tao's blog + Mindplex coverage:**

> "Kevin Barreto announced that he had a proof from the AI system Aristotle by Harmonic. This is a Lean system, and the input to Aristotle was based on an informal argument from GPT-5.2 Pro."

GPT-5.2 Pro is *unambiguously* the mathematical author for #728, #729, #397, #457, #635, #897, #1197. Aristotle is the *Lean autoformalizer* with some auto-correction capability when the informal proof has minor errors. In #729, Aristotle "produced a mess of spaghetti Lean code" and could not close `exists_good_m_medium_primes`; the informal proof had to be re-examined.

Aristotle's *value-add* over a pure proof-checker is:
1. It can fill in residual minor gaps in the informal proof (the way a strong proof assistant + auto-tactic stack would).
2. It can be invoked autonomously from a formal statement alone (#124, #264, etc.) — but in those runs the math is essentially always already-known.

It is **not** the case that Aristotle is the mathematical author of the "GPT-5.2 Pro + Aristotle" Erdős results.

---

## Repo evidence

- **plby/lean-proofs** (Boris Alexeev): Public repo containing Lean files for ~95 Erdős problems. Includes Erdos124b.lean, Erdos728b.lean, Erdos1026.lean, Erdos1043.lean, Erdos1047.lean, etc.
  - Each file's header explicitly credits Aristotle and notes whether it was Aristotle-alone or Aristotle+GPT.
  - Lean toolchain v4.24.0, Mathlib f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- **github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems**: Tao's wiki, the authoritative tracker.
- **github.com/google-deepmind/superhuman/aletheia**: Aletheia's own repo (separate from Aristotle entirely).

---

## Depth assessment summary table

| Problem | Aristotle role | Math author | Novelty | Lean lines | Verdict |
|---|---|---|---|---|---|
| #728 | autoformalize | GPT-5.2 Pro | marginal (Pomerance-style) | 1422 | real math by GPT, strong formalization by Aristotle |
| #729 | autoformalize (rough) | GPT-5.2 Pro | low (adapted #728) | ? | derived |
| #397 | autoformalize | GPT-5.2 Pro | none (China TST 2012) | ? | known result rediscovered |
| #457 | autoformalize | GPT-5.2 Pro | low (elementary) | ? | possibly mis-stated problem |
| #635 | autoformalize | GPT-5.2 Pro | none (Elliott 1979) | ? | known result rediscovered |
| #1197 | autoformalize | GPT-5.4 Pro | ? | ? | unclear |
| #897 | autoformalize | Archivara | none (Wirsing 1981) | ? | known result rediscovered |
| **#124** | **autonomous** | **Aristotle** | **none** (Brown's criterion + spotting weak hypothesis) | **407** | **best autonomous evidence — math is known but proof is reconstructed from scratch** |
| #1026 | autonomous | Aristotle | none (Tidor/Wang/Yang 2016) | 3658 | strong formalization, not novel math |
| #1043 | autonomous | Aristotle | none (Pommerenke 1961) | 225 | very compact rediscovery |
| #1047 | autonomous | Aristotle | none (Goodman 1966) | ? | rediscovery |
| #1048 | autonomous | Aristotle | none (Pommerenke 1961, special case) | ? | rediscovery |
| #1007 | autonomous | Aristotle | none (House 2013) | ? | rediscovery |
| #966 | autonomous | Aristotle | none (Spencer, unpublished) | ? | rediscovery |
| #1051 (NOT Aristotle) | n/a | Aletheia | genuine | n/a | real math, but by Aletheia/Gemini Deep Think |

---

## Verdict on the fraction "real math vs strong formalization"

Among Aristotle-credited Erdős results (n ≈ 25-30 confirmed):
- **~0% are novel math authored by Aristotle.** Every "Aristotle alone" autonomous solve matches a prior literature result — Aristotle is finding the proof from scratch but the *theorem* is already in literature (the only ambiguity is #124, where the "result" itself is a corollary of Brown's criterion that nobody had pointed out).
- **~80% are strong formalization assistance to a GPT-family mathematical argument.** GPT-5.2 Pro / GPT-5.5 Pro / Claude Opus 4.7 etc. provide the math; Aristotle auto-formalizes with some gap-filling.
- **~20% are autonomous Lean proofs of already-known results** with no novel math, but a non-trivial formalization effort (e.g., 3658 lines for #1026, 407 for #124).

**Net: Aristotle is *not* a mathematician. It is a *strong proof-search-plus-autoformalizer.*** When credited with "GPT-5.2 Pro + Aristotle," it is doing the formalization. When credited alone, it is producing a Lean proof of an existing result starting only from the formal statement.

**Best-evidence autonomous reasoning:** Erdős #124, where Aristotle independently found that a problem Erdős had restated in 1996/1997 was a corollary of Brown's criterion. Even here, the contribution is "noticing that the restated problem became easy" + reproving Brown's criterion from scratch — not creating new mathematics.

**Worst-evidence "solution":** Erdős #397, where the proof matches China TST 2012 — Aristotle (with GPT-5.2 Pro) effectively reproved a known competition problem.

---

## Most useful problem for our project to study in detail

**Erdős #1026** — `https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1026.lean`

Why:
1. 3658 lines of Lean — by far the largest "Aristotle alone" file, so we can examine the full footprint of what Aristotle's autoformalization machinery produces.
2. Header explicitly documents the collaborative process: Alexeev + Aristotle + KoishiChan + Tao + AlphaEvolve + Lawrence Wu + literature (Baek/Koizumi/Ueoro + Praton + Wagner).
3. Reduces to Seidenberg's 1959 packing argument — a *non-trivial* classical mathematical structure that Aristotle had to *reconstruct* in Lean. So this is the best window into "what does Aristotle's automation actually do when the math is real and non-elementary?"
4. Has companion blog post by Tao with detailed role-split commentary.

URL: https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1026.lean
Companion: https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/

---

## Sources

- [arXiv 2601.07421 — Resolution of Erdős Problem #728](https://arxiv.org/abs/2601.07421)
- [arXiv 2601.22401 — Semi-Autonomous Mathematics Discovery with Gemini (Aletheia paper)](https://arxiv.org/html/2601.22401v3)
- [arXiv 2602.10177 — Towards Autonomous Mathematics Research](https://arxiv.org/html/2602.10177)
- [arXiv 2510.01346 — Aristotle: IMO-level Automated Theorem Proving](https://arxiv.org/pdf/2510.01346)
- [arXiv 2605.22763 — Advancing Mathematics Research with AI-Driven Formal Proof Search (AlphaProof Nexus)](https://arxiv.org/html/2605.22763v1)
- [github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- [github.com/plby/lean-proofs](https://github.com/plby/lean-proofs)
- [github.com/google-deepmind/superhuman/aletheia](https://github.com/google-deepmind/superhuman/blob/main/aletheia/README.md)
- [Terence Tao's blog on Erdős #1026](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/)
- [Xena Project — Alexeev guest post on Erdős formalization](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/)
- [erdosproblems.com forum thread 728](https://www.erdosproblems.com/forum/thread/728)
- [erdosproblems.com forum thread 457](https://www.erdosproblems.com/forum/thread/457)
- [erdosproblems.com forum thread 694](https://www.erdosproblems.com/forum/thread/694)
- [erdosproblems.com forum thread 124](https://www.erdosproblems.com/forum/thread/124)
- [the-decoder.com — Tao on GPT-5.2 Pro speed vs difficulty](https://the-decoder.com/terence-tao-says-gpt-5-2-pro-cracked-an-erdos-problem-but-warns-the-win-says-more-about-speed-than-difficulty/)
- [techcrunch.com 2026-05-20 — OpenAI 80-year-old math problem](https://techcrunch.com/2026/05/20/openai-claims-it-solved-an-80-year-old-math-problem-for-real-this-time/)
- [Mindplex — Harmonic Aristotle](https://magazine.mindplex.ai/post/harmonics-ai-aristotle-claims-solution-to-historic-math-puzzle)
- [Varsity — Kevin Barreto profile](https://www.varsity.co.uk/science/31116)
- [emergentmind.com — Erdős #728 summary](https://www.emergentmind.com/papers/2601.07421)
- [aigazine.com — Erdős #729 coverage](https://aigazine.com/llms/gpt52-pro-cracks-729th-erds-problem-in-major-ai-reasoning-leap--v)
