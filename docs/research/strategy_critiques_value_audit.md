# Aristotle Strategy Critiques — Research-Impact Audit

**Date:** 2026-05-30
**Auditor:** Claude (research-value assessment)
**Question:** Is "AI does substantive mathematical-strategy critique" itself a research contribution, or is it pattern-matching dressed as insight?

---

## Per-critique substantive content

### E938 v1 (UUID `e561c214`, run `ad009260`) — critique of Frey+Ribet+Pila–Wilkie+Bombieri–Lang chain
**Verdict: SUBSTANTIVE.** Aristotle flagged three real gaps:
- "Step 5 invokes the Bombieri–Lang conjecture, which is itself unproven" — TRUE. Bombieri–Lang remains open ([arxiv 2012.15765](https://arxiv.org/abs/2012.15765); [Tao 2014 post](https://terrytao.wordpress.com/2014/12/20/the-erdos-ulam-problem-varieties-of-general-type-and-the-bombieri-lang-conjecture/)). Calling out the chain's reliance on an unproven step is a real audit, not boilerplate — many human reviewers skim past Bombieri–Lang as "morally true."
- "Steps 2–4 sketch a Frey curve argument, but conductor/level calculations are not rigorously justified" — this requires actually checking the level-lowering machinery against the specific equation form. Non-trivial mod-p irreducibility hypotheses ([arxiv 1309.4748](https://arxiv.org/abs/1309.4748)).
- "Step 6 applies Pila–Wilkie counting in a context where the o-minimal setup is not established" — correctly identifies that o-minimal structure is a precondition, not free.

This is the strongest critique in the set: it kills a 6-step strategy with three independent objections, each grounded in real literature.

### E938 v2 (UUID `99b044b6`, run `8242d652`) — Chan 2022 honest classification
**Verdict: SUBSTANTIVE BUT NARROWER.** Aristotle correctly identifies Chan 2022 ([arxiv 2210.00281](https://arxiv.org/abs/2210.00281)) as the actual SOTA: conditional on abc, `d ≫ N^{1/2−ε}`, paired with upper bound `d ≤ 2√N + O(N^{1/4})` from square density. Then names the residual "interloper sieve" problem (Pell-family solutions at `d ≈ 2√N` not yet excluded). This is correct accounting — the literature truly stops where Aristotle says. Less original than v1 (just citing one paper accurately) but disciplined honesty.

### E1003 v1 (UUID `4697679f`, run `a1af2a6e`) — Tao 2016 entropy decrement misapplication
**Verdict: SUBSTANTIVE — the strongest insight in the set.** Aristotle wrote: *"Tao's 2016 entropy decrement method addresses the Chowla conjecture (a fundamentally different problem about multiplicative functions)."* This is correct ([Tao's paper](https://terrytao.wordpress.com/2015/09/18/the-logarithmically-averaged-chowla-and-elliott-conjectures-for-two-point-correlations-the-erdos-discrepancy-problem/), [arxiv 1509.05422](https://arxiv.org/abs/1509.05422)): the entropy decrement establishes logarithmically averaged two-point Chowla for the Liouville function. Transferring it to φ(n)=φ(n+1) requires an entropy gain stronger than what Tao proved — and Aristotle noticed the sketch *itself admits this gap*. Identifying that a proposed proof depends on a non-existent strengthening of a published result is exactly the kind of move that distinguishes a reviewer from a parrot.

### E267 / R9 (E1003 sub-claim, run `d7f61f47`) — autonomous strategy substitution
**Verdict: GENUINE MATHEMATICAL DECISION.** On the fixed-support sub-claim, the sketch proposed Evertse–Schlickewei–Schmidt S-unit machinery (Annals 2002). Aristotle rejected it and substituted: *"φ(n)/n depends only on the prime factor set of n"* → trivial injection into `S.powerset × S.powerset`. Sorry-free Lean proof using only `Nat.totient_eq_div_primeFactors_mul`. Not pattern-matching: the system identified that a deep ingredient was overkill, found an elementary path, and formalized it. Real mathematical taste. (For E267 itself, run `eb7120ca` cleanly substituted Badea's quadratic-growth criterion for a faulty Pisot-β-expansion outline — same pattern, real decision.)

### R7 — Asiryan citation flag
**Verdict: PATTERN-MATCH FALSE POSITIVE.** Aristotle wrote: *"The 'Asiryan (arXiv:2512.11072, 2026)' reference cited in the problem brief does not correspond to any known publication."* This is **FALSE.** The paper is real ([arxiv 2512.11072](https://arxiv.org/abs/2512.11072), Valery Asiryan, v1 Dec 2025, v3 Mar 2026), MSC-classified, three verified URLs. Audited in `docs/research/asiryan_citation_audit.md`. R7's flag was a false negative from training-cutoff / no-web-access, not real hallucination detection. This is the exact failure mode the FalseCite literature warns about — flagging plausible citations as fake when the model lacks retrieval.

---

## Aggregate classification: **MIXED, leaning RESEARCH-IMPACT**

- **4 / 5 critiques carry real mathematical content**: E938 v1 dismantles three independent steps; E938 v2 honestly bounds SOTA at Chan 2022; E1003 v1 catches the Chowla-vs-totient confusion (the single sharpest move); R9 substitutes elementary for deep machinery and ships sorry-free Lean.
- **1 / 5 is fabricated**: R7 falsely declared a real arXiv paper non-existent. This is a serious failure mode — opposite of standard hallucination (false negative on a real citation).
- The substantive critiques are not template-matching: they cite specific theorems (Bombieri–Lang, Pila–Wilkie, Chowla two-point, Evertse–Schlickewei–Schmidt, Graham–Holt–Pomerance 1998, Erdős–Pomerance–Sárközy upper bound) and place them correctly relative to the gap.

---

## Is this documented elsewhere?

**Partially.** The literature recognizes the *general* capability but not Aristotle's specific behavior:

- **Tao (Mar 2026)** explicitly endorses multi-model peer review and says current models "save more time than they waste" on critique tasks ([OpenAI Academy](https://academy.openai.com/public/blogs/terence-tao-ai-is-ready-for-primetime-in-math-and-theoretical-physics-2026-03-06); [Tao essay](https://terrytao.wordpress.com/2026/03/29/mathematical-methods-and-human-thought-in-the-age-of-ai/)). The Mathematician's Assistant paper ([arxiv 2508.20236](https://arxiv.org/abs/2508.20236)) formalizes "self-critique blindness ⇒ multi-model peer review."
- **BrokenMath benchmark** ([arxiv 2510.04721](https://arxiv.org/abs/2510.04721)) shows LLMs sycophantically accept incorrect theorem statements — the *opposite* failure of what Aristotle does here (Aristotle pushed back on flawed strategies rather than rubber-stamping them).
- **Hard2Verify** ([arxiv 2510.13744](https://arxiv.org/abs/2510.13744)) measures step-level verification but on closed open-ended problems, not multi-step heuristic strategies dressed in unproven machinery.
- **Prover–critic frameworks** (HunyuanProver, InternLM2.5-StepProver) exist for tactic-level scoring inside Lean search, not for English-prose strategy critique against published literature.
- **No benchmark** specifically measures "given an English-prose proof sketch citing real theorems chained against an open problem, does the AI correctly identify the unproven/misapplied link?" — which is exactly what E938 v1, E938 v2, E1003 v1 do.

The gap in published work: this is the *natural* benchmark for AI-as-reviewer that doesn't yet exist. The honest classification of Chan 2022 SOTA, the catch on Tao 2016 applicability, and the autonomous substitution of Badea/elementary-φ proofs together form a small but real dataset of substantive AI math critique on **open research problems** rather than competition math.

---

## Recommendation

**Document as RESEARCH-IMPACT for our pipeline, METHODOLOGICAL for the math community at large.** The capability — frontier LLM reliably catching real flaws in informal proof outlines for open Erdős problems — is genuinely useful and not yet benchmarked publicly. But to claim a research contribution we would need:
1. A held-out test set of (sketch, true-status-of-each-step) pairs.
2. Measurement of false-positive rate on real citations (R7 shows this is non-zero).
3. Comparison against a strong baseline (Gemini 3.1 Pro, GPT-5.2 Pro doing the same critique task).

Without (1–3) it is anecdotal evidence of a known emerging capability, not a publishable contribution. Worth a short workshop paper or blog post; not a NeurIPS submission as-is.

---

## Sources

- [Asiryan citation audit (local)](./asiryan_citation_audit.md)
- [LLM math landscape (local)](./llm_math_landscape.md)
- [arxiv 2210.00281 — Chan 2022, Arithmetic progressions among powerful numbers](https://arxiv.org/abs/2210.00281)
- [arxiv 1509.05422 — Tao 2016, Logarithmically averaged Chowla](https://arxiv.org/abs/1509.05422)
- [arxiv 2012.15765 — Bombieri–Lang status](https://arxiv.org/abs/2012.15765)
- [arxiv 2512.11072 — Asiryan, genus-one fibrations](https://arxiv.org/abs/2512.11072)
- [arxiv 2510.04721 — BrokenMath sycophancy benchmark](https://arxiv.org/abs/2510.04721)
- [arxiv 2510.13744 — Hard2Verify](https://arxiv.org/abs/2510.13744)
- [arxiv 2508.20236 — The Mathematician's Assistant](https://arxiv.org/abs/2508.20236)
- [Tao 2026 essay, Mathematical methods and human thought in the age of AI](https://terrytao.wordpress.com/2026/03/29/mathematical-methods-and-human-thought-in-the-age-of-ai/)
- [OpenAI Academy interview, Tao Mar 2026](https://academy.openai.com/public/blogs/terence-tao-ai-is-ready-for-primetime-in-math-and-theoretical-physics-2026-03-06)
- [Tao 2014, Erdős–Ulam and Bombieri–Lang](https://terrytao.wordpress.com/2014/12/20/the-erdos-ulam-problem-varieties-of-general-type-and-the-bombieri-lang-conjecture/)
