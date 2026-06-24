# Alignment Audit: Strategy Generation Pipeline (A2 of 10)

**Date:** 2026-05-30
**Auditor:** Claude (A2)
**Scope:** Every Codex/Gemini/Grok-suggested technique that landed in a `.fusion.json` this session.
**Question:** Do LLM technique-scouts generate novel research-grade attacks, or do they retrieve folklore?

---

## 1. Per-strategy classification

| ID | Strategy proposed | LLMs that surfaced it | Class | Aristotle's actual response |
|---|---|---|---|---|
| **E938 v1** | Frey-Hellegouarch + Ribet + Bennett-Skinner + Bombieri-Lang + Pila-Wilkie chain | F5 + I7 (Grok+Gemini+Codex) | **SPECULATIVE CHAIN** — chains *real* techniques into an unproven composite (Bombieri-Lang open, no fixed exponent for Frey, no Pila-Wilkie o-min structure) | CRITIQUED, refused. Named all 3 unproven steps explicitly. |
| **E938 v2** | Chan 2022 abc-conditional `d ≫ N^{1/2-ε}` | Codex+Gemini debate | **PUBLISHED PARTIAL** (arXiv 2210.00281, Bull. AMS 2022) | Acknowledged + named the residual "interloper sieve" gap. No closure. |
| **E1003 v1** | S-unit ESS-2002 + **Tao 2016 entropy decrement** | Multi-AI debate | **PUBLISHED PARTIAL** mis-applied: Tao 2016 is for *Chowla*, not pair `(φ(n), φ(n+1))` | CRITIQUED: "Tao addresses a fundamentally different problem." Substituted **elementary rad-injection** (folklore, ≈1pg). |
| **E1003 v2 (R9)** | ESS-2002 fixed-support only | Debate stripped Pillar 2 | **PUBLISHED PARTIAL** | SUBSTITUTED: elementary `φ(n)/n = ∏(1-1/p)` injection. The deep machinery was unused. |
| **E267** | Pisot β-expansion + Frougny transducers (1992) | 3-AI debate consensus | **PUBLISHED PARTIAL** — legit symbolic-dynamics framing (Schmidt 1980), but no Mathlib infra | SUBSTITUTED: Fermat-descent on rational tail numerator (textbook, predates Brun 1910). Closes only `c ≥ 2`. |
| **E1052** | Bilu-Hanrot-Voutier + UnitaryDependencyGraph | Gemini coined the graph object | **PUBLISHED PARTIAL** (BHV is real, but support-closure bridge is novel-by-Gemini and unproven) | 6 prior failures. Aristotle either compiled empty wrappers or escaped via `wall_k2`/`wall_k3` elementary case-split. |
| **E672** | Frey curve + Chabauty for 4-term 3-full APs | Multi-AI | **PUBLISHED PARTIAL** — actually solved by Bajpai-Bennett-Chan 2023 (which we missed) | Bounded computational verification only. |
| **E647** | sigma₀ multiplicativity + Cunningham-residue witness table | Internal pipeline + Codex | **NOVEL TECHNIQUE** (project-internal: slot737 DNA + 35-case enumeration) | EXECUTED. Compiled clean — but only the bounded `[3000,10⁶]` version. |
| **E944** | small-cancellation Cayley graph for Dirac k=4 | Debate proposal | **FOLKLORE / never materialized** — no submission shipped, S5 ranked but no fusion.json | N/A |
| **E324 R7** | Asiryan 2026 `30 \| h` + Mordell-Weil rank-1 + Gusic-Tadic | Codex debate | **PUBLISHED PARTIAL** (arXiv 2512.11072 real) | Aristotle produced ONLY the trivial `h=0` slice (3-line strict-convexity proof, **folklore since Newton 1666**). Skipped the entire MDO argument. |

---

## 2. Aristotle response pattern per class

| Strategy class | Sample N | "Executes" | "Substitutes elementary" | "Critiques as speculative" |
|---|---:|---:|---:|---:|
| **NOVEL (internal-pipeline)** | 1 (E647) | 1/1 | 0/1 | 0/1 |
| **PUBLISHED PARTIAL** | 6 | 0/6 | **5/6** | 1/6 |
| **SPECULATIVE CHAIN** | 1 (E938 v1) | 0/1 | 0/1 | **1/1** |
| **FOLKLORE / never shipped** | 1 (E944) | — | — | — |

The pattern is unambiguous: **when LLMs suggest "deep" cross-domain machinery (Frey, Subspace, Pisot, BHV, Asiryan), Aristotle silently swaps in an elementary path** (Fermat descent, rad-injection, h=0 convexity, native_decide enumeration). It engages the deep machinery only when forced to *critique* a chain (E938 v1) — never to execute one.

---

## 3. Honest verdict: can our LLM scouts generate novel techniques?

**No — they retrieve and recombine. They do not invent.**

Evidence:
1. **Every named technique in every fusion.json is published** (Frey-Hellegouarch, Ribet, Bombieri-Lang, Pila-Wilkie, Chan 2022, ESS 2002, Tao 2016, Pisot/Schmidt 1980, Frougny 1992, BHV 2001, Asiryan 2026, Wall 1972, Goto 2007). Zero technique is invented; all are mined from the corpus.
2. **The single "novel" object** — Gemini's `UnitaryDependencyGraph` for E1052 — is a *reformulation* of the multiplicative identity `∏(1+p^{a_p}) = 2n` as a directed graph. The mathematical content is unchanged; it's a packaging move.
3. **"Cross-domain" suggestions cluster narrowly** (`analysis/llm_consultation_audit.md` §4): zero of 107 LLM consultations asked for technique imports from outside the problem's native sub-field. The "cross-domain" we celebrate is mostly *within-NT cross-area*.
4. **The room they cover is the union of arxiv abstracts they were trained on.** Tao 2016 surfaced for E1003 because it's *the* famous entropy-decrement paper — not because it fits. Pisot for E267 because Badea 1987 cites β-expansions. Frey for E938 because the equation has powers in it.

This matches the **published trend** (BrokenMath, Mathematician's Assistant): LLMs are reliable *literature scouts* and *critique engines*, not technique-inventors.

---

## 4. The single biggest unlock

**Stop asking "which technique solves problem X?" and start asking "what is the analog of problem X in a domain we have not yet considered?"**

Per `llm_consultation_audit.md`: 87% of our LLM debates were META-PROCESS (which problem to attack), 13% were technique-naming inside the chosen field, **0% were cross-domain analog discovery**. The harness (`scripts/debate.py`) is fully general — the bottleneck is prompt convention. Proposed prompts already drafted in §6 of that audit: "what is the closest analog of this open problem in elliptic-curve point counting / additive combinatorics / model theory, and what cracked the analog?"

The novelty bottleneck is not the model — it is the *prompt template*. Until we ask for analog transplant, we will continue retrieving folklore dressed as strategy.

---

## Sources

- `/Users/patrickkavanagh/math/analysis/llm_consultation_audit.md` (87% meta-process finding)
- `/Users/patrickkavanagh/math/docs/research/strategy_critiques_value_audit.md` (Aristotle critique impact)
- `/Users/patrickkavanagh/math/docs/research/e1003_phi_n_trick_audit.md` (R9 folklore classification)
- `/Users/patrickkavanagh/math/docs/research/e267_badea_verification.md` (Aristotle substituted Fermat descent for Badea/Brun)
- `/Users/patrickkavanagh/math/docs/research/e324_h_zero_audit.md` (trivial h=0 slice, folklore since Newton)
- `/Users/patrickkavanagh/math/docs/research/PILOT_ERDOS850.md` (em-tautology root cause)
- 11 `submissions/sketches/*.fusion.json` files examined
