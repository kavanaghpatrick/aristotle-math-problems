# LLM Consultation Audit (Agent F3)

**Date:** 2026-05-30
**Scope:** Every recorded Codex / Gemini / Grok consultation in `docs/`, `docs/research/`, and `analysis/`.
**Total LLM-consultation artifacts examined:** ~107
- 92 files matching `docs/DEBATE_*.md` or `docs/debate_*.md`
- 15 files matching `docs/AI_*.md`, `docs/GROK_*.md`, `docs/GEMINI_*.md`, `docs/NU4_*GEMINI*.md`
- 6 files in `analysis/` matching `codex_*.md`, `gemini_*.md`, `grok_*.md`
- `docs/research/debate_*.md`, `docs/research/llm_math_landscape.md`

---

## 1. Category counts

Each consultation classified by the dominant question it asked the LLMs:

| Category | Count | % | Examples |
|---|---:|---:|---|
| **STRATEGY / PROBLEM-SELECTION / LABELING** | ~70 | ~65% | `debate_strategy_may29.md`, `debate_results_may30.md`, `debate_best_targets.md`, all six `analysis/{codex,gemini,grok}_{closure,labeling}_*.md`, `DEBATE_NOVEL_TARGETS_FEB13.md`, `DEBATE_PROBLEM_SELECTION_FEB9.md`, `AI_STRATEGY_REVIEW_DEC26.md`, `AI_REVIEW_SUBMISSIONS_DEC24.md`, `debate_prime_directive.md` |
| **PROCESS DESIGN / PIPELINE** | ~12 | ~11% | `debate_prime_directive.md` (drop directive?), `DEBATE_LP_PRD_JAN1_2026.md`, `DEBATE_MULTIAGENT_FEB4/FEB6.md`, taxonomy designs in `codex_labeling_taxonomy.md` / `gemini_labeling_taxonomy.md` / `grok_labeling_taxonomy.md` |
| **CRITIQUE / CROSS-CONTEST** | ~7 | ~7% | The "endorse / contest other agent's list" portions of `codex_closure_candidates.md`, `gemini_closure_candidates.md`, `AI_REVIEW_ROUND2_DEC24.md`, debate "Round 2/3" cross-responses |
| **MATHEMATICAL CONTENT** (actual proof ideas, techniques, structural lemmas) | ~14 | ~13% | `AI_CONSULTATION_DEC24.md` (Tuza nu=4 lemma proposals), `DEBATE_FT_P3_MOD72_71_DEBATE.md`, `DEBATE_FT_P3_FEB10.md`, `debate_erdos850_feb18.md`, `debate_lehmer_totient_feb18.md`, `debate_union_closed_feb18.md`, `debate_bmo1_feb18.md`, `debate_leinster_groups_feb18.md`, `debate_erdos1052_feb18.md`, `DEBATE_BRIDGE_GAP_FEB8.md`, `DEBATE_COMPOSITION_FEB9.md`, `DEBATE_NEW_DECOMPOSITION_FEB9.md`, `DEBATE_TE_COVER_FEB9.md`, `GROK_GEMINI_CONSENSUS_JAN8.md`, `GROK_DEBATE_PATH4_TAU8.md`, `GEMINI_PAIRWISE_DESCENT.md` |
| **LITERATURE RECON** (identify papers, known results) | ~4 | ~4% | `docs/research/llm_math_landscape.md` (cited benchmarks/papers), `TUZA_LITERATURE_DATABASE.md` (paper-finding), `analysis/literature_freshness_summary.md`, Codex's web-search-driven closure list |

**Coarse split:**
- **META-PROCESS** (strategy + process + critique + literature recon): ~93 of 107 = **~87%**
- **MATHEMATICAL CONTENT** (proof ideas, structural lemmas, technique suggestions): ~14 of 107 = **~13%**

---

## 2. Math-content drill-down

The math-content cluster is concentrated in two narrow regimes:

**(a) Tuza nu=4 (Dec 2024 – Feb 2026):** ~7 of the 14 are Tuza-specific structural lemma proposals (`AI_CONSULTATION_DEC24.md`, `DEBATE_BRIDGE_GAP_FEB8.md`, `DEBATE_COMPOSITION_FEB9.md`, `DEBATE_NEW_DECOMPOSITION_FEB9.md`, `DEBATE_TE_COVER_FEB9.md`, `GROK_DEBATE_PATH4_TAU8.md`, `GROK_GEMINI_CONSENSUS_JAN8.md`). All stayed inside graph theory — no algebraic/topological/analytic technique borrowed.

**(b) Feit-Thompson p=3 q ≡ 71 mod 72 (Feb 2026):** ~3 (`DEBATE_FT_P3_MOD72_71_DEBATE.md`, `DEBATE_FT_P3_FEB10.md`, `DEBATE_FT_P3_STRATEGY.md`). The single richest math-content consultation in the project (see §3).

**(c) Single-problem Feb 18 batch:** 6 sister debates (erdos850, erdos1052, lehmer, leinster, union_closed, bmo1) — all ~3-paragraph "is this likely True or False, what's the structural obstruction" questions. Light math content; mostly classifying the problem.

Everything else (~93 consultations) was about which problem to attack, which submission pattern to use, how to label results, or whether the pipeline rules should change.

---

## 3. The single highest-content math consultation

**File:** `docs/DEBATE_FT_P3_MOD72_71_DEBATE.md` (Feb 11 2026, 4 rounds, accumulating to ~25k chars).

**Prompt (verbatim from line 1):**

> "What approach can resolve FT p=3 for q ≡ 71 (mod 72)? Character methods of ALL orders are exhausted (GCD of indices = 12, χ₁₂(3)=1 universally). Eisenstein integers are provably insufficient. k-congruence tower extends to mod 972 and mod 108q. Bounded to q<200000. What fundamentally new technique — Kummer theory, Weil-bound character sums, p-adic analysis, Wieferich conditions, or density/size arguments — can produce a universal contradiction?"

**Why it stands out:**

1. The prompt enumerates **five named techniques** from class-field-theory / analytic-number-theory and asks the LLMs to pick and justify.
2. Codex Round 1 produced concrete derivations — e.g., "`3^{(A-1)/3} = 3^{q(q+1)/3} = (3^q)^{(q+1)/3} = 1`" showing the cubic character is tautological under the standing assumption, then proposed a local-norm computation in `K = Q(ζ_q, 3^{1/q})` as the only non-circular route.
3. Grok proposed sieve-on-k-congruence-tower with a quantitative density target (`< 1/q^c`, `c > 1`) and an evidence-that-would-change-my-mind clause.
4. Both sides exchanged specific algebraic claims (`(1-q)^{12q} = 1`, `ord_A(3) = q`, A = x² + 9y² class number 2, Hardy–Littlewood / Brun-Titchmarsh sieve analogies) instead of trading abstractions.

**Honest qualifier:** Even this — the strongest math-content prompt we ever issued — stayed entirely **inside one narrow regime of analytic number theory** (characters, sieves, Kummer, p-adic). The prompt named only the techniques already considered by the team's own prior work. It did not, for instance, ask "could étale cohomology of the auxiliary curve give this", "is there a tropical-geometry analog", or "what would Deligne–Lusztig theory contribute".

---

## 4. Did we ever ask for cross-domain technique fusion?

**No.** Searched all 107 LLM-consultation artifacts for the phrasings any cross-domain prompt would contain:

- `"techniques from algebraic geometry"`, `"from topology"`, `"from representation theory"`, `"from category theory"`, `"from harmonic analysis"`, `"from combinatorics"` (as imports into another domain), `"techniques outside"`, `"borrow from"`, `"transfer from X to Y"`, `"import technique"` → **zero hits** as cross-domain technique-import prompts.

- The only `"outside"` mentions are about running computations outside the Lean kernel.

- `"cross-domain"` and `"across domain"` → zero hits.

The closest we ever came is the FT debate above, which named five techniques but all from inside the same sub-field. We have **never** asked an LLM:

- "Tell us 5 techniques from algebraic geometry / representation theory / harmonic analysis that might apply to this Erdős combinatorics problem."
- "What would Tao / Granville / Bhargava / Scholze try here?"
- "What partial results in adjacent fields (e.g., additive combinatorics, model theory, ergodic theory) might transplant?"
- "What's the closest analog of this open problem in a different domain, and what techniques worked there?"

Every math-content consultation we ran asked an LLM to refine the technique we'd already chosen, never to suggest a discipline outside our default toolkit.

---

## 5. `scripts/debate.py` capability check

`scripts/debate.py` (read in full, lines 1-580) **is fully general**. It is *not* locked into strategy-debate format:

- `--topic` is a free-form string. Nothing constrains it.
- `--context` is any path. Nothing constrains the content.
- `--round-instructions` accepts arbitrary JSON for per-round prompts; the default `default_round_instructions()` is a debate-style template but is overridable.
- All three model callers (`call_grok`, `call_gemini`, `call_codex`) just pass the assembled prompt through.

The strategy-debate format is **a usage convention, not a tool limitation.** A prompt like "List 5 techniques from algebraic geometry that might apply to Tuza nu=4, with the most plausible adaptation path for each" works as-is — we have simply never written that prompt.

---

## 6. Recommendations (math-content prompts the harness already supports)

The same `scripts/debate.py` could carry prompts shaped like:

1. **Cross-domain technique fusion**
   `"For Tuza nu=4 (triangle packing/covering on simple graphs), list five techniques from outside extremal graph theory — algebraic geometry, representation theory, additive combinatorics, ergodic theory, or model theory — that have been applied to graph-theoretic problems with similar finite-structure-vs-global-bound shape. For each technique, name a concrete paper that applied it, the adaptation step, and the failure mode that would block it here."`

2. **Adjacent-analog discovery**
   `"What is the closest mathematical analog of the FT p=3 q ≡ 71 mod 72 obstruction in (a) elliptic-curve point counting, (b) lattice point counting, (c) class-number divisibility? For each analog, what technique cracked the analog, and what is the minimal porting cost into our setting?"`

3. **"What would <name> try" prompts**
   Pick three living mathematicians known for technique transplants (e.g., Tao, Bhargava, Maynard, Sawin, Scholze, Granville) and ask each LLM to roleplay each, suggesting their most-likely first move on a specific stalled problem in our queue. Use the multi-round debate format to surface disagreements about which transplant is most promising.

4. **Bias-flush prompts**
   Before any new attack on a stalled problem, ask: `"Name three techniques you have NOT yet suggested for this problem that you would suggest if I told you Tuza nu=4 was a problem in (a) commutative algebra, (b) p-adic analysis, (c) finite model theory. Force yourself to discard the graph-theory frame."`

5. **Literature-mining prompts** (Codex with web search)
   `"Search arxiv math.CO / math.NT 2023-2026 for any paper using technique X in a context structurally similar to our FT p=3 obstruction. Surface the three most surprising hits, with arxiv IDs."` (Codex's closure-candidates retry already did ~20 web searches for the Erdős corpus — we have the capability and never use it for technique transplant.)

The pipeline gate enforces gap-targeting on **Aristotle submissions**. It does **not** constrain LLM consultation prompts. Switching consultation prompts from "rank these five problems" to "name techniques we have not considered from domains we have not considered" costs nothing in pipeline-rule terms.

---

## 7. Net finding

**Of our LLM consultations, ~87% were META-PROCESS** (which problem, which pattern, which gate, which schema column, which model). **~13% were math-content**, and almost all of that math content stayed inside the technique family the team had already chosen.

**Zero consultations have ever asked an LLM to import a technique from a domain we are not already working in.** The harness supports it. The convention does not.

The single highest-leverage change is: **stop using the multi-AI debate as a portfolio committee, and start using it as a cross-domain technique scout.** The infrastructure is already there.
