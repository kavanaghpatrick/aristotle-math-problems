# Codex Consultation: Math-Research-Fusion Approach

**Date**: 2026-05-30
**Consulting agent**: F8 of 10
**Model**: gpt-5.5 (Codex CLI, reasoning effort xhigh, web search enabled)
**Session**: 019e77c2-e0bc-7be3-a924-b94c408d21c3

**Prompt context summary**: Our pipeline is currently computational verification of bounded versions of open problems (6 advances, all via native_decide / σ-multiplicativity tables / finite enumeration). We want to shift to math-research-fusion: surveying adjacent domains, identifying technique transfers, fusing seemingly-unrelated areas. Tools: Aristotle (Lean 4), GPT-5.2/Codex, Gemini-2.5, Grok-4.20, WebSearch, Mathlib.

---

## Operating Rule

Stop submitting "find a finite certificate" problems unless the upstream dossier contains a noncomputational bridge theorem. Aristotle is the formalizer/prover, not the research-strategy engine. Keep fusion dossiers separate from the final `<=30` line sketch.

## A. Research-Fusion Pipeline

| Stage | Input | Tool / Corpus | Prompt Skeleton | Output | Gate |
|---|---|---|---|---|---|
| `00_problem_screen` | Erdős DB card + Aristotle prior results | Codex + `teorth/erdosproblems` DB | "Classify this problem. Return JSON: native_domain, obstruction_type, computational_trap, prior_overlap, likely_source_domains. Reject routes that are finite enumeration only." | `runs/E###/00_problem_card.json` | Pass only if open, not already solved, and non-computation score `>=4/5`. |
| `01_literature_delta` | Problem card | Grok + WebSearch + arXiv/OpenAlex/OEIS/comments | "Find current primary literature for Erdős #X. Include theorem statements, not summaries. Flag claimed solutions, conditional results, adjacent-field methods." | `01_lit_delta.json`, `papers.bib` | At least 8 real references, 2 adjacent-domain references, no known complete solution. |
| `02_transfer_mining` | Statement + lit delta | Gemini 2.5 Pro, 1M context | "Generate 12 cross-domain transfers. For each: source domain, named theorem/method, object map, target lemma, why native methods stall, failure mode." | `02_transfer_candidates.jsonl` | Keep only candidates with a concrete object map, e.g. "Fibonacci denominator sum → beta-shift orbit." |
| `03_obstruction_matrix` | Transfer candidates | Codex + Gemini judge | "Compress each transfer into one obstruction type: S-unit, beta-expansion periodicity, Cantor intersection, modular curve, profinite tiling, etc. State the smallest theorem that would move the problem." | `03_obstruction_matrix.json` | One obstruction must reduce to a named theorem + one local lemma, not a whole new theory. |
| `04_mathlib_surface` | Top 3 transfers | Codex over Mathlib index + Aristotle dry run | "Map objects to Mathlib declarations. Produce Lean statement skeletons. List missing lemmas. Do not prove." | `04_formal_surface.json`, `Candidate.lean` | Missing primitives `<=5`; no massive library build required. |
| `05_fusion_tournament` | Dossiers | Gemini judge + Codex judge | "Rank by insight, novelty, formalizability, and distance from brute force. Penalize enumeration and vague analogy." | `05_ranked_targets.md` | Submit only if score `>=75/100`; otherwise mine more. |
| `06_airlock_sketch` | Winning target only | Codex | "Write a bare informal `.txt` conjecture in <=30 lines. No proof strategy, no theorem names, no literature, no source-domain hints." | `submission/sketch.txt`, `airlock_report.json` | Hard fail if strategy terms appear: `Subspace`, `S-unit`, `Furstenberg`, `modular`, `ABC`, `entropy`, etc. |
| `07_aristotle_run` | Bare sketch only | Aristotle | Existing gap-targeting submission | `aristotle.log`, proof artifacts | Pass if Aristotle closes or finds reducible missing lemma. |
| `08_postmortem` | Aristotle logs + dossier | Codex | "Classify failure: false bridge, missing formal lemma, tactic gap, wrong target. Produce next upstream task." | `08_postmortem.md`, updated DB | No resubmission without a new noncomputational bridge. |

## B. Three Fusion-First Erdős Targets

| Problem | Native Domain | Source Domain | Technique To Transfer | Why Fusion Beats Computation |
|---|---|---|---|---|
| **Erdős #267**: lacunary reciprocal Fibonacci sums irrational. Open for `1 < c < 2`; known for `c >= 2`. ([erdosproblems.com](https://www.erdosproblems.com/267)) | Irrationality of recurrence series | Symbolic dynamics / Pisot numeration | **Schmidt beta-expansion periodicity for Pisot bases**, plus Zeckendorf/Ostrowski numeration. Schmidt-type results say Pisot-base rationals have eventually periodic beta-expansions. ([link.springer.com](https://link.springer.com/article/10.1007/s00605-017-1063-9?utm_source=openai)) | Finite testing is useless because the input is an arbitrary infinite subsequence. The real move is: rationality forces eventual periodicity in a `φ`-beta expansion; lacunarity forces unbounded gaps incompatible with periodicity after carry normalization. This is the best ROI target. |
| **Erdős #406**: finitely many powers of `2` with only ternary digits `0,1`. Only known examples appear to be `1,4,256`; computation already reaches `5.9e21`. ([erdosproblems.com](https://www.erdosproblems.com/406)) | Base representation / exponential Diophantine | Fractal geometry / ergodic theory | **Furstenberg `×2,×3` orbit philosophy**, Hochman-Shmerkin entropy/intersection methods, Bourgain discretized sum-product. | Computation has already gone absurdly far and still proves nothing global. Recast as intersection of the orbit `{2^n}` with a `3`-adic/Cantor digit set. The desired insight is a rigidity/entropy obstruction, not another range extension. |
| **Erdős #850**: Erdős-Woods conjecture for three consecutive shifts with identical prime supports. ([erdosproblems.com](https://www.erdosproblems.com/850)) | Prime divisors of consecutive integers | Diophantine geometry / logarithmic geometry | **Simultaneous S-unit equations**, Evertse-Schlickewei-Schmidt finiteness, Baker/ABC-style height inequalities. General S-unit finiteness is a real imported theorem, not a search heuristic. ([academic.oup.com](https://academic.oup.com/blms/article/32/2/163/463826?utm_source=openai)) | Equality of prime supports is a radical/S-unit condition. Searching `x,y` is hopeless because counterexamples, if any, can hide behind huge smooth radicals. The fusion move is to force bounded support or bounded height, then Aristotle can formalize the elementary collapse. |

## C. Most Novel Suggestion

Attack **#267 through beta-shifts**, not irrationality estimates.

Concrete bet: transform
`Σ 1/F_{n_k}`
into a controlled `φ`-base expansion. If the sum is rational, Schmidt/Pisot theory predicts eventual periodicity. But `n_{k+1}/n_k > 1` gives gaps tending to infinity. The work is then a carry-propagation lemma: sparse Fibonacci-denominator contributions cannot normalize into an eventually periodic `φ`-expansion.

That is counterintuitive because it turns an Erdős irrationality problem into symbolic dynamics of numeration systems.

## D. Tooling To Build

```text
research_fusion/
  data/erdos/problems.jsonl
  data/lit/papers.sqlite
  data/mathlib/decls.sqlite
  prompts/
    00_problem_screen.md
    01_literature_delta.md
    02_transfer_mining.md
    04_mathlib_surface.md
    06_airlock_sketch.md
  schemas/
    problem_card.schema.json
    technique_card.schema.json
    fusion_candidate.schema.json
    airlock_report.schema.json
  runs/E267/
  src/
    sync_erdos.py
    query_lit.py
    mine_transfers.py
    score_candidates.py
    index_mathlib.py
    airlock_check.py
```

Minimum schemas:

```json
{
  "fusion_candidate": {
    "erdos_no": 267,
    "native_domain": "irrationality",
    "source_domain": "Pisot beta-expansions",
    "named_method": "Schmidt periodic beta-expansion theorem",
    "object_map": "Fibonacci reciprocal sum -> phi-base expansion",
    "target_lemma": "sparse normalized expansion is not eventually periodic",
    "noncomp_score": 5,
    "mathlib_score": 3,
    "novelty_score": 5,
    "risk": "medium"
  }
}
```

Build this first:

1. `sync_erdos.py`: mirror official problem data/comments from the community DB. The GitHub repo is the live machine-readable source. ([github.com](https://github.com/teorth/erdosproblems))
2. `query_lit.py`: pull arXiv/OpenAlex/Crossref/OEIS and cache theorem snippets.
3. `mine_transfers.py`: run Gemini transfer prompts and emit `technique_card` JSONL.
4. `index_mathlib.py`: dump declarations/import graph so Codex can score formalization surface.
5. `airlock_check.py`: enforce `<=30` lines and reject proof-strategy leakage before Aristotle.

---

## Codex's Web-Sourced Citations

During reasoning, Codex web-searched and verified against:
- `github.com/teorth/erdosproblems` (machine-readable problem DB)
- `erdosproblems.com/203`, `/406`, `/1052`, `/398`, `/267`, `/850`
- Schmidt theorem beta expansions / Pisot numbers
- Narkiewicz–Saye 2022 (Erdős #406 status)
- Shorey–Tijdeman, Erdős–Woods conjecture, S-unit equations
- Bennett–Siksek 2020 (modular method) for #672

## Session Metadata

- Tokens used: 83,859
- Tools invoked: web_search (10+ calls before composition)
- Self-verification: Codex explicitly stated it would verify Erdős problem statements before recommending, to avoid "giving a plausible fusion plan against the wrong problem text."
