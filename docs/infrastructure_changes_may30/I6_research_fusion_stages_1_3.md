# I6 — research_fusion/ Stages 1-3 (literature / analogy / technique)

**Agent:** I6 of 10 (Part B) | **Date:** 2026-05-30 | **Status:** LANDED
**Owns:** Stages 1-3 of F7's 5-stage research-fusion pipeline.
**Builds on:** I1 (auto-context fix), I2 (lane/fusion_json schema), I4 (literature-check skill).
**Consumed by:** I8 (Stages 4-5 — fusion-lane sketch + Aristotle follow-up).

---

## TL;DR

`research_fusion/` is a per-problem research dossier builder. Given a `problem_id`
(e.g. `erdos_938`), it pulls 2020-2026 arXiv abstracts across the home and
adjacent domains, asks Grok + Gemini + Codex in parallel for cross-domain
analogies, then asks Codex deep-think for technique-transfer cards (with a
`fit_score`). The aggregated dossier (`fusion_candidate.json`) is what I8's
Stage 4 reads to assemble a fusion-lane `.txt` sketch + `.fusion.json`
companion.

`mk fusion <problem_id>` runs all three stages in sequence and prints a
summary. No Aristotle submission is triggered — this is research-context
assembly only.

---

## Architecture

```
                          ┌────────────────────────┐
                          │  problem_card.json      │
                          │  (auto-derived for      │
                          │   erdos_N or hand-      │
                          │   written for other)    │
                          └─────────┬──────────────┘
                                    │
                                    ▼
┌──────────────────────────────────────────────────────────────────────┐
│ STAGE 1 — stage1_literature.py                                       │
│ - arXiv API (HTTPS, 2020-2026, ~10 papers per adjacent domain)       │
│ - erdosproblems.com forum HTML scrape (best effort)                  │
│ - formal-conjectures Lean source                                     │
│ → 01_literature.md  + 01_literature.json                             │
│   (≤ 50 papers, grouped by domain)                                   │
└──────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌──────────────────────────────────────────────────────────────────────┐
│ STAGE 2 — stage2_analogy.py                                          │
│ - Invokes scripts/debate.py (Grok+Gemini+Codex parallel, 1 round)    │
│ - Prompt: prompts/stage2_analogy.md                                  │
│ - Forbids same-home-domain analogs                                   │
│ - Consolidates JSON arrays from all models, deduplicates, ranks      │
│   by supporter-count + mean confidence                               │
│ → 02_analogies.md  + 02_analogies.json + 02_analogies_debate.md      │
└──────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌──────────────────────────────────────────────────────────────────────┐
│ STAGE 3 — stage3_techniques.py                                       │
│ - One Codex call per top analog (~5 calls)                           │
│ - Prompt: prompts/stage3_techniques.md                               │
│ - Codex returns single JSON technique card                           │
│ - We RECOMPUTE fit_score = (#YES + 0.5*#PARTIAL) / total             │
│   for honesty (no trusting LLM's own scoring)                        │
│ → 03_techniques.md  + 03_techniques.json                             │
│   + fusion_candidate.json (aggregated dossier, for I8)               │
└──────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
                          (I8's Stage 4 consumes
                           fusion_candidate.json
                           to build a fusion-lane
                           .txt + .fusion.json)
```

---

## Per-stage interface contracts

### Stage 1 — Literature Breadth

**Module:** `research_fusion/stage1_literature.py`
**Entry:** `python3 -m research_fusion.stage1_literature --problem-id <id>`

**Input** (one of):
- An existing `runs/<problem_id>/problem_card.json` (preferred for non-Erdős).
- For `erdos_NNN` ids: the Lean source at
  `formal-conjectures/FormalConjectures/ErdosProblems/<N>.lean` is parsed
  to auto-derive a minimal card.

**CLI flags:**
- `--problem-id` (required)
- `--max-papers N` (default 50)
- `--force` (bypass 7-day cache)
- `--keywords "a, b, c"` (override auto-extracted keywords)

**Output:**
- `runs/<id>/problem_card.json` (if absent, derived)
- `runs/<id>/01_literature.md` (markdown, paper list grouped by domain +
  erdosproblems.com excerpt + Lean source pointer)
- `runs/<id>/01_literature.json` (structured payload; consumed by Stage 2/3)

**External deps:** Public arXiv API (HTTPS), erdosproblems.com (best-effort).
No paid LLM calls in Stage 1 by default; the LLM-summarization layer
described in F7's design is deferred to keep Stage 1 cheap and deterministic.

**Failure modes:**
- arXiv 429 → exponential backoff (5s → 40s, 4 retries) and stage continues
  with whatever was already cached.
- erdosproblems.com timeout → log warning, continue without forum excerpt.
- All requests cached for 7 days on `(problem_id, domain, query)` key.

### Stage 2 — Analogy Mining

**Module:** `research_fusion/stage2_analogy.py`
**Entry:** `python3 -m research_fusion.stage2_analogy --problem-id <id>`

**Input:** `runs/<id>/01_literature.md` + `problem_card.json`.

**CLI flags:**
- `--problem-id` (required)
- `--models grok,gemini,codex` (CSV; default all three)
- `--rounds N` (default 1; debate.py supports multi-round but a single
  round of structured analogy elicitation has been sufficient on E938)
- `--timeout N` (per-model, default 300s)
- `--force`

**Output:**
- `runs/<id>/02_analogies_debate.md` (raw debate.py transcript)
- `runs/<id>/02_analogies.md` (top-5 ranked + honourable mentions +
  appended transcript)
- `runs/<id>/02_analogies.json` (structured top_analogs list)

**How `debate.py` is invoked:** through `subprocess.run` with the existing
`--round-instructions` JSON pathway — our analogy-mining prompt is passed
as the round-1 instruction. **`debate.py` itself is NOT modified.**

**Consolidation rule** (`stage2_analogy.consolidate`):
1. Collect every JSON-fenced array from every model's response.
2. Reject same-home-domain analogs (gate against trivial transfers).
3. Deduplicate by lowercased problem-name key.
4. Rank by `(supporter_count, mean_confidence)` desc.
5. Return top 10 (top 5 are surfaced in the markdown; rest as
   "honourable mentions").

### Stage 3 — Technique Transfer

**Module:** `research_fusion/stage3_techniques.py`
**Entry:** `python3 -m research_fusion.stage3_techniques --problem-id <id>`

**Input:** `runs/<id>/{problem_card.json, 01_literature.json, 02_analogies.json}`.

**CLI flags:**
- `--problem-id` (required)
- `--max-cards N` (default 5)
- `--timeout N` (per-Codex-call, default 240s)
- `--force`

**Output:**
- `runs/<id>/03_techniques.md` (3-5 technique cards, ranked by fit_score)
- `runs/<id>/03_techniques.json` (structured cards + declines)
- `runs/<id>/fusion_candidate.json` (aggregated dossier — this is what
  I8 consumes)

**Fit score calibration:**
```
fit_score = (# YES + 0.5 * # PARTIAL) / # input_requirements
```
We **recompute** this from the `input_match` table even when Codex
returns its own number — this prevents the LLM from optimistically
overstating fit on a single-shot card.

**Schema validation:** every Codex response is parsed, ID-stamped with the
source analog, and validated against `schemas/technique_card.schema.json`
field-by-field. Validation failures are bucketed into `declines[]` rather
than silently dropped.

---

## Cache invalidation strategy

| Stage | Cache key | TTL | Where |
|---|---|---|---|
| 1 | `(problem_id, domain, keywords, arxiv_cats)` | 7d | `runs/<id>/.cache/*.json` |
| 1 | `(problem_id, erdos_forum, N)` | 7d | `runs/<id>/.cache/*.json` |
| 2 | `(stage2, sorted(models), sha256(prompt))` | 7d | `runs/<id>/.cache/*.md` |
| 3 | `(stage3, sha256(prompt))` (one per analog) | 7d | `runs/<id>/.cache/tech_*.txt` |

**Force-rerun:** `--force` on any stage bypasses every cache check for
that stage. To force from scratch: `rm -rf runs/<id>/.cache/` then
`mk fusion <id>`.

**Implicit invalidation:** Stage 2/3 caches are keyed on the prompt hash.
If `01_literature.md` content changes (Stage 1 re-run with different
keywords), Stage 2's prompt hash changes and Stage 2 cache misses — and
because Stage 3's prompt embeds Stage 2's analog text, Stage 3 also
misses. This means a Stage 1 keyword change cascades correctly through
all three stages on next run.

---

## Test dossier — Erdős 938 (powerful 3-AP)

**Problem** (formal-conjectures path
`formal-conjectures/FormalConjectures/ErdosProblems/938.lean`):
> Are there only finitely many three-term arithmetic progressions among
> consecutive powerful numbers?

**Stage 1 yield** (curated keywords:
`powerful numbers, arithmetic progression, squarefull, consecutive integers`):
- 7 unique papers across 6 domains
- erdosproblems.com forum excerpt captured (notes Erdős also conjectured
  no triples `n, n+1, n+2` of powerful numbers — useful cross-link to E364)
- Top papers: "Mixed thresholds in the Lonely Runner Conjecture" (Jensen 2026),
  Linnik's problem for multiplicative functions (Matomäki/Teräväinen 2026),
  Sylvester cube-sum 4,7-mod-9 cases (Yin 2026), Erdős-Borwein constant
  binary digits (Campbell 2026), pairs of square-free arithmetic
  progressions in words (Delépine et al. 2026), Erdős-Ginzburg-Ziv
  linear-time (Jo 2026), Box Progressions + Abelian k-power-free morphisms
  (Eyidoğan et al. 2026).

**Stage 2 yield** (Grok+Gemini+Codex, 1 round; Grok returned an API error
for `grok-4.3`, so 2/3 models effective):
- 10 consolidated analogs, top 5 (latest re-run, 2026-05-30T08:29Z):
  1. **Cap Set Problem** → slice rank method (Ellenberg-Gijswijt 2017)
  2. **Corners Theorem** → hypergraph removal lemma (Rödl et al. 2005)
  3. **Dejean's Conjecture** → Currie-Rampersad template method (2011)
  4. **Roth's Theorem on Arithmetic Progressions** → Fourier analytic method
  5. **Arithmetic removal lemma for 3-term progressions** → Green 2005
- Earlier independent run surfaced overlapping but distinct analogs:
  Thue square-free morphisms, Mordell/Faltings + Arakelov, Fermat's
  4-squares-not-in-AP + infinite descent. The consistency across reruns
  is in *cluster* (additive combinatorics + combinatorics on words +
  arithmetic geometry) more than in specific named results.

**Stage 3 yield** (Codex one-shot per analog):
- 4-5 technique cards across the two runs; top fit_score = **0.375**
  (Thue square-free morphisms / Fermat infinite descent in run 1) and
  **0.25** (slice-rank / arithmetic removal lemma in run 2).
- Codex declined 1 card (Fourier method on `Roth's Theorem`) in run 2 —
  decline was respected, not coerced.
- Honest assessment: E938 has **no high-fit technique** in the consulted
  surface — the top fit_score across two independent runs is 0.25-0.375.
  The cap-set / slice-rank analog is structurally tempting but mismatches
  on the finite-field requirement (powerful numbers live in `ℕ`, not
  `F_q^n`). Honest disclaimers in every card flag this.

### fit_score calibration for E938

Across the two independent runs:

| Run | Top fit | Top card | Rationale |
|---|---|---|---|
| 1 (initial) | 0.375 | Thue square-free morphisms | 1/4 YES, 1/4 PARTIAL on input requirements (word-encoding present, morphism absent) |
| 2 (mk fusion) | 0.25 | Slice rank method | 0/4 YES, 2/4 PARTIAL (AP condition present, finite-field not) |

**Calibration meaning:** any fit < 0.5 on E938 suggests Stage 4 should
NOT proceed with a fusion-lane sketch citing that technique as a primary
claim. F7's design recommends a `--rank N` operator override for I8 when
the auto-rank-1 is too speculative; this test confirms that override
will likely be needed for E938. Or — equally honestly — E938 may be a
problem where no current named technique transfers, and the right move
is to remain in the bare-gap lane.

The fit-score recomputation step (`recompute_fit_score`) caught one
case in run 2 where Codex returned a slightly inflated number; we
overrode with the formula-derived value. This is the honesty guardrail
working as designed.

---

## How to add a Stage 0 or Stage 4 hook

The pipeline is intentionally a thin orchestrator: each stage is a
standalone Python module that reads `runs/<id>/{prev_stage}.json` and
writes `runs/<id>/{this_stage}.json + .md`. To add a new stage:

1. **Stage 0** (pre-processing — e.g. a deeper problem-card enrichment via
   MathSciNet or a Mathlib lemma-name extractor): create
   `research_fusion/stage0_<name>.py`. Read/write
   `runs/<id>/problem_card.json` — Stage 1 will pick it up unchanged.

2. **Stage 4** (sketch generation, I8's territory) reads
   `runs/<id>/fusion_candidate.json`. The contract is: every field in
   `schemas/fusion_candidate.schema.json` is populated, every referenced
   path under `stage_outputs` exists. I8's gate should validate against
   this schema before consuming.

3. **Wire into mk:** add a case branch in `math-forge/scripts/mk` mirroring
   the existing `fusion)` block — keep the `(cd "$PROJECT_ROOT" && python3 -m
   research_fusion.stage<n>_<name> ...)` pattern so PROJECT_ROOT resolution
   stays consistent.

4. **Cache discipline:** new stages should follow the same
   `_cache_dir(problem_id) / "<stage>_<hash>.json"` pattern with 7d TTL.

---

## Files

| Path | Purpose |
|---|---|
| `research_fusion/__init__.py` | package init + TTL constants |
| `research_fusion/stage1_literature.py` | Stage 1 implementation |
| `research_fusion/stage2_analogy.py` | Stage 2 implementation |
| `research_fusion/stage3_techniques.py` | Stage 3 implementation |
| `research_fusion/prompts/stage1_literature.md` | Stage 1 LLM template (currently unused; kept for the planned Grok-summarization upgrade) |
| `research_fusion/prompts/stage2_analogy.md` | Stage 2 LLM template (used) |
| `research_fusion/prompts/stage3_techniques.md` | Stage 3 LLM template (used) |
| `research_fusion/schemas/problem_card.schema.json` | Stage-1 input contract |
| `research_fusion/schemas/technique_card.schema.json` | Stage-3 per-card contract |
| `research_fusion/schemas/fusion_candidate.schema.json` | Aggregated dossier (I8 input) contract |
| `research_fusion/runs/README.md` | per-problem dossier convention |
| `research_fusion/runs/erdos_938/*` | live test dossier |
| `math-forge/scripts/mk` | adds `mk fusion <id>` subcommand |

---

## Known limitations

- **arXiv keyword extraction is heuristic.** For problems where the
  English blurb is sparse, you'll want to supply `--keywords` explicitly.
  We auto-detected `powerful, numbers, sequence, terms, ...` for E938 and
  had to override with the more semantic `powerful numbers, arithmetic
  progression, squarefull, consecutive integers` to get useful arXiv hits.
- **Grok model id pinned to `grok-4.3`** in `scripts/debate.py`. If the
  account doesn't have access, that model errors and Stage 2 effectively
  becomes 2-AI. Stage 2 handles this gracefully (consolidation just folds
  to fewer supporters) but the operator should know.
- **No Stage 1 LLM-summarization layer (yet).** F7's design described a
  "relevance" paragraph per paper generated by Grok. We deferred that
  to keep Stage 1 deterministic + cheap; the current `relevance` field is
  a simple keyword-overlap heuristic. Plugging Grok in is a 30-line
  enhancement that can ship after pilot evaluation.
- **Domain hint for `problem_card` is AMS-code-based.** For non-Erdős
  problems, hand-write `problem_card.json` to set `domain` and
  `adjacent_domains` properly.

---

## What I6 does NOT do

- Does NOT write fusion-lane `.txt` sketches (I8).
- Does NOT submit to Aristotle (I8 via `safe_aristotle_submit.py --fusion-lane`).
- Does NOT touch `tracking.db` — research dossier is a pure filesystem artefact.
- Does NOT modify `scripts/debate.py`, `scripts/safe_aristotle_submit.py`, or
  any other existing script. Only the `mk` CLI was extended.
