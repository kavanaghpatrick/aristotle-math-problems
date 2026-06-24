# Research-Fusion Pipeline Design (5-Stage)

**Author:** Agent F7 of 10
**Date:** 2026-05-30
**Inputs synthesized:**
- `analysis/cross_domain_breakthroughs_catalog.md` (F4) — 15 breakthroughs, the human recipe, honest Aristotle estimate (~5%)
- `analysis/sketch_context_audit.md` (F2) — 0/220 sketches have cross-domain content, `gather_context()` status-filter is broken (no auto-context for any submission since rename)
- `docs/research/PILOT_ERDOS850.md` — em-tautology pathology; 3-arm pilot showed sketches DID NOT change Aristotle behavior when the theorem itself was vacuous
- `docs/research/improvement_proposals.md` — Proposal #1 (already drafted) argues for an informal sketch ≥150 words + 3-5 candidate lemmas, citing arxiv 2510.01346 that says Aristotle benefits from informal reasoning
- `scripts/safe_aristotle_submit.py` — current gate (`check_gap_targeting`, `check_closure_axis`), `--rubric-points` escape hatch, `gather_context()`
- `docs/closure_axis_companion_spec.md` — `.closure.json` companion file pattern (taxonomy + machine-readable classification)

---

## Executive Summary

F4's catalog is the brutal truth: cross-domain fusion is what mathematicians actually do for breakthroughs, but **the bridge lemma is where 100% of the math sits, and Aristotle does not generate bridge lemmas.** F2's audit confirms we are doing none of it — 0/220 sketches reference adjacent literature, and the auto-context plumbing is silently broken anyway.

This design proposes a **fusion-sketch lane** (companion to the existing bare-gap lane) that injects literature breadth + analogy mining + named technique candidates as *context*, NOT *strategy*. The lane is opt-in, governed by a new companion file (`.fusion.json`) and an existing escape hatch (`--rubric-points` extended to `--fusion-lane`), and is honest about the fact that it is a **different distribution of bets** — not a claim that it beats the bare-gap lane.

The prime directive conflict (Section 6) is real and unavoidable. We recommend option **(a) — update the directive** to permit fusion sketches as a distinct submission type with explicit honesty guardrails, because option (b) "cross-domain analogies aren't proof strategies" is sophistry and option (c) means we never test the hypothesis.

---

## 1. What F4's catalog teaches us about the recipe

From the 15 breakthroughs, the universal pattern is:

1. **IDENTIFY A WALL** — natural method almost works, blocks on a named obstruction (EH > ½, no link to anything tractable, AOC dependence).
2. **IMPORT A FOREIGN OBJECT** — from an *adjacent* (not random) domain — Frey curve, Ricci flow + entropy, polynomial method, multidim sieve. The import is usually suggested by formal analogy or a weaker version solved foreign.
3. **BUILD THE BRIDGE LEMMA** — the single technical innovation. This is where math lives.
4. **VERIFY** — computation/exhaustion is the closing step (Hales LP, Helfgott 10^27, Polymath witness tables).
5. **REFORMULATE** post hoc (slice rank, heat kernel).

**Honest empirical finding (F4 §5):** ~50-60% of these breakthroughs would have been *anticipated* by lit-search; ~15-25% by technique-transfer suggestion; ~5% by Aristotle directly. The bridge lemma is the bottleneck and is currently outside Aristotle's reach.

**Implication for our pipeline:** Steps 1, 2, and 5 are *literature-shaped*, and the LLM consultation chain (Grok with X search + Gemini long-context + Codex) is well-suited to Steps 1-2. Step 4 (verify) is *Aristotle's home turf*. Step 3 (bridge lemma) is the dangerous one — if we cargo-cult fusion sketches that *guess* at the bridge lemma, we re-create the multi-page proof-strategy essays that the prime directive was designed to prevent.

The right framing: **Stages 1-3 of our pipeline assemble Steps 1, 2, and 5 of the human recipe as `context` for Aristotle. Aristotle still has to invent Step 3 (or recognize a Mathlib-or-prior-result form of it). Step 4 (verify) remains Aristotle's terminal step.** We do not generate Step 3.

---

## 2. What F2's audit shows we are missing

| Category | Current state | What fusion lane adds |
|---|---|---|
| 1. GAP_ONLY (bare conjecture) | 57% of sample, default lane | Unchanged. Bare-gap lane preserved as the default. |
| 2. + COMPUTABLE_BRIDGE | 20% (witness Lean definition) | Unchanged — still helpful for C1/C2 problems. |
| 3. + WITNESS_DATA | 20% (explicit candidate) | Promoted. Fusion lane *requires* witness data when applicable. |
| 4. + PRIOR_ARISTOTLE_CONTEXT | 23% in-sketch, ~0% via auto-context (BUG) | Fix the bug first; then layer fusion context on top. |
| 5. + CROSS_DOMAIN_LITERATURE | **0/220** | **The new lane.** External literature paragraphs become legal. |
| 6. + RESEARCH_SYNTHESIS | **0/220** | **The new lane.** Multi-subfield technique cards become legal. |

Three concrete bugs/gaps F2 surfaced that this design must address:

- **B1.** `gather_context()` filters on `status IN ('compiled_clean','near_miss','completed')` — none of which exist in the post-2026-05-28 schema. The function returns `[]` for every problem. *Must fix before measuring fusion effects, otherwise we cannot isolate "is it the fusion content or the (newly-working) self-context that helped?".*
- **B2.** Even when fixed, `gather_context()` only returns our own `_result.lean` files. There is no path for external context (arxiv, MathSciNet, MathReviews, math-forge knowledge base) into Aristotle's prompt.
- **B3.** The `literature_lemmas` table mentioned in `scripts/import_all_to_sqlite.py` is never read by the submission flow. We have curated literature data sitting unused.

---

## 3. The 5-stage pipeline (overview)

```
┌─────────────────────────────────────────────────────────────┐
│ STAGE 1 — Literature Breadth (Grok + arxiv API)             │
│ Pull 2020-2026 papers across ALL adjacent domains.          │
│ Output: docs/research/fusion/<problem>/literature.md        │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ STAGE 2 — Analogy Mining (multi-LLM consultation)           │
│ Ask: what structurally similar problems exist in OTHER math │
│ areas? What techniques unlocked them?                       │
│ Output: docs/research/fusion/<problem>/analogies.md         │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ STAGE 3 — Technique Transfer (ranked technique cards)       │
│ Identify 3-5 named techniques that COULD apply, with        │
│ explicit obstruction analysis for each.                     │
│ Output: docs/research/fusion/<problem>/techniques.md        │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ STAGE 4 — Fusion Sketch (≤80 lines, named lane)             │
│ Sketch with: bare gap + 1 cross-domain analogy + ranked     │
│ technique list + explicit "Aristotle: please try X first".  │
│ NOT a proof strategy. NO step-by-step outline. NO bridge    │
│ lemma proposed.                                             │
│ Output: submissions/sketches/<name>_fusion.txt +            │
│         <name>_fusion.fusion.json companion                 │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ STAGE 5 — Aristotle as Junior Collaborator                  │
│ Submit via safe_aristotle_submit.py --fusion-lane.          │
│ Fusion gate replaces gap-targeting gate for this lane.      │
│ Result audited via project.ask() follow-up if it fails:     │
│ "which technique did you try? what blocked you?"            │
│ Output: submissions/nu4_final/slot<N>_result.lean +         │
│         followup transcript                                  │
└─────────────────────────────────────────────────────────────┘
```

---

## 4. Stage details

### Stage 1 — Literature Breadth

**Goal.** For problem P (e.g. Erdős 850), pull recent (2020-2026) papers across ALL adjacent domains, not just the home domain (NT). For Erdős 850 the home is NT, but adjacent includes: analytic NT (Maynard, Tao recent), additive combinatorics (Green-Tao), Diophantine approximation, abc/Vojta height theory, and possibly arithmetic geometry if rad-pairs are interpreted via S-units.

**Concrete tool.** `scripts/fusion_stage1_literature.py`:
- Uses `grok-search` (Grok-4 with live web + arxiv) to pull abstracts from the last 5 years
- For each adjacent domain (configurable per archetype), runs N=2 search rounds
- Writes structured markdown: `# Domain / ## Paper title / arxiv link / abstract / one-line relevance to P`
- Hard caps: 50 papers total, 10 per domain, ≤200 words of abstract per paper

**LLM template (Grok search):**
```
You are a research librarian for mathematics. The user is investigating an open problem:

[PROBLEM STATEMENT]

Search arxiv.org and recent (2020-2026) literature for papers across these adjacent domains:
[DOMAIN LIST — auto-populated based on archetype]

For each paper:
1. Cite full arxiv ID and title.
2. One-paragraph abstract (≤200 words).
3. ONE sentence: how, if at all, the paper's technique might bear on the open problem.

Do NOT propose proofs. Do NOT make leap-of-faith claims. Catalog only.
Hard requirements: only papers from 2020 onward; no Wikipedia/blogs; arxiv preferred.
Max 50 papers. Group by domain.
```

**Output format:** `docs/research/fusion/<problem_id>/literature.md`
```markdown
# Literature breadth — <problem_id>
Date: YYYY-MM-DD  Stage: 1
Domains queried: [analytic_nt, additive_combinatorics, ...]

## Domain: analytic_nt (10/50)
### Paper: <title> (arxiv:<id>)
Abstract: ...
Relevance: <one sentence>
```

**Integration with `safe_aristotle_submit.py`:** Stage 1 produces a file that is later bundled as part of the `.fusion.json` companion. No direct submission integration at Stage 1.

---

### Stage 2 — Analogy Mining

**Goal.** Ask multiple LLMs in parallel: "what structurally similar problems exist in OTHER math areas? What techniques unlocked them?" Force ANALOGY (an external object/result) rather than PROOF.

**Concrete tool.** `scripts/fusion_stage2_analogy.py`:
- Reads `literature.md` + the bare-gap sketch
- Issues parallel calls to Grok / Gemini / Codex (existing harness in `scripts/debate.py`)
- Each LLM is given the same prompt; the orchestrator consolidates
- Writes `analogies.md` — top 5 analogies ranked by structural distance (how-foreign-is-the-import) + technique name

**LLM template (per model):**
```
You are <model_name>, consulting on an open mathematics problem.

Problem (bare statement):
[BARE GAP TEXT]

Recent literature in adjacent domains (pre-curated, NOT exhaustive):
[STAGE 1 LITERATURE.MD]

Identify 5 structurally similar problems IN OTHER MATH AREAS, NOT in this problem's home domain. For each:

1. Name the analogous problem and its home domain.
2. Identify the NAMED technique that closed it (or made progress on it).
3. Identify the SPECIFIC structural feature that maps between the two problems.
4. ONE sentence on what could obstruct the transfer to OUR problem.
5. Rank confidence (1-5): how strong is the structural analogy?

Output JSON list of {analog_problem, analog_domain, named_technique, structural_map, obstruction, confidence}.

CRITICAL: We are NOT asking you to write a proof. We are asking you to identify cross-domain neighbors. Reject any urge to outline a proof. If no honest analogy exists, say so — empty list is a valid answer.
```

**Output format:** `docs/research/fusion/<problem_id>/analogies.md`
```markdown
# Analogy mining — <problem_id>
Stage: 2  Models consulted: grok, gemini, codex

## Top 5 analogies (consensus, ranked by confidence)
### 1. <analog problem> — <named technique>
- Confidence: 4/5 (3 of 3 models surfaced this)
- Home domain: <other domain>
- Structural map: <one sentence>
- Obstruction: <one sentence>

## Honest disagreements
- Grok proposed X, Gemini did not see it, Codex flagged it as "obstruction too severe"
```

**Integration with `safe_aristotle_submit.py`:** None at Stage 2.

---

### Stage 3 — Technique Transfer

**Goal.** From the consensus analogies, distill 3-5 *concrete, named, citable* techniques that COULD apply. The deliverable is a **technique card per candidate**, not a proof outline.

**Concrete tool.** `scripts/fusion_stage3_techniques.py`:
- Reads `analogies.md`
- For each top-3 analogy, fetches the seminal paper for the named technique (auto-citation via Grok search or already in `literature.md`)
- Writes a technique card per candidate: name / paper / what-it-does / what-it-requires-as-input / what-it-produces-as-output
- Ranks by *fit score* (how many of the named requirements are satisfiable from our problem's data)

**LLM template (single model, deep-think):**
```
You are Codex/Gemini-Pro, drafting a technique-transfer card.

We have analyzed the open problem:
[BARE GAP]

We've identified the analogy:
[TOP ANALOGY FROM STAGE 2 — single analogy at a time]

Now write a TECHNIQUE CARD with these fields, ONLY:
- name: The named technique (Frey curve, polynomial method, multidim sieve, etc.)
- seminal_paper: arxiv ID / journal cite
- what_it_does: 2-3 sentences, NO PROOFS
- input_requirements: Bullet list of what mathematical objects the technique demands as input
- output_signature: What the technique produces (e.g., "a Galois rep, modulo p")
- our_problem_input_match: Bullet list — for each input requirement, does our problem supply it? YES/NO/PARTIAL
- known_obstructions: Bullet list — what is documented to block this transfer
- fit_score: 0-1, computed as (# YES in input_match) / (# input_requirements)

DO NOT WRITE A PROOF SKETCH. DO NOT PROPOSE A BRIDGE LEMMA. This is a catalog card.
```

**Output format:** `docs/research/fusion/<problem_id>/techniques.md`
```markdown
# Technique transfer — <problem_id>
Stage: 3  Candidate count: 5

## Card 1 (rank 1, fit_score=0.83)
- name: <named technique>
- seminal_paper: arxiv:XXXX.YYYYY
- what_it_does: ...
- input_requirements:
  - [x] requirement 1
  - [x] requirement 2
  - [ ] requirement 3 (PARTIAL — see notes)
- output_signature: ...
- known_obstructions: ...
- fit_score: 0.83 (5/6 inputs satisfied)
```

**Integration with `safe_aristotle_submit.py`:** None at Stage 3.

---

### Stage 4 — Fusion Sketch

**Goal.** Write a sketch that ships to Aristotle. Includes the bare gap (verbatim, unchanged) + 1 chosen cross-domain analogy + the top-ranked technique card + a "what to try first" hint.

**Critical constraints:**
- Sketch ≤ 80 lines (vs. 30 for bare-gap lane — this is the carve-out)
- No multi-step proof outline
- No bridge lemma proposed (the lemma we'd LIKE to invoke can be named, but not stated as if we've proven it)
- No "first apply X, then Y, then Z" — that is proof strategy
- Cross-domain content is FACTUAL CITATIONS, not directives
- Must include a `<name>.fusion.json` companion file with required fields

**Format of the sketch:**
```
OPEN GAP: <problem name>
Source: <formal-conjectures path>
Domain: <home domain>
Lane: fusion (NOT bare-gap)

<English statement of the open conjecture, 1-3 sentences>

theorem problem_name (vars : Types) : conclusion := by sorry

# Cross-domain context (Stage 2-3 artifact, FACTUAL ONLY)
- Analog: <analog problem> in <other domain>
- Named technique: <technique name> (cite: arxiv:XXXX.YYYYY)
- Structural map: <one sentence>
- Fit score: <0-1>
- Documented obstruction: <one sentence>

# What we'd like to attempt (advisory — Aristotle may ignore)
- Try invoking <technique name>'s standard form on this gap.
- If the technique requires <input X>, our problem supplies it via <Mathlib def / prior slot>.
- Aristotle: if you reach a step that needs <prior result>, the lemma name in Mathlib is <lemma>.

Status: OPEN. <one sentence on what is known>
```

**`<name>.fusion.json` companion (new):**
```json
{
  "lane": "fusion",
  "primary_analogy": "<text>",
  "named_technique": "<text>",
  "seminal_paper_arxiv": "<id>",
  "fit_score": 0.83,
  "input_requirements_matched": ["mathlib_def_X", "prior_slot_NNN"],
  "input_requirements_missing": [],
  "honest_disclaimer": "This is a fusion-lane submission. We do not claim the technique closes the gap; we are testing whether priming Aristotle with named cross-domain context changes its behavior.",
  "stage1_literature_path": "docs/research/fusion/<id>/literature.md",
  "stage2_analogies_path": "docs/research/fusion/<id>/analogies.md",
  "stage3_techniques_path": "docs/research/fusion/<id>/techniques.md"
}
```

**Concrete tool.** `scripts/fusion_stage4_sketch.py`:
- Reads bare-gap sketch (if exists) + `techniques.md`
- Picks the rank-1 technique (or operator override via `--rank N`)
- Generates the fusion sketch via Codex (single deep-think call)
- Validates against the **new fusion gate** (Section 5 below)
- Writes both the `.txt` and `.fusion.json`

**LLM template (Codex, single shot):**
```
Generate a FUSION-LANE sketch for Aristotle.

Bare gap (verbatim, do not modify the theorem statement):
[BARE GAP TEXT]

Chosen technique card:
[STAGE 3 TECHNIQUE CARD]

Write a fusion sketch following the EXACT format below. Hard requirements:

- Total lines ≤ 80 (including blank lines)
- Theorem statement IDENTICAL to the bare-gap version (do not refactor)
- Cross-domain section is FACTUAL CITATIONS only — papers, named techniques, lemma references
- "What we'd like to attempt" section is ADVISORY, ≤6 lines, names objects/lemmas only
- NO proof step-list. NO bridge lemma stated. NO "first prove X, then Y" structure.

Sketch format: [exact template above]

If you cannot honestly produce a fusion sketch under these constraints (e.g. the technique card requires too much speculation to write the advisory section), output `FUSION_LANE_DECLINED: <reason>` and stop. Decline is a valid output — we'd rather have a missing sketch than a proof-strategy violation.
```

**Integration with `safe_aristotle_submit.py`:** Detailed in Section 5.

---

### Stage 5 — Aristotle as Junior Collaborator

**Goal.** Submit the fusion sketch + companion. If Aristotle fails (compile_failed or compiled_no_advance), trigger a `project.ask()` follow-up to ask Aristotle which technique it actually attempted and what blocked it. This converts every failure into a signed "what did we learn" record.

**Concrete tool.** Extend `scripts/safe_aristotle_submit.py` with `--fusion-lane`:
- Skips `check_gap_targeting()`, runs new `check_fusion_lane()`
- Skips `check_closure_axis()` (closure axis is for bare-gap closure lane only); runs new `check_fusion_companion()`
- After submission, if result is non-advance, automatically calls `project.ask()` with a structured prompt (see template below)
- Records the follow-up in `submissions.fusion_followup_transcript` (new column)

**`project.ask()` template (only triggered on non-advance):**
```
We submitted this fusion-lane sketch with a candidate cross-domain technique. The result you produced did not resolve the gap. We'd like to learn from this. Please answer briefly:

1. Did you attempt the suggested technique (<named_technique>)? YES/NO.
2. If yes, at what point did it block? Name the specific lemma/step where you couldn't continue.
3. Is there a Mathlib result or known theorem that would close the missing step, that you couldn't find?
4. Would a DIFFERENT cross-domain technique (you may name one) plausibly close this gap? If so, which?

Keep each answer to ≤2 sentences. We are using this to triage our fusion-sketch pipeline; honest "no" answers help us most.
```

**DB integration:**
- New column `submissions.fusion_followup_transcript TEXT` (JSON object)
- New column `submissions.fusion_technique_attempted TEXT` (the technique name Aristotle says it tried, or NULL)
- New column `submissions.fusion_blocker TEXT` (named lemma/step Aristotle says it blocked on)
- These columns are populated only for lane=fusion submissions; bare-gap submissions leave them NULL

**Integration with audit:**
- `scripts/audit_proven.py` extended: if `lane=fusion` and `status=compiled_advance`, also verify the result file actually invokes the named technique (string-grep the Lean source for `Frey`/`modularity_lifting`/`Bilu_Tichy`/etc.)
- If lane=fusion and status=compiled_advance but the technique-name doesn't appear in the proof, that's still a win (Aristotle found a different path) but is flagged for human review

---

## 5. Integration with `safe_aristotle_submit.py`

### New CLI flag

```
python3 scripts/safe_aristotle_submit.py <sketch.txt> --fusion-lane
```

### New gate: `check_fusion_lane(input_file: Path) -> dict`

Replaces `check_gap_targeting()` for the fusion lane. Hard requirements (any violation = REJECT):

1. **File suffix .txt** — same as bare lane. No .lean.
2. **Line count ≤ 80** — vs. 30 for bare lane. Anything more is proof-strategy creep.
3. **Theorem statement IDENTICAL to bare-gap version** — checked via hash of the canonical theorem AST (or a string-normalized regex match against a registered bare sketch for the same problem_id). This is the *single biggest guardrail*: the fusion lane can add CONTEXT but cannot rewrite the goal.
4. **No proof step-list patterns** — same `STRATEGY_PATTERNS` regex check, but with two patterns RELAXED:
   - `Cross-domain context` / `Named technique` / `Fit score` allowed (factual citation)
   - `What we'd like to attempt` (advisory section) allowed *if* ≤6 lines and ≤2 named lemmas
5. **NO bridge-lemma proposals** — added regex set:
   - Lines like "Step 1: prove X. Step 2: prove Y." → REJECT
   - Lines like "It suffices to show ..." → REJECT
   - Lines like "By the following lemma, ..." → REJECT
   - Lines naming a UNNAMED lemma (`lemma claim_X : ...`) → REJECT
6. **`<name>.fusion.json` companion exists and validates** — see `check_fusion_companion()`.
7. **em-tautology guard** — unchanged from bare lane.

### New gate: `check_fusion_companion(input_file: Path) -> dict`

Validates `<name>.fusion.json`:

- File exists adjacent to sketch (same naming pattern as `.closure.json`)
- Strict JSON, schema (all required fields, no extras)
- `lane == "fusion"`
- `seminal_paper_arxiv` is a valid arxiv ID (regex `^\d{4}\.\d{4,5}$`)
- `fit_score` ∈ [0,1]
- `stage1_literature_path` / `stage2_analogies_path` / `stage3_techniques_path` all exist on disk
- `honest_disclaimer` is non-empty

### Bundling

The submission tar-bundle (already implemented for `context_files`) is extended to include:
- `<name>.fusion.json` (companion)
- `literature.md` (Stage 1)
- `analogies.md` (Stage 2)
- `techniques.md` (Stage 3)
- Any prior-slot `_result.lean` files (existing auto-context — assuming B1 bug is fixed)

### DB integration

`submissions` table extensions (forward-compatible, NULL for non-fusion rows):
```sql
ALTER TABLE submissions ADD COLUMN lane TEXT DEFAULT 'bare';  -- 'bare' | 'fusion'
ALTER TABLE submissions ADD COLUMN fusion_json TEXT;            -- JSON payload of .fusion.json
ALTER TABLE submissions ADD COLUMN fusion_technique_attempted TEXT;
ALTER TABLE submissions ADD COLUMN fusion_blocker TEXT;
ALTER TABLE submissions ADD COLUMN fusion_followup_transcript TEXT;
```

The `lane` column lets us A/B compare: for each `problem_id` with ≥2 submissions, which lane(s) advanced? Over time we can answer "does fusion produce a higher rate of compiled_advance than bare?" Without this column, the experiment is unmeasurable.

---

## 6. The Prime Directive Conflict (REAL, must be resolved)

CLAUDE.md §Mission:
> We do NOT develop proof strategies. We do NOT write step-by-step proof outlines. We state the open gap, attach prior Aristotle results as context, and submit. Aristotle constructs the proof.

The fusion sketch contains:
- A cross-domain analogy paragraph (FACTUAL)
- A named technique with citation (FACTUAL)
- A fit score and obstruction analysis (ANALYTICAL — but not a proof step)
- A 1-6 line advisory "what we'd like to attempt" section (THIS IS STRATEGY-ADJACENT)

### Option (a) — Update the directive (RECOMMENDED)

Add a second lane to the mission:
> **Primary lane (bare-gap, default).** State the open gap in ≤30 lines and submit. Aristotle constructs the proof.
>
> **Fusion lane (opt-in, ≤80 lines).** Some open problems are demonstrably blocked by single-domain technique exhaustion (FT q≡71 mod 72, em-tautology pilot, 0/317 Tuza nu=4). For these we permit a fusion sketch carrying ONE cross-domain analogy + ONE named technique citation + factual fit analysis. Fusion sketches must pass `check_fusion_lane()` and ship a `.fusion.json` companion. Fusion is NOT a license to propose proof outlines — the advisory section is ≤6 lines and names objects/lemmas only, never proof steps.

Then update hard-rule #2:
> 2. **Sketches are bare conjecture statements OR fusion-lane sketches.** Bare-gap (default) has no proof strategy. Fusion-lane permits factual cross-domain citations + ≤6-line advisory, but bans proof step-lists and bridge-lemma proposals.

This is the honest path. It explicitly enumerates the carve-out, sets a hard cap on advisory content, and adds a machine-readable companion file that lets the gate enforce the rule.

### Option (b) — "Cross-domain analogies aren't proof strategies" (REJECT)

This is sophistry. A sketch that says "try Frey's technique on this gap, the input requirements are satisfied, the seminal paper is X" *is* proof guidance, even if no lemma is explicitly stated. Pretending otherwise re-creates the original failure mode (multi-page strategy essays that fight Aristotle's MCGS).

### Option (c) — Concede the directive prevents this (REJECT)

This is the easy answer but is wrong on the evidence:
- F4's catalog confirms cross-domain fusion is *how breakthroughs happen*
- F2's audit confirms we are doing zero of it
- The em-tautology pilot showed bare sketches alone produced identical pathological results across 3 arms
- Proposal #1 in `improvement_proposals.md` already documented this tension and recommended the same direction

If we concede here, we are choosing not to test a hypothesis that the empirical record suggests is correct.

### Recommendation

Adopt option (a) — with the explicit guardrail of the `.fusion.json` companion + a stricter line-pattern gate + the `--fusion-lane` opt-in flag. Run a 5-problem N=1 pilot (chosen from C2/C3 archetypes where bare-gap has exhausted) and audit honestly whether fusion changes the outcome distribution.

---

## 7. Honesty guardrails

Designed in deliberately to prevent cargo-cult fusion:

1. **Decline is valid.** Stage 4's prompt explicitly allows `FUSION_LANE_DECLINED: <reason>`. Many problems have no honest cross-domain analogy; we should NOT force a fit.
2. **Companion file mandatory.** No companion → REJECT at submit time. This forces the `fit_score`, `honest_disclaimer`, and audit trail.
3. **Theorem statement frozen.** The fusion gate checks the theorem AST against the bare-gap version. We cannot quietly weaken the gap to fit a technique.
4. **A/B measurable.** `lane` column on every submission. We will know within 50 fusion submissions whether the lane outperforms (or ties, or underperforms) bare-gap on the same problem-IDs.
5. **Failure as data.** Aristotle's `project.ask()` follow-up converts every fusion failure into a structured "which technique blocked you, where?" record. After 100 failures we have a calibration set for Stage 3's fit-score rank.
6. **Audit extension.** `audit_proven.py` grep for the named technique in successful proofs. If the technique doesn't appear, the success is flagged for human review (Aristotle may have found a better path — or may have ignored the fusion content entirely).
7. **Cost line.** Each fusion submission's `cost_usd` column should populate from Stage 1+2+3 LLM bills + Aristotle's own cost. Fusion is expected to be 5-10× more expensive per submission. We are explicit about that.

---

## 8. Single highest-value LLM template to build first

Of the four LLM templates above (Stages 1-4), the **highest-leverage is Stage 2 (Analogy Mining)**, because:

- Stage 1 (literature breadth) is doable with existing `grok-search` skill; the LLM call is high-volume but per-call simple
- Stage 3 (technique cards) is mechanical given Stage 2 output
- Stage 4 (fusion sketch) is template-fill given Stage 3 output
- **Stage 2 is the only stage that requires genuine cross-domain reasoning** — identifying structural analogies between an NT problem and an additive-combinatorics result, or between an algebraic problem and a geometric one. F4's catalog shows ~15-25% of breakthroughs *would* be findable by good analogy mining. If our Stage 2 prompt is too cautious, fusion produces nothing. If too aggressive, we cargo-cult.

The Stage 2 prompt (Section 4) is therefore the keystone: it must elicit honest analogies AND reject false-positives. We should run it on 10 known-fusion problems first (Wiles/FLT, Maynard, Hough, etc.) with the analogy *hidden* and see whether the LLMs surface the correct analog. Only then do we trust the prompt on our open-gap shortlist.

---

## 9. 30-day implementation plan

### Week 1 — Plumbing (no new submissions yet)
| Day | Build |
|---|---|
| 1 | Fix B1: `gather_context()` status filter (one-line PR; immediately enables auto-context for all submissions). |
| 2 | Schema migration: add `lane`, `fusion_json`, `fusion_technique_attempted`, `fusion_blocker`, `fusion_followup_transcript` columns. Backfill `lane='bare'` for all existing rows. |
| 3 | Build `scripts/fusion_stage1_literature.py` (Grok search wrapper, structured markdown out). Test on 3 problems. |
| 4 | Build `scripts/fusion_stage2_analogy.py` (parallel Grok+Gemini+Codex via debate.py harness). |
| 5 | Build `scripts/fusion_stage3_techniques.py`. |

### Week 2 — Gate + Sketch (still no submissions)
| Day | Build |
|---|---|
| 6 | Implement `check_fusion_lane()` + `check_fusion_companion()` in `safe_aristotle_submit.py`. Unit tests on 5 hand-crafted sketches (1 pass, 4 reject patterns). |
| 7 | Implement `--fusion-lane` CLI flag + companion bundling. |
| 8 | Build `scripts/fusion_stage4_sketch.py`. Validate end-to-end on 2 problems (Erdős 850 existence form, Erdős 672 lim variant). |
| 9 | Calibrate Stage 2 prompt against 10 known-fusion problems (Wiles, Maynard, Hough, Croot-Lev-Pach, Helfgott, etc.) with analogy redacted. Score: does Stage 2 surface the actual analog? Target ≥4/10. |
| 10 | Add `project.ask()` follow-up loop for non-advance fusion submissions. Test path via a deliberately-failing sketch. |

### Week 3 — Pilot (5 fusion submissions)
| Day | Build |
|---|---|
| 11 | CLAUDE.md update + memory directive — formal "lane: fusion" addition. PR for review. |
| 12-13 | Pick 5 pilot problems (from C2/C3 archetypes where bare-gap has been exhausted). Run Stages 1-3 for each. |
| 14 | Generate 5 fusion sketches + companions. Manual review for proof-strategy creep before submission. |
| 15-16 | Submit all 5 to Aristotle (one per day if needed, respecting 5-slot capacity). Track via `lane=fusion` queries. |
| 17 | Audit results. Run `project.ask()` follow-up on any non-advance. Tabulate technique-attempted / blocker. |

### Week 4 — A/B + decision
| Day | Build |
|---|---|
| 18-19 | For each pilot problem, also submit (or pull from history) the bare-gap version. Direct comparison: same problem, two lanes, two outcomes. |
| 20 | Run audit: did any fusion sketch produce `compiled_advance`? Did any bare-gap produce something fusion did not? |
| 21 | Stage 2 prompt re-calibration based on failures. |
| 22-23 | Decision gate: extend pilot to 20 problems or kill the lane. Document the criterion in advance (e.g., "if 0/5 fusion submissions produce a measurable improvement over bare, abandon Stage 4-5 and keep only Stages 1-3 as a research-context source for human use"). |
| 24-25 | Documentation: write up pilot results in `docs/research/PILOT_FUSION_<date>.md`. Honest assessment. |
| 26-30 | Buffer for slow Aristotle responses, follow-up audits, schema refinements. |

### Hard exit criteria (defined NOW, before bias creeps in)

- **Go decision:** ≥1/5 fusion submissions produces `compiled_advance` with the named technique actually appearing in the proof, AND zero submissions are flagged for proof-strategy violation by an external auditor.
- **No-go decision:** 0/5 fusion advances OR ≥2/5 flagged for proof-strategy creep. Fusion lane shut down; Stages 1-3 retained as human research aid only.

---

## 10. What this design intentionally does NOT do

- **Does NOT propose bridge lemmas.** That's Step 3 of the F4 recipe, where 100% of the math sits. Aristotle's job.
- **Does NOT replace the bare-gap lane.** Bare-gap is still the default. Fusion is opt-in, problem-specific, and honest about the trade-off.
- **Does NOT promise breakthroughs.** F4's catalog gives ~5% Aristotle hit-rate on this shape of work. Realistic expectation: 0-1 wins out of 5 pilot submissions. The expected ROI is *learning whether fusion changes the distribution*, not landing a Wiles-class result.
- **Does NOT auto-publish "compiled_advance" on fusion submissions.** The `lane=fusion` flag plus the named-technique audit grep are mandatory pre-conditions for the schema-honesty status.

---

## Appendix A — Examples

### Example bare-gap (unchanged): `submissions/sketches/erdos850_existence.txt`
```
OPEN GAP: Erdős 850 — Three consecutive same-radical pairs (existence form)
Source: FormalConjectures/ErdosProblems/850.lean
Domain: nt

Existence: there are distinct positive x, y with rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2).

theorem erdos_850_existence :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y
    ∧ x.primeFactors = y.primeFactors
    ∧ (x+1).primeFactors = (y+1).primeFactors
    ∧ (x+2).primeFactors = (y+2).primeFactors := by sorry

Status: OPEN. Existence direction; no witness known.
```

### Example fusion-lane (new): `submissions/sketches/erdos850_existence_fusion.txt`
```
OPEN GAP: Erdős 850 — Three consecutive same-radical pairs (existence form)
Source: FormalConjectures/ErdosProblems/850.lean
Domain: nt
Lane: fusion

Existence: there are distinct positive x, y with rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2).

theorem erdos_850_existence :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y
    ∧ x.primeFactors = y.primeFactors
    ∧ (x+1).primeFactors = (y+1).primeFactors
    ∧ (x+2).primeFactors = (y+2).primeFactors := by sorry

# Cross-domain context (Stage 2-3 artifact, FACTUAL ONLY)
- Analog: Erdős–Woods conjecture (do there exist 4 consecutive integers with the same prime factor set?). Closest known: density-of-S-units bounds from Diophantine approximation.
- Named technique: Bilu–Tichy theorem on polynomial decompositions of f(x)=g(y) (cite: arxiv:math/0006163; also in J. Reine Angew. Math 2000).
- Structural map: same-radical condition is equivalent to (x, x+1, x+2) lying on a finite intersection of S-unit equations for specific S; Bilu–Tichy gives the decomposition classification.
- Fit score: 0.5 (S-unit framework applies, but obstruction below significant)
- Documented obstruction: Bilu–Tichy classifies POLYNOMIAL decompositions; same-radical is a SET equality, not a polynomial relation. Transfer is via the rad-equality → S-unit reduction step, which itself is unproven for triples.

# What we'd like to attempt (advisory — Aristotle may ignore)
- Reduce to S-unit equation system via the rad-equality observation (lemma: `Nat.primeFactors_eq_iff` in Mathlib).
- If reduction works, check whether Bilu–Tichy's classification of polynomial-decomposition exceptional curves overlaps the resulting S-unit shape.

Status: OPEN. No witness known. Bare-gap lane attempted (slots 717-719) produced em-tautology; this lane forces existence direction.
```

### Example `<name>.fusion.json`
```json
{
  "lane": "fusion",
  "primary_analogy": "Erdős–Woods conjecture (same-prime-factor-set on consecutive integers)",
  "named_technique": "Bilu–Tichy polynomial decomposition theorem",
  "seminal_paper_arxiv": "math/0006163",
  "fit_score": 0.5,
  "input_requirements_matched": ["Nat.primeFactors_eq_iff (Mathlib)", "ℕ structure"],
  "input_requirements_missing": ["rad-equality → S-unit reduction lemma (unproven for triples)"],
  "honest_disclaimer": "Fit score 0.5 reflects significant obstruction. Bilu–Tichy classifies polynomial decompositions; our gap is a set equality. Transfer is plausible but not mechanical.",
  "stage1_literature_path": "docs/research/fusion/erdos850/literature.md",
  "stage2_analogies_path": "docs/research/fusion/erdos850/analogies.md",
  "stage3_techniques_path": "docs/research/fusion/erdos850/techniques.md"
}
```

---

End of design.
