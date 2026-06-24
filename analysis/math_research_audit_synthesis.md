# Math Research Audit — Synthesis (Agent F10)

**Date:** 2026-05-30
**Synthesizer:** F10 of 10
**Question:** How close is our current process to math-via-research-fusion?
**Inputs:** F1 (math vs compute), F2 (sketch context), F3 (LLM consultations), F4 (cross-domain catalog), F5 (5 per-problem fusion analyses: E#64, E#203, E#672, E#938, E#952), F6 (reasoning probe), F8 (Codex pipeline), F9 (Gemini approach). F7 (pipeline design) not on disk; substituted from F8 spec + Codex/Gemini convergence.

---

## 1. The Verdict (1–10 scale)

**We are at 2/10 on research-fusion. We are at 9/10 on computational-brute-force-via-bounded-`native_decide`.**

This is not a deficit of *effort*. It is a deficit of *aim*. The pipeline is a finely-tuned witness-verifier wrapped in an LLM that pattern-matches to that verifier. The shape "find an integer / find a graph / find a residue class / decide" is what we submit, what we celebrate, and what gets celebrated upstream. Of seven `compiled_advance` artifacts (F1):

- **Pure compute:** 1 (slot736 — `native_decide` on 3^1439).
- **Compute + light glue:** 2 (slot722, slot738 — Brocard chunks; slot738 imported 2000 Python-precomputed witness primes).
- **Structural reasoning (in-domain):** 3 (slot720 mild Fermat reduction, slot737 σ₀ multiplicativity, slot739 Bezout + normal-subgroup classification).
- **Structural-external + compute-internal:** 1 (slot740: greedy set cover + CRT done off-Lean, `native_decide`-verified).
- **Cross-domain fusion:** **0**.

Across **107 LLM consultations** (F3): **0** asked an LLM to import a technique from a domain we are not already working in. The single richest math-content consult (FT p=3 q≡71) enumerated five techniques — all from inside one narrow regime of analytic NT. Across **220 non-ID sketches** (F2): **0** contain external URLs, **0** contain cross-domain literature synthesis, **0** match category 5/6 ("cross-domain literature" or "research synthesis"). The auto-context plumbing has been **silently broken** since the status rename — `gather_context()` filters for `status IN ('compiled_clean','near_miss','completed')`, none of which exist any more. We have been shipping bare gaps with **no context at all** for an unknown stretch.

So when the user asks "how close are we to research-fusion?" the technical answer is: **we are not on the path at all.** The pipeline name says "math via Aristotle"; the pipeline behavior is "computational verifier with broken auto-context."

---

## 2. The Biggest Gap

**Not the gate, not the sketch length, not the auto-context bug. The gap is the missing research stage *before* Aristotle ever sees the problem.**

The 14-breakthrough catalog (F4) is unambiguous: every modern cross-domain breakthrough has the same structure — IDENTIFY WALL → IMPORT FOREIGN OBJECT → BUILD BRIDGE LEMMA → VERIFY. Aristotle is excellent at the VERIFY step (slot740 verified a 43-digit CRT witness; slot738 verified 2000 Python-sieved primes). Aristotle does not do the first three steps. **Nothing in our pipeline does the first three steps.** The `/sketch` step skips them by design (PRIME DIRECTIVE: "no proof strategy, no key lemmas, no guidance"). The `/debate` infrastructure is general (F3 §5: `scripts/debate.py` is fully free-form), but the convention is to debate "which problem to submit," not "which technique transplant might crack it."

Two architectural facts make this gap unrecoverable inside the current pipeline:

1. **Aristotle's design wants informal sketches.** Per `aristotle_state.md` and arxiv 2510.01346: external Lean blocks with "already proven background results or lemmas tailored to the target theorem … boost performance." Every public open-Erdős win (Aristotle's own #124, #401, #645, #728; AlphaProof Nexus's 9 wins) paired a strong informal strategist with Aristotle as formalizer. Our PRIME DIRECTIVE forbids exactly the input shape the architecture is built for.

2. **Cross-domain fusion is upstream of formalization.** F4 §4: ~25–30% of historical fusion breakthroughs would have been *anticipated* by an LLM doing rich literature search; ~15–25% would be plausibly transferable by an LLM doing technique-suggestion; ~5% are within Aristotle's tactic-level reach. The leverage is at the *upstream* LLM stage, not at the Lean stage. Our 87/13 split (F3: 87% META-PROCESS consults vs 13% MATH-CONTENT consults) inverts that ratio.

---

## 3. The 5 Highest-Leverage Upgrades (Ranked)

### Upgrade #1 — Build the research-fusion dossier stage upstream of Aristotle

**Adopt Codex's 9-stage pipeline** (F8 §A): `00_problem_screen → 01_literature_delta → 02_transfer_mining → 03_obstruction_matrix → 04_mathlib_surface → 05_fusion_tournament → 06_airlock_sketch → 07_aristotle_run → 08_postmortem`. The dossier is OFF-Lean. The final Aristotle submission is still INFORMAL, ≤30 lines, and pass-the-gate clean — only because the bridge lemma was already chosen at stage 06. Gemini's Phase 1–4 (F9) maps onto the same skeleton.

**Why this is #1:** every upgrade below depends on having a structured upstream stage that can hold cross-domain content without violating the gate. Without it, the team is forced to choose between "bare gap that Aristotle pattern-matches" and "essay that the gate rejects." With it, the gate is preserved AND research fusion is possible.

**Operational test:** after dossier construction for one problem, the 06 airlock sketch must (a) pass `check_gap_targeting()` unchanged, (b) read as a bare gap, (c) be backed by a 500–2000 word dossier that an Aristotle prompt *could* selectively cite via `--context` if we choose. The dossier is the project's institutional memory; the sketch is the wire submission.

### Upgrade #2 — Fix `gather_context()` AND extend it to literature

F2 §4: the status filter is broken — has been returning empty for an unknown duration. Fix it (`status IN ('compiled_advance','compiled_partial','disproven')`). Then add a `gather_external_context(problem_id)` helper that pulls from (a) `analysis/literature_freshness_may30.csv` and (b) a new `research_fusion/data/lit/papers.sqlite` (F8 §D) of arxiv/Crossref/OEIS theorem snippets.

**Why this is #2:** if upgrade #1 lands but the auto-context plumbing still attaches nothing on the wire, the dossier is invisible to Aristotle. This is the highest-leverage one-day engineering change.

### Upgrade #3 — Drop the PRIME DIRECTIVE's "bare conjecture only" clause for serious gap-targeting attempts

The directive's spirit ("zero bloated proof essays") is correct. Its letter ("zero proof guidance, ≤30 lines, no key lemmas") prevents the documented Aristotle-winning workflow. Replace with:

> Gap-targeting submissions for OPEN problems require a bounded informal sketch (150–400 words) + 3–5 candidate lemmas + 1 bridge-lemma citation. Bare conjectures are permitted only for falsification probes, baseline controls, or schema-honesty ablations.

This is the consensus position from F1 (slot737/739 show structural reasoning *is* possible when invited), F2 (sketch shape is the bottleneck), F3 (consultations stay inside the chosen technique because the convention is to ask "which problem"), F6 (the H2 hypothesis must be tested — rich sketches may unlock latent reasoning), F8 (Codex: "stop submitting 'find a finite certificate' problems unless the upstream dossier contains a non-computational bridge theorem"), F9 (Gemini: Phase 3 simplified conjecture comes AFTER analogical mapping).

**Cost:** rewriting Hard Rules #2, #3, #6; the new `check_gap_targeting()` accepts bounded sketches with lemma lists, still rejects bloated essays, still rejects em-tautologies and `(P) ∨ ¬ (P)`.

### Upgrade #4 — Re-purpose `scripts/debate.py` from "portfolio committee" to "cross-domain technique scout"

F3 §5–6: the harness is fully general; the convention is the limit. Add 4 prompt templates (F3 §6) — cross-domain technique fusion, adjacent-analog discovery, "what would Tao/Bhargava/Maynard try", bias-flush — and run them BEFORE submission. Each template costs ~$3–5 in API spend; budget 3 per attempted closure.

**Why this is #4:** F4 §4 says LLM technique-transfer suggestion is the most leverageable AI capability. F5 confirms this concretely — every one of the five fusion analyses (E#64 Cayley graphs of small-cancellation groups, E#672 Frey curves + Chabauty, E#938 Bennett-Skinner modular method, E#203 multiplicative-orbit structure of ⟨2,3⟩ in (ℤ/p)*, E#952 percolation theory) **was generated** by F5 doing exactly the work we have never asked our debate harness to do.

### Upgrade #5 — Refuse to count brute-force advances as "advance"

F1: 4 of 7 advances are dominated by external precomputation or single-line `native_decide`. Add a `closure_axis_json` column (per `closure_list_may30.md` decision rule: CS/CM/CR/HM) AND a `mathematical_content_score` (1–5) populated by the audit hook by counting `native_decide` invocations + flagging Python-precomputed witnesses (any literal integer >10^10, or any literal Finset literal with >50 elements that didn't come from a prior Aristotle context).

**Operational:** Submissions where `mathematical_content_score ≤ 2` are tagged `compiled_no_advance_mechanical` regardless of compilation status. This is the operational version of CLAUDE.md Rule 12.

**Why this is #5 (not #1):** without it, the upgrades above will land and we will not be able to tell whether they worked. With it, the cost of doing things wrong becomes immediately visible.

---

## 4. 30 / 60 / 90 Day Plan

### Days 1–30 — Build the dossier stage; do not change submission policy yet.

- Land Upgrade #2 (gather_context fix + literature pull) — half-day.
- Land Upgrade #5 (audit columns + math-content score) — one day.
- Build Codex's 9-stage scaffolding (F8 §D): `sync_erdos.py`, `query_lit.py`, `index_mathlib.py`, `airlock_check.py`. — 4–5 days.
- Run dossier construction on the 2 ACTUAL fusion-amenable problems from F5 (see §6 below): **E#672 k=4 ℓ=3** (Frey curve + Chabauty) and **E#938** (Frey-Hellegouarch + Ribet level-lowering). Each dossier ~$50 API spend, ~2 days wallclock.
- Do **not** submit during this window. The dossier is the deliverable.
- Quick win to celebrate: the broken `gather_context()` will be the single biggest reveal of the audit; landing the fix turns "bare conjecture only" from a *policy* into a *measurement* — we'll know if attaching prior `compiled_advance` results actually changes Aristotle's behavior.

### Days 31–60 — Run Experiment A (F6) and one dossier-backed submission.

- Run F6 Experiment A (bare vs rich Brocard [51,100]) — Aristotle clean comparison on a guaranteed-closeable target. Information value: distinguishes H1 (capability ceiling) from H2 (sketch ceiling). Cost: 1 slot pair, $20, 1 day wallclock.
- Submit **ONE** dossier-backed sketch from the day-1–30 dossiers (probably E#672 k=4 ℓ=3 — strongest Aristotle-history match per F5 and closure_list top-20 #20). Sketch passes gate; dossier attached as `--context`. Cost: 1 slot, $50–100, 9 hours wallclock.
- Hold all other submissions. The 30-shortlist of `snipe_list_may30.md` is still active in parallel via existing pipeline; the closure track is the test.
- F6 Experiment B (E#952 Gaussian moat research-fusion sketch) — defer until A returns.

### Days 61–90 — Scale or roll back.

If days 31–60 produced **any** of: (a) measurably different proof structure on rich-sketch arm, (b) compiled non-trivial bridge lemma from a dossier-backed submission, (c) Aristotle citing the dossier's literature in `ARISTOTLE_SUMMARY.md`:
- Relax the PRIME DIRECTIVE per Upgrade #3.
- Build out 5 more dossiers from `closure_list_may30.md` top-20 (focus: σ-multiplicativity family, Goormaghtigh (5,3), E#203, Erdős 137 k=4).
- Run Experiment B (E#952 percolation theory) — high-cost, low-probability, high-signal.

If days 31–60 produced none of the above:
- Roll back. PRIME DIRECTIVE stays.
- Keep the audit columns (Upgrade #5) and the fixed `gather_context` (Upgrade #2).
- Re-orient the project: we are a computational-verification pipeline, not a research-fusion pipeline. The 30-shortlist is correctly targeted. The honest expected output is ~1–2 `compiled_advance` per month, all bounded-version closures. Stop calling it "math."

---

## 5. Trade-offs (Honest)

| Dimension | Current pipeline | Research-fusion pipeline |
|---|---|---|
| **Speed per attempt** | 9 hours wallclock, $5–20 API spend | 2–5 days wallclock, $200–500 (dossier + Codex/Gemini + Aristotle) |
| **Base rate** | 7 advances / 1166 submissions ≈ 0.6% (and most are mechanical) | F4 honest estimate: ~1–3% on well-chosen dossier-backed targets; rest still `compiled_no_advance` |
| **Cognitive load on operator** | Pick problem → submit. ~5 minutes. | Pick problem → 3 LLM consults → dossier review → airlock check → submit. ~3 hours per submission. |
| **Uncertainty per submission** | LOW. We know what Aristotle will produce (native_decide template or sorry). | HIGH. Every dossier-backed attempt is genuinely betting that a bridge lemma exists and Aristotle can verify it. |
| **Meaning per success** | "We verified n=1500." Tabulation. | "We closed (k=4, ℓ=3) of Erdős 672 via Frey-curve + Chabauty." Journal-clean novel mathematics. |
| **Recovery from failure** | Re-submit with bigger bound. Cheap. | Postmortem dossier reveals which bridge failed; next attempt picks a different bridge. Expensive but informative. |
| **Risk of theater** | LOW. Aristotle returns compute or sorry. | HIGH. A polished dossier can produce a polished but mathematically-empty Lean wrapper. Mitigation: Upgrade #5's math-content score. |
| **AlphaProof Nexus comparison** | 0 / 1166 vs 9 / 353 — we are 30× behind on hit rate. | If we hit 1–3%, we close 5–15 advances per 500 attempts. Comparable to AlphaProof Nexus. |

**What gets harder:** Honesty. The current pipeline lies to us via "compiled_advance" labels on mechanical tabulations. The research-fusion pipeline requires us to publicly accept that 95–99% of our prior advances were not, in fact, mathematical advances. CLAUDE.md Rule 12 already says this. The pipeline does not enforce it.

**What gets slower:** Volume. We currently submit ~30/month. Research-fusion submits ~5–8/month. The discipline shift is from "more cheap shots" to "fewer expensive bets."

**What gets more uncertain:** Per-submission outcome. We currently know roughly what will happen on each submission. We will not know what will happen on a dossier-backed submission — the bridge may not work, or Aristotle may not be able to formalize it. That uncertainty is the price of admission to the only workflow that has ever produced a public open-Erdős resolution.

---

## 6. The Closure-Candidate Reality Check (Top-20 → Fusion-Amenable)

F5 ran research-fusion analyses on the five closure_list top-20 candidates with the most "open creative step" load. Verdict (per F5 own honest assessments):

| Problem | F5 plausibility | Fusion type | Verdict |
|---|---|---|---|
| **E#64 (Erdős-Gyárfás 2^k cycles)** | 3/10 | Cayley graphs of small-cancellation groups via Magnus/Lyndon | **FUSION-AMENABLE.** Real cross-domain ingredient (combinatorial group theory → graph theory). No current SAT search has tried the group-theoretic framing. |
| **E#203 (2D Sierpiński)** | 6/10 | Multiplicative orbit structure of ⟨2,3⟩ in (ℤ/p)* | **MIXED.** The fusion ingredient (multiplicative subgroup structure) is the *standard* approach. Real novelty would be Aurifeuillean factorization import. Borderline. |
| **E#672 k=4 ℓ=3** | 5/10 | Frey curve + Chabauty on rank-1 Jacobian + Mordell-Weil sieve | **FUSION-AMENABLE.** Genus-2 curve at threshold; Chabauty machinery; LMFDB rank lookup. Genuine algebraic-geometry import. Caveat: GHP 2009 may already cover it — must do literature delta first. |
| **E#938 (powerful 3-AP)** | 4/10 | Frey-Hellegouarch curve + Ribet level-lowering | **FUSION-AMENABLE.** Frey curve attached to consecutive powerful triple; weight-2 cusp forms space; Bennett-Skinner machinery. Genuine modular-forms import. |
| **E#952 (Gaussian moat)** | 2/10 | Site percolation + Aizenman-Barsky + de-randomization via L-functions | **NOT FUSION-AMENABLE BY US.** The de-randomization step is the open problem itself. 2024 withdrawn proof shows researchers can't close this. Bridge lemma does not exist. |

**Honest count: 2 of our top-20 closure candidates are actually fusion-amenable for us right now: E#672 k=4 ℓ=3 (Frey+Chabauty) and E#938 (Bennett-Skinner Frey).**

Both share the same machinery (Frey curves attached to Diophantine triples → level-lowering → small cusp-form space). This is the **single highest-leverage fusion direction** the project can pursue in days 31–60. Both are within the algebraic-NT region where Mathlib has growing infrastructure (`ModularForms`, `EllipticCurve`, `CuspForm`). Aristotle has demonstrated structural-reasoning capability on σ-multiplicativity (slot737) and group theory (slot739) — the Frey + level-lowering chain is one or two steps farther down the same road.

The remaining 18 candidates in the top-20 are computational by nature (Brocard bumps, FT q-bumps, multiplicativity-shape extensions, witness-table chunkings). Useful as engineering output, NOT closure candidates under the C2 rubric. The honest path: keep the engineering lane running on those, and put the fusion lane on E#672 k=4 ℓ=3 + E#938.

---

## 7. The Single Most Important Change

**Stop ASKING "which problem should we submit to Aristotle?" Start ASKING "what cross-domain technique might crack the wall on this problem, and can our 4-LLM ensemble find and formalize it?"**

The harness is built. F3 §5: `scripts/debate.py` is fully general. The bottleneck is the prompt convention and the gate philosophy. 87/13 META-PROCESS-vs-MATH-CONTENT is the diagnostic; 50/50 (or 30/70 in favor of math content) is the target.

If we land Upgrade #1 (research-fusion dossier stage) and Upgrade #4 (debate.py as cross-domain technique scout), and we test it on **E#672 k=4 ℓ=3** (the strongest fusion-amenable candidate, with both algebraic-geometric depth and an Aristotle-friendly Lean target), and Aristotle either (a) verifies a non-trivial Frey-curve discriminant computation, (b) cites Bennett-Skinner in its summary, or (c) reaches for the Mathlib `EllipticCurve.Jacobian` API even partially — then the H2 hypothesis (latent reasoning unlocks with rich input) gets meaningful posterior weight, and the next 6 months should look like a pivot toward research-fusion across the whole pipeline.

If none of those happen on the cleanest possible fusion target, then F4's honest verdict stands: Aristotle is a verifier, not a discoverer. The 30-shortlist is correctly targeted; we should drop the "research-fusion" framing and rebrand internally as a computational-verification engine that occasionally surfaces structural micro-insights (slot737-class).

Either outcome is informative. Today, we cannot tell which is true — because we have never tested the rich-input mode on a fusion-amenable target. That single experiment is the highest-information-value move available.
