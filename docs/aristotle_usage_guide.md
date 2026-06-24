# Aristotle Usage Guide (v1.0)

**Date**: 2026-05-30
**Author**: I5 (documentation synthesis), drawing on W1 / W4 / W7 / W8 research and F-team audit findings.
**Headline**: **Aristotle is a hybrid solver-formalizer with three subsystems. We have historically used only one (the formalizer). The FUSION lane is how we start using the other two.**

This document is the single source of truth for what Aristotle is, what it can do, and how to invoke it.

---

## 1. What is Aristotle?

### Provenance

- **Built by**: Harmonic AI (Harmonic Inc.). NOT Anthropic, NOT DeepMind, NOT Bates, NOT UC Berkeley.
- **Co-founder / CEO context**: Vlad Tenev (also CEO of Robinhood). Harmonic raised ~$120M; valuation $1.45B+ (Implicator, late 2025).
- **Endpoint**: `https://aristotle.harmonic.fun` (server-side; ~22KB SDK, all heavy lifting remote).
- **SDK**: `aristotlelib` (current version 0.7.0; wheel at `/Users/patrickkavanagh/math/aristotlelib-0.7.0-py3-none-any.whl`).
- **Author roster** (arXiv:2510.01346): "The Harmonic Team" (23 authors), including Tudor Achim, Alex Best (Mathlib contributor), Sergei Gukov (Caltech), Daniel Halpern-Leistner, Yury Kudryashov (Mathlib maintainer), Vlad Tenev, Harold Williams.
- **Public talks**: Lean Together 2026 (Cambridge), Alex Best — "Aristotle, an AI theorem prover using Lean."

### Citations

- arXiv paper: <https://arxiv.org/abs/2510.01346>
- HTML version: <https://arxiv.org/html/2510.01346v1>
- Harmonic PDF: <https://harmonic.fun/pdf/Aristotle_IMO_Level_Automated_Theorem_Proving.pdf>
- Cambridge seminar: <https://www.cst.cam.ac.uk/seminars/list/243277>
- E728 writeup: <https://arxiv.org/abs/2601.07421>
- Tao Mathstodon thread: <https://mathstodon.xyz/@tao/115639984077620023>

---

## 2. The Three Subsystems

Aristotle is **NOT a single LLM call**. It is an agentic system with three subsystems, memory, and test-time training (TTT). Knowing which subsystem fires on which submission is the difference between 0.8% hit rate and a real shot at the problem.

### 2.1 Monte Carlo Graph Search (MCGS) — the formalizer

- 200B+ parameter transformer as policy + value function over Lean states.
- Generalizes MCTS to a directed graph with equivalence classes (states compared by goal expressions, local context, local variable names).
- Action history included in prompts to reduce circular trajectories.
- **Fires on**: bare Lean sketch with `sorry`, no informal prompt. This is the BARE lane.
- **Strength**: closes short proofs, finite verifications, bounded extensions.
- **Weakness**: cannot invent global strategy; if the proof requires a non-obvious auxiliary set or invariant, MCGS will time out.

### 2.2 Lemma-based informal reasoner — the discovery engine

- Natural-language proof generation → lemma decomposition → autoformalization → Lean REPL feedback loop → iteration.
- Hidden chain-of-thought with dynamic thinking budget.
- Co-evolution of formal Lean + informal comments + hidden CoT during training.
- Documented behavior: **repairs flawed informal reasoning during formalization** (e.g., caught the "strictly vs. weakly decreasing" confusion mid-attempt).
- **Fires on**: informal prompt (natural-language problem statement) OR paired strategy in a `.fusion.json` companion.
- **Strength**: invents auxiliary definitions (IMO 2025 P3 — invented set S "not directly defined or suggested by the problem statement"; IMO P5 — invented invariant f(k)), repairs flawed strategy mid-attempt, identifies redundant hypotheses, finds counterexamples to false statements.
- **W8 finding**: this project has **NEVER** used this subsystem. The FUSION lane (added May 30 2026) is the lever.

### 2.3 Yuclid geometry solver

- AlphaGeometry-style; algebraic + diagram-based.
- Used for IMO 2025 Problem 2.
- **Fires on**: plane geometry problems (synthetic, not analytic).
- **Out of scope for this project** (we target Erdős / number theory / combinatorics).

### 2.4 Test-Time Training (TTT)

When a problem isn't solved on the first attempt, Aristotle **retrains the model on search traces from these attempts**. This enables cross-pollination between lemmas from different proof sketches. The model literally learns mid-submission.

- Implication: a `compiled_no_advance` result is not pure waste; the lemma traces feed TTT for subsequent submissions on related problems.
- This is why `mk context <problem_id>` matters — it gives Aristotle the prior trace material.

---

## 3. The Four Lanes

Per the I2 schema unification (May 30 2026), `submissions.lane` takes one of four values: `bare`, `closure`, `fusion`, `informal`. Section 7 below describes the CLI flags that select each lane.

### 3.1 BARE lane (default)

**What it is**: A bare ≤30-line `.txt` sketch with the open conjecture as a single `theorem ... := by sorry`. Auto-context attaches prior Aristotle results.

**Subsystems invoked**: MCGS only.

**When to use**: Default for first submission. Best for long-tail Erdős problems with explicit finite or decidable cores. Best for falsification ("is this gap real?").

**Hit rate (empirical)**: 0.8% on hard Erdős, higher on easy-tail combinatorics.

**Example success**: slot737 (E647 Sophie residue subclass) — Aristotle independently constructed σ₀ bounds 6 and 7 for the residual class. Constructive-search closure, mathematical_content_score ~6.

**Example failure**: slot725 / slot726 (Erdős 850) — produced em-tautology `(P) ∨ ¬P`, Aristotle discharged via `exact em _` in one line. Gate now rejects em-tautology disjunctions.

### 3.2 CLOSURE lane

**What it is**: BARE sketch + `.closure.json` companion (per `docs/closure_axis_companion_spec.md`). The gate (`check_closure_axis()`) reads the companion and rejects unless `real_closure_candidate=true` or `--rubric-points` override.

**Subsystems invoked**: MCGS only. The closure axis is for our audit honesty, not for Aristotle.

**When to use**:
- Mechanical extensions of prior `compiled_advance` rows (with `--rubric-points` override + honest `mathematical_content_score ≤ 4`).
- Problems where the closure mechanism is known and explicit (`explicit_witness`, `witness_table_chunked`).
- Anytime you want to commit ex-ante to "this submission targets real closure, not a bounded extension."

**Hit rate (estimated)**: 2-5%. New lane; insufficient data.

**Anti-pattern**: Counting `bounded_version_closure` as `compiled_advance`. The closure lane exists precisely to block this.

### 3.3 FUSION lane

**What it is**: BARE sketch + `.fusion.json` companion containing an informal strategy outline (≤80 lines) produced by paired LLMs (Codex, Grok, Gemini, GPT-5.2 Pro, Claude). The companion is airlocked: kept in a separate directory until human review before submission. CLI flag: `--fusion-lane --paired-llm <model>`.

**Subsystems invoked**: MCGS, plus informal reasoner if the strategy material is meaty enough.

**When to use**:
- After a BARE-lane submission has returned `compiled_no_advance`.
- For novel problems where the closure mechanism is unknown but a paired-LLM strategy dossier exists.
- For problems requiring auxiliary-set / invariant invention (the W7 sweet spot).
- E728 (paired GPT-5.2 Pro + Aristotle, Jan 2026) is the public proof-of-concept; the first AI-resolved Erdős problem fully via this pattern.

**Hit rate**: unknown. E728 is the prototype.

**Required companion fields** (`.fusion.json`, schema TBD; see sibling I-agent outputs):
- `paired_llm`: model name (lowercase, see `feasibility_filter_rubric.md` v1.1 enum)
- `strategy_outline`: ≤80-line natural-language strategy (NOT proof; lemma decomposition is OK)
- `key_lemmas`: list of stated lemmas with informal justification (NO `by sorry` Lean blocks — that goes in the BARE sketch)
- `cross_domain_literature`: at least one citation (per F2 finding, this column starts at zero attached)
- `airlock_status`: `pending_review | approved | rejected`
- `rationale`: one English paragraph; why is this novel? what failed in BARE?

### 3.4 INFORMAL lane

**What it is**: Submission of the bare problem statement in natural-language form (no Lean scaffold required) to Aristotle's informal-reasoner subsystem. CLI flag: `--informal-mode`. Sets `informal_mode_used=1` in DB.

**Subsystems invoked**: Lemma-based informal reasoner FIRST (subsystem #2), then MCGS formalizes.

**When to use**:
- Novel problems where no Lean scaffold yet exists.
- Re-running a problem that BARE / CLOSURE / FUSION has exhausted.
- Replicating the Boris Alexeev E124 workflow (informal problem statement only, ~6 hours wall time).

**Hit rate**: unknown; E124 is the prototype (Boris Alexeev, Dec 2025, ~6 hours, problem #124).

**Caveat (W8 finding)**: This project has historically never used this lane. It is the W8 expansion lever as of May 30 2026.

---

## 4. Documented Success Patterns

### 4.1 E124 (Erdős Problem #124, Boris Alexeev, Dec 2025)

- **Lane**: FUSION (informal-mode, bare problem statement only — no Lean scaffold)
- **Operator**: Boris Alexeev (Harmonic)
- **Wall time**: ~6 hours autonomous + ~1 minute Lean formalization
- **Mechanism**: Aristotle's informal reasoner located the proof; the MCGS subsystem formalized it.
- **Endorsement**: Terence Tao publicly accepted on Mathstodon.
- **Caveat (community)**: "the most simple proof possible" — Erdős had omitted a key hypothesis; the problem was open due to neglect rather than depth.
- **Reproduction lesson**: informal-mode submission of the bare problem statement, no proof guidance, ~6 hour wall clock. THIS IS THE FUSION LANE PROTOTYPE.

### 4.2 E728 (Erdős Problem #728, Jan 2026)

- **Lane**: FUSION (paired GPT-5.2 Pro + Aristotle)
- **Operator**: Kevin Barreto (Harmonic); writeup by Nat Sothanaphan (arXiv:2601.07421)
- **First Erdős problem fully resolved autonomously by an AI system** (per writeup).
- **Mechanism**: GPT-5.2 Pro generated the informal strategy; Aristotle's informal reasoner + MCGS formalized and extended.
- **Mathematical content**: Kummer's theorem + base-p carry counting + "carry-rich but spike-free" choices of m.
- **Lesson**: stronger informal-reasoner pairing → stronger formalization. The paired-LLM model is the load-bearing pattern.

### 4.3 E1026 (Aristotle, formalize-and-extend role)

- **Lane**: FUSION (paired role)
- **Mechanism**: Existing human strategy formalized + extended by Aristotle.
- **Lesson**: Aristotle's informal reasoner can extend a partial human strategy in formalization.

### 4.4 E481 (Barreto, alone)

- **Lane**: FUSION (informal mode, no human strategy)
- **Lesson**: Aristotle alone CAN solve a non-trivial Erdős problem given the bare problem statement in informal mode.

### 4.5 Polya–Szegő (Igor Rivin, 80 inequalities, 100% formalization)

- **Lane**: BARE (autoformalization role)
- **Mechanism**: MCGS closes 80/80 inequality formalizations from a textbook.
- **Calibration**: This is the benchmark where general LLMs alone scored 2.8% and Aristotle scored 100% — the 30x gap is real for textbook-style problems.

### 4.6 IMO 2025 (5/6 gold-level Lean)

- **Lane**: FUSION (problem-specific)
- **P3**: Aristotle invented an auxiliary set S "not directly defined or suggested by the problem statement."
- **P5**: Aristotle invented an invariant f(k).
- **Lesson**: invariant invention is a real capability when the informal reasoner is engaged.

---

## 5. Documented Failure Modes

### 5.1 Overclaiming (the 33% semantic-drift problem)

- **Source**: Igor Rivin, post-Polya-Szegő analysis.
- **Finding**: Aristotle proves 97.6% of attempted theorems, but only 67% are semantically correct. It can "prove the wrong theorem a third of the time, fluently and confidently."
- **Mitigation**: `audit_proven.py` audit gate; `mathematical_content_score` ex-ante check; `target_resolved` column in DB.

### 5.2 Hallucinated proofs via axiomatization

- **Pattern**: Aristotle introduces a new `axiom Foo : ...` to close a proof obligation. The Lean kernel accepts it, but mathematically it's `sorry` in disguise.
- **Mitigation**: `axiom_count` and `axiomatizes_prior_work` columns; `compiled_advance` requires `axiomatizes_prior_work=0`.

### 5.3 EM-tautology pathology

- **Pattern**: Conjecture stated as `(P) ∨ ¬P`. Aristotle discharges via `exact em _` in one line. PILOT_ERDOS850 (May 28 2026) found 3/3 arms produced this under the disjunction template.
- **Mitigation**: `check_gap_targeting()` C6 — gate rejects em-tautology disjunctions. State as existence OR impossibility, never their disjunction.

### 5.4 `iff_rfl_trap`

- **Pattern**: Conjecture restated as `P ↔ P` or trivially equivalent forms. Aristotle proves with `rfl`. No mathematical content.
- **Mitigation**: closure-axis CR enum includes `iff_rfl_trap`; closure-axis gate rejects.

### 5.5 Bounded-version-as-advance

- **Pattern**: Submit `∀ n ≤ N, P n` for some bounded N, succeed via `native_decide`, claim closure of the unbounded conjecture. Slot736 (FT q ≤ 1500) and slot738 (Brocard [501,1000]) are clean examples.
- **Mitigation**: closure-axis CS enum forces `bounded_version_closure` vs `full_closure`; honesty marker HM forces `journal_partial` vs `journal_clean`.

### 5.6 Smuggled falsified approach

- **Pattern**: An approach previously documented in `failed_approaches` (Tuza apex bridge, etc.) is rephrased and resubmitted.
- **Mitigation**: `mk failed <keywords>` query before drafting; audit cross-checks.

### 5.7 Brute force masquerading as discovery (F1 audit finding)

- **Pattern**: 57% of historical `compiled_advance` rows in this project were brute-force bounded extensions, not genuine mathematical content.
- **Mitigation**: `mathematical_content_score` (0-10, audit-populated, capped by closure-axis CS); FUSION lane shifts work toward subsystem #2.

### 5.8 Stale literature (F2 audit finding)

- **Pattern**: 0/220 sketches had cross-domain literature attached; auto-context query was silently broken.
- **Mitigation**: I1 fix to auto-context query; literature-check hard rule (CLAUDE.md #13); FUSION lane `cross_domain_literature` required field.

---

## 6. Calibration: What Hit Rate To Expect

These are honest priors as of May 30 2026, based on the F-team and W-team audits. Update as data lands.

| Lane | Problem class | Hit rate (expected) | Confidence |
|---|---|---|---|
| BARE | Easy-tail Erdős (combinatorics, NT with finite core) | 1-5% | medium |
| BARE | Structural-open Erdős (Tuza, Lehmer, etc.) | <0.1% | high (empirical floor) |
| BARE | Bounded verification (`finite-verification` category) | 50-80% if `native_decide` budget fits | high |
| BARE | Constructive-search with explicit recipe | 10-30% | medium |
| BARE | Formalization-only (known math, port to Lean) | 80-95% | high (Polya-Szegő type) |
| CLOSURE | Same as BARE, but with honest closure-axis classification | same as BARE | new lane, May 30 2026 |
| FUSION | Long-tail Erdős paired with strong informal reasoner | 5-15% (extrapolating E728 + E124 + E481) | low (small sample) |
| FUSION | Structural-open paired with strong informal reasoner + literature | unknown; this is the bet | speculative |
| FUSION | Famous open conjectures (Goldbach, twin primes, etc.) | 0% | high (Tao "long tail" caveat) |

**Tao's framing** (from public Mathstodon thread, late 2025): "automated sweeps are now beginning to resolve the lowest hanging fruit." The easy tail is the AI sweet spot. Famous open conjectures remain out of reach.

**Operational rule**: budget ~6 hours per FUSION submission (E124 wall time); don't expect breakthroughs on famous conjectures; do expect a slow trickle of long-tail Erdős closures.

---

## 7. How to Invoke Each Lane (current commands)

```bash
# BARE lane (default) — implicit
/sketch <problem>           # Draft bare ≤30-line .txt
/submit <file>              # Gap-targeting gate -> auto-context -> submit INFORMAL
# DB: lane='bare', informal_mode_used=0, paired_llm='none'

# CLOSURE lane (requires .closure.json companion)
# Draft .txt as usual, then create submissions/sketches/<name>.closure.json
# (see closure_axis_companion_spec.md)
/submit <file>              # check_closure_axis() reads companion
# DB: lane='closure' (when real_closure_candidate=true), 'bare' otherwise
# For mechanical extensions: pass --rubric-points to override

# FUSION lane (requires .fusion.json companion, airlocked)
python3 scripts/safe_aristotle_submit.py <file> \
    --fusion-lane \
    --paired-llm gpt-5.2-pro
# DB: lane='fusion', paired_llm=<model>, fusion_json=<dossier>

# INFORMAL lane (Aristotle informal-reasoner subsystem)
python3 scripts/safe_aristotle_submit.py <file> \
    --informal-mode \
    [--paired-llm <model>]
# DB: lane='informal', informal_mode_used=1
```

CLI flag precedence (in `safe_submit()`):
1. `--informal-mode` → `lane='informal'`
2. `--fusion-lane` → `lane='fusion'`
3. `.closure.json` has `real_closure_candidate=true` → `lane='closure'`
4. Default → `lane='bare'`

(The FUSION and INFORMAL lane companion schemas are being defined by sibling I-agents — see CHANGELOG. Details may shift; this section will update once those land.)

---

## 7.5 BARE vs INFORMAL Mode Output: Empirical Comparison

**As of May 30 2026, we have a direct empirical comparison between the two output formats.** This section documents what each lane returns, the four validation criteria for confirming subsystem #2 engagement, and when to use each lane.

### Side-by-side output comparison

| | BARE-mode output (typical) | INFORMAL-mode output (I9 smoke test) |
|---|---|---|
| **Tarball contents** | Single `.lean` file in `RequestProject/` | `ARISTOTLE_SUMMARY.md` + `RequestProject/Main.lean` |
| **`ARISTOTLE_SUMMARY.md`** | Absent OR auto-generated minimal header | Present with explicit `## Informal proof:` and `## Formalization:` sections |
| **NL narrative** | None, or in Lean comments only | Standalone Markdown document explaining the proof in English before the Lean form |
| **Lean body** | `theorem name : type := by native_decide` or `:= by decide` or a few tactic lines | Minimal wrapper around a Mathlib lemma (e.g. `Exists.imp (by tauto) (Nat.exists_infinite_primes (n + 1))`); the strategy lives in the Markdown, not the Lean |
| **Subsystem invoked** | MCGS (subsystem #1) only | Lemma-based informal reasoner (subsystem #2) → MCGS for formalization |
| **Two-channel response?** | No — single artifact | Yes — formal Lean + informal narrative |
| **Canonical reference** | (no single artifact; the historic 1166 BARE submissions are the corpus) | `docs/research/aristotle_smoke_test_euclid_may30.md` (UUID `8d500201-0786-4bb2-8489-2f6aad91be91`) |

**The decisive marker:** a standalone `ARISTOTLE_SUMMARY.md` with an explicit "Informal proof:" header section is empirical evidence the informal reasoner was engaged. Its absence is empirical evidence MCGS ran alone.

### The 4 validation criteria (S10 pivot rule)

When an INFORMAL or FUSION lane submission returns, check the result against these four criteria (originally defined in `docs/e938_fusion_validation_watch.md` for E938's Frey-Hellegouarch attempt; they generalize to any informal-lane submission):

1. **Named-technique citation.** Does the NL summary cite the specific technique named in the companion's `named_technique` field? (e.g. "Bennett-Skinner", "Frey curve", "Euclid's argument", "Kummer's theorem")
2. **Mathlib cross-domain import.** Does the returned `.lean` import a Mathlib module that maps to the strategy domain? (e.g. `Mathlib.NumberTheory.ModularForms.*` for E938, `Mathlib.NumberTheory` for Euclid)
3. **Separate NL reasoning trace.** Is there a natural-language artifact (the standalone `ARISTOTLE_SUMMARY.md`) distinct from the Lean source, with an "Informal proof:" or equivalent section?
4. **Non-trivial candidate-lemma partial.** Does the `.lean` reference any of the candidate lemmas listed in the companion's `candidate_lemmas` field, with a partial proof body (not a bare `sorry`)?

**Decision rule** (per S10):

| Criteria firing | Decision |
|---|---|
| 0 / 4 | Shelve the lane; treat as too costly relative to BARE baseline. |
| 1 / 4 | Lane validated. Continue but tighten companion JSON. |
| 2-3 / 4 | Lane strongly validated. Scale to additional `problem_id`s. |
| 4 / 4 | Pivot confirmed. FUSION/INFORMAL is the new default for high-difficulty problems. |

The I9 Euclid smoke test fires criteria 1, 2, 3 (cites "Euclid's argument", imports `Mathlib`, has standalone NL trace). It does not fire criterion 4 because the Euclid sketch had no candidate lemmas (it was a routing test, not a fusion test). For Euclid this is 3/4 — strong validation that the pipeline routes correctly when an informal companion is present.

### When to use each lane (consolidating the S1 lane-routing matrix)

Per `docs/lane_routing_matrix.md`, route by problem class:

| Problem class | Recommended lane | Why |
|---|---|---|
| Finite verification with computable bridge | BARE | MCGS closes `native_decide` cleanly. |
| Bounded narrowing of unbounded conjecture | BARE + CLOSURE companion | MCGS handles the bounded check; CLOSURE companion forces honest classification. |
| Explicit witness construction | BARE | MCGS verifies the witness given the explicit recipe. |
| Disproof via small counterexample | BARE | MCGS evaluates the counterexample. |
| Solved-upstream formalization | BARE | Pure autoformalization role; Polya-Szegő pattern. |
| Structural-open with cross-domain potential | FUSION | Bare returns `compiled_no_advance` >99% of the time per F1 audit; the informal reasoner is the lever for invariant invention. |
| Famous deep conjectures | (none — Tao "long tail" caveat) | Don't submit. |
| Long-tail neglected Erdős (Tao "lowest hanging fruit") | INFORMAL (no Lean scaffold) | E124 / E481 prototype: bare problem statement, ~6h wall time, informal reasoner alone. |

**Operational sequence for a new structural-open problem:**

1. BARE lane first (default). If `compiled_no_advance`, move to step 2.
2. Build a `.fusion.json` companion with a paired-LLM strategy. Submit via FUSION lane (`--fusion-lane`). Check criteria 1-4.
3. If FUSION returns 0/4, fall back to INFORMAL lane (no Lean scaffold; bare problem statement only). This is the E124 / E481 reproduction.
4. If 0/4 across all three lanes for the same problem after 3 attempts, shelve. Move on.

### Canonical reference

The single source of truth for "what informal-mode output looks like" is `docs/research/aristotle_smoke_test_euclid_may30.md`. Any audit ambiguity about whether subsystem #2 was engaged on a future submission should be resolved by comparing to that artifact.

---

## 8. Sanity Checks Before Submitting

For all lanes:

1. `mk failed <keywords>` — Already disproven approach? STOP.
2. `mk context <problem_id>` — What did Aristotle try before? Use that as auto-context.
3. Is the gap stated as `(P) ∨ ¬P`? STOP. State as existence OR impossibility.
4. Does the sketch say "Proof strategy"? STOP. Move strategy to companion JSON, leave sketch bare.
5. Is the conjecture in Mathlib? `lake build` check first.
6. Cross-domain literature attached? (≤2 years for structural-open targets.)

For CLOSURE:
7. `closure.json` populated with all 6 fields per `docs/closure_axis_companion_spec.md`?
8. `real_closure_candidate` honestly set per the combined rule?

For FUSION:
9. `.fusion.json` companion in airlock with human review pending?
10. `paired_llm` field populated?
11. `cross_domain_literature` populated with at least one ≤2-year citation?

---

## 9. Versioning

- v1.0 (2026-05-30, this doc) — Initial. Three lanes, three subsystems, F + W + I team synthesis.
- v1.1: FUSION lane companion schema once finalized by I-agents.
- v2.0: New documented Aristotle behavior or subsystem.

---

## 10. Authority

- W1 (Aristotle system architecture): `analysis/web_research_aristotle_system.md`
- W4 (academic papers): `analysis/web_research_academic_papers.md`
- W7 (capabilities): `analysis/web_research_aristotle_capabilities.md`
- W8 (informal-mode usage): (referenced by F-team audit; see CHANGELOG)
- F1 (brute-force audit): F-team audit, May 30 2026
- F2 (literature audit): F-team audit, May 30 2026
- F3 (LLM consultation audit): F-team audit, May 30 2026
- This doc (I5, May 30 2026): synthesis only; per-claim citations above.
