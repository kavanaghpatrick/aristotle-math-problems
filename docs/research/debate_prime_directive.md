# Multi-AI Debate: Should we drop our PRIME DIRECTIVE (bare conjecture, zero proof guidance) and adopt an informal-sketch-first pipeline before every Aristotle submission?
## May 28, 2026

### Participants
- **Grok-4 (xAI)**
- **Gemini (Google)**
- **Codex/GPT-5.2 (OpenAI)**

### Format
- **3 rounds** of structured debate
- **Full context accumulation**: every model receives the complete original context + ALL prior debate responses in every round
- **Context source**: `/tmp/debate_prime_directive_context.md` (45024 chars, ~11256 tokens)

---

## ROUND 1

### Grok-4 (xAI)

[ERROR: curl failed with code 35: ]

### Gemini (Google)

[Gemini stderr: Loaded cached credentials.
API returned invalid content after all retries. Full report available at: /var/folders/tv/mjd7bwd918b7745mldgg045w0000gn/T/gemini-client-error-generateJson-invalid-content-2026-05-27T16-20-55-042Z.json Error: Retry attempts exhausted
    at retryWithBackoff (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/utils/retry.js:212:11)
    at async BaseLlmClient._generateWithRetry (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/core/baseLlmClient.js:141:20)
    at async BaseLlmClient.generateJson (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/core/baseLlmClient.js:44:24)
    at async ClassifierStrategy.route (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/routing/strategies/cl]

### Codex/GPT-5.2 (OpenAI)

1. **Opening Position**

My position: **drop the PRIME DIRECTIVE as a hard rule, but do not replace it with “sketches before every submission” until accountability is fixed.**

More precisely:

- **Yes:** abandon “bare conjecture, zero proof guidance” as the default doctrine.
- **Yes:** run an informal-sketch-first experiment immediately after schema honesty lands.
- **No:** do not make sketches mandatory for every Aristotle submission yet.
- **No:** do not proceed without fixing `target_resolved`, `compiled_clean`, and axiom-count auditing first.

The right replacement is:

> Gap-targeting submissions should normally include a bounded informal sketch plus 3–5 candidate lemmas, except for explicit falsification probes and controlled bare-baseline tests.

2. **The Current Directive Has Failed Empirically**

Fact: context §2 says the pipeline has **1,157 submissions and 0 with `target_resolved=1`**.

Fact: context §5 says `compiled_clean` is structurally misleading: 211 compiled-clean rows, 135 of them containing `axiom`, and many proving wrappers, necessary conditions, or tautologies.

That is enough to reject the current doctrine as a success strategy.

The PRIME DIRECTIVE says:

> “GAP-TARGETING ONLY. Bare conjecture. Zero proof guidance. Let Aristotle find the path.”

The observable result is: Aristotle has not found the path in this pipeline. Not once.

Opinion: after 1,157 attempts, “keep doing it because the rule had prior buy-in” is no longer discipline; it is process inertia. Prior buy-in matters, but it does not outweigh repeated negative evidence.

3. **The Research Evidence Is Strong Enough To Override The Doctrine**

Fact: context §3 says Aristotle’s documented workflow includes an informal-reasoning system that drafts natural-language proofs, decomposes into lemmas, autoformalizes, and iterates.

Fact: context §3 also says Aristotle can be initialized with Lean blocks containing proven background results or tailored lemmas, and that this boosts performance.

Fact: context §3 says:

> “Our workflow ... bare conjecture, ≤30 lines, INFORMAL .txt, no proof strategy, no lemmas, no guidance.”

Fact: the same section concludes:

> “This is provably the harder mode of operation by Aristotle's own design.”

I agree with that conclusion.

The strongest evidence is not benchmark trivia; it is the open-problem pattern. Context §3 says confirmed open-problem wins paired a strong informal strategy with Aristotle as formalizer. Context §4 says AlphaProof Nexus achieved 9 Erdős resolutions using Gemini-driven Lean loops.

Opinion: the directive was probably a correction against bad proof essays that overconstrained Aristotle. But it overshot. The enemy is not “any informal reasoning”; the enemy is bloated, directive, low-quality reasoning.

4. **But “Sketch Before Every Submission” Is Too Broad**

I disagree with the Synthesizer’s strongest version:

> “Drop the bare-conjecture doctrine; require an informal sketch ... before Aristotle submission.”

I would change that to:

> Require sketches for serious gap-targeting attempts; preserve bare submissions for falsification probes, baselines, and controlled comparisons.

Reason: if every submission becomes sketched, we lose the ability to measure whether sketches actually help versus cleaner triage, better target selection, or better auditing.

Evidence that would change my mind: if a ≤10 submission pilot shows sketch-first produces at least one `compiled_advance` or materially better partial results while bare controls do not, I would support making sketches default for all non-falsification submissions.

5. **Model Choice: Hybrid, With Gemini Primary**

For sub-question (b): use **Gemini 3.1 Pro primary, GPT-5.2 Pro fallback, Codex as editor/auditor**.

Fact: context §4 says AlphaProof Nexus used Gemini 3.1 Pro and got 9/353 Erdős hits.

Fact: context §3 and §4 say GPT-5.2 Pro plus Aristotle solved Erdős #728.

Opinion: Gemini should be primary because the closest published pipeline analogue is AlphaProof Nexus. GPT-5.2 Pro should be fallback or second-opinion because it has direct Aristotle synergy in #728. Codex should not be the main sketch generator if the point is to test whether stronger informal reasoning changes outcomes.

Concrete action:

- Generate one Gemini sketch.
- Generate one GPT-5.2 critique or alternate lemma list.
- Codex merges into a bounded final sketch: 150–400 words, 3–5 lemmas, no tactic script.

6. **The Third Path Is Useful, But Not Enough**

Sub-question (c): should we keep bare-first and add sketches only after `COMPLETE_WITH_ERRORS` via `project.ask()`?

My answer: **use that as one arm of the experiment, not the whole policy.**

A bare-first approach still spends Aristotle budget asking the system to invent the strategy from scratch. Context §3 says that is the harder mode. But bare-first has value as a control and may be useful when Aristotle’s failure reveals the exact formal obstruction.

Concrete experiment should compare:

1. Bare-first control.
2. Sketch-first submission.
3. Bare-first followed by sketch-after-error using `project.ask()`.

Do not decide by philosophy. Run the comparison.

7. **The Compiled-Clean Theater Risk Is Real**

Sub-question (d): yes, sketches can absolutely create higher-cost theater.

Fact: context §5 says the current pipeline already confuses compilation with progress. It cites tautologies, known-result wrappers, and axiom-stuffed files.

A better sketch generator could make that worse by producing plausible lemma lists that Aristotle formalizes into harmless partials, while the database records “success-looking” artifacts.

Therefore #2 must precede #1. I agree with the Implementer:

> “We can't measure #1 without it.”

Concrete gates before any sketch pilot:

- `axiom_count` populated.
- `axiomatizes_prior_work` populated.
- `contribution_statement` required for terminal statuses.
- `compiled_advance` only if `target_resolved=1`, no prior-work axiom, and a clear novelty statement.
- Sketch submissions tagged `pattern='informal_sketch_v1'`.

8. **Smallest Reversible Experiment**

For sub-question (e), I propose a **9-submission experiment**, not 10:

Select 3 problems from `formal-conjectures`:

- 1 number theory
- 1 algebra
- 1 geometry or analysis
- Avoid Tuza/combinatorics for this first test

For each problem run:

1. Bare PRIME DIRECTIVE submission.
2. Gemini/GPT hybrid sketch-first submission.
3. Bare-first, then `project.ask()` sketch-after-error follow-up.

Success metrics:

- Primary: `target_resolved=1`.
- Secondary: `compiled_advance`.
- Tertiary: non-axiom candidate lemma proven and reusable.
- Failure marker: `compiled_no_advance`, tautology, axiom-stuffed wrapper, or known-result restatement.

Stop after 9. Review manually. If zero signal, do not scale.

9. **My Key Claims**

Claim 1: The PRIME DIRECTIVE should be retired as a hard doctrine because 0/1,157 is decisive negative evidence.

Claim 2: The replacement should be bounded informal reasoning, not long proof-strategy essays.

Claim 3: Schema honesty must land before sketch-first scaling, or we will manufacture better-looking noise.

Claim 4: Gemini primary + GPT-5.2 fallback is the right test, because both have the strongest evidence in context §3–§4.

Claim 5: The first experiment should compare bare, sketch-first, and sketch-after-error on the same small target set.

The most important unresolved issue is not whether sketches are philosophically allowed. It is whether we can measure mathematical advance honestly enough to avoid repeating the same failure mode with more expensive inputs.

*Round 1 completed in 225s*

---

## ROUND 2

### Grok-4 (xAI)

[ERROR: curl failed with code 35: ]

### Gemini (Google)

[Gemini stderr: Loaded cached credentials.
API returned invalid content after all retries. Full report available at: /var/folders/tv/mjd7bwd918b7745mldgg045w0000gn/T/gemini-client-error-generateJson-invalid-content-2026-05-27T16-24-45-854Z.json Error: Retry attempts exhausted
    at retryWithBackoff (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/utils/retry.js:212:11)
    at async BaseLlmClient._generateWithRetry (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/core/baseLlmClient.js:141:20)
    at async BaseLlmClient.generateJson (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/core/baseLlmClient.js:44:24)
    at async ClassifierStrategy.route (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/routing/strategies/cl]

### Codex/GPT-5.2 (OpenAI)

**Round 2 Position**

I still think we should **drop the PRIME DIRECTIVE as a hard ban**, but I am sharpening my answer: **do not adopt “informal sketch before every Aristotle submission” as an unconditional rule.** Adopt **sketch-first for serious proof attempts**, keep **bare mode for falsification, controls, and baseline measurement**.

The only substantive Round 1 response was mine; Grok and Gemini produced tool errors, so I’m engaging the concrete claims from Round 1 plus the Synthesizer/Implementer proposals.

**Where I Agree**

> “The current directive has failed empirically.”

Agree. Fact: context §2 has 1,157 submissions, 0 `target_resolved=1`. Fact: context §5 shows `compiled_clean` is mostly not mathematical success. Opinion: that is enough to revoke the directive’s privileged status.

> “The enemy is not ‘any informal reasoning’; the enemy is bloated, directive, low-quality reasoning.”

Strong agree. This is the key distinction. The original PRIME DIRECTIVE was probably reacting to bad proof-strategy essays. But banning all lemma sketches also blocks the workflow Aristotle and AlphaProof Nexus actually appear to benefit from (§3, §4).

> “#2 must precede #1.”

Mostly agree, but with one adjustment. Schema honesty must precede **scaling** sketch-first. It does not need to precede writing the gate or drafting the experiment harness. Concrete sequencing:

1. Land status/schema audit.
2. Build sketch gate and generator behind a flag.
3. Run ≤9 controlled submissions.
4. Only then change default behavior.

**Where I Disagree**

> “Require an informal sketch ... before Aristotle submission.”

Disagree with “before every.” Fact: context §3 explicitly preserves a role for bare submissions as falsification probes. Opinion: if we eliminate bare submissions entirely, we lose a control arm and will not know whether improvement came from sketches, domain triage, or better accounting.

> “Gemini should be primary because the closest published pipeline analogue is AlphaProof Nexus.”

I still lean Gemini-primary, but less strongly than in Round 1. Fact: AlphaProof Nexus used Gemini 3.1 Pro (§4). Fact: GPT-5.2 Pro has the cleanest Aristotle-specific success story in Erdős #728 (§3, §4). Opinion: the first experiment should not choose one prematurely. Generate both sketches, then have Codex merge/audit them into one bounded submission. That tests the pipeline shape, not model tribalism.

**New Argument**

The main risk is not just “compiled-clean theater at higher cost.” It is **strategy contamination without traceability**.

If Gemini proposes Lemma A, GPT proposes Lemma B, Codex edits both, and Aristotle proves a wrapper, we need to know which upstream claim caused progress or failure. Otherwise we cannot learn. So every sketch submission should store:

- `sketch_model_primary`
- `sketch_model_secondary`
- `sketch_hash`
- `candidate_lemmas_json`
- `prior_context_used`
- `pattern='informal_sketch_v1'`

This is cheap and more important than debating Gemini vs GPT abstractly.

**Position Revision**

I changed my mind slightly on timing. In Round 1 I said:

> “run an informal-sketch-first experiment immediately after schema honesty lands.”

I now think implementation can begin before schema migration is fully deployed, but **no result should be counted** until the audit fields exist. Build in parallel; measure only after #2 lands.

**Smallest Reversible Experiment**

Run 9 submissions, not 10:

- 3 formal-conjectures targets: NT, algebra, geometry/analysis.
- For each:
  1. bare submission,
  2. Gemini+GPT hybrid sketch-first,
  3. bare-first then `project.ask()` sketch-after-error.

Success hierarchy:

1. `target_resolved=1`
2. `compiled_advance`
3. reusable non-axiom lemma
4. honest failure note

Hard failure: axiom wrapper, tautology, known-result restatement, or no contribution statement.

**Questions For Round 3**

1. Should the experiment include one combinatorics target despite Tuza’s 317-failure history, or exclude combinatorics to test the highest-yield domains first?
2. Should Gemini and GPT sketches be submitted separately, or merged into one Codex-audited sketch?
3. What exact threshold promotes sketch-first from experiment to default: one resolution, one `compiled_advance`, or multiple reusable lemmas?

**Genuine Disagreement vs Miscommunication**

Genuine disagreement: whether sketches should precede **every** Aristotle submission.

Miscommunication: “drop PRIME DIRECTIVE” does not mean “return to long proof essays.” The proposed replacement is bounded: 150–400 words, 3–5 lemmas, no Lean tactics, no step-by-step directive script.

My Round 2 vote: **override the hard PRIME DIRECTIVE, but adopt controlled sketch-first, not universal sketch-first.**

*Round 2 completed in 231s*

---

## ROUND 3

### Grok-4 (xAI)

[ERROR: curl failed with code 35: ]

### Gemini (Google)

[Gemini stderr: Loaded cached credentials.
API returned invalid content after all retries. Full report available at: /var/folders/tv/mjd7bwd918b7745mldgg045w0000gn/T/gemini-client-error-generateJson-invalid-content-2026-05-27T16-28-44-000Z.json Error: Retry attempts exhausted
    at retryWithBackoff (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/utils/retry.js:212:11)
    at async BaseLlmClient._generateWithRetry (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/core/baseLlmClient.js:141:20)
    at async BaseLlmClient.generateJson (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/core/baseLlmClient.js:44:24)
    at async ClassifierStrategy.route (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/node_modules/@google/gemini-cli-core/dist/src/routing/strategies/cl]

### Codex/GPT-5.2 (OpenAI)

**Revised Positions**

I revised two things.

First, I no longer think schema honesty must block *all* implementation of sketches. In Round 1 I said, “run an informal-sketch-first experiment immediately after schema honesty lands.” I now agree with the Round 2 refinement: build the sketch machinery in parallel, but **do not count or scale results until audit fields exist**.

Second, I softened “Gemini primary.” Context §4 supports Gemini via AlphaProof Nexus, but context §3 supports GPT-5.2 Pro via Erdős #728. So the first experiment should use **both**, with Codex merging/auditing the final bounded sketch.

**Remaining Disagreements**

I still disagree with the Synthesizer’s broad wording:

> “require an informal sketch ... before Aristotle submission”

Too broad. Bare submissions should remain for falsification probes and controls. Removing them entirely makes measurement worse.

I agree with the Implementer’s warning:

> “We can't measure #1 without it.”

Fact: context §5 shows `compiled_clean` is already polluted by axioms, tautologies, and known-result wrappers. Opinion: sketch-first without accountability will create more expensive fake progress.

I also disagree with keeping the PRIME DIRECTIVE as default. Fact: context §2 says 1,157 submissions produced 0 `target_resolved=1`. Fact: context §3 says Aristotle’s successful public workflow benefits from informal proof sketches and lemma decomposition. Opinion: prior buy-in does not justify preserving a rule after that much negative evidence.

**Final Recommendation**

Drop the PRIME DIRECTIVE as a hard doctrine.

Replace it with:

> Serious gap-targeting submissions require a bounded informal sketch, 150-400 words, plus 3-5 English candidate lemmas. Bare conjectures are allowed only for falsification probes, baseline controls, or explicit ablation tests.

Do **not** adopt “sketch before every submission” yet. Adopt a controlled experiment first.

Model choice: **Gemini 3.1 Pro + GPT-5.2 Pro hybrid**, Codex as editor/auditor, Aristotle as formalizer. Track provenance for every lemma.

Promotion threshold: do not require a full resolution to continue. One honest `compiled_advance` or two reusable non-axiom lemmas across 9 submissions is enough to expand. But making sketch-first the global default should require either one `target_resolved=1` or repeated `compiled_advance` without axiom theater.

**Next Actions**

1. Ship schema honesty first: `axiom_count`, `axiomatizes_prior_work`, terminal `contribution_statement`, sane statuses, `cost_usd`, and `execution_seconds`.

2. Implement the sketch gate behind a flag: require 150-400 words and 3-5 candidate lemmas; reject Lean tactic scripts, numbered proof programs, and directive “first prove, then apply” essays.

3. Run a 9-submission experiment on 3 formal-conjectures targets: number theory, algebra, geometry/analysis. For each target: bare control, hybrid sketch-first, bare-first then `project.ask()` follow-up.

4. Store provenance: `sketch_model_primary`, `sketch_model_secondary`, `sketch_hash`, `candidate_lemmas_json`, `prior_context_used`, and `pattern='informal_sketch_v1'`.

5. Exclude combinatorics from the first experiment. Context §5 shows Tuza consumed 317 attempts for 0 resolutions; test the highest-yield domains first.

**Single Most Important Next Step**

Fix the accountability schema before counting another “success.” Without that, the team cannot tell whether sketches improve mathematics or just produce better-looking compiled-clean theater.

*Round 3 completed in 239s*

---

## DEBATE STATISTICS

- **Rounds**: 3
- **Models**: 3
- **Total responses**: 9
- **Total debate text**: 19026 chars (~4756 tokens)
- **Errors**: 3 responses failed
