# Multi-AI Debate: Which 5 open problems should we hit FIRST with the new tooling to maximize a target_resolved=1 win in 2 weeks?
## May 28, 2026

### Participants
- **Grok-4 (xAI)**
- **Gemini (Google)**
- **Codex/GPT-5.2 (OpenAI)**

### Format
- **3 rounds** of structured debate
- **Full context accumulation**: every model receives the complete original context + ALL prior debate responses in every round
- **Context source**: `/tmp/debate_inventory_context.md` (9291 chars, ~2322 tokens)

---

## ROUND 1

### Grok-4 (xAI)

[ERROR: curl failed with code 35: ]

### Gemini (Google)

## Round 1 Opening Position: The "Iterative Breakthrough" Portfolio

To maximize a `target_resolved=1` win in 14 days, we must pivot away from "one-shot" attempts and toward **iterative refinement**. The newly built `scripts/aristotle_fetch.py ask` tool is our highest-leverage asset. It allows us to treat "Moderate Depth" problems not as failed history, but as "partially initialized" states.

### 1. The Priority 5 Selection

| Rank | Problem ID | Type | Submission Mode | Primary Justification |
| :--- | :--- | :--- | :--- | :--- |
| **1** | `feit_thompson` | NT/Algebra | **Split** (Exist/Imposs) | 11 attempts with real partial wins on $p=3$. Best candidate for the `ask` follow-up tool to push partial theory into a full proof. |
| **2** | `erdos_647` | NT | **Split** (Exist/Imposs) | 8 attempts, 6 sketches. Sub-results like `tau_ge_two` already proven. It is "closest to the finish line" of all active Erdős targets. |
| **3** | `Leinster: Nonabelian` | Algebra | **Existence-only** | Scored 51. Concrete witness strategy ($S_3 \times C_5$) is perfectly suited for `native_decide` verification—a high-probability "quick win." |
| **4** | `erdos_1052` | NT | **Existence-only** | 6 attempts but effectively "cold" (never fetched). Unitary perfect numbers are structurally rigid; the new schema honesty will prevent false "advance" claims. |
| **5** | `erdos_273` | NT | **Split** (Exist/Imposs) | Untouched with 2 sketches. Covering systems are Aristotle's historical "sweet spot" (e.g., #203, #124). Low risk/high reward for a new pipeline. |

---

### 2. Key Strategic Claims

#### (a) Prioritize "Warm" over "Cold" via `Project.ask()`
Historical wins (#124, #645, etc.) were never bare-statement. By picking `feit_thompson` and `erdos_647`, we start with a pre-existing "context" in the DB. We should use the first 48 hours to `ask` existing slots to refine their `compiled_no_advance` results into `compiled_advance`.

#### (b) The "Split Submission" Mandate (Proposal #0 Compliance)
The new `em-tautology` gate is a filter, not just a warning. Any problem involving a "there exists or there does not exist" conjecture must be submitted as two distinct tasks. This doubles our slot usage for top picks but is **mandatory** to avoid the structural triviality that plagued the `erdos_850` pilot.

#### (c) Avoid the "Modular Sinkhole"
The Erdős-Straus modular family (6 residue classes) represents a single point of failure. If the underlying "Egyptian fraction decomposition" approach is flawed for $r=1 \mod 840$, it is likely flawed for all six. We should **exclude** this family from the first 5 slots to ensure domain diversity.

#### (d) Domain Diversification (3 NT, 2 Algebra)
While Number Theory is our most successful domain, the Leinster problems (specifically the nonabelian witness) offer a different failure mode. If the NT solver hits a wall with Sophie Germain primes, the Algebra solver might succeed with finite group search.

---

### 3. Response to Context Constraints

*   **Evidence for `feit_thompson`:** The context notes "First algebraic structure theory for ord_A(3) in FT p=3" was already achieved. This proves the sketches are providing non-trivial Lean code. We are not starting from zero; we are finishing a 90% complete task.
*   **The Model Gap:** Since Gemini 3.x is 404, we must rely on Claude Opus 4.7 for strategic "asking." Claude’s strength is in debugging and refinement, which favors the "Warm" problem strategy over "Cold" one-shots.

---

### 4. Portfolio Risk: "The Verification Bottleneck"
The biggest risk to this portfolio is the **9-hour wall-clock time**. If we submit a split (Exist/Imposs) for three problems, we use 6 "virtual" slots. Since we only have 5 concurrent slots, we are looking at an immediate 18-hour queue. 

**I propose we stagger:** Submit `Leinster` and `erdos_1052` (single slots) first, while simultaneously using the `ask` tool on existing `feit_thompson` and `erdos_647` slots. This utilizes the new CLI without burning new submission slots.

**Most Important Question for the next round:** Should we sacrifice `erdos_273` (a "safe" NT bet) to include one Erdős-Straus modular "scout" to test if the new pipeline can handle the highly-correlated Egyptian fraction sketches?

### Codex/GPT-5.2 (OpenAI)

No prior participant claims to quote in Round 1, so this is my opening position.

1. **Key Claim: Start with a spread portfolio, not a family bet.**

Facts from context: Aristotle has 5 concurrent slots, each run takes about 9 hours, and Erdos-Straus residue classes are explicitly flagged as “highly correlated risk.”

Opinion: the first wave should maximize independent chances of one `target_resolved=1`, not maximize volume inside one approach. I would treat the Erdos-Straus modular family as one idea, not six separate chances.

2. **My First 5, In Priority Order**

1. `feit_thompson`  
   Mode: existence + impossibility split.  
   Reason: 11 attempts, 2 sketches, and real prior partial wins: algebraic structure for `ord_A(3)` and quartic residue analysis for `q ≡ 71 mod 72`. This is the strongest “warm context + non-tautological progress” target. The new follow-up CLI should matter here because there is actual prior structure to ask against.

2. `brocard`  
   Mode: existence + impossibility split.  
   Reason: only 1 prior attempt, scored candidate version at 56, and the hint is concrete: “no solutions for specific n ranges” via modular constraints. That sounds like a bounded theorem Aristotle may actually close. This is my wildcard, but not a random one.

3. `erdos_647`  
   Mode: existence-only first.  
   Reason: 8 attempts, 6 sketches, and existing sub-results: `tau_ge_two`, `exists_large_m_plus_tau`, `max_m_plus_tau_unbounded`. I would avoid splitting initially because divisor-gap/Sophie Germain formulations are easy to turn into weak necessary-condition lemmas. Use one sharply stated existence target.

4. `agoh_giuga`  
   Mode: existence-only first.  
   Reason: 5 attempts, 8 sketches, recent work extending beyond the 9-factor bound. Risk is known-equivalence rediscovery, so I would only submit a statement whose contribution is explicitly beyond existing equivalences. No split until we confirm the statement is not just another wrapper.

5. `erdos_242`  
   Mode: existence-only first.  
   Reason: untouched with 4 sketches, likely Straus-related. I want one untouched sketch-ready problem in the first batch to test whether the new pipeline lifts cold starts. I prefer `erdos_242` over the scored Erdos-Straus residue family because it gives Straus exposure without spending multiple first-wave slots on correlated residue classes.

3. **Why Not All Moderate-Depth?**

Fact: moderate-depth targets have prior context and sketches, but they also have failed attempts.

Opinion: the best first wave is 3 warm, 1 lightly touched high-score wildcard, 1 untouched sketch-ready target. That gives us signal across the exact question we need answered: whether new tooling helps warm restarts more than cold sketch problems.

4. **Why Not Bet Hard On Erdos-Straus Residues?**

Fact: the packet says the six residue classes share one approach and are correlated.

Opinion: I would not put more than one Straus-like target in the first 5. Evidence that would change my mind: if one residue class already has a concrete Lean-near decomposition template or prior compiled partials distinct from the others. Without that, six residues are not six independent shots.

5. **Existence vs Split**

My split choices are only `feit_thompson` and `brocard`.

Reason: those have concrete enough prior structure or modular boundedness that the impossibility side may be productive. For `erdos_647`, `agoh_giuga`, and `erdos_242`, I would avoid doubling slot use until the statement is narrowed, because the new em-tautology lesson says bad disjunction framing can waste every arm.

6. **Biggest Portfolio Risk**

The biggest risk is that “warm context” mostly means accumulated near-misses, not latent solvability. `feit_thompson`, `erdos_647`, and `agoh_giuga` may all produce polished partials but no `target_resolved=1`.

Concrete mitigation: before submission, require each target to have a one-sentence `contribution_statement` that would still be meaningful if the proof compiles, and reject any statement that merely axiomatizes prior work or proves a necessary condition.

*Round 1 completed in 180s*

---

## ROUND 2

### Grok-4 (xAI)

[ERROR: curl failed with code 35: ]

### Gemini (Google)

## Round 2: The "Precision and Pruning" Strategy

I have reviewed the opening positions, specifically the "Spread vs. Concentrate" argument from Codex. While we agree on the primacy of `feit_thompson`, we differ on the efficiency of "split" submissions and the specific selection of wildcard targets.

### 1. Response to Participants

**On `feit_thompson` (Consensus):**
Codex and I agree this is the #1 priority. Codex notes the "algebraic structure for $ord_A(3)$" as a strong signal. I agree and add that since `scripts/aristotle_fetch.py ask` is now available, we should **not** submit a new slot for this immediately. 
*   **Revised Action:** Use `ask` on the most successful existing `feit_thompson` slot (e.g., the one that hit the $q \equiv 71$ mod 72 result) to push for the full theorem. This saves a submission slot for a "Cold" target.

**On the "Split" Submission Efficiency:**
Codex argues for "Existence-only" for `erdos_647` and `agoh_giuga` to avoid wasting slots on "weak necessary-condition lemmas." 
*   **Disagreement:** I disagree with Codex here. The "em-tautology gate" (Proposal #0) was implemented specifically because the model defaults to triviality when faced with a disjunction. If we submit "Existence-only" for a problem where the answer is actually "Does not exist," the model will hallucinate a witness or fail.
*   **Counter-proposal:** We must split any problem where the existence of a witness is not already established by prior partials. For `erdos_647`, where we already have `tau_ge_two`, we can stick to existence. For "Cold" targets like `brocard`, we **must** split.

**On `agoh_giuga` vs. `Leinster: Nonabelian`:**
Codex picks `agoh_giuga` (warm); I picked `Leinster` (scored 51).
*   **Argument for Leinster:** Codex admits `agoh_giuga` has a "risk of rediscovery" and "axiomatizing known equivalences." The new auditor will flag these as `compiled_no_advance`. Conversely, `Leinster: Nonabelian` is a **search-and-verify** task ($S_3 \times C_5$). In a 2-week window, Aristotle is much more likely to find and verify a concrete witness via `native_decide` than it is to extend a factor-bound theory in `agoh_giuga`.

### 2. Updated Priority 5 Portfolio

I am revising my list to incorporate Codex's high-score `brocard` wildcard while maintaining the "Search-and-Verify" advantage of the Leinster problems.

| Rank | Problem ID | Mode | Justification |
| :--- | :--- | :--- | :--- |
| **1** | `feit_thompson` | **Ask** (Follow-up) | Use `scripts/aristotle_fetch.py ask` on existing partial wins. No new slot used. |
| **2** | `brocard` | **Split** (Exist/Imposs) | Scored 56. "Modular constraints per range" is a highly automatable Lean tactic. High "target_resolved" potential. |
| **3** | `erdos_647` | **Existence-only** | Adopting Codex's "Exist-only" stance here because prior sub-results confirm the "Existence" path is the productive one. |
| **4** | `Leinster: Nonabelian`| **Existence-only** | Best "Search-and-Verify" candidate. Concrete witness $S_3 \times C_5$ provides a clear success condition for `native_decide`. |
| **5** | `erdos_242` | **Existence-only** | Adopting Codex's pick for an untouched target. It provides Straus-domain exposure without the correlated risk of the 6-residue family. |

### 3. New Evidence & Arguments

**The "Axiomatizes Prior Work" Trap:**
The new schema honesty (Proposal #2) is our biggest internal risk. If we submit a "Warm" problem and the model simply re-states the lemmas found in the `sketches/` folder, the auditor will mark it `axiomatizes_prior_work=1` and `compiled_no_advance`. 
*   **Strategic Shift:** For all "Warm" problems (`feit_thompson`, `erdos_647`), we must provide a `contribution_statement` in the submission that *excludes* the already-proven sub-lemmas. We are effectively forcing the model to "delta-code."

**Claude 4.7 vs. The Pipeline:**
Since Gemini 3.x is 404, we are relying on Claude 4.7 for the "Ask" loops. Claude is superior at **refactoring and debugging** rather than "blue-sky" invention. This reinforces the value of the `Leinster` and `brocard` picks, where the "invention" (the witness or the modular range) is already suggested by the score/hint, leaving Claude to do the "heavy lifting" of Lean implementation.

### 4. Questions for the Next Round

1.  **For Codex:** How do we mitigate the risk that `brocard`'s modular constraints are too large for `native_decide` to solve within the 9-hour limit? Should we use a "Modular Scout" submission first?
2.  **For All:** Given the 5-slot limit, should we intentionally leave 1 slot open for "Rapid Response" (e.g., if an `ask` follow-up fails and needs a quick manual tweak)?
3.  **For All:** Is the "Existence-only" path for `erdos_647` dangerous if the Sophie Germain prime distribution is the bottleneck? Does the impossibility side provide a "safety net" for a partial win?

### 5. Genuine Disagreement vs. Miscommunication

The disagreement on **Splitting vs. Exist-only** is a matter of resource management. Codex views it as "doubling the data" (good) but "wasting slots" (bad). I view it as **structural necessity** to avoid the `em-tautology` gate. If we don't split, and the model tries to prove `P ∨ ¬P`, the `safe_aristotle_submit.py` script will **reject the submission entirely**, wasting the slot before it even starts.

**Biggest Risk Call:** The "Axiom Audit." If our "Warm" targets are too similar to prior work, we will end the 2-week window with 5 `compiled_no_advance` results and zero wins. We must prioritize "Cold" targets with "Warm" hints (like `brocard`) to avoid this.

### Codex/GPT-5.2 (OpenAI)

**Round 2 Position**

I changed my mind on two slots. I now include `Leinster: Nonabelian Leinster exists (S3×C5)` and drop `agoh_giuga`; I also replace my earlier `erdos_242` pick with `erdos_203`.

Gemini wrote: “`Leinster: Nonabelian`… concrete witness strategy (`S3 × C5`) is perfectly suited for `native_decide` verification.” I agree. Fact: the inventory gives a concrete witness and score 51. Opinion: for a 2-week `target_resolved=1` target, a finite witness has a better risk profile than another warm NT problem likely to produce only partial lemmas.

I disagree with Gemini’s “`erdos_1052`… effectively cold” as a positive. Fact: it has 6 stale compile-failed/never-fetched attempts. Opinion: stale is not warm; it gives less leverage than `brocard`, `erdos_647`, or a fresh high-sketch untouched target.

I also disagree with “Split Submission Mandate” if interpreted broadly. Fact: the gate blocks `(P) ∨ ¬P`. Opinion: split is mandatory for bad disjunction templates, not automatically worth two slots for every conjecture. With 5 concurrent slots and 9-hour runs, split only where both sides are independently meaningful.

**Revised First 5**

| Rank | Problem | Mode | Reason |
|---:|---|---|---|
| 1 | `feit_thompson` | existence + impossibility split | Best warm target: 11 attempts, 2 sketches, real non-tautological partial wins. Use `ask` against prior strongest slot before broad resubmission. |
| 2 | `Leinster: Nonabelian Leinster exists (S3×C5)` | existence-only | Concrete finite witness plus `native_decide` path. Best “quick win” candidate if it avoids axiomatizing group facts. |
| 3 | `brocard` | split, but submit impossibility/range side first | Score 56, only 1 prior attempt, modular range constraints. This is the best wildcard because it is bounded and concrete. |
| 4 | `erdos_647` | existence-only | 8 attempts, 6 sketches, real sub-results. Do not split first; Sophie Germain/divisor-gap complements risk becoming weak necessary-condition lemmas. |
| 5 | `erdos_203` | existence-only | Untouched, 8 sketches, covering-systems topic. If Gemini wants a covering-systems bet, this looks stronger than `erdos_273` with only 2 sketches. |

**Where We Agree**

Gemini wrote: “Avoid the ‘Modular Sinkhole.’” I agree. The Erdos-Straus six-residue family is one correlated approach, not six independent chances. Evidence that would change my mind: one residue class has a distinct near-Lean decomposition template or compiled partials not shared by the others.

**Where We Really Disagree**

Gemini ranks `erdos_273`; I prefer `erdos_203`. If the argument is “covering systems are promising,” then the inventory favors the untouched covering target with 8 sketches over the one with 2.

Gemini includes `erdos_1052`; I exclude it. “Cold but stale” is not the same as “fresh with a clear verifier.”

**Biggest Risk**

The biggest portfolio risk is target-formulation drift: we may prove crisp, compiling lemmas that still land as `compiled_no_advance` because they do not resolve the declared target. Mitigation: before launch, every file needs a one-sentence `contribution_statement`, no prior-work axioms, and a direct explanation of why `target_resolved=1` would be legitimate.

**Questions For Round 3**

1. What exact Lean target name/ID backs `Leinster: Nonabelian Leinster exists (S3×C5)`?
2. Why `erdos_273` over `erdos_203` if both are covering-system bets?
3. Which prior `feit_thompson` slot has the strongest non-axiomatic compiled material for `ask`?
4. For `brocard`, what specific `n` range is narrow enough to be a real 2-week theorem?

*Round 2 completed in 210s*

---

## ROUND 3

### Grok-4 (xAI)

[ERROR: curl failed with code 6: ]

### Gemini (Google)

## Round 3: Closing Position & Action Plan

### 1. Revised Positions (Changing My Mind)

Based on the debate with **Codex/GPT-5.2**, I am revising my portfolio in two key ways:

*   **Switching `erdos_273` to `erdos_203`:** Codex correctly points out that if we are betting on covering systems, `erdos_203` (8 sketches, untouched) offers significantly more initialization data than `erdos_273` (2 sketches). The higher sketch count suggests a broader set of formalization paths for Claude 4.7 to explore.
*   **Dropping `erdos_1052` (The "Stale" Problem):** I concede that "cold but stale" attempts (6 failures) are a signal of high structural friction in the formalization itself. I am replacing it with **`brocard`** (impossibility-side focus), which Codex successfully argued is a superior "wildcard" due to its modular boundedness and high score (56).

---

### 2. Lingering Disagreements

*   **The "Split" Necessity:** I still maintain that for "Cold" targets or any problem involving a search for a non-existent witness, a split is a **functional requirement** to bypass the `em-tautology` gate. However, I agree with Codex that we should not waste two slots simultaneously. 
*   **Actionable Compromise:** For `brocard`, we will submit the **Impossibility-only** side (proving no solutions in a modular range). This treats the "split" as a sequential strategy rather than a concurrent one, preserving our 5-slot limit.

---

### 3. FINAL RECOMMENDATION: The "Informed-Search" Portfolio

To maximize a `target_resolved=1` event in 14 days, we will focus on problems where the "witness" or "counter-example" is finite and verifiable via `native_decide`, or where "warm" partial results provide a clear delta for the new `ask` tool.

| Rank | Problem ID | Mode | Primary Justification |
| :--- | :--- | :--- | :--- |
| **1** | `feit_thompson` | **Ask** (Follow-up) | **Category: Warm.** Use `scripts/aristotle_fetch.py ask` on the slot that achieved the $q \equiv 71$ mod 72 result. Leverage Claude 4.7 to bridge the final gap. |
| **2** | `Leinster: Nonabelian`| **Existence-only** | **Category: Scored.** High-probability "quick win." Target the $S_3 \times C_5$ witness. Success condition: `native_decide` on Fin 30. |
| **3** | `brocard` | **Impossibility-only**| **Category: Wildcard.** Focus on proving "no solutions" for a specific $n$ range using modular constraints. Avoids the tautology gate by being existence-specific. |
| **4** | `erdos_647` | **Existence-only** | **Category: Warm.** Use prior successes (`tau_ge_two`) as a foundation. Focus on the divisor-gap formulation. |
| **5** | `erdos_203` | **Existence-only** | **Category: Untouched.** Best covering-system bet (8 sketches). High historical alignment with Aristotle's solver strengths. |

**Biggest Portfolio Risk:** **The "Axiom/Drift" Auditor.** The new schema honesty (Proposal #2) will aggressively flag results as `compiled_no_advance` if they merely re-state sketches or axiomatize prior work. We must ensure every submission has a unique `contribution_statement`.

---

### 4. Prioritized Next 5 Actions (Next 7 Days)

1.  **[T-0 to T-12h] Audit & Initialize:** Identify the exact slot ID for the most successful `feit_thompson` run and use `scripts/aristotle_fetch.py ask` to prompt Claude 4.7 for a "final theorem completion" sketch based on the quartic residue results.
2.  **[T-12h to T-24h] Formulate Contribution Statements:** Draft the mandatory one-sentence `contribution_statement` for the 4 new submissions, explicitly excluding all existing lemmas in the `sketches/` folder to prevent the "Axiom Audit" failure.
3.  **[T-24h to T-48h] Launch First Wave:** Submit the `Leinster` witness search and the `brocard` modular range check. These are our fastest potential wins.
4.  **[T-48h to T-7d] Launch Second Wave:** Submit `erdos_647` and `erdos_203`. By this point, the `ask` result for `feit_thompson` should be back for manual review or further "asking."
5.  **[Ongoing] Verification Loop:** After each 9-hour run, use `audit_proven.py` specifically to check for the `em-tautology` flag. If a result hits the flag, immediately re-submit as a split without waiting for the next cycle.

---

### 5. The Single Most Important Action

The team must **strictly enforce the `contribution_statement` requirement.** 

Because the pipeline is now "honest," a compiling proof is no longer a win if it doesn't advance the state of the art. We must force the model—via the `contribution_statement` field—to declare exactly which open conjecture it is closing and why that result is not just a formalization of the informal sketch provided in the prompt. This shift from "make it compile" to "make it advance" is the only path to a genuine `target_resolved=1`.

### Codex/GPT-5.2 (OpenAI)

**Revisions**

I changed my mind on `agoh_giuga`. Gemini wrote: “Conversely, `Leinster: Nonabelian` is a search-and-verify task (`S3 × C5`).” I agree. Fact: the inventory gives a concrete witness path. Opinion: that is a better 2-week win bet than `agoh_giuga`, which has explicit rediscovery risk.

I also partly accept Gemini’s point: “Use `ask` on the most successful existing `feit_thompson` slot… This saves a submission slot.” I still rank `feit_thompson` first, but the first move should be follow-up `ask`, not a blind fresh resubmission.

**Still Disagree**

Gemini wrote: “We must split any problem where the existence of a witness is not already established.” I disagree. Fact: the gate blocks `P ∨ ¬P`; it does not require spending two slots on every uncertain conjecture. Opinion: broad splitting burns scarce 5-slot capacity. Split only where both sides are concrete targets.

I still prefer `erdos_203` over Gemini’s `erdos_273`. Fact: both are covering-system bets; `erdos_203` has 8 sketches, `erdos_273` has 2. Opinion: if we want one untouched covering target, use the one with more sketch material.

**Final Recommendation**

1. `feit_thompson`  
   Mode: existence + impossibility split, but start with `ask` on strongest existing slot.  
   Reason: 11 attempts, real non-tautological partial wins, best use of prior context.

2. `Leinster: Nonabelian Leinster exists (S3×C5)`  
   Mode: existence-only.  
   Reason: concrete finite witness plus `native_decide` path. Best quick-win shape.

3. `brocard`  
   Mode: split, with impossibility/range side first.  
   Reason: scored 56, only 1 prior attempt, modular range constraints are bounded and checkable.

4. `erdos_647`  
   Mode: existence-only.  
   Reason: 8 attempts, 6 sketches, real sub-results. Avoid complement side until target is sharper.

5. `erdos_203`  
   Mode: existence-only.  
   Reason: untouched, 8 sketches, covering-system domain, independent from warm NT failures.

Do not include the six Erdos-Straus residue classes in wave 1. Treat them as one correlated bet until one residue has a near-Lean decomposition template.

**Biggest Risk**

The biggest risk is not compilation failure; it is `compiled_no_advance`. We may get polished Lean proofs that prove known lemmas, necessary conditions, or prior-work wrappers without `target_resolved=1`.

**Next 7 Days**

1. Day 1: identify strongest prior `feit_thompson` and `erdos_647` slots; run `ask` with delta-only prompts and explicit contribution statements.
2. Day 1: validate exact Lean target names for `Leinster: Nonabelian` and `brocard`; reject any target requiring prior-work axioms.
3. Day 2: submit first 5-slot wave: `Leinster`, `brocard` range-impossibility, `erdos_647`, `erdos_203`, and one `feit_thompson` follow-up/fresh split side if `ask` output is strong.
4. Days 3-4: fetch, audit for em-tautology, prior axioms, and `target_resolved`; immediately follow up only on non-tautological partials.
5. Days 5-7: second wave doubles down only on targets that produced real delta evidence; otherwise rotate in one Erdos-Straus scout, not the whole family.

Single most important next step: choose the exact strongest existing `feit_thompson` slot and run a focused `ask` that asks for the missing final theorem, not more supporting lemmas.

*Round 3 completed in 478s*

---

## DEBATE STATISTICS

- **Rounds**: 3
- **Models**: 3
- **Total responses**: 9
- **Total debate text**: 25665 chars (~6416 tokens)
- **Errors**: 3 responses failed
