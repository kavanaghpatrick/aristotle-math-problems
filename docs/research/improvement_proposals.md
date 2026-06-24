# Improvement Proposals — Ranked by Impact/Cost

Synthesized 2026-05-28 from `aristotle_state.md`, `llm_math_landscape.md`, `db_evaluation.md`, current `CLAUDE.md`. Five proposals. #1–2 are load-bearing; #3–5 amplify.

---

## #1 — Drop the bare-conjecture doctrine; require an informal sketch from Gemini 3.1 Pro / GPT-5.2 Pro before Aristotle submission

**Diagnosis.** `aristotle_state.md §3`: the Aristotle paper (arxiv 2510.01346) says external Lean blocks with "already proven background results or lemmas tailored to the target theorem … boost performance using higher-level informal reasoning." `§4`: every confirmed open-Erdős win — #124, #645, #728, #729, #401 — paired a strong informal strategist (GPT-5.2 Pro or human expert) with Aristotle as formalizer. None used a bare-statement-only sketch. `llm_math_landscape.md`: AlphaProof Nexus hit 9/353 Erdős in May 2026 using Gemini 3.1 Pro → Lean exactly this way. `db_evaluation.md §Pattern 5`: our `proof_orchestrator` Codex→Aristotle pipeline was built but 0/6 sorry-free proofs ever promoted. Our hard-rule gate forbids what every public winner did.

**Concrete change.**
1. Replace CLAUDE.md hard-rules #2, #3, #6. New policy: bare statement is allowed only for falsification probes; gap-targeting requires an informal sketch ≥150 words + 3–5 candidate lemmas.
2. Rewrite `scripts/check_gap_targeting.py` to reject sketches with NO informal reasoning instead of those that contain it.
3. Add `scripts/informal_sketch.py` invoking Gemini 3.1 Pro (primary) / GPT-5.2 Pro (fallback) with the problem + `mk failed` + `mk context` outputs. `/sketch` calls this by default.
4. Wire `proof_orchestrator` so any Codex `sorry_count=0` proof auto-promotes to an Aristotle axiom-discharge job.

**Expected impact.** AlphaProof Nexus hit ~2.5% on formal-conjectures Erdős with this exact shape; Aristotle's own wins all used it. Plausibly lifts us from 0/1,157 to 1–3% on well-formalized targets — 5–15 wins per 500 attempts.

**Cost.** Two-three days engineering. API spend ~$200–500 per serious attempt (AlphaProof Nexus reports "few hundred USD per problem") vs near-zero today. Patrick's `[depth-over-breadth]` memory and the "GAP-TARGETING ONLY" prime directive both need rewriting.

**Counter-argument.** The bare-conjecture rule was a deliberate corrective against multi-page "Proof Strategy" essays that fought Aristotle's MCGS. Risk: sliding back. Mitigation: the new gate enforces the *shape* (≥150 words + lemma list), not unbounded essays, and bans directive language ("first prove… then apply…").

---

## #2 — Fix the `target_resolved` accountability gap

**Diagnosis.** `db_evaluation.md §Pattern 1,§Pattern 3`: 0/1,157 `target_resolved=1`, yet 211 rows are `compiled_clean`; 135/211 contain `axiom ` declarations restating prior literature; `contribution_statement` populated on 3.3%; `verified` NULL on 65%; the status enum has 25 values, with `disproven` rows that actually prove 1932 theorems. We cannot tell what we've accomplished.

**Concrete change.**
1. Collapse `status` to 6 values: `submitted | compile_failed | compiled_partial | compiled_no_advance | compiled_advance | disproven`. One-shot backfill.
2. Add `axiomatizes_prior_work` boolean + `axiom_count` int, populated by grep `^axiom ` in the audit hook.
3. Make `contribution_statement` NOT NULL on terminal status. Audit must answer "what novel claim, if any, did this advance?" before any `compiled_advance` label.
4. Add `execution_seconds` + `cost_usd` columns (currently 0/1,157 populated) so hit-rate-per-dollar becomes measurable.

**Expected impact.** Unblocks every downstream decision. Without it, #1's success rate is unmeasurable and we keep declaring fake "compiled clean" wins.

**Cost.** One day. Risk: rewriting status values may break `mk` queries — but `mk` is internal.

**Counter-argument.** Pure accountability, not capability. Reply: without it, every other proposal here is unevaluable.

---

## #3 — Domain triage + restrict to formal-conjectures corpus

**Diagnosis.** `aristotle_state.md §2`: Aristotle missed IMO P6 (combinatorics), like every other system; strong on NT/algebra/geometry. `db_evaluation.md §Pattern 2`: tuza_nu4 (combinatorics) ate 27% of submissions for 0 resolutions. `llm_math_landscape.md`: AlphaProof Nexus restricted to the 353-problem `google-deepmind/formal-conjectures` Erdős set — the corpus we ad-hoc formalize anyway.

**Concrete change.**
1. Add domain weights to `/sweep`: NT 2.0, algebra 2.0, geometry 1.5, analysis 1.0, combinatorics 0.3 (until a combinatorial win).
2. Hard cap per problem-id: 30 submissions until first `compiled_advance`. tuza_nu4 stays in the queue but stops eating the budget.
3. `/screen` prefers problems with an existing formal-conjectures Lean statement.

**Expected impact.** Reallocates ~300 wasted tuza_nu4 attempts/year to higher-yield domains.

**Cost.** Half-day.

**Counter-argument.** Contradicts `[depth-over-breadth]` for combinatorics. Reply: depth on tuza_nu4 hasn't paid in 317 attempts; depth on a *tractable* problem is the actual rule.

---

## #4 — Goedel-Prover-V2-32B / Seed-Prover 1.5 as cheap pre-filter

**Diagnosis.** `llm_math_landscape.md` Medium #4: Goedel-Prover-V2-32B runs on one 80GB GPU, beats DeepSeek-Prover-V2-671B by 80× compute (90.4% MiniF2F self-correct); Seed-Prover 1.5 = 88% Putnam. Both dramatically cheaper than Aristotle API per attempt.

**Concrete change.** Stand up Goedel-Prover-V2-32B. `/submit` first attempts there; escalates to Aristotle only on failure. Log both attempts under the same `problem_id`.

**Expected impact.** If 10–20% of well-formalized problems fall to the open prover, saves $1–5K/month at Nexus-style costs.

**Cost.** GPU + 1–2 weeks integration. Risk: hallucinated `Admitted` (Rocq-MCP study: 14/244) → strictly downstream of #2's honest audit hook.

**Counter-argument.** Don't start until #2 lands, else we add another stream of fake wins.

---

## #5 — Correct the "5-agent" architectural framing in docs

**Diagnosis.** `aristotle_state.md §1`: arxiv 2510.01346 specifies 3 components (MCGS + informal-reasoning loop + Yuclid geometry solver), not "5 agents." Our README and tooling repeat the 5-agent framing — decisions based on a wrong mental model compound.

**Concrete change.** Update README + memory: "Aristotle = (i) parallel MCGS over Lean states with 200B+ policy/value transformer, (ii) informal-reasoning loop drafting NL proofs and autoformalizing lemmas, (iii) Yuclid geometry solver." Cite arxiv 2510.01346.

**Expected impact.** Small but compounding. The 5-agent framing was the unspoken justification for "Aristotle will find the path." Naming the real architecture (an MCGS that *wants* informal sketches) makes #1 obvious instead of contested.

**Cost.** 30 minutes.

**Counter-argument.** None of substance.

---

## Ranking + sequencing

| # | Proposal | Impact | Cost | Ratio |
|---|----------|--------|------|-------|
| 1 | Informal-sketch stage; drop bare-only gate | Very High | Medium | **Top** |
| 2 | `target_resolved` schema honesty | High | Low | High |
| 3 | Domain triage + formal-conjectures restriction | Medium-High | Very Low | High |
| 4 | Open-source prover pre-filter | Medium | Medium | Medium |
| 5 | Correct architectural facts | Low | Negligible | Easy win |

**Order.** #5 immediately (free). #2 next (unblocks measurement). #1 third (the actual capability change). #3 in parallel with #1. Defer #4 until #2 has produced two weeks of clean data.

**Biggest risk to the program.** Patrick's "GAP-TARGETING ONLY. Bare conjecture. Zero proof guidance." is durable memory with explicit user directives behind it. Proposal #1 inverts it. The research strongly suggests the directive was a corrective overshoot — the right anti-pattern was "multi-page essays that fight Aristotle's MCGS," not "any informal reasoning at all." Surface this tension to Patrick before code changes.
