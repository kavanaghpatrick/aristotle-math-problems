# TARGETS_2026_05 — ranked top 5 + 7-day action plan

**Date:** 2026-05-28
**Source:** 3-round multi-AI `/debate` between Gemini and Codex/GPT-5.2 (Grok SSL-blocked again, see `debate_best_targets.md`). Both AIs converged on the same 5 targets and 4/5 of the modes. Lingering disagreement: how aggressively to split into existence + impossibility.

---

## The 5 (consensus)

| Rank | Problem | Mode | Category | First move |
|---|---|---|---|---|
| **1** | `feit_thompson` | existence+impossibility split (but start with `ask` follow-up before fresh resubmission) | Warm — real prior partial wins | `aristotle_fetch.py ask` against slot 613 |
| **2** | `Leinster: Nonabelian Leinster exists (S3×C5)` | existence-only | Scored 51 — concrete witness | Fresh submission, existence form |
| **3** | `brocard` | split, **impossibility-only first** | Wildcard, scored 56 | Submit impossibility/range side first |
| **4** | `erdos_647` | existence-only | Warm — proven sub-results exist | Fresh submission, existence form, contribution_statement excluding `tau_ge_two`, `exists_large_m_plus_tau`, `max_m_plus_tau_unbounded` |
| **5** | `erdos_203` | existence-only | Untouched, 8 sketches | Fresh submission, pick the strongest of the 8 staged sketches |

---

## Why these 5

**The convergence pattern is informative:**
- Both AIs agreed on `feit_thompson` #1 from Round 1 onwards (real non-tautological prior wins, two specific unpublished structural results catalogued in DB).
- Both AIs ended up at `Leinster: Nonabelian Leinster exists (S3×C5)` for #2 — Codex flipped from `agoh_giuga` after Gemini pointed out it's a search-and-verify task with a clear witness and `native_decide` path.
- Both AIs ended up at `brocard` for #3 — Gemini flipped from `erdos_1052` after Codex argued "stale ≠ warm."
- Both AIs ended up at `erdos_203` for #5 — Gemini flipped from `erdos_273` after Codex argued the higher sketch count (8 vs 2) gives more initialization data.

**What got rejected and why:**
- ❌ Erdős-Straus residue family (6 sister problems) — "correlated risk; one approach failure kills all six. Wait until one residue has a near-Lean decomposition template distinct from the others."
- ❌ `erdos_1052` — "stale (compile_failed/never_fetched) ≠ warm. Stale means high structural friction, not latent solvability."
- ❌ `agoh_giuga` — "explicit rediscovery risk; one prior submission already flagged 'KNOWN: formalizes known equivalences.'"
- ❌ `erdos_273` — "fewer staged sketches than `erdos_203` in the same domain."
- ❌ Tuza nu4 (also Aristotle-team rule) — 317 attempts, 0 wins.

---

## Concrete first-action commands

### Day 1 — `feit_thompson` `ask` follow-up (target slot 613)

Slot 613 (uuid `16006bd6...`, output `submissions/nu4_final/slot613_ft_p3_wieferich_kA2_result.lean`) contains the strongest unpublished partial: "First algebraic structure theory for ord_A(3) in FT p=3: k≡2mod12q, v₂(k)=1, v₃(k)=0, k≥4q+2, Fermat quotient connection. All unpublished. Stephens/Le did computation only, no structural theory."

Run:
```bash
python3 scripts/aristotle_fetch.py ask 613 "Using the Wieferich structure theory already proved in this project (k≡2mod12q, v₂(k)=1, v₃(k)=0, k≥4q+2, the Fermat quotient identity Q_A(3)≡(q+1)k, and the 4(S₂/A)≡k relation), close the Feit-Thompson conjecture for p=3, q=71 by deriving the final contradiction. Do NOT re-derive existing lemmas; add only the missing step from the structure theory to the final impossibility. State the contribution explicitly in a contribution_statement comment."
```

If the slot UUID 403s (our current API key may not own it — same problem the original /debate hit), fall back to a fresh submission using slot 613's result.lean as input context + the same delta prompt.

### Day 2 — Wave 1 (4 fresh submissions)

```bash
# 1. Leinster Nonabelian — existence-only, witness search
python3 scripts/safe_aristotle_submit.py submissions/sketches/leinster_nonabelian_S3xC5.txt 720

# 2. Brocard — impossibility-only, modular range
python3 scripts/safe_aristotle_submit.py submissions/sketches/brocard_impossibility_range.txt 721

# 3. erdos_647 — existence-only, with explicit exclusion of prior sub-results
python3 scripts/safe_aristotle_submit.py submissions/sketches/erdos647_existence_delta.txt 722

# 4. erdos_203 — existence-only, untouched
python3 scripts/safe_aristotle_submit.py submissions/sketches/erdos203_existence.txt 723
```

**Note:** sketches for 720–723 do NOT exist yet. They need to be written first (Day 1 second-half task). Each must:
- Pass the new em-tautology gate (single direction, not disjunction)
- Pass the strategy-keywords gate (no "Proof Strategy" or "Key Lemma" sections)
- Include a `contribution_statement` field at the top declaring what `target_resolved=1` would mean for THIS submission

### Day 3-4 — Fetch + audit

```bash
python3 scripts/aristotle_fetch.py status   # see all 5 active
python3 scripts/aristotle_fetch.py fetch    # download completed results
python3 scripts/audit_proven.py             # populate axiom_count + em-tautology check
```

Reject any result that hits:
- `em-tautology` flag (CRITICAL audit issue)
- `axiomatizes_prior_work=1` (lemmas were imported as axioms — `compiled_no_advance`, not `_advance`)
- Empty `contribution_statement` despite the auditor request

### Day 5-7 — Second wave

Only double down on targets that produced **real delta evidence** (proven non-axiomatic lemmas with a meaningful `contribution_statement`). Otherwise rotate in one Erdős-Straus scout (single residue class, not the full 6) to test if the modular approach is salvageable.

---

## What we need to BUILD before Day 1

Per the debate, the absolute prerequisite before any submission is the **per-target `contribution_statement`**. The new schema-honesty pipeline will mark anything without one as `compiled_no_advance` no matter how clean the Lean compiles. Codex's biggest-risk call was unanimous: "we may get polished Lean proofs that prove known lemmas, necessary conditions, or prior-work wrappers without `target_resolved=1`."

So Day 1 second-half work (after the `feit_thompson` `ask`):
1. Write 4 fresh sketches matching the gate (existence-form only, 30-line cap, mandatory `contribution_statement`):
   - `leinster_nonabelian_S3xC5.txt`
   - `brocard_impossibility_range.txt` (pick a specific narrow range — Codex Q4 asked "what specific n range is narrow enough to be a real 2-week theorem?" — needs answer)
   - `erdos647_existence_delta.txt` (must enumerate which prior sub-results are off-limits)
   - `erdos203_existence.txt` (pick from the 8 staged variants; favor the one with the cleanest formal statement)

---

## Open uncertainties (not resolved by the debate)

1. **Will the `feit_thompson` slot 613 UUID 403 under the current API key?** Earlier today we hit 403 on March-12 batch UUIDs because key was rotated. Need to test before counting on the `ask` path.
2. **Exact Lean target name for `Leinster: Nonabelian Leinster exists (S3×C5)`** — Codex Q1. The candidate_problems entry exists but the formal-conjectures Lean theorem may need to be located.
3. **`brocard` modular range size** — Codex Q4. "No solutions for specific n ranges" needs a concrete range (e.g., `n ∈ [10, 100]`, or `n ≡ k mod m` for some specific k, m).
4. **Whether Claude Opus 4.7 alone (as sketch-writer) is enough**, vs waiting for Gemini 3.x access / Codex GPT-5.5 Pro transport to settle. Codex's view: "Claude's strength is debugging and refinement, which favors warm restarts over cold sketch problems." This argues for the `feit_thompson` `ask` strategy first.

---

## Single most important next action (both AIs agreed)

> "Choose the exact strongest existing `feit_thompson` slot and run a focused `ask` that asks for the missing final theorem, not more supporting lemmas."

That slot is **613** (uuid `16006bd6-747...`). The `ask` prompt is drafted above. Estimated cost: 0 new Aristotle slots (reuses existing project), 1 new AgentTask, ~9 hours wall-clock for completion.

This is the cheapest, highest-information experiment we can run today. If `ask()` works against the old UUID and produces a non-axiom result advancing the prior structure theory, that's the strongest possible validation of the new tooling. If it 403s (API key doesn't own the slot), we learn that too and pivot to fresh-submission mode.

---

## Portfolio risk summary

**The dominant failure mode is no longer "the pipeline is broken" or "the gate rejects."** It is now: **5 clean Lean compiles that all land as `compiled_no_advance`**, none of which resolve any open problem.

Mitigation: every single submission needs (1) a single-direction theorem (no disjunction), (2) a written `contribution_statement` declaring what `target_resolved=1` would mean, (3) explicit exclusion of axiomatized prior work. The schema honesty migration makes this measurable; the gate enforces (1); the auditor enforces (2) and (3).
