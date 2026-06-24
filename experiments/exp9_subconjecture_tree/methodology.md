# EXP9 — Sub-Conjecture Tree Search: Methodology Spec

**Agent:** EXP9
**Date:** 2026-05-31
**Target:** Erdős Problem 938 (finitely many 3-term APs of consecutive powerful numbers)
**Hypothesis:** Explicit tree search of conjecture space surfaces sub-claims that single-shot prompts miss.

## Setup

Generator: `grok-4.3` (xAI) — highest-capacity math-reasoning model accessible to project.
Reviewer: `codex exec` (OpenAI) — independent perspective, cross-critique.

## Protocol

### Step 1 — Tree generation (Grok-4.3)
Prompt Grok with:
- The full statement of E938 (informal + Lean).
- A "prior work / falsified angles" packet (drawn from `analysis/e938_deep_synthesis.md`, `analysis/research_fusion_erdos938.md`, slot-history 1259-1343).
- A schema requiring exactly 50 sub-conjectures grouped into 7 categories:
  - **W** Weakening
  - **R** Restriction
  - **S** Sharpening
  - **G** Generalization
  - **D** Dual
  - **N** Negation
  - **C** Decomposition
- For each, demand a Tractability/Impact/Novelty 1-10 rubric with rationales, EV = T × I.
- Enforce score discipline: average T ~5, average I ~5, no inflation.
- Final sections: top-10 ranking + bottom-5 floor + meta-observations (which category has highest mean EV, which 3 are most underrated, what new gap is surfaced).

### Step 2 — Cross-critique (Codex)
Pipe Grok's full tree to `codex exec`, ask:
- Identify ≥3 sub-conjectures that are **underrated** (Tractability or Impact is too low given known infrastructure).
- Identify ≥3 sub-conjectures that are **overrated** (T/I too high; flaw or known obstruction).
- Identify ≥1 sub-conjecture that is **redundant** (near-equivalent to an existing slot 1259-1343 submission).
- Adjust the EV rankings; produce a new top-5.
- Identify **one decomposition (C) that Grok missed** but is implicit in known literature.

### Step 3 — Top-5 attack
For each of the 5 highest cross-critique-adjusted EV sub-conjectures:
- Lift to a 5-10 line BARE sketch.
- Compare against existing slot 1259-1343 sketches — flag if duplicate (anti-redundancy filter).
- Estimate Aristotle's plausibility (formalizer reach: which Mathlib modules apply?).

(Note: actual Aristotle submission is OUT OF SCOPE for EXP9 — the experiment evaluates whether tree search surfaces high-EV sub-claims, not whether Aristotle can prove them. The attack stage is a paper attack: a bare sketch + plausibility estimate.)

### Step 4 — Verdict
Compare the top-5 from EXP9 against the 18 historical E938 submission angles (slots 1259-1343). Three measurable outcomes:

| Outcome | Verdict |
|---|---|
| ≥3 of top-5 are genuinely new angles (not in any prior slot) | **TREE SEARCH WINS** |
| 1-2 of top-5 are new | **MARGINAL** |
| 0 are new (all duplicates of slots 1259-1343) | **TREE SEARCH FAILS** |

## Falsification criteria for the hypothesis

Tree search **fails to surface novel high-EV sub-claims** if:
1. ≥80% of the 50 sub-conjectures are restatements of slot 1259-1343 angles.
2. The cross-critique-adjusted top-5 contain 0 sub-claims unobserved in prior E938 attack history.
3. Codex's "underrated" picks all overlap with Grok's own top-10.

If any 2 of these 3 fire, EXP9 concludes tree search is *not* additive over single-shot prompting for E938.

## Risk

- Grok may pattern-match to surface-level "variations" rather than genuine alternative angles. Mitigated by explicit Categories (W/R/S/G/D/N/C) demanding structural diversity.
- The 50-tree size may inflate noise. Mitigated by the EV threshold (top-5 by Codex-adjusted rank).
- Tractability/Impact scores may be self-serving. Mitigated by Codex cross-critique.

## Cost

- Grok-4.3 single call (~15K output tokens).
- Codex review (~5K output).
- Manual top-5 attack (10-15 mins).
- Total: ~30 min wall clock + minor API spend.
