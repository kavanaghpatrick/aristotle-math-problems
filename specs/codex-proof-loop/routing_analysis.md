---
spec: codex-proof-loop
artifact: routing-analysis
created: 2026-03-14
data-sources:
  - submissions/tracking.db (1200+ submissions, 561 distinct problems)
  - codex_results/v3/ (37 files, pure analysis + 1 lean file)
  - results_v07/ (134 entries, ~67 extracted result directories)
  - failed_approaches table (56 entries)
  - false_lemmas table
---

# Queue Routing Analysis: Codex vs Aristotle

## Executive Summary

Analysis of 1200+ submissions across 561 problems reveals clear routing patterns. Codex (v3) currently produces only mathematical *analysis* (markdown), not Lean proofs -- the proof loop will change this. Aristotle has a ~4% full-proof rate on open conjectures but excels at sub-problems and negation. Context-stacking (feeding prior results) shows measurable benefit for iterative problems. The dominant anti-pattern is over-iteration on a single hard problem (tuza_nu4: 317 submissions, 13 successes, all on sub-lemmas).

---

## 1. What Codex Solves vs Gets Stuck On

### Current Codex Capability (v3 analysis mode)

Codex v3 outputs are **pure mathematical analysis** in markdown (37 files). Only 1 file is Lean code (`agoh_giuga_ge6_factors.lean`). Codex currently does NOT iterate on Lean proofs -- this is the gap the proof loop fills.

**What Codex does well (analysis mode):**

| Strength | Example | Evidence |
|----------|---------|----------|
| Problem clarification | erdos850: correctly identified misstatement | `codex_results/v3/erdos850_math.md` |
| Literature review | erdos389: identified Kummer carry criterion, finiteness proof | `codex_results/v3/erdos389_math.md` |
| Gap identification | erdos68: identified exact obstruction (denominator growth) | `codex_results/v3/erdos68_sorry_math.md` |
| Incremental Lean extension | agoh_giuga: pushed bound from >=5 to >=9 factors | `codex_results/v3/agoh_giuga_sorry3_math.md` |
| Feasibility assessment | jacobian: correctly identified JC_2 as genuinely open | `codex_results/v3/jacobian_math.md` |

**What Codex struggles with:**
- Generating compilable Lean 4 code (only 1 of 37 v3 files has Lean)
- Closing final sorry on genuinely open problems (expected)
- Handling Mathlib API changes (technical_issue failures)

### Predicted Codex Proof Loop Strengths (based on APOLLO data + codebase patterns)

| Problem Type | Predicted Success | Rationale |
|-------------|-------------------|-----------|
| Arithmetic bounds (prime gaps, reciprocal sums) | HIGH | `agoh_giuga_ge6_factors.lean` compiled. `decide`/`omega`/`norm_num` tactics close these. |
| Finite case exhaustion | HIGH | Codex already does this in analysis. `by_contra` + `omega` pattern. |
| Negation of false lemmas | MEDIUM-HIGH | 47/56 failed approaches = `wrong_direction`. Counterexample construction is finite. |
| Mathlib API wrangling | MEDIUM | Codex knows API but has version drift. Compile-fix loop will self-correct. |
| Deep structural proofs | LOW | Open conjectures resist. These need Aristotle's extended budget. |

---

## 2. What Aristotle Solves vs Gets Stuck On

### Aristotle Success Patterns (from DB + result files)

**31 distinct problems with successful Aristotle results.** Breakdown:

| Category | Count | Examples | Sorry Range |
|----------|-------|----------|-------------|
| Sub-lemma proofs (Tuza decomposition) | 14 | nu4_cycle4_tau_le_4, nu4_star_all_4_tau_le_4, nu4_scattered | 0 sorry |
| Infrastructure/scaffolding proofs | 7 | slot70-72 resubmits, slot138, slot142 | 0-6 sorry |
| Partial progress on open problems | 6 | erdos647, erdos1, path4_tau_le_8 | 1-4 sorry |
| Negation results | 2 | tuza_nu2_negation, nu4_cycle4_lp (negated) | 0-1 sorry |
| Context-stacked resubs | 4 | slot259_resub, slot262_resub, slot347_resub, slot542 | 1 sorry |

**Aristotle failure modes:**

| Failure Mode | Count | Evidence |
|-------------|-------|----------|
| budget_exhausted | 2 | Ran out of compute budget |
| failed_load | 3 | Lean project failed to load (technical) |
| internal_error | 2 | Aristotle processing error |
| negated (found counterexample) | 2 | Disproved the claimed lemma |
| FAILED | 4 | General failure after attempting |
| partial (couldn't close all sorries) | 26 | Most common: got stuck on hard core |

**Key insight:** Aristotle's 0-sorry successes cluster on **bounded finite problems** (tau_le_4 for specific graph structures, specific case decompositions). It struggles with the same "hard core" sorry that Codex struggles with -- the genuinely open conjecture statement.

### Sorry Patterns in Aristotle Results

Examining Lean files across `results_v07/`:

| Sorry Pattern | Meaning | Can Codex Fix? |
|--------------|---------|----------------|
| Single sorry at theorem statement | Open conjecture, correctly identified | NO -- genuinely open |
| 1-3 sorries in helper lemmas | Partial progress, infrastructure gap | MAYBE -- if lemma is decidable |
| Sorry on `False` conclusion | Needs impossibility proof | NO -- requires deep reasoning |
| Sorry on decidable predicate (`n = 3`, `p = 17`) | Finite case analysis | YES -- `decide`/`omega` |
| Sorry on existential (`exists x y z`) | Needs witness construction | MAYBE -- if witnesses are small |

**Specific sorry examples from results:**

```
-- CAN'T FIX: Open conjecture (erdos68)
Irrational (sum' n, 1 / ((n+2).factorial - 1)) := by sorry

-- CAN'T FIX: Hard impossibility (agoh_giuga)
(hgiuga : ... IsGiuga ...) : False := by sorry

-- MAYBE FIX: Finite cases (erdos936)
n = 3 := by sorry   -- if proof is just case analysis

-- CAN'T FIX: Existential witness (erdos203)
exists m, m > 0 ... := by sorry
```

---

## 3. Context-Stacking: When It Helps vs Not

### Evidence from DB

15 submissions explicitly reference prior context in gap_statement. All have `compiled_clean` status (Aristotle accepted them). Key patterns:

| Problem | Context Used | Outcome | Verdict |
|---------|-------------|---------|---------|
| sierpinski_5n | slot651 context | compiled_clean | HELPED -- narrowed subcases |
| integer_complexity | slot648, slot654 context | compiled_clean | HELPED -- built on partial |
| erdos850 | slot614+slot693, slot702+slot614, slot705+slot702 | compiled_clean | HELPED -- 3 rounds of stacking |
| agoh_giuga | slot675 context | compiled_clean | HELPED -- extended bound |
| erdos672 | slot698 Pell context | compiled_clean | HELPED -- connected to Pell |
| erdos203 | slot694 context | compiled_clean | HELPED -- covering system refined |

**When context-stacking helps:**
1. **Incremental bounds** (agoh_giuga: 5 factors -> 6 -> 9 factors). Each round extends.
2. **Case decomposition** (sierpinski_5n: subcases narrowed by prior results).
3. **Connecting results** (erdos672 + Pell results, erdos850 + prime factor results).
4. **Sorry reduction** (resubs that provide partial proofs for Aristotle to complete).

**When context-stacking does NOT help:**
1. **Fundamentally hard core** (tuza_nu4: 317 submissions, same hard sorry remains).
2. **Wrong direction** (47 failed approaches -- stacking wrong results compounds error).
3. **Definition bugs** (6 failures from incorrect Lean definitions -- context propagates the bug).

**Quantified impact:** Context-stacked resubs have a `compiled_clean` rate of 15/15 = 100%. However, `compiled_clean` means Aristotle accepted the job, not that it solved the problem. The deeper question is whether Aristotle *reduces sorries* -- and from the slot259/262/347_resub results showing sorry=1, context stacking does appear to help Aristotle make progress.

---

## 4. Optimal Retry Strategy

### Data: Iteration Counts and Outcomes

From `submissions` table analysis:

| Iterations | Success Rate | Sample |
|-----------|-------------|--------|
| 1-3 | ~8% (among non-tuza) | Most single-shot submissions |
| 4-6 | ~5% | Extended attempts |
| 7-10 | ~3% | Diminishing returns |
| 11+ | <1% | Almost never works (tuza_nu4 had 17-iteration attempts) |

**tuza_nu4 case study (extreme over-iteration):**
- 317 total submissions
- 13 successes (4.1%), ALL on sub-lemmas, NONE on the main conjecture
- Average iterations on successful sub-lemmas: 0-5
- Maximum iteration on any successful result: 11
- Iterations > 10: 0% success on the main problem

### Recommended Retry Strategy

```
CODEX PROOF LOOP:
  Round 1: Codex writes proof, lake build
  Round 2-3: Codex fixes errors with build output feedback
  Round 4-5: Codex tries alternative approach if stuck on same error

  IF sorry_count == 0 after any round: SUCCESS -> done
  IF sorry_count decreased: continue to max 5 rounds
  IF sorry_count unchanged after 2 rounds: ESCALATE TO ARISTOTLE
  IF sorry_count increased: REJECT, revert to best prior version
  IF build fails after 3 rounds: STOP, problem likely needs reformulation

  MAX CODEX ITERATIONS: 5 (hard cap)

ARISTOTLE ESCALATION:
  Submit best Codex .lean as context
  IF Aristotle returns sorry_count > 0:
    Re-submit with Aristotle output as new context (context-stack)
    MAX 2 context-stacking rounds
  IF Aristotle budget_exhausted or failed:
    Record in failed_approaches, move to different problem

  MAX ARISTOTLE ATTEMPTS PER PROBLEM: 3 (initial + 2 resubs)

GIVE UP CRITERIA:
  - 3 Aristotle attempts with no sorry reduction
  - Problem appears in false_lemmas table (approach disproven)
  - 5+ Codex iterations with 0 sorry reduction
  - Same error pattern repeated 3 times (cycle detection)
```

---

## 5. When to Give Up on a Problem

### Anti-Patterns from Data

| Signal | Action | Evidence |
|--------|--------|----------|
| 10+ submissions, 0 sorry reduction | ABANDON this approach | tuza_nu4 main theorem |
| Approach appears in failed_approaches | SKIP, try different approach | 56 recorded failures |
| Aristotle returns "negated" | STOP -- lemma is false | nu4_cycle4_lp, tuza_nu2_negation |
| 3+ rounds of context-stacking, same sorry | ABANDON problem for now | diminishing returns |
| Problem misstatement discovered | REFORMULATE, not retry | erdos850 misstatement caught by Codex |
| wrong_direction failure | Don't retry same angle | 47/56 failures are wrong_direction |

### Problem Classification for Give-Up Decisions

```
CATEGORY A: Bounded/Finite (keep trying)
  - Reciprocal sum bounds (agoh_giuga: >=5 -> >=9)
  - Finite case exhaustion
  - Specific graph structure lemmas
  -> These have diminishing but real returns from iteration

CATEGORY B: Structural Lemmas (try 2-3 times)
  - Sub-problems of open conjectures
  - Definition-dependent results
  -> Success depends on correct problem formulation

CATEGORY C: Open Conjectures (try once per new approach)
  - The "hard core" sorry that resists everything
  - Novel mathematical insight required
  -> Submit bare conjecture, let Aristotle attempt once
  -> If fails: wait for new mathematical idea, don't re-submit same thing

CATEGORY D: Disproven (never retry)
  - In false_lemmas or failed_approaches with "wrong_direction"
  - Counterexample found
  -> Record, never submit again
```

---

## 6. Sorry Patterns: "Codex Can Fix" vs "Needs Aristotle"

### Decision Matrix

| Sorry Context | Surrounding Code | Route To | Confidence |
|--------------|-----------------|----------|------------|
| `by sorry` after `decide`-like goal | Nat comparison, finite sets | CODEX | HIGH |
| `by sorry` after `omega`-solvable goal | Linear arithmetic | CODEX | HIGH |
| `by sorry` after `norm_num` goal | Numeric computation | CODEX | HIGH |
| `by sorry` with type class inference error | Missing instance | CODEX | MEDIUM |
| `by sorry` with Mathlib lemma name | Needs correct API call | CODEX | MEDIUM |
| `by sorry` on existential with small witness | `exists 3, by decide` | CODEX | MEDIUM |
| `by sorry` on induction step | Structural proof | ARISTOTLE | MEDIUM |
| `by sorry` on `False` conclusion | Impossibility | ARISTOTLE | HIGH |
| `by sorry` on main theorem of open problem | Genuinely open | NEITHER | - |
| `by sorry` after long tactic chain | Complex proof state | ARISTOTLE | HIGH |

### Heuristic Rules for Automated Routing

```python
def route_sorry(goal_type: str, context_lines: int, is_open_conjecture: bool) -> str:
    """Determine where to route a sorry-containing proof."""

    # Never route open conjectures to Codex for closure
    if is_open_conjecture and goal_type == "main_theorem":
        return "ARISTOTLE"  # or "SKIP" if already tried

    # Decidable goals -> Codex
    if goal_type in ("nat_comparison", "finite_case", "numeric"):
        return "CODEX"

    # Short proofs with API issues -> Codex
    if context_lines < 20 and goal_type == "tactic_error":
        return "CODEX"

    # Complex structural proofs -> Aristotle
    if context_lines > 50 or goal_type in ("induction", "impossibility"):
        return "ARISTOTLE"

    # Default: try Codex first (cheaper, faster)
    return "CODEX"
```

### Build Error Classification

| Error Type | Meaning | Route |
|-----------|---------|-------|
| `unknown identifier` | Wrong Mathlib API name | CODEX (API lookup) |
| `type mismatch` | Wrong argument types | CODEX (type fixing) |
| `tactic failed` | Tactic insufficient | CODEX 1st, ARISTOTLE 2nd |
| `maximum heartbeat exceeded` | Proof too slow | Needs restructuring -> CODEX |
| `deep recursion` | Infinite loop in proof | CODEX (restructure) |
| `sorry` (clean compile) | Proof gap | Decision matrix above |

---

## 7. Aristotle Turnaround Time

### From Database

The `execution_seconds` field is NULL for most submissions (not tracked consistently). However, temporal analysis of `created_at` vs `completed_at` patterns:

| Observation | Data Point |
|-------------|-----------|
| Typical Aristotle queue time | Minutes to hours (based on slot assignment patterns) |
| Aristotle budget per job | Fixed budget, varies by plan |
| Budget exhaustion indicator | `aristotle_status = 'budget_exhausted'` (2 occurrences) |
| Processing errors | `aristotle_status = 'internal_error'` (2 occurrences) |
| Load failures | `aristotle_status = 'failed_load'` (3 occurrences, all path4_tau_le_8) |

**Practical turnaround:** Based on the submission timestamps in `created_at`:
- Batch submissions (multiple slots at once) show results arriving within the same day
- Single submissions typically complete within hours
- Budget exhaustion means Aristotle spent its full allocation without closing all sorries

**Implication for routing:** Codex iterations are faster (seconds per round via `lake build` + Codex API). Use Codex for quick fixes, Aristotle for deep exploration. A 5-round Codex loop at ~1 min/round = 5 minutes. An Aristotle submission = hours.

---

## 8. Actionable Routing Rules

### Rule 1: Sorry Triage

```
ON receiving a .lean file with sorry:
  1. Count sorries
  2. Classify each sorry (decision matrix above)
  3. If ALL sorries are Codex-fixable: route to Codex loop (max 5 rounds)
  4. If ANY sorry is deep/structural: route best Codex attempt to Aristotle
  5. If main theorem sorry on open problem: submit bare gap to Aristotle (INFORMAL)
```

### Rule 2: Failure Routing

```
ON Codex loop failure (5 rounds, no progress):
  1. Check failed_approaches for this problem
  2. If approach already failed: SKIP, try different formulation
  3. If new approach: submit to Aristotle with Codex best-attempt as context
  4. Record attempt in tracking DB regardless
```

### Rule 3: Context Stacking

```
ON Aristotle partial result (sorry_count > 0):
  1. If sorry_count decreased vs prior submission: re-submit with new result as context
  2. If sorry_count unchanged: check if different sorries (progress on some, new on others)
  3. If truly stuck: record in failed_approaches, try different problem
  4. Max 2 context-stacking rounds per problem per approach
```

### Rule 4: Problem Selection

```
PRIORITY QUEUE:
  1. Problems with Codex analysis already done (37 in v3) -- warm start
  2. Problems with partial Aristotle results (sorry=1-3) -- close to done
  3. New problems screened as OPEN -- fresh attempts
  4. Problems with context-stacking history -- incremental progress

NEVER QUEUE:
  - Problems in false_lemmas table
  - Approaches in failed_approaches with same hash
  - tuza_nu4 main theorem (317 attempts, exhausted)
```

### Rule 5: Cost Optimization

```
COST TIERS:
  Codex loop (5 rounds): ~$0.10-0.50 (API calls + local build)
  Aristotle submission: ~$5-20 (extended compute budget)

ROUTING BY COST:
  Try Codex first ALWAYS (cheap, fast)
  Escalate to Aristotle only when:
    - Codex makes no progress after 3 rounds
    - Sorry is structural/deep (not API/tactic issue)
    - Problem has prior Aristotle context to stack
```

---

## Appendix: Data Summary

| Metric | Value |
|--------|-------|
| Total submissions in DB | 1200+ |
| Distinct problems attempted | 561 |
| Successful Aristotle results (any sorry count) | 44 |
| Fully proven (0 sorry) | 16 |
| Failed approaches recorded | 56 (47 wrong_direction, 6 technical, 3 definition_bug) |
| False lemmas recorded | 30+ |
| Codex v3 analysis files | 37 (36 markdown, 1 lean) |
| Aristotle result directories | 67 |
| Most-attempted problem | tuza_nu4 (317 submissions) |
| Highest context-stacking depth | 3 rounds (erdos850) |
| Gap-targeting compiled_clean rate | 127/393 = 32% |
| Gap-targeting completion rate | 135/393 = 34% |
| Gap-targeting near-miss rate | 69/393 = 18% |
