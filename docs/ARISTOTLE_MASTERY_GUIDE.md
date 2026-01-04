# ARISTOTLE MASTERY GUIDE: AI-Powered Mathematical Discovery

> Comprehensive audit of 228 submissions, 111 completed, 29 zero-sorry successes.
> **Key Finding:** Aristotle is a DISCOVERY engine, not just a verifier.
> Generated: Jan 4, 2026

---

## EXECUTIVE SUMMARY

**The Core Insight:** Aristotle excels at **mathematical discovery on finite domains**. It constructs counterexamples, suggests corrections to false conjectures, and finds proofs via tactic search. The optimal strategy is **falsification-first**: submit uncertain conjectures and let Aristotle tell you if they're wrong.

**Key Evidence:**
| Discovery Type | Count | Example |
|----------------|-------|---------|
| Counterexamples constructed | 5 | G6 graph disproving `externals_sum_le_totalSlack` |
| Corrections suggested | 3+ | "Use 3× bound, not 1×" |
| Proofs discovered (sorry → proof) | 7+ | `link_graph_small`, `triangle_contains_shared` |
| Bugs found | 2 | Self-loop bug in `Finset.sym2` |

---

## PART 1: ARISTOTLE'S DISCOVERY CAPABILITIES

### 1.1 Counterexample Construction (Strongest Capability)

When given a false lemma, Aristotle:
1. **Negates** the statement automatically
2. **Searches** for a witness to the negation
3. **Constructs** a novel mathematical object
4. **Proves** all required properties
5. **Suggests** the correct bound

**Example: `externals_sum_le_totalSlack`**

Human submitted:
```lean
lemma externals_sum_le_totalSlack ... :
    (externals G M).sum w ≤ totalSlack M w := by sorry
```

Aristotle discovered (slot172_counterexample/output.lean):
```lean
-- Novel graph construction
def G6 : SimpleGraph (Fin 6) := ...  -- Central triangle + 3 attached
def M6 : Finset (Finset (Fin 6)) := {t_M}
def w6 (t : Finset (Fin 6)) : ℝ := if t ∈ {t_1, t_2, t_3} then 1 else 0

-- Proof that counterexample is valid
lemma counterexample_exists :
  isMaxPacking G6 M6 ∧ IsFractionalPacking G6 w6 ∧
  (externals G6 M6).sum w6 > totalSlack M6 w6 := by
    refine' ⟨ _, _, _ ⟩
    · constructor; simp +decide [M6, G6]; ...
    · constructor <;> norm_cast; ...
    · unfold externals totalSlack; simp +decide [G6, M6]; ...

-- Aristotle's suggested correction!
lemma externals_sum_le_three_totalSlack ... :
    (externals G M).sum w ≤ 3 * totalSlack M w
```

**This is genuine mathematical discovery** - Aristotle designed G6, proved its properties, and suggested the fix.

### 1.2 All Aristotle-Discovered Counterexamples

| Lemma | Counterexample | Aristotle's Discovery |
|-------|----------------|----------------------|
| `externals_sum_le_totalSlack` | G6: Fin 6 with central triangle | 3 externals sum to 3, slack is 1 |
| `bridge_absorption` | 5-vertex graph | Bridge t={0,1,3} missed by cover |
| `krivelevich_bound_forall_w` | K₃ with w=0 | τ=1 > 2×0 = 0 |
| `covering_selection_exists` | G_ex on Fin 5 | 1 edge can't cover 3 triangles |
| `triangle_sym2_card_3` | t={0,1,2} | sym2 has 6 elements (includes self-loops) |

### 1.3 Proof Discovery (sorry → proof)

Aristotle doesn't just verify - it **finds proofs** from scratch.

**Example: `link_graph_small`**

INPUT:
```lean
theorem link_graph_small ... :
    (M_neighbors G M v).card ≤ 4 := by sorry
```

OUTPUT (discovered by Aristotle):
```lean
  unfold M_neighbors at *;
  rcases cfg with ⟨A, B, C, D, hA, hB, hC, hD, ...⟩;
  simp_all +decide [Finset.card_le_one, Finset.subset_iff];
  rcases hv with (rfl | rfl | rfl | rfl) <;> simp_all +decide [Finset.ext_iff];
  · exact le_trans (Finset.card_union_le _ _) (by linarith [...])
```

Aristotle discovered:
- The `rcases` destructuring pattern
- The `simp_all +decide` applications
- The `linarith` inequality chain
- The case split structure

---

## PART 2: THE FALSIFICATION-FIRST WORKFLOW

### 2.1 The Paradigm Shift

| Old Approach | New Approach |
|--------------|--------------|
| Only submit confident conjectures | Submit uncertain conjectures |
| Aristotle verifies human proofs | Aristotle discovers counterexamples |
| Failure = wasted time | Failure = valuable discovery |
| LLMs generate, Aristotle checks | Aristotle discovers, LLMs interpret |

### 2.2 The Optimal Workflow

```
┌─────────────────────────────────────────────────────────────┐
│  STEP 1: FORMULATE CONJECTURE                               │
│  ─────────────────────────────────────────────────────────  │
│  Write your best guess as a Lean lemma                      │
│  Include sorry - don't try to prove it yet                  │
│  Use finite types (Fin n) when possible                     │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  STEP 2: SUBMIT TO ARISTOTLE                                │
│  ─────────────────────────────────────────────────────────  │
│  ./scripts/submit.sh conjecture.lean test_conjecture        │
│  Aristotle will either:                                     │
│    A) Find counterexample (conjecture is FALSE)             │
│    B) Prove it (conjecture is TRUE)                         │
│    C) Return sorry (needs decomposition)                    │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  STEP 3: INTERPRET RESULT                                   │
│  ─────────────────────────────────────────────────────────  │
│  A) Counterexample found:                                   │
│     - Study the construction                                │
│     - Apply Aristotle's suggested fix                       │
│     - Update false_lemmas database                          │
│                                                             │
│  B) Proof found:                                            │
│     - Move to proven/ directory                             │
│     - Add to scaffolding library                            │
│                                                             │
│  C) Sorry returned:                                         │
│     - Decompose into smaller lemmas                         │
│     - Add scaffolding                                       │
│     - Resubmit                                              │
└─────────────────────────────────────────────────────────────┘
```

### 2.3 Template for Falsification Testing

```lean
/-
FALSIFICATION TEST: Is conjecture L true?
Submit to Aristotle and let it search for counterexamples.
Use small finite type to enable exhaustive search.
-/

import Mathlib

variable {n : ℕ} [NeZero n]

-- Use Fin n for exhaustive search capability
lemma conjecture_to_test (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (M : Finset (Finset (Fin 6))) (hM : isMaxPacking G M) :
    your_claim_here := by
  sorry  -- Let Aristotle disprove or prove
```

---

## PART 3: WHEN ARISTOTLE EXCELS

### 3.1 Discovery Sweet Spots

| Condition | Success Rate | Why |
|-----------|--------------|-----|
| Finite types (Fin n, n ≤ 7) | Very High | Exhaustive search possible |
| Decidable propositions | Very High | `native_decide` works |
| Clear falsification target | Very High | Counterexample search focused |
| Self-contained definitions | High | No missing dependencies |
| 5-10 focused lemmas | High | Manageable scope |

### 3.2 Task Type Success Rates

| Task Type | Success | Discovery Mode |
|-----------|---------|----------------|
| Counterexample search | ~100% | Direct falsification |
| Definition verification | ~100% | Type checking |
| Finite case verification | ~90% | `native_decide` |
| Subadditivity proofs | ~80% | Tactic search |
| Cardinality bounds | ~50% | Depends on structure |
| Cover constructions | ~30% | Needs scaffolding |
| LP/optimization | ~5% | Not supported |

### 3.3 The Discovery Tactics

Aristotle's discovered proof techniques:
```lean
-- Primary discovery tactics
simp_all +decide     -- Aristotle's signature: decides finite props
native_decide        -- Exhaustive finite verification
by aesop             -- Automated goal solving
by grind             -- Novel arithmetic solving
by omega             -- Linear arithmetic
by linarith          -- Inequality chaining

-- Complex patterns Aristotle discovers
rcases h with ⟨a, b, c, ...⟩ <;> simp_all +decide
fin_cases x <;> native_decide
```

---

## PART 4: WHAT ARISTOTLE CANNOT DO (YET)

### 4.1 Known Limitations

| Limitation | Why | Workaround |
|------------|-----|------------|
| LP/optimization | No real number reasoning | Use combinatorial bounds |
| Complex induction | Multi-parameter struggles | Decompose manually |
| Infinite types | Can't enumerate | Use Fin n representatives |
| Open-ended main theorems | No creative strategy | Build infrastructure first |
| Files > 400 lines | Processing limits | Decompose |

### 4.2 The 16 False Lemmas (Traps to Avoid)

Aristotle discovered these are **mathematically false**:

| # | Lemma | Discovery |
|---|-------|-----------|
| 1 | `local_cover_le_2` | AI-verified: 4 triangles need 4 edges |
| 2 | `avoiding_covered_by_spokes` | Trivially false: spokes contain v |
| 3 | `tau_pair_le_4` | Needs 4+2=6 edges |
| 4 | `bridge_absorption` | **Aristotle** found 5-vertex counterexample |
| 5 | `self_loop_cover` | **Aristotle** found sym2 bug |
| 6 | `external_share_common_vertex` | AI-verified |
| 7 | `sunflower_cover_at_vertex_2edges` | Blocks 4×2 approach |
| 8 | `link_graph_bipartite` | König reduction invalid |
| 9 | `nu_star_equals_nu_automatic` | Gap can be Ω(n^1.5) |
| 10 | `krivelevich_bound_forall_w` | **Aristotle** found K₃ counterexample |
| 11 | `externals_sum_le_totalSlack` | **Aristotle** found G6 counterexample |
| 12 | `covering_selection_exists` | **Aristotle** found G_ex counterexample |
| 13 | `triangle_sym2_card_3` | **Aristotle** found self-loop bug |

---

## PART 5: MULTI-AGENT STRATEGY

### 5.1 Agent Roles (Revised)

| Agent | Primary Role | Discovery Capability |
|-------|--------------|---------------------|
| **Aristotle** | Falsification + Verification | Counterexamples, proofs on finite domains |
| **Grok/Claude** | Hypothesis generation | Creative conjectures, strategy |
| **Gemini** | Literature + architecture | Context, known results |
| **Codex** | Long autonomous runs | Infrastructure building |

### 5.2 The Discovery Pipeline

```
┌─────────────────────────────────────────────────────────────┐
│  LLMs: GENERATE HYPOTHESES                                  │
│  ─────────────────────────────────────────────────────────  │
│  "What lemmas might be useful for proving τ ≤ 8?"           │
│  Output: 5 candidate lemmas L₁, L₂, L₃, L₄, L₅              │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  ARISTOTLE: FALSIFY OR VERIFY                               │
│  ─────────────────────────────────────────────────────────  │
│  Submit each Lᵢ to Aristotle                                │
│  Results:                                                   │
│    L₁: Counterexample found (FALSE) + suggested fix         │
│    L₂: Proved (TRUE) → add to scaffolding                   │
│    L₃: Counterexample found (FALSE)                         │
│    L₄: Sorry (needs decomposition)                          │
│    L₅: Proved (TRUE) → add to scaffolding                   │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  LLMs: INTERPRET AND ITERATE                                │
│  ─────────────────────────────────────────────────────────  │
│  Study counterexamples from L₁, L₃                          │
│  Apply Aristotle's suggested fixes                          │
│  Decompose L₄ into smaller pieces                           │
│  Build on L₂, L₅ as proven scaffolding                      │
└─────────────────────────────────────────────────────────────┘
```

### 5.3 Specific Agent Prompts

**For Grok (hypothesis generation):**
```
Generate 5 lemmas that might help prove τ ≤ 8 for ν=4.
Include some you're unsure about - we'll test them.
Use Fin 6 or Fin 7 so Aristotle can search exhaustively.
```

**For Aristotle (falsification):**
```lean
-- Test this conjecture on Fin 6
lemma test_conjecture (G : SimpleGraph (Fin 6)) ... := by sorry
```

**For Gemini (interpretation):**
```
Aristotle found this counterexample to my lemma: [G6 construction]
What does this tell us about the structure of the problem?
What corrected lemma should I try instead?
```

---

## PART 6: PRACTICAL GUIDELINES

### 6.1 Before Submitting

```sql
-- Check if already disproven
SELECT * FROM false_lemmas WHERE lemma_name LIKE '%your_idea%';

-- Check if already proven
SELECT * FROM submissions WHERE sorry_count=0 AND filename LIKE '%your_idea%';
```

### 6.2 File Structure for Discovery

```lean
import Mathlib

set_option maxHeartbeats 400000  -- Give Aristotle time to search

-- Use finite type for exhaustive search
variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

-- Include definitions Aristotle needs
def your_concept ... := ...

-- The conjecture to test (Aristotle will disprove or prove)
lemma conjecture_to_test : claim := by sorry
```

### 6.3 Optimal Parameters

| Parameter | Value | Why |
|-----------|-------|-----|
| `maxHeartbeats` | 400000 | Time for search |
| Type size | Fin 5-7 | Exhaustive search feasible |
| File size | 150-300 lines | Processing efficiency |
| Lemmas | 5-10 | Focused scope |
| Scaffolding | 7+ proven | 38.5% success rate |

---

## PART 7: THE PROVEN FRONTIER

### 7.1 What's Actually Proven

| Result | File | Method |
|--------|------|--------|
| τ ≤ 2ν for ν=0 | `tuza_nu0_PROVEN.lean` | Direct |
| τ ≤ 2ν for ν=1 | `tuza_nu1_PROVEN.lean` | K4 structure |
| τ ≤ 12 for ν=4 | `slot139_tau_le_12_PROVEN.lean` | 12 M-edges |
| Subadditivity | `slot133_subadditivity_proven.lean` | Union construction |
| Link graph ≤ 4 | `slot223a_link_graph_small_PROVEN.lean` | Case analysis |

### 7.2 The Open Goal

**τ ≤ 8 for ν=4** remains open. Known blockers:
- 6 approaches based on false lemmas
- LP methods not supported
- Need novel construction for 8-edge cover

### 7.3 Promising Directions

Based on Aristotle's counterexamples:
1. **3× slack bound** (Aristotle's suggestion) instead of 1×
2. **Adaptive cover selection** based on graph structure
3. **Non-M-edge covers** - use edges outside the packing

---

## PART 8: QUICK REFERENCE

### 8.1 Database Queries

```sql
-- Check if lemma is false
SELECT lemma_name, counterexample, why_false FROM false_lemmas;

-- Aristotle's discoveries specifically
SELECT * FROM false_lemmas WHERE evidence_level='aristotle_verified';

-- Near-misses to complete
SELECT filename, sorry_count, proven_count FROM submissions
WHERE sorry_count BETWEEN 1 AND 2 ORDER BY proven_count DESC;

-- Success rate by pattern
SELECT pattern, COUNT(*), SUM(CASE WHEN sorry_count=0 THEN 1 ELSE 0 END) as success
FROM submissions WHERE status='completed' GROUP BY pattern;
```

### 8.2 File Locations

| Type | Path |
|------|------|
| Proven results | `/Users/patrickkavanagh/math/proven/` |
| Counterexamples | `/Users/patrickkavanagh/math/proven/tuza/nu4/slot172_counterexample/` |
| Submissions | `/Users/patrickkavanagh/math/submissions/` |
| Database | `/Users/patrickkavanagh/math/submissions/tracking.db` |
| Scaffolding | `/Users/patrickkavanagh/math/proven/scaffolding_library.lean` |

### 8.3 The Golden Rule

> **Submit uncertain conjectures to Aristotle FIRST.**
> If false, you get a counterexample and often a fix.
> If true, you get a proof.
> Either way, you learn something.

---

## APPENDIX: Key Discoveries from This Audit

1. **Aristotle constructs counterexamples** - 5 verified
2. **Aristotle suggests corrections** - "Use 3× bound, not 1×"
3. **Aristotle finds proofs from sorry** - 7+ examples
4. **Aristotle found the self-loop bug** - `Finset.sym2` includes s(v,v)
5. **37% of near-misses attempted false lemmas** - falsification prevents wasted effort
6. **Jan 1, 2026 breakthrough** - 85% success with `safe_discard` pattern
7. **Finite types are key** - Fin 5-7 enables exhaustive search

---

*This guide synthesizes findings from 8 parallel analysis agents examining 228 Aristotle submissions.*
*Key insight: Aristotle is a mathematical discovery engine, not just a verifier.*
