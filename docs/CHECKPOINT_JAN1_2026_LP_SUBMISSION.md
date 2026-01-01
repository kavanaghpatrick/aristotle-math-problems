# Tuza ν=4 Project Checkpoint - January 1, 2026 (LP Submission)

## Executive Summary

**Mission**: Prove Tuza's conjecture τ(G) ≤ 2ν(G) for ν=4, i.e., τ ≤ 8.

**What Changed This Session**:
- Slot152 vertex-centric approach **unanimously rejected** by 3-AI debate
- LP relaxation approach formally documented in PRD
- AI debate identified **missing ν* ≤ 4 proof** (we only had ν* ≥ 4)
- Pattern 10 bug identified: Krivelevich must use sSup, not ∀w
- **3 new Aristotle submissions launched** (slot153, slot153b, slot154)

**Current State**:
- **Best PROVEN bound**: τ ≤ 12 (slot139, 0 sorry, 0 axiom)
- **Target bound**: τ ≤ 8 (LP submissions now pending)
- **False lemma patterns**: 10 documented (Pattern 10 added today)
- **Active Aristotle jobs**: 3

---

## Part 1: Today's Key Findings

### 1.1 Slot152 Rejection (Pattern 7 Confirmed)

**3-AI Debate Verdict**: UNANIMOUS INVALID

The claim `adaptiveCoverAt_exists ... E_v.card ≤ 2` is **mathematically impossible**.

**Counterexample at v_ab**:
```
Triangles: A, B, T1, T2, T3, T4
- {v_ab, x} covers T1-T4 but NOT A, B (x ∉ A, x ∉ B)
- A.sym2 ∩ B.sym2 = ∅ (no common edge)
- MINIMUM: 3 edges
```

**Why 4×2=8 Fails**: Each shared vertex needs minimum 3 edges (M-elements + externals). 4×3=12 is the actual bound.

See: `docs/DEBATE_SLOT152_JAN1_2026.md`

### 1.2 LP Relaxation Strategy (Only Remaining Path)

**The Approach**:
1. Krivelevich (1995): τ ≤ 2ν* (axiomatize published theorem)
2. Prove ν* = 4 for cycle_4 (our novel contribution)
3. Conclude: τ ≤ 8

**Critical Insight from AI Debate**:
The PRD originally only proved ν* ≥ 4 (constructive). We need BOTH:
- **ν* ≥ 4**: M_char construction achieves weight 4 ✓
- **ν* ≤ 4**: Edge-counting argument bounds all packings ← MISSING

**Edge-Counting Argument (from Grok)**:
```
Sum edge constraints over 12 M-edges:
- Each M-element contributes 3× (3 M-edges per triangle)
- 3(w(A)+w(B)+w(C)+w(D)) + externals ≤ 12
- Since externals ≥ 0: w(A)+w(B)+w(C)+w(D) ≤ 4
```

### 1.3 Pattern 10: Krivelevich Must Use sSup

**WRONG** (Pattern 10):
```lean
axiom krivelevich_forall_w (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    (τ G : ℝ) ≤ 2 * packingWeight G w
-- Counterexample: K₃ with w=0 gives τ=1 > 0
```

**CORRECT**:
```lean
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G
-- Uses SUPREMUM (ν*), not any particular packing
```

---

## Part 2: Aristotle Submissions (Active)

### 2.1 Submission Summary

| Slot | File | Description | Project ID | Expected Sorry |
|------|------|-------------|------------|----------------|
| 153 | slot153_nu_star_ge_4.lean | ν* ≥ 4 (lower bound) | `30006cc9-3f0c-4cd1-a49e-5bb9689c6c70` | 0 |
| 153b | slot153b_nu_star_le_4.lean | ν* ≤ 4 (upper bound) | `5f4ef776-e28a-4452-86ec-d29d5e9be9b3` | 2-3 |
| 154 | slot154_tau_le_8_krivelevich.lean | τ ≤ 8 (main theorem) | `463f73ab-915d-4f1e-86dc-ab7aa9e53028` | 0 (1 axiom) |

### 2.2 Files Structure

**slot153_nu_star_ge_4.lean** (Lower Bound):
```lean
def M_char (M : Finset (Finset V)) (t : Finset V) : ℝ :=
  if t ∈ M then 1 else 0

theorem M_char_is_fractional_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    IsFractionalPacking G (M_char M)

theorem nu_star_ge_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4) :
    ∃ w : Finset V → ℝ, IsFractionalPacking G w ∧ packingWeight G w = 4
```

**slot153b_nu_star_le_4.lean** (Upper Bound):
```lean
-- Key theorem (edge-counting)
theorem packingWeight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ M.card

theorem nu_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ 4
```

**slot154_tau_le_8_krivelevich.lean** (Main Theorem):
```lean
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G

theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    fractionalPackingNumber G = 4

theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    triangleCoveringNumber G ≤ 8
```

### 2.3 Fixes Applied (from AI Review)

| File | Issue | Fix |
|------|-------|-----|
| slot153 | `Finset.card_smul_eq_smul_card` doesn't exist | → `smul_eq_mul` + `Finset.sum_const` |
| slot153b | `Finset.card_filter_sym2_diag` doesn't exist | → sorry for Aristotle |
| slot153b | `h_ext_bound : externals ≤ 0` is FALSE | → Removed, use direct edge-counting |
| slot154 | `norm_cast` + `linarith` doesn't work | → `norm_num` + `exact_mod_cast` |

---

## Part 3: Updated False Lemma Patterns

### 3.1 All 10 Patterns (Summary)

| # | Lemma | Evidence | Impact |
|---|-------|----------|--------|
| 1 | `local_cover_le_2` | AI-VERIFIED | 4 M-edges needed at vertex |
| 2 | `avoiding_covered_by_spokes` | TRIVIAL | Spokes contain v, avoiding doesn't |
| 3 | `bridge_absorption` | ARISTOTLE | Bridges need separate handling |
| 4 | `trianglesContainingVertex_partition` | REASONING | Wrong partition |
| 5 | `support_sunflower_tau_2` | REASONING | Includes M-elements |
| 6 | `external_share_common_vertex` | AI-VERIFIED | Externals use different M-triangles |
| 7 | `sunflower_cover_at_vertex_2edges` | AI-VERIFIED | Need 3+ edges (slot152 blocker) |
| 8 | `tau_pair_le_4` | TRIVIAL | Correct bound is 6 |
| 9 | `fixed_8_edge_M_subset` | REASONING | Any 8 omits 4 needed edges |
| 10 | `krivelevich_bound_forall_w` | ARISTOTLE | Must use sSup, not ∀w |

### 3.2 Pattern 10 (NEW)

**Statement** (FALSE):
```lean
∀ w, IsFractionalPacking G w → (τ G : ℝ) ≤ 2 * packingWeight G w
```

**Counterexample**: K₃ with w=0 gives τ=1 > 2×0=0

**Correct**: τ ≤ 2 × sSup{packingWeight(w) | IsFractionalPacking(w)}

---

## Part 4: Strategy Status

### 4.1 What's Blocked

| Approach | Why Blocked | Pattern(s) |
|----------|-------------|------------|
| Vertex-centric 2 edges | Need 3+ edges per vertex | 1, 5, 7 |
| Fixed 8-edge M-subset | Any 8 omits 4 needed | 9 |
| External common vertex | Externals use different M-triangles | 6 |
| Konig via bipartiteness | Link graph has odd cycles | 8 |
| Krivelevich ∀w | Must use sSup | 10 |

### 4.2 What's Open

| Approach | Status | Chance |
|----------|--------|--------|
| **LP relaxation (ν* = 4)** | SUBMITTED | 70% |
| Adaptive non-M-edge cover | Not started | 40% |
| Complete simpler cases | Partial | 60% |
| Accept τ ≤ 12 | Already proven | 100% |

---

## Part 5: PRD and Documentation

### 5.1 Documents Created This Session

| File | Purpose |
|------|---------|
| `docs/PRD_LP_RELAXATION_TAU8.md` | Comprehensive PRD with 5 strategies |
| `docs/DEBATE_LP_PRD_JAN1_2026.md` | 3-AI debate synthesis on PRD |
| `docs/DEBATE_SLOT152_JAN1_2026.md` | 3-AI debate rejecting slot152 |
| `docs/CHECKPOINT_JAN1_2026_LP_SUBMISSION.md` | This file |

### 5.2 Key PRD Strategies

| Strategy | File | Description |
|----------|------|-------------|
| A | slot153 | Direct ν* = 4 proof |
| B | slot154 | Axiom + Application |
| C | slot155 | Constructive weight (not submitted) |
| D | slot156 | Dual LP (not viable) |
| E | slot157 | Hybrid structural (not submitted) |

---

## Part 6: Metrics

| Metric | Previous | Current | Delta |
|--------|----------|---------|-------|
| Proven files | 11 | 11 | 0 |
| False lemma patterns | 10 | 10 | 0* |
| Active submissions | 0 | 3 | +3 |
| Best proven τ bound | 12 | 12 | 0 |
| AI debate rounds | 12+ | 15+ | +3 |

*Pattern 10 existed in database but not in checkpoint doc

---

## Part 7: Next Steps

### 7.1 Immediate (Wait for Aristotle)

1. Monitor slot153, slot153b, slot154 results (~6-24 hours)
2. If slot153 succeeds: ν* ≥ 4 proven
3. If slot153b succeeds: ν* ≤ 4 proven
4. If both succeed: ν* = 4 established
5. If slot154 succeeds: **τ ≤ 8 PROVEN** (with 1 axiom)

### 7.2 If Aristotle Fails

| Failure | Action |
|---------|--------|
| slot153 fails | Fix Mathlib issues, resubmit |
| slot153b fails | Simplify edge-counting, resubmit |
| slot154 fails | Fix cast issues, resubmit |
| All fail | Try Strategy C (constructive weight) |

### 7.3 If All LP Approaches Fail

1. Accept τ ≤ 12 as final result
2. Document as "best achievable via current methods"
3. Consider τ ≤ 12 = τ ≤ 3ν (matches Haxell's 2.87ν bound asymptotically)

---

## Appendix A: Database Queries

```sql
-- Active submissions
SELECT uuid, filename, status FROM submissions
WHERE status = 'submitted' ORDER BY created_at DESC LIMIT 5;

-- False lemmas
SELECT pattern_number, lemma_name, evidence_level FROM false_lemmas;

-- Case status
SELECT case_name, status, key_insight FROM nu4_cases;
```

## Appendix B: Aristotle Project IDs

```
slot153:  30006cc9-3f0c-4cd1-a49e-5bb9689c6c70
slot153b: 5f4ef776-e28a-4452-86ec-d29d5e9be9b3
slot154:  463f73ab-915d-4f1e-86dc-ab7aa9e53028
```

---

*Generated: January 1, 2026*
*Status: τ ≤ 12 PROVEN, τ ≤ 8 PENDING (3 Aristotle jobs)*
