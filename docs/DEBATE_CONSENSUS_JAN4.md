# MULTI-AGENT DEBATE CONSENSUS: τ ≤ 8 for cycle_4
## Date: January 4, 2026
## Participants: Grok-4, Gemini, Codex (via Claude moderation)
## Status: CONSENSUS REACHED

---

## EXECUTIVE SUMMARY

After 3 debate rounds with research enrichment, all agents converge on:

1. **The Key Question**: `bridge_externals_share_apex` - Do externals of A and externals of B at shared vertex v_AB share a common external apex?

2. **Likelihood**: τ ≤ 8 has ~40% success chance (range 35-45%)

3. **Direction**: Investigate the key question first, with τ ≤ 12 as proven fallback

---

## THE CRITICAL INSIGHT

### Triangle Classification (Refined)

| Category | Definition | Count | Fan Structure? |
|----------|------------|-------|----------------|
| M-elements | {A, B, C, D} | 4 | N/A |
| True Externals | Share edge with EXACTLY ONE M-element | Variable | YES (slot224f) |
| Bridges | Share edges with 2+ M-elements | Variable | UNKNOWN |

**Key Distinction**: Externals and Bridges are DISJOINT by definition. Pattern 17's {v_ab, a_priv, b_priv} is a BRIDGE, not an external.

### The Make-or-Break Lemma

```lean
lemma bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv : v ∈ A ∩ B)  -- shared vertex
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂
```

**If TRUE**: 2 edges per shared vertex suffices → τ ≤ 8
**If FALSE**: Vertex-local approach blocked → Accept τ ≤ 12 or find alternative

---

## WHAT WE KNOW (Proven)

| Theorem | File | Implication |
|---------|------|-------------|
| τ ≤ 12 | slot139_tau_le_12_PROVEN.lean | Baseline bound |
| two_externals_share_edge | slot182 | Externals of SAME M share edge |
| different_edges_share_external_vertex | slot224f | Externals using different A-edges share apex |
| triangle_contains_shared | literature_lemmas | Every triangle passes through v_ab, v_bc, v_cd, or v_da |

## WHAT BLOCKS τ ≤ 8 (False Lemmas)

| Pattern | Lemma | Impact |
|---------|-------|--------|
| 6 | external_share_common_vertex | Externals from DIFFERENT M-elements don't share apex |
| 17 | externals_partition_by_M_element | Bridges share edges with 2+ M-elements |
| 20 | four_vertex_cover | Link Graph + König fails |

---

## CONSENSUS DIRECTION

### Step 1: Lock in τ ≤ 12 (Done)
slot139 is PROVEN with 0 sorry. This is our baseline.

### Step 2: Investigate `bridge_externals_share_apex`

**Approach A - Try to prove it**:
- Use ν = 4 constraint: if x_A ≠ x_B for externals at v_AB, can we form a 5-packing?
- This would extend slot182's technique to cross-M-element externals

**Approach B - Find counterexample**:
- Construct explicit graph with ν = 4 where externals have distinct apexes
- This would definitively block the 2-edge-per-vertex approach

### Step 3: Based on Result

**If bridge_externals_share_apex is TRUE**:
- Construct 8-edge cover: {v_ab, x_AB}, {v_bc, x_BC}, {v_cd, x_CD}, {v_da, x_DA} + 4 M-edges
- Each x_XY is the common apex for all externals at v_XY

**If bridge_externals_share_apex is FALSE**:
- Option A: Investigate τ ≤ 10 (60% confidence)
- Option B: Accept τ ≤ 12 and document as open problem

---

## LIKELIHOOD ESTIMATES (Final)

| Target | Confidence | Reasoning |
|--------|------------|-----------|
| τ ≤ 8 | 40% | Depends on bridge_externals_share_apex |
| τ ≤ 10 | 60% | More slack, less constraint |
| τ ≤ 12 | 95% | Already PROVEN |

---

## WHAT ALL AGENTS AGREE ON

1. Pattern 6 counterexample uses adjacent M-elements (A and B share vertex)
2. The ν = 4 constraint is our strongest tool (5-packing contradiction)
3. Externals vs Bridges must be distinguished (different by definition)
4. `triangle_contains_shared` is proven and useful
5. τ ≤ 12 is locked in as baseline
6. The key question is bridge_externals_share_apex

---

## CONCRETE NEXT ACTIONS

1. **Immediate**: Attempt to prove `bridge_externals_share_apex` using 5-packing contradiction
   - If T₁ (external of A at v_AB) and T₂ (external of B at v_AB) have different apexes x₁ ≠ x₂
   - Can we construct M' = {T₁, T₂, C, D} that is a 4-packing?
   - If so, this doesn't immediately contradict ν = 4, so the approach might not work

2. **Parallel**: Search for counterexample graph
   - Construct G with cycle_4 packing M where externals at v_AB have distinct apexes
   - Verify ν(G) = 4 (no 5-packing exists)
   - If such G exists, τ ≤ 8 via this approach is blocked

3. **Fallback**: If both fail, explore τ ≤ 10 or document gap as open problem

---

## SIGNATURES

- **Grok-4**: Agrees (45% on τ ≤ 8)
- **Gemini**: Agrees (40% on τ ≤ 8)
- **Codex**: Agrees with modification (35% on τ ≤ 8)

*Consensus achieved after 3 debate rounds on January 4, 2026*
