# Historical Approaches Audit - What We've Already Tried

**Date**: 2025-12-25
**Purpose**: Before pursuing "new" approaches, verify we haven't already tried them

---

## Summary: We've Tried Most Alternative Approaches - They Failed!

| Approach | Slot | Status | Why It Failed |
|----------|------|--------|---------------|
| **LP Rounding** | slot12 | All sorry | `integrality_gap_zero_nu4` unproven |
| **Fractional Hammer** | slot3 | All sorry | Just definitions, no proofs |
| **LLL Probabilistic** | slot37 | 2 sorry | "Gives asymptotic bounds only" |
| **Link Graph VC** | slot31 | All sorry | `bridges_inter_card_eq_one` NEGATED |
| **Vertex Partition** | slot45 | Still running | Unknown |

---

## Detailed Analysis

### 1. LP Rounding Approach (slot12_lp_rounding.lean)

**Proposed Strategy**:
```
1. Fractional cover τ* ≤ 2ν* (known via LP duality)
2. For ν=4: τ* ≤ 8
3. Show integrality gap is 0: τ = τ* when ν ≤ 4
```

**Key Lemmas Attempted**:
- `fractional_duality` → sorry
- `tau_ge_tau_star` → sorry
- `fractional_tuza` → sorry
- `integrality_gap_zero_nu4` → sorry (THE BLOCKER)

**Why It Failed**:
The integrality gap claim requires showing that the LP relaxation is tight for small ν. This is a deep result that would essentially solve the problem. Aristotle couldn't make progress.

**Lesson**: LP approach just pushes the difficulty elsewhere.

---

### 2. Fractional Hammer (slot3_fractional_hammer.lean)

**Proposed Strategy**:
Use `chapuy_improved_bound`: τ ≤ 2ν* - (1/√6)√ν*

**Key Lemmas Attempted**:
- `fractional_duality` → sorry
- `tau_le_2_nu_star` → sorry
- `chapuy_improved_bound` → sorry

**Why It Failed**:
Same issue - all fractional bounds require proving LP duality or related results that are equally hard.

**Lesson**: Fractional methods don't simplify the problem.

---

### 3. LLL Probabilistic (slot37_lll_probabilistic.lean)

**Proposed Strategy**:
```
1. Assign probability p to each edge
2. Bad events: triangle t not covered
3. Apply LLL: if e*p*(d+1) ≤ 1, cover exists
4. Show d ≤ 12 (dependency degree)
```

**Key Lemmas Attempted**:
- `dependency_bounded` → sorry
- `lll_cover_exists` → sorry
- `tuza_nu4_lll` → sorry

**Why It Failed**:
From failed_approaches database:
> "Probabilistic gives asymptotic bounds only; no finite construction"

LLL proves existence but doesn't give the explicit bound τ ≤ 8 for finite ν=4.

**Lesson**: Probabilistic methods are for asymptotics, not small cases.

---

### 4. Link Graph Vertex Cover (slot31_link_graph_vc.lean)

**Proposed Strategy**:
```
1. In star case, reduce to vertex cover on link graph L_v
2. Bridges form matching on outer vertices
3. Use 2-SAT to select 4 spokes covering all bridges
```

**Key Lemmas Attempted**:
- `packing_forms_matching_in_link` → sorry
- `bridges_form_matching` → sorry (depends on negated lemma!)
- `spoke_cover_exists` → sorry

**Why It Failed**:
`bridges_inter_card_eq_one` was NEGATED by Aristotle!
> Counterexample: V=Fin 5, e={0,1,2}, f={0,3,4}, M={e,f}.
> Bridges t1={0,1,3}, t2={0,1,4} share {0,1} (card=2).

Bridges DON'T form a matching - they can share vertices!

**Lesson**: Link graph approach had a false assumption at its core.

---

### 5. Vertex Partition (slot45_vertex_partition_complete.lean)

**Status**: Still running in Aristotle queue
**Approach**: Unknown - need to examine file

---

## Failed Approaches Database Summary (19 entries)

| Category | Count | Examples |
|----------|-------|----------|
| Wrong structure assumptions | 8 | `cycle_opposite_disjoint`, `bridges_inter_card_eq_one` |
| False coverage lemmas | 5 | `avoiding_covered_by_spokes`, `bridge_absorption` |
| Wrong bounds | 3 | `tau_pair_le_4`, `tau_containing_vertex_le_2` |
| Wrong direction | 3 | `Parker_induction`, `probabilistic`, `global_induction` |

---

## What HASN'T Been Tried

Based on our database, these approaches from the AI debate have NOT been attempted:

### 1. SAT/SMT Verification ❌ NOT TRIED
No submissions with SAT/SMT encoding to verify small counterexamples.
**Recommendation**: High priority - fast to implement, definitive answer.

### 2. Iterative LP Rounding (Codex's specific method) ❌ NOT TRIED
Different from slot12 - uses sparsity argument:
> "Residual LP has ≤ 6 edges → brute-force 64 cases"

**Recommendation**: Worth trying with explicit enumeration.

### 3. Sherali-Adams Lift-and-Project ❌ NOT TRIED
Order-2 lift forces y_e ∈ {0, 1/2, 1}, enables rounding.
**Recommendation**: Medium priority - requires careful formalization.

### 4. Minimal Counterexample + Discharging ❌ NOT TRIED
Assume minimal G with τ ≥ 9, derive δ(G) ≥ 4, 3-connected, contradiction.
**Recommendation**: High priority - classical technique.

### 5. Type Classification of Triangles ❌ NOT TRIED
Classify by intersection pattern with packing.
**Recommendation**: Low effort - just enumeration.

---

## Key Insights from History

### 1. False Lemmas Are the Killer
19 failed approaches, most from FALSE lemmas:
- `avoiding_covered_by_spokes` - MATHEMATICALLY IMPOSSIBLE
- `bridges_inter_card_eq_one` - COUNTEREXAMPLE FOUND
- `tau_pair_le_4` - WRONG BOUND (correct is ≤6)

### 2. Aristotle is Good at Finding Counterexamples
Many "negated by Aristotle" entries. Use this strength!

### 3. Asymptotic Methods Don't Work
LLL, probabilistic - give bounds for large n, not n=4.

### 4. LP/Fractional Push Difficulty Around
Proving integrality gap = 0 is as hard as direct proof.

---

## Recommended New Directions

1. **SAT Encoder** - Fast verification of small cases
2. **Discharging** - Classical technique not yet tried
3. **Continue S_e** - Already in queue (slot74b, 76)
4. **Type Classification** - Low effort enumeration

---

## Conclusion

**We ARE somewhat narrow, but many alternatives have already failed.**

The failed approaches show:
- Structure-based assumptions (bridges form matching) are often FALSE
- Fractional methods push difficulty elsewhere
- Probabilistic methods don't apply to small cases

**The S_e decomposition and All-Middle approaches are actually well-chosen** because:
- They use PROVEN structural lemmas (τ(S_e) ≤ 2)
- They avoid the FALSE lemmas that killed other approaches
- They're specific to ν=4 structure, not generic

**But we should still try**: SAT verification, discharging, type classification.
