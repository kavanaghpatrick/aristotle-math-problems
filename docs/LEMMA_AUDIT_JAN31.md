# Lemma Audit Results - January 31, 2026

## Executive Summary

After comprehensive audit by 5 parallel agents:
- **3 key lemmas VALIDATED as truly proven**
- **1 key lemma FALSIFIED** (was incorrectly marked proven)
- **PATH_4 is concrete-only** (not general theorem)

---

## VALIDATED TRUE (Safe to Use)

### 1. `tau_S_le_2` ✅
**Status**: PROVEN (0 sorry, 0 axiom)
**File**: `proven/tuza/aristotle_parker_full_e7f11dfc.lean`
**Statement**: τ(S_e) ≤ 2 for exclusive externals of packing element e
**Proof**: Case analysis - S_e forms star (τ≤1) or K4 structure (τ≤2)

### 2. `tau_X_le_2` ✅
**Status**: PROVEN (0 sorry, 0 axiom)
**File**: `proven/tuza/lemmas/slot28/204aea51...lean`
**Statement**: τ(X_ef) ≤ 2 for bridges between adjacent elements
**Proof**: Bridges forced to contain shared vertex v; 2 spokes from v suffice

### 3. `tau_pair_le_6` ✅
**Status**: PROVEN (0 sorry, 0 axiom)
**File**: `submissions/nu4_final/slot52_tau_pair_hyperfocused_aristotle.lean`
**Statement**: τ(T_pair) ≤ 6 using 4 spokes + 2 base edges
**Proof**: V-decomposition: containing(v) ≤ 4, avoiding(v) ≤ 2

### 4. `tau_union_le_sum` ✅
**Status**: PROVEN
**Statement**: τ(A ∪ B) ≤ τ(A) + τ(B) (subadditivity)

---

## FALSIFIED (Do NOT Use)

### `externals_share_edge` / `two_externals_share_edge` ❌

**Previous Status**: Marked "proven" in database
**Actual Status**: FALSE (Aristotle-verified counterexample)

**Counterexample**:
```
Graph: Fin 10
Packing M = {A={0,1,2}, B={0,3,4}, C={3,7,8}, D={7,1,9}}

X-externals of A:
  T₁ = {0, 1, 7}  shares edge {0,1} with A
  T₂ = {1, 2, 8}  shares edge {1,2} with A

T₁ ∩ T₂ = {1}  ← Only 1 vertex, NOT an edge!
```

**Why the "proof" was wrong**:
The proof assumed that if T₁, T₂ don't share an edge, we get a 5-packing.
But T₁ ∩ T₂ = {1} has cardinality 1, so {T₁, T₂, B, C, D} IS a valid 5-packing.
This doesn't contradict ν=4 when the construction is VALID.

**Impact**: Any proof relying on "externals share edge" is blocked.

---

## PATH_4 Status: Concrete Only

### What IS Proven
- 107 theorems across 3 files (slot451, slot452, slot453)
- All compile with 0 sorry, 0 axiom
- Three-case split is complete for Fin 9 and Fin 10

### What is NOT Proven
- General theorem: ∀ G with ν(G)=4 and path_4 structure, τ(G)≤8
- Transfer lemma: any path_4 configuration embeds into concrete instances

### Case Analysis
| Case | Description | Result | File |
|------|-------------|--------|------|
| 1 | No bridges | τ = 4 | slot453 |
| 2a | Bridge, 1 external | τ ≤ 8 | slot452 |
| 2b | Bridge, 2 externals | ν ≥ 5 (impossible) | slot451 |

---

## Related False Lemmas (From Database)

| Lemma | Evidence | Issue |
|-------|----------|-------|
| `external_share_common_vertex` | AI | Externals don't share common apex |
| `bridge_externals_share_apex` | AI | Bridge externals independent |
| `fan_apex_outside_A` | AI | "Book" case has apex IN A |
| `sym2_cover_cardinality` | Aristotle | Finset.sym2 includes self-loops |
| `triangle_sym2_card_3` | Aristotle | t.sym2 has 6 elements, not 3 |
| `bridge_absorption` | Aristotle | S_e cover doesn't auto-cover bridges |

---

## Recommendations

1. **Use tau_S_le_2, tau_X_le_2, tau_pair_le_6** - These are solid
2. **Do NOT use externals_share_edge** - It's false
3. **PATH_4 needs Phase 2 work** - Lift to general SimpleGraph V
4. **Avoid Finset.sym2 for edges** - Use explicit enumeration

---

## Files Updated
- `submissions/tracking.db`: Marked externals_share_edge variants as false
- This document created for future reference
