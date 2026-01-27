# Tuza ν=4 Proof Assembly Plan

**Date**: 2026-01-21
**Status**: Ready for assembly from proven components

## Executive Summary

The multi-agent audit of slot473 identified 4 critical gaps. However, investigation of the database reveals that **all necessary components exist in proven form** - they just need to be properly assembled.

## Proven Components Available

### 1. Proper Graph Modeling (slot452)
```lean
def G : SimpleGraph V9 where
  Adj x y := (x = 0 ∧ y = 1) ∨ ...
  symm := by intro x y; simp only; tauto
  loopless := by intro x; simp only; omega
```
- 855 files with SimpleGraph
- DecidableRel G.Adj instances

### 2. Correct τ/ν Definitions (proven/tuza/nu1/)
```lean
def IsTriangleCovering (F : Finset (Sym2 V)) : Prop :=
  F ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F
```
- Proper constraint: `F ⊆ G.edgeFinset`
- No self-loops

### 3. Maximality (slot63, slot139)
```lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2
```
- PROVEN with ν+1 contradiction

### 4. 6-Packing Constraint (slot412)
```lean
theorem not_all_three_edge_types :
  ¬((S_e_edge G M a b c).Nonempty ∧
    (S_e_edge G M b c a).Nonempty ∧
    (S_e_edge G M a c b).Nonempty)
```
- At most 2 of 3 edge-types per element have externals
- PROVEN via 6-packing contradiction

### 5. External Triangle Key Lemma (slot381)
```lean
theorem external_has_other_home :
    ∀ T ∈ trianglesInG, ∀ e ∈ M,
      isExternalFor T e = true →
      ∃ f ∈ M, f ≠ e ∧ sharesEdgeWith T f = true
```
- Externals share edge with OTHER M-element
- Therefore externals ∈ S_f for some f ≠ e

### 6. S_e Bound (literature_lemmas)
```lean
tau_S_le_2 : τ(S_e) ≤ 2 for any packing element e
```
- 181 validated lemmas available

## The Proof Strategy

### Key Insight
Combining slot381 + slot412:
1. Every triangle T shares edge with some M-element (maximality)
2. If T ∈ S_e (shares edge with e), covered by S_e's 2 edges
3. "Externals" of e are just S_f triangles for f ≠ e
4. Each element needs ≤ 2 edges (6-packing constraint)
5. 4 elements × 2 edges = **8 edges**

### Assembly Steps

1. **Import foundation** from `proven/scaffolding_library.lean`
2. **Import graph model** from `slot452` pattern
3. **Import maximality** from `slot63_scaffolding.lean`
4. **Import 6-packing** from `slot412_6packing_proof_aristotle.lean`
5. **Import external lemma** from `slot381_external_test_hard_aristotle.lean`
6. **Construct 8-edge cover**:
   - For each e ∈ M, pick 2 edges covering S_e
   - Union of all 8 edges
7. **Prove coverage**:
   - Every triangle ∈ some S_e (by maximality + external_has_other_home)
   - S_e covered by its 2 edges
   - QED

## Remaining Work

### Transfer Principle (slot463 - 4 sorry)
Need to complete:
- `packing_embeds_fin12`: Injection V(M) → Fin 12
- `tuza_nu4_from_transfer`: Combine with Fin 12 result

### Exhaustiveness
Need formal proof that 11 graphs exhaust all simple graphs on 4 vertices.
- Mathematical fact is well-known
- Could enumerate via DecidableEq on adjacency matrices

## File Structure for New Assembly

```
slot474_tuza_nu4_assembly.lean
├── import Mathlib
├── import proven/scaffolding_library
├──
├── -- Section 1: Graph Setup (from slot452 pattern)
├── def G : SimpleGraph V ...
├──
├── -- Section 2: Definitions (from proven/tuza/nu1/)
├── def IsTriangleCovering ...
├── def triangleCoveringNumber ...
├──
├── -- Section 3: Maximality (from slot63)
├── lemma triangle_shares_edge_with_packing ...
├──
├── -- Section 4: 6-Packing (from slot412)
├── theorem not_all_three_edge_types ...
├──
├── -- Section 5: External Key Lemma (from slot381)
├── theorem external_has_other_home ...
├──
├── -- Section 6: Cover Construction
├── def cover_for_Se (e : Finset V) : Finset (Sym2 V) := ...
├── def full_cover : Finset (Sym2 V) := ⋃ e ∈ M, cover_for_Se e
├──
├── -- Section 7: Main Theorem
├── theorem tau_le_8_nu_4 :
├──     ν(G) = 4 → τ(G) ≤ 8
```

## Success Criteria

- [ ] 0 sorry
- [ ] 0 axiom
- [ ] Uses proper SimpleGraph
- [ ] Cover ⊆ G.edgeFinset
- [ ] Handles ALL triangles (not just packing)
- [ ] Passes multi-agent audit
