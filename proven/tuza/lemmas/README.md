# Parker Lemmas for Tuza's Conjecture

## Overview

These lemmas follow the approach in Parker's paper (arXiv:2406.06501, May 2025) for proving Tuza's conjecture for small packing numbers.

## Key Definitions

```lean
-- Triangles sharing an edge with packing element e
def T_e (G : SimpleGraph V) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

-- S_e: Triangles in T_e that don't share edge with OTHER packing elements
def S_e (G : SimpleGraph V) (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ m ∈ M, m ≠ e → (t ∩ m).card ≤ 1)
```

## Proven Lemmas

### Lemma 2.2: S_e Pairwise Share Edges

```lean
lemma lemma_2_2 (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S G e M → t2 ∈ S G e M → shareEdge t1 t2
```

**Meaning**: Any two triangles in S_e share an edge with each other.

**Proof idea**: If t1, t2 ∈ S_e don't share an edge, replace e with {t1, t2} to get larger packing.

### Lemma 2.3: Packing Number Decreases

```lean
lemma lemma_2_3 (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    trianglePackingNumber (G.deleteTriangles (T_e G e)) = M.card - 1
```

**Meaning**: After removing T_e, the remaining graph has packing number ν - 1.

### Inductive Bound

```lean
lemma inductive_bound (G : SimpleGraph V) (e : Finset V) :
    triangleCoveringNumber G ≤ triangleCoveringNumber_of (T_e G e) +
                               triangleCoveringNumber (G.deleteTriangles (T_e G e))
```

**Meaning**: τ(G) ≤ τ(T_e) + τ(G \ T_e)

### τ(S_e) ≤ 2

```lean
lemma tau_S_le_2 (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ S G e M, ∃ edge ∈ E, edge ∈ t.sym2
```

**Meaning**: Triangles in S_e can always be covered by ≤ 2 edges (since they pairwise share edges).

## The Gap for ν ≥ 4

Parker's approach proves τ ≤ 2ν for ν ≤ 3 by showing τ(T_e) ≤ 2 for some e.

For ν ≥ 4, this breaks down:
- S_e ⊆ T_e (strictly)
- τ(S_e) ≤ 2 (proven)
- But T_e \ S_e may require additional edges
- Induction gives τ ≤ 3 + 2(ν-1) = 2ν + 1, not 2ν

## Verification

```bash
lake env lean proven/tuza/lemmas/parker_lemmas.lean
```

## Aristotle Details

- **UUID**: 181fa406-e8a7-4f19-925a-f3ae337bc3db
- **Date**: December 19, 2025
- **Lean version**: leanprover/lean4:v4.24.0
- **Mathlib**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
