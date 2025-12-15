# Tuza's Conjecture: Complete Strategy Analysis

## Executive Summary

**Tuza's Conjecture (1981)**: For any graph G, τ(G) ≤ 2ν(G)
- ν(G) = maximum edge-disjoint triangle packing
- τ(G) = minimum edges to cover all triangles

**Status**: Open for 44 years. Best general bound is τ ≤ 2.87ν (Haxell, 1999).

---

## What We've Proven (via Aristotle)

### Proven Lemmas

| Lemma | File | Description |
|-------|------|-------------|
| `tuza_base_case` | tuza_SUCCESS_nu1_case.lean | ν=0 ⟹ τ=0 |
| `tuza_case_nu_1` | tuza_SUCCESS_nu1_case.lean | ν=1 ⟹ τ≤2 |
| `triangleCoveringNumber_le_card_add_deleteEdges` | tuza_SUCCESS_nu1_case.lean | Deletion lemma |
| `packing_mono_deleteEdges` | tuza_FULL_v2_OUTPUT.lean | Monotonicity |

### The ν=1 Proof (400+ lines)

**Key insight**: When ν=1, the graph contains K₄ (or less).

**Logic**:
1. ν=1 means exactly one triangle can be packed
2. This forces K₄ structure (4 vertices forming complete graph)
3. K₄ has exactly 4 triangles sharing edges
4. Any outside triangle would create ν≥2, contradiction
5. Two edges suffice to cover all K₄ triangles (τ≤2)

---

## Why Direct Induction Fails

**The Attempted Approach** (tuza_full_induction_FAILED.lean):

```
For ν > 0:
1. Find triangle T in max packing
2. Delete T's 3 edges (S = triangleEdges(T))
3. Claim: ν(G-S) = ν(G) - 1
4. By induction: τ(G-S) ≤ 2(ν-1)
5. By deletion lemma: τ(G) ≤ 3 + τ(G-S) ≤ 3 + 2(ν-1) = 2ν + 1
```

**THE FATAL FLAW**: Step 3 is FALSE.

Removing a triangle's edges might create NEW triangles that become edge-disjoint:
- Before deletion: triangles A, B share edge with T
- After deletion: A and B might now be edge-disjoint!
- So ν(G-S) could EQUAL ν(G), not decrease

**The "2-Edge Reduction Lemma"** we need (equivalent to conjecture):
> For any G with ν(G) > 0, there exist 2 edges S such that ν(G-S) < ν(G)

Our ν=1 proof establishes this for ν=1. For ν>1, it's the full conjecture.

---

## Why Standard Approaches Don't Apply

### 1. Discharging Method (Puleo 2015)
**Works for**: max average degree < 7
**Fails for dense graphs**: Too many configurations to analyze

### 2. Fractional Relaxation (Krivelevich 1995)
**Proves**: τ ≤ 2ν* (fractional packing number)
**Gap**: Need integer ν, not fractional ν*
**Integrality gap**: No known rounding preserves factor 2

### 3. Probabilistic Methods
**Works for**: Random graphs, very dense graphs (asymptotic)
**Fails for**: Deterministic middle-density graphs

### 4. Greedy Approaches
**Best achievable**: τ ≤ 3ν (trivial bound)
**No greedy gets**: τ ≤ 2ν

---

## Graph Classes Where Tuza Is Proven

| Class | Method | Reference |
|-------|--------|-----------|
| Planar | Structural | Tuza (1985) |
| K₃,₃-free | Fractional | Krivelevich (1995) |
| Tripartite | Combinatorial | Haxell (1993) |
| mad < 7 | Discharging | Puleo (2015) |
| Threshold | Structural | Bonamy (2021) |
| Random G(n,p) | Probabilistic | Kahn-Park (2022) |
| K₈-free chordal | Structural | Botler et al. |

**Still Open**: General chordal, split graphs, interval graphs

---

## Strategic Options for Aristotle

### Option A: ν=2 Case (Recommended)

**Approach**: Extend our ν=1 K₄ argument to ν=2.

**Required**:
1. Characterize minimal graphs with ν=2
2. Show structure forces τ≤4
3. Key cases: 2 disjoint K₄, K₅, other configurations

**Why promising**:
- Builds on proven techniques
- Finite case analysis
- Could reveal pattern for general induction

### Option B: Restricted Graph Classes

**Target**: Prove for a class NOT yet covered.

**Candidates**:
1. **Interval graphs** - open, has structure
2. **Split graphs** - open, relatively simple
3. **Chordal with ω≥9** - K₈-free proven, extend?

**Why promising**: Special structure might yield to Aristotle's search

### Option C: Alternative Induction

**Instead of induction on ν, try**:
1. Induction on number of triangles
2. Induction on number of vertices
3. Induction on edges with specific ordering

**Key need**: Find quantity that decreases predictably when removing 2 edges

### Option D: LP-Based Approach

**Idea**: Formalize Krivelevich's fractional proof, then:
1. Prove integrality gap ≤ 2ν* - ν
2. Show τ ≤ 2ν* ≤ 2(ν + gap)
3. Bound the gap

**Why difficult**: Rounding LP solutions is notoriously hard to formalize

---

## Recommended Next Submission

### ν=2 Formalization

```lean
/-- For graphs with exactly 2 edge-disjoint triangles, τ ≤ 4 -/
theorem tuza_case_nu_2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    triangleCoveringNumber G ≤ 4 := by
  sorry
```

**Key subcases to analyze**:
1. Two disjoint K₄ subgraphs
2. K₅ (has ν=2, τ=4)
3. K₄ + separate triangle
4. Overlapping structures with shared vertices

---

## What Literature Tells Us NOT To Try

1. **Pure greedy** - Can't achieve factor 2
2. **Direct induction on ν** - The 2-edge reduction lemma IS the conjecture
3. **Hoping for counterexample** - 44 years, none found
4. **General LP rounding** - Integrality gap is the core difficulty
5. **Discharging for dense graphs** - Configuration explosion

---

## Key Papers to Study

1. **Puleo (arXiv:1308.2211)** - Discharging method, reducible configurations
2. **Krivelevich (1995)** - Fractional version proof
3. **Baron-Kahn (arXiv:1408.4870)** - Tightness construction
4. **Bonamy (arXiv:2105.09871)** - Threshold graphs technique

---

## Success Criteria

For Aristotle to "solve" Tuza would require one of:
1. ✓ Special case ν=1 (DONE)
2. ○ Special case ν=2 (next target)
3. ○ New graph class (interval, split)
4. ✗ General conjecture (unlikely without new math)

Even proving ν=2 would be notable progress, demonstrating:
- Aristotle can extend hand-crafted proofs
- The structural argument generalizes (partially)
- ATP contribution to open problem

---

## Files Reference

| File | Status | Content |
|------|--------|---------|
| tuza_SUCCESS_nu1_case.lean | ✓ Success | ν=1 case, base case, deletion lemma |
| tuza_full_induction_FAILED.lean | ✗ Failed | Attempted full induction |
| tuza_FULL_v2_OUTPUT.lean | Partial | Some lemmas proven, main failed |
| TUZA_BIBLIOGRAPHY.md | Reference | Complete literature survey |
