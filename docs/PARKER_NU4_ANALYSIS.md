# Why Parker's Proof Works for ν ≤ 3 But Not ν = 4

## Parker's Inductive Structure

### Key Definitions
- **M**: Maximum edge-disjoint triangle packing (|M| = ν)
- **T_e**: Triangles sharing an edge with e ∈ M
- **S_e**: Triangles sharing an edge with e but NOT with any other f ∈ M

### Key Lemmas

**Lemma 2.2**: ν(S_e) = 1
- Any two triangles in S_e share an edge
- Proof: If h₁, h₂ ∈ S_e don't share edge, then (M \ {e}) ∪ {h₁, h₂} is larger matching

**Lemma 2.3**: ν(G \ T_e) = ν - 1
- Removing T_e reduces packing number by exactly 1
- Proof: M \ {e} is maximum in G \ T_e

### Inductive Bound
```
τ(G) ≤ τ(T_e) + τ(G \ T_e)
     ≤ τ(T_e) + 2(ν - 1)   [by induction, assuming τ ≤ 2ν for smaller ν]
```

For Tuza (τ ≤ 2ν), need: **τ(T_e) ≤ 2**

---

## Why τ(T_e) ≤ 2 for Small ν

### Structure of T_e
T_e contains all triangles sharing an edge with e = {a, b, c}.

The triangles in T_e share one of:
- Edge {a,b}: Forms potential K₄ with vertex d if all triangles {a,b,d} exist
- Edge {b,c}: Similar
- Edge {a,c}: Similar

### Case ν = 1
- Only e exists, T_e = {e}
- τ(T_e) = 1 ≤ 2 ✓

### Case ν = 2
- M = {e, f} for some disjoint e, f
- T_e contains triangles intersecting e
- By Lemma 2.2, S_e has ν = 1 (all share an edge)
- Can show T_e has structure allowing 2-edge cover
- τ(T_e) ≤ 2 ✓

### Case ν = 3
- M = {e, f, g} for disjoint e, f, g
- More complex interaction patterns
- Paper uses case analysis on how T_e, T_f, T_g overlap
- Still manages to show τ(T_e) ≤ 2 for at least one e ∈ M
- τ(T_e) ≤ 2 ✓ (for suitable choice of e)

---

## What Breaks at ν = 4

### The Problem
At ν = 4, M = {e₁, e₂, e₃, e₄} with 4 edge-disjoint triangles.

The T_eᵢ sets can have more complex overlap patterns:
- More ways for triangles to share vertices across different T_eᵢ
- Case analysis becomes intractable
- Cannot guarantee τ(T_e) ≤ 2 for any e ∈ M

### Potential Counterexample Structure
Consider a graph where:
1. 4 edge-disjoint triangles form the matching
2. Each T_eᵢ has triangles that require 3+ edges to cover
3. The triangles in T_eᵢ are "spread out" (don't form K₄-like structure)

Example sketch:
```
    a---b
   /|\ /|\
  c-+-d-+-e
   \|/ \|/
    f---g
```
With careful edge selection, can create T_e needing 3 edges.

### Why Induction Fails
If τ(T_e) = 3 for all e ∈ M when ν = 4:
```
τ(G) ≤ τ(T_e) + τ(G \ T_e)
     ≤ 3 + 2(3)
     = 9
```
But Tuza requires τ ≤ 2(4) = 8.

The extra edge in τ(T_e) accumulates, breaking the bound.

---

## Paths Forward for ν = 4

### Option 1: Different e Selection
- Maybe τ(T_e) ≤ 2 for SOME e ∈ M, even if not all
- Paper might do this for ν ≤ 3
- Harder to guarantee for ν = 4

### Option 2: Joint Covering
- Cover multiple T_eᵢ together, sharing edges
- Exploit overlap structure
- More complex analysis

### Option 3: Different Proof Method
- Our K₄-extension approach
- Hybrid with Parker's method
- Completely novel technique

### Option 4: Restricted Graph Classes
- Planar graphs (proven by Tuza 1985)
- Bounded treewidth (Botler 2021)
- K₅-minor-free, etc.

---

## Formalization Strategy

1. **Parker ν ≤ 3** (Current focus)
   - Formalize Lemmas 2.2, 2.3
   - Let Aristotle find case analysis for τ(T_e) ≤ 2
   - If succeeds, validates Parker's approach in Lean

2. **Our K₄ method for ν = 2**
   - Already 90% complete (v12 running)
   - Different proof structure, might extend differently

3. **Hybrid for ν = 4**
   - Combine insights from both approaches
   - Use Parker's matching reduction
   - Use our K₄ analysis for T_e structure
