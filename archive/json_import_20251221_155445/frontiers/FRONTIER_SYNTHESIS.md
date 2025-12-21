# Tuza Frontier Problems: Synthesis Document

**Last Updated**: December 21, 2025
**Purpose**: Map our 32 proven lemmas to 4 frontier problems for optimal Aristotle scaffolding

---

## Quick Reference: Our Lemma Portfolio

| Lemma | Split Graphs | Counterexample | Hypergraph | Bound Improvement |
|-------|:------------:|:--------------:|:----------:|:-----------------:|
| `intersecting_family_structure` | ✅ Direct | ✅ Constraint | ✅ Generalizes | ✅ Structure |
| `tau_star` | ✅ Direct | ⚪ N/A | ✅ Generalizes | ✅ Baseline |
| `structural_cover` | ✅ Direct | ⚪ N/A | ✅ Generalizes | ✅ Structure |
| `inductive_bound` | ✅ Framework | ✅ Constraint | ✅ Generalizes | ✅ Framework |
| `lemma_2_2` (S_e pairwise) | ✅ Framework | ✅ Constraint | ✅ Generalizes | ✅ Framework |
| `lemma_2_3` (ν reduction) | ⚪ Indirect | ✅ Constraint | ✅ Generalizes | ✅ Framework |
| `tau_S_le_2` | ✅ Direct | ✅ Constraint | ✅ Template | ✅ Baseline |
| `tau_X_le_2` | ⚪ Indirect | ⚪ N/A | ⚪ Specializes | ✅ Structure |
| `covering_number_le_two_of_subset_four` | ✅ High | ⚪ N/A | ⚪ Specializes | ⚪ N/A |
| `K4_counterexample` | ⚪ N/A | ✅ Ruled out | ⚪ N/A | ⚪ N/A |
| `fan_counterexample` | ⚪ N/A | ✅ Ruled out | ⚪ N/A | ⚪ N/A |

Legend: ✅ = Directly useful, ⚪ = Indirect/N/A

---

## Frontier 1: Split Graphs

**Status**: Genuinely OPEN (only threshold subclass proven)
**Risk**: MEDIUM | **Reward**: HIGH

### What We Know
- Threshold graphs proven (Botler et al. 2021)
- All triangles use ≥2 clique vertices
- Simple structure but non-trivial general case

### Our Applicable Lemmas (Ranked)
1. **`structural_cover`** - Pairwise sharing common in split graphs
2. **`tau_star`** - Star structures arise from clique edges
3. **`intersecting_family_structure`** - Dichotomy simplifies cases
4. **`covering_number_le_two_of_subset_four`** - Small clique → τ ≤ 2

### Key Formalization Needed
```lean
def isSplitGraph (G : SimpleGraph V) (K I : Finset V) : Prop :=
  (∀ u v ∈ K, u ≠ v → G.Adj u v) ∧   -- K is clique
  (∀ u v ∈ I, ¬G.Adj u v) ∧           -- I is independent
  K ∪ I = Finset.univ ∧ Disjoint K I  -- partition

lemma split_triangle_in_clique (G : SimpleGraph V) (K I : Finset V)
    (h_split : isSplitGraph G K I) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (t ∩ K).card ≥ 2 := by sorry
```

### Attack Strategy
1. Induction on clique size |K|
2. Use `tau_star` when triangles share clique edge
3. Use `covering_number_le_two_of_subset_four` for small cliques
4. Combine with `inductive_bound` for residual

---

## Frontier 2: Constrained Counterexample Hunt

**Status**: Genuinely OPEN
**Risk**: LOW (negative results valuable) | **Reward**: EXTREMELY HIGH if found

### Necessary Conditions (From Literature + Our Work)
| Condition | Bound | Source |
|-----------|-------|--------|
| Packing number | ν ≥ 4 | Parker + Our ν≤3 proof |
| Chromatic number | χ ≥ 5 | Haxell 1993 |
| Treewidth | tw ≥ 7 | Botler-Sambinelli 2024 |
| Max avg degree | mad ≥ 7 | Puleo 2015 |

### Our Constraints (From Proven Lemmas)
1. **`tau_S_le_2`** - Any counterexample must have bridges overwhelming S_e
2. **`intersecting_family_structure`** - Can't have all triangles pairwise sharing
3. **`inductive_bound`** - Must be bad at EVERY level of decomposition

### Search Strategy
```lean
def isPotentialCounterexample (G : SimpleGraph V) : Prop :=
  coveringNumber G > 2 * packingNumber G ∧
  packingNumber G ≥ 4 ∧
  chromaticNumber G ≥ 5 ∧
  treewidth G ≥ 7

-- For finite graphs, this is decidable
instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Decidable (isPotentialCounterexample G) := inferInstance
```

### Candidate Graph Classes
1. **Cayley graphs of non-abelian groups** - High symmetry might evade our lemmas
2. **Graph products** - Can amplify chromatic number
3. **Algebraic constructions** - Paley, polarity graphs

---

## Frontier 3: Aharoni-Zerbib Hypergraph Generalization

**Status**: Genuinely OPEN for r ≥ 3
**Risk**: MEDIUM | **Reward**: HIGH (new territory)

### The Conjecture
For r-uniform hypergraph H: τ(H) ≤ ⌈(r+1)/2⌉ · ν(H)

| r | Bound | Status |
|---|-------|--------|
| 2 | τ ≤ 1.5ν | Known |
| 3 | τ ≤ 2ν | **Tuza (OPEN)** |
| 4 | τ ≤ 2.5ν | OPEN - First new case |
| 5 | τ ≤ 3ν | OPEN |

### Our Lemmas → Hypergraph Generalizations

| Our Lemma (r=3) | Generalized (r-uniform) |
|-----------------|-------------------------|
| `intersecting_family_structure` | Pairwise sharing r-edges → common (r-1)-face OR ≤r+1 vertices |
| `tau_star` | Common (r-1)-face → τ ≤ 1 |
| `structural_cover` | Pairwise sharing → τ ≤ ⌈(r+1)/2⌉ |
| `lemma_2_2` | S_e r-edges pairwise share (r-1)-faces |

### Target: r=4 Case
```lean
-- Define r-uniform hypergraph
structure Hypergraph (V : Type*) (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

theorem aharoni_zerbib_r4 (H : Hypergraph V 4) :
    coveringNumber H ≤ 3 * packingNumber H := by sorry
```

### Why Tractable
- Our 30 lemmas are the r=3 case, already formalized
- Generalizing to r=4 is natural next step
- Less competition than main Tuza

---

## Frontier 4: Improve 2.87 → 2.5 Bound

**Status**: Genuinely OPEN (26 years without progress)
**Risk**: HIGH | **Reward**: HIGH (but realistic expectation: LOW success)

### Current Situation
- Haxell 1999: τ ≤ 2.87ν via probabilistic + local ratio
- No improvement since then

### Our Relevant Lemmas
1. **`tau_S_le_2`** - Baseline: can cover S_e cheaply
2. **`inductive_bound`** - Framework for recursive analysis
3. **`structural_cover`** - Good structure → better than 2.87

### Three Attack Approaches

**Approach A: Integrality Gap**
- Target: Bound τ/τ* directly
- Idea: Show τ ≤ 2τ* would give τ ≤ 2ν
- Our contribution: `tau_star` shows good integrality for structured cases

**Approach B: Parker Extension**
- Target: Extend ν≤3 induction globally
- Idea: Amortize over multiple T_e simultaneously
- Our contribution: Full Parker machinery + packing pair lemmas

**Approach C: LP Rounding**
- Target: Improve Guruswami-Sandeep additive bound
- Idea: Convert additive to multiplicative for bounded ν
- Literature: t/2 + O(√t log t) already achieved

### Realistic Assessment
This is HIGH RISK. 26 years of no progress suggests either:
1. 2.87 is tight for current techniques
2. Fundamentally new approach needed
3. Our lemmas provide unprecedented scaffolding (hope!)

---

## Portfolio Recommendation

Based on risk/reward analysis:

| Frontier | Priority | Slots | Rationale |
|----------|----------|-------|-----------|
| **Split Graphs** | **HIGH** | 3 | Best risk/reward, our lemmas apply directly |
| **Counterexample Hunt** | MEDIUM | 2 | Low risk, even negatives valuable |
| **Hypergraph r=4** | MEDIUM | 2 | Natural extension, less competition |
| **Bound Improvement** | LOW | 0-1 | High risk, but moonshot potential |

### Submission Strategy

**Week 1: Split Graphs Focus**
1. Boris minimal (just definitions + theorem)
2. Scaffolded with `structural_cover`, `tau_star`
3. Informal proof sketch for Parker-style induction

**Week 2: Diversified**
1. Counterexample hunt with constrained search
2. Hypergraph r=4 with generalized lemmas
3. (Optional) Bound improvement moonshot

---

## Files in This Database

```
db/frontiers/
├── index.json                      # Overview of all frontiers
├── FRONTIER_SYNTHESIS.md           # This document
├── split_graphs/
│   ├── index.json                  # Problem description
│   └── lemmas.json                 # Applicable lemmas
├── counterexample_hunt/
│   ├── index.json                  # Constraints and search space
│   └── lemmas.json                 # What counterexample must avoid
├── hypergraph_aharoni_zerbib/
│   ├── index.json                  # r-uniform generalization
│   └── lemmas.json                 # Lemma generalizations
└── bound_improvement/
    ├── index.json                  # 2.87 → 2.5 challenge
    └── lemmas.json                 # Relevant techniques
```

---

## Next Steps

1. [ ] Create `.lean` submission files for each frontier
2. [ ] Build context folders with proven lemmas for each
3. [ ] Submit Boris minimal versions first
4. [ ] Track results and iterate based on Aristotle feedback
