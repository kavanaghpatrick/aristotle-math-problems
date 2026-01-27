# Multi-Agent Debate: Closing the General Theorem Gap

## Date: January 19, 2026

## Mission
Find a formulation of "τ ≤ 8 for all graphs with ν = 4" that Aristotle can prove.

## Current Status

### What We Have (215+ theorems, 0 sorry)
1. **slot454** (37 theorems): τ ≤ 8 for concrete instances of all 6 patterns on Fin 12
2. **slot455** (26 theorems): InteractionGraph foundation, `external_shares_at_most_two`
3. **slot459** (58 theorems): Pattern exhaustive classification with covers
4. **slot460** (41 theorems): Bridge vs Private classification, parent counting
5. **slot461** (53 theorems): Degree bounds, 4-edge independent set construction

### What's Missing (1 sorry)
The abstract general theorem:
```lean
theorem tuza_nu4_general_statement :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∃ M : Finset (Finset V), M ⊆ G.cliqueFinset 3 ∧ M.card = 4 ∧
      ∀ T₁ ∈ M, ∀ T₂ ∈ M, T₁ ≠ T₂ → T₁.sym2 ∩ T₂.sym2 = ∅) →
    (¬∃ M' : Finset (Finset V), M' ⊆ G.cliqueFinset 3 ∧ M'.card = 5 ∧
      ∀ T₁ ∈ M', ∀ T₂ ∈ M', T₁ ≠ T₂ → T₁.sym2 ∩ T₂.sym2 = ∅) →
    ∃ C : Finset (Sym2 V), C ⊆ G.edgeFinset ∧ C.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ C, e ∈ T.sym2 := by
  sorry
```

### Why Aristotle Failed
- Abstract quantification over arbitrary type V
- Tier 3-4 problem (abstract reasoning beyond native_decide)
- Stuck at 35-36% for 24+ hours before timing out

## The Mathematical Argument (Sound but Not Formalized)

1. **Pattern Exhaustiveness**: Any edge-disjoint 4-packing M = {A,B,C,D} of triangles has an "intersection graph" I(M) where vertices are M-elements and edges connect pairs sharing a vertex.

2. **Finite Cases**: I(M) is a simple graph on 4 vertices where each pair shares ≤1 vertex (edge-disjointness). The possible structures are:
   - 0 edges: scattered
   - 3 edges (path): path_4
   - 3 edges (star): three_share_v
   - 2 edges (matching): two_two_vw
   - 4 edges (cycle): cycle_4
   - 6 edges (complete): star_all_4

3. **Each Case Proven**: We've proven τ ≤ 8 for concrete instances of each.

## Aristotle's Capabilities

| Tier | Success Rate | What Works |
|------|--------------|------------|
| 1 | 70-90% | `native_decide` on Fin n (n ≤ 9), decidable predicates |
| 2 | 30-50% | Simple induction, LP witnesses, scaffolded proofs |
| 3 | 10-20% | Deep combinatorics with human-outlined structure |
| 4 | <5% | Abstract reasoning, optimal selection |

## Key Insight
The problem is that we're quantifying over arbitrary V. But actually:
- Any 4-packing uses at most 12 vertices (4 triangles × 3 vertices)
- The intersection pattern is determined by which pairs share vertices
- We can encode this finitely!

## Debate Questions

1. **Can we reformulate to avoid abstract V?**
   - Use Fin 12 as universal domain?
   - Prove: "Any 4-packing on any graph is isomorphic to one of our concrete instances"?

2. **Can we prove pattern exhaustiveness directly?**
   - Enumerate all ways 4 triangles can share vertices
   - Show each falls into one of 6 categories

3. **Can we use a transfer principle?**
   - Prove on Fin 12, then argue it transfers to arbitrary V?

4. **Alternative formulation ideas?**
   - State theorem differently but equivalently?
   - Use different Lean structures?

## What Would Success Look Like?
A Lean theorem with:
- 0 sorry
- States that τ ≤ 8 for ν = 4 (in some form)
- Aristotle can verify (Tier 1-2)

## Your Task
Propose a concrete approach to close this gap. Be specific about:
1. The exact Lean formulation
2. Why Aristotle can handle it
3. What helper lemmas are needed
4. Estimated number of new theorems required
