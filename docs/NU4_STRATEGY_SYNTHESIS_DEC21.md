# Tuza ν=4 Strategy Synthesis

**Date**: December 21, 2025
**Sources**: Web research, Gemini, Grok-4, proven lemmas database

---

## Executive Summary

**ν ≤ 3 is COMPLETE** (matches Parker arXiv:2406.06501, EJC May 2025).
**ν = 4 is GENUINELY OPEN** - no published proof exists.

Our proven lemmas provide a solid foundation, but counterexamples show Parker's method (τ(T_e) ≤ 2 for some e) fails at ν=4.

---

## Latest Research (2024-2025)

| Paper | Key Result | Relevance to ν=4 |
|-------|------------|------------------|
| [Parker arXiv:2406.06501](https://arxiv.org/abs/2406.06501) | Proves Tuza for ν ≤ 3 | Our formalization matches this |
| [arXiv:2405.11409](https://arxiv.org/abs/2405.11409) | τ ≤ (3/2)ν for complete 4-partite | Dense graphs have BETTER bounds |
| Haxell | τ ≤ (66/23)ν ≈ 2.87ν | Best general bound |
| Random graphs | Tuza holds for G(n,m) | Probabilistic approaches work |

**Key insight**: No one has published ν=4. This is genuinely open territory.

---

## What WON'T Work (From Counterexamples)

| Approach | Why It Fails | Counterexample |
|----------|--------------|----------------|
| τ(T_e) ≤ 2 for some e | Bridges attach to 3 different fᵢ | FlowerGraph |
| |S_e| ≤ 4 | S_e can have 5+ triangles | Fan (Fin 7) |
| Cover with edges FROM e | K4 needs all 3 edges of e | K4 counterexample |
| Vertex-disjoint packing | Overlapping packings exist | bridge_shares_vertex |

---

## What WILL Work (From Analysis)

### Gemini's Key Insight: Compensating Hypothesis

> "If a graph is 'bad' enough to force τ(T_e) ≥ 3 for all e ∈ M, it must be extremely dense. Prove this density forces the residual G \ T_e to be sparse: τ(G \ T_e) ≤ 2(ν-1) - 1"

**Result**: τ(G) ≤ 3 + (2ν - 3) = 2ν ✓

### Grok-4's Key Insight: Packing-Pair Decomposition

> "There exists M' ⊆ M of size 2 such that τ(∪_{t∈M'} T_t) ≤ 4"

**Logic**:
- Apply to G' = G \ ∪_{t∈M'} T_t where ν(G') ≤ 2
- Since ν=2 is proven (τ ≤ 4), we get τ(G) ≤ 4 + 4 = 8 ✓

---

## Universal Lemmas (Already Proven)

These work for ALL ν and should be included as context:

```lean
-- S_e structure
lemma S_e_pairwise_share_edges ...  -- S_e triangles pairwise share
lemma pairwise_sharing_implies_tau_le_2 ...  -- τ(S_e) ≤ 2 always

-- Decomposition
lemma inductive_bound ... -- τ(G) ≤ τ(T_e) + τ(G \ T_e)
lemma lemma_2_3 ...       -- ν(G \ T_e) = ν(G) - 1

-- K4 structure
lemma k4_cover ...        -- ≤4 vertices → τ ≤ 2
lemma intersecting_triangles_structure ... -- star OR K4
```

---

## Three Attack Strategies for ν=4

### Strategy A: Compensating Density Bound
**Target Lemma**:
```lean
lemma density_compensation (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4)
    (h_bad : ∀ e ∈ M, coveringNumberOn G (T_e G e) ≥ 3) :
    ∃ e ∈ M, coveringNumberOn G ((G.cliqueFinset 3) \ (T_e G e)) ≤ 5
```
**Proof sketch**: High τ(T_e) implies dense local structure, which forces sparse residual.

### Strategy B: Packing-Pair Decomposition
**Target Lemma**:
```lean
lemma packing_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4) :
    ∃ e f ∈ M, e ≠ f ∧ coveringNumberOn G (T_e G e ∪ T_e G f) ≤ 4
```
**Proof sketch**: Among 6 pairs, at least one has bounded joint covering.

### Strategy C: Bridge Classification
**Target Lemma**:
```lean
lemma bridge_attachment_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4)
    (e : Finset V) (he : e ∈ M) :
    -- Bridges attach to at most 2 other packing elements in "bad" way
    ∃ f ∈ M, f ≠ e ∧
    ∀ b ∈ T_e G e \ S_e G M e, ¬(shares_edge b f ∧ shares_edge b (other f))
```

---

## Recommended Submission Portfolio

| Slot | Strategy | File Pattern | Notes |
|------|----------|--------------|-------|
| 1 | Compensating | nu4_compensating.lean | Density → sparse residual |
| 2 | Packing-Pair | nu4_pair_bound.lean | Find good pair in M |
| 3 | Bridge Analysis | nu4_bridge_classify.lean | Characterize bridge attachments |
| 4 | Direct Induction | nu4_direct.lean | Minimal, let Aristotle explore |
| 5 | Dense Graph | nu4_dense.lean | Exploit 4-partite result |
| 6 | Informal | nu4_strategy.md | Natural language proof |
| 7 | Counterexample | nu4_negation.lean | Find obstruction if τ > 8 |

---

## Key Connections to Literature

### Complete 4-Partite (arXiv:2405.11409)
- τ ≤ (3/2)ν = 6 for complete 4-partite
- **Implication**: Dense ν=4 graphs are EASIER, not harder
- **Strategy**: Show "bad" graphs (τ(T_e) ≥ 3 ∀e) resemble 4-partite

### Hypergraph Generalization (Aharoni-Zerbib)
- Parker proved for ν^(k-1) ≤ 3 in k-uniform hypergraphs
- **Connection**: Triangle hypergraph is 3-uniform
- **Strategy**: Apply hypergraph covering bounds

### Random Graphs
- Tuza holds for G(n,m) for all m
- **Implication**: Counterexamples (if any) are structured, not random
- **Strategy**: Focus on highly structured graphs (flowers, K6 configs)

---

## Finite Verification Insight

**From Grok-4**: "Minimal obstructions" to ν=4 are finite and small.

If Tuza fails at ν=4, there exists a minimal graph G with:
- ν(G) = 4
- τ(G) = 9
- Removing any edge reduces τ or ν

Such graphs have bounded size (likely ≤ 20 vertices). Computational search is feasible.

---

## Next Actions

1. **Create submission files** for strategies A, B, C
2. **Include proven lemmas** as full proofs in context folder
3. **Submit 7-slot portfolio** with mix of formal/informal
4. **Run counterexample search** for τ > 8 obstruction

---

## References

- Parker, A. (2024). "New bounds on a generalization of Tuza's conjecture." [arXiv:2406.06501](https://arxiv.org/abs/2406.06501)
- Dense graphs paper. [arXiv:2405.11409](https://arxiv.org/abs/2405.11409)
- Haxell. τ ≤ (66/23)ν bound.
- Aharoni & Zerbib (2020). "A generalization of Tuza's conjecture." J. Graph Theory.
- [Wikipedia: Tuza's conjecture](https://en.wikipedia.org/wiki/Tuza's_conjecture)
