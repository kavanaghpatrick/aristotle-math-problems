# Multi-Agent Debate Synthesis: τ ≤ 8 for PATH_4

**Date**: Jan 17, 2026
**Rounds**: 2 (partial Round 2 due to API issues)
**Participants**: Gemini, Grok, Claude (analysis)

---

## EXECUTIVE SUMMARY

### Round 1 Consensus (PARTIALLY WRONG)
1. ✓ 6-packing is key to generalization
2. ✓ Component-wise: 2 edges per element
3. ✗ "Bridges are S_e instances" - **FALSE!**
4. ✓ Middle priority: spine first if S_e(spine) nonempty

### Round 2 Discovery (Critical)
**Bridges are NOT S_e externals** - they share edges with BOTH adjacent elements.

The "spine priority" algorithm can leave bridges uncovered in worst-case scenarios.
However, τ ≤ 8 still holds via bridge external edges like {b, c}.

---

## KEY TECHNICAL FINDINGS

### Finding 1: Bridge Definition Mismatch

S_e(E) requires: triangle shares edge with E, but NOT with other M-elements.
Bridge requires: triangle shares edge with BOTH adjacent elements.

These are disjoint categories!

### Finding 2: The Worst-Case Scenario

On 13 vertices with:
- S_e(B, spine) ≠ ∅, S_e(B, left) ≠ ∅, S_e(B, right) = ∅
- S_e(C, spine) ≠ ∅, S_e(C, right) ≠ ∅, S_e(C, left) = ∅
- Bridge {v2, b, c} exists

Algorithm picks:
- B: spine + left (forced by S_e coverage)
- C: spine + right (forced by S_e coverage)

Bridge needs B's right leg or C's left leg - neither picked!

### Finding 3: The Bridge External Edge Solution

Bridge {v2, b, c} has edges: {v2, b}, {v2, c}, {b, c}

The edge {b, c} is:
- NOT in B's edge set (B = {v1, b, v2})
- NOT in C's edge set (C = {v2, c, v3})
- But it covers the bridge!

This "external" edge allows B and C to focus on S_e coverage.

### Finding 4: Optimal Cover Uses ≤ 8 Edges

For the worst-case graph:
```
A: 1 edge (any spoke)
B: 2 edges (spine + left)
C: 2 edges (spine + right)
D: 1 edge (any spoke)
Bridge: 1 edge {b, c}
Total: 7 edges ≤ 8 ✓
```

---

## REVISED PROOF STRATEGY

### Approach: Two-Phase Cover

**Phase 1**: Cover packing elements and S_e externals
- Each element E contributes ≤ 2 edges
- Total: ≤ 8 edges from packing elements

**Phase 2**: Cover bridges using external edges if needed
- Bridge {v, x, y} between E and F has external edge {x, y}
- This edge is in G.edgeFinset (bridge is a clique)
- At most 3 bridges (A-B, B-C, C-D)

**Key Insight**: Phase 1 edges may already cover some bridges!
- If B picks right leg {v2, b}, covers B-C bridge via {v2, b}
- Only need external edge if BOTH middles avoid shared-side legs

### Counting Argument

Let b = number of bridges needing external edges.

Phase 1 uses: ≤ 8 - b edges (since bridges covered by Phase 2)
Phase 2 uses: b edges

Total: ≤ 8 edges.

The challenge: proving this counting works out.

---

## RECOMMENDED NEXT SUBMISSIONS

### Priority 1: slot448_bridge_classification.lean

Prove that bridges are distinct from S_e externals:

```lean
/-- A bridge shares edge with TWO M-elements, so not in any S_e -/
theorem bridge_not_in_Se {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E F T : Finset V)
    (hE_in : E ∈ M) (hF_in : F ∈ M) (hEF : E ≠ F)
    (hT_bridge : 2 ≤ (T ∩ E).card ∧ 2 ≤ (T ∩ F).card) :
    T ∉ S_e G M E ∧ T ∉ S_e G M F := by
  sorry
```

### Priority 2: slot449_bridge_external_edge.lean

Prove the external edge property:

```lean
/-- Bridge external edge covers the bridge but no other triangles -/
theorem bridge_external_edge_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v x y : V)
    (hEF : E ∩ F = {v})
    (hx : x ∈ E ∧ x ≠ v) (hy : y ∈ F ∧ y ≠ v)
    (hT : {v, x, y} ∈ G.cliqueFinset 3) :
    -- External edge covers bridge
    s(x, y) ∈ ({v, x, y} : Finset V).sym2 ∧
    -- External edge not in E or F
    s(x, y) ∉ E.sym2 ∧ s(x, y) ∉ F.sym2 := by
  sorry
```

### Priority 3: slot450_tau_le_8_two_phase.lean

Main theorem with two-phase cover:

```lean
theorem tau_le_8_path4_two_phase {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (M : Finset (Finset V))
    (hPath4 : IsPath4Config A B C D)
    (hM : M = {A, B, C, D})
    (hPacking : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, 2 ≤ (T ∩ E).card) :
    ∃ Cover : Finset (Sym2 V),
      Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  -- Phase 1: adaptive cover for S_e externals
  -- Phase 2: external edges for uncovered bridges
  sorry
```

---

## ALTERNATIVE APPROACHES

### A. Finite Case Exhaustion

slot447 proves τ ≤ 8 on Fin 9.
Could prove for Fin 10, 11, ... up to some bound, then show larger cases reduce.

### B. LP Relaxation

Formulate as linear program and prove optimal value ≤ 8.
Harder to formalize in Lean.

### C. König/Matching Theory

The edge-triangle incidence is a hypergraph.
Matching bounds might give τ ≤ 2ν directly.
Note: link_graph_bipartite is FALSE (False Lemma #8).

---

## CONCLUSION

The Round 1 strategy of "spine priority" is incomplete due to bridge handling.
The corrected approach uses bridge external edges when needed.
This still achieves τ ≤ 8 but requires more careful proof structure.

**Next Step**: Submit slot448 to prove bridge classification lemma, then build toward the two-phase cover theorem.
