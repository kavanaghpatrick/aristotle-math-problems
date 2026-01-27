# Multi-Agent Debate Final Synthesis: Tuza ν=4 Formalization Gap

**Date**: January 18, 2026
**Participants**: Grok-4, Gemini
**Rounds**: 4
**Moderator**: Claude

---

## EXECUTIVE SUMMARY

After 4 rounds of debate, both agents converged on a unified approach to close the formalization gap between our 273 concrete theorems and a fully general proof of Tuza's conjecture τ ≤ 8 for ν = 4.

---

## CONSENSUS APPROACH: Interaction Graph with Classification

### Core Strategy
1. **Reuse slot64 infrastructure** - `edgesInteract`, `M_edges`, `externalTriangles`
2. **Define InteractionGraph** as `SimpleGraph (Sym2 V)` where edges interact via external triangles
3. **Classify interactions** as Bridge (dangerous) vs Private (safe)
4. **Key lemma**: `external_shares_at_most_two` - any external triangle shares ≤2 edges with M

### Why This Works
- **Edge-centric** (avoids failed vertex saturation)
- **Leverages existing 273 theorems**
- **Tier 1-2 verifiable** (no deep abstraction)
- **Pattern-agnostic** (doesn't require exhaustive pattern classification)

---

## FINAL ACTION PLAN

### File 1: `slot455_interaction_foundation.lean`
**Purpose**: Define InteractionGraph and key structural lemma

**Theorems**:
```lean
def InteractionGraph (G : SimpleGraph V) (M : Finset (Finset V)) : SimpleGraph (Sym2 V)
lemma classify_interaction : BridgeInteraction e f ∨ PrivateInteraction e f
lemma external_shares_at_most_two : ((M_edges G M).filter (· ∈ t.sym2)).card ≤ 2
```

**Estimated**: 3 theorems, 0 sorry
**Dependencies**: slot64_interaction_graph_def.lean

---

### File 2: `slot456_degree_bounds.lean`
**Purpose**: Bound degrees in InteractionGraph

**Theorems**:
```lean
lemma bridge_degree_bound : IG.degree e ≤ 4
lemma private_degree_bound : IG.degree e ≤ 4
lemma total_interactions_bound : IG.edgeFinset.card ≤ 12
```

**Estimated**: 3 theorems, 1 sorry
**Dependencies**: slot455

---

### File 3: `slot457_cover_construction.lean`
**Purpose**: Construct τ ≤ 8 cover from interaction structure

**Theorems**:
```lean
lemma matching_to_covering : ∃ C, IsTriangleCovering G C ∧ C.card ≤ 2 * M.card
lemma interaction_graph_independent_set : ∃ I ⊆ M_edges, I.card ≥ 4 ∧ IsIndependent IG I
lemma discard_independent_cover : C.card ≤ 8
```

**Estimated**: 4 theorems, 1 sorry
**Dependencies**: slot455, slot456

---

### File 4: `slot458_tuza_nu4_general.lean`
**Purpose**: Main theorem - general τ ≤ 8 for ν = 4

**Theorems**:
```lean
theorem tuza_nu4 (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (hν : ∃ M, isMaxPacking G M ∧ M.card = 4) : τ G ≤ 8
```

**Estimated**: 2 theorems, 0 sorry
**Dependencies**: slot455, slot456, slot457

---

## SUMMARY TABLE

| File | Theorems | Sorries | Tier |
|------|----------|---------|------|
| slot455_interaction_foundation | 3 | 0 | 1 |
| slot456_degree_bounds | 3 | 1 | 2 |
| slot457_cover_construction | 4 | 1 | 2 |
| slot458_tuza_nu4_general | 2 | 0 | 2 |
| **TOTAL** | **12** | **2** | |

---

## KEY INSIGHTS FROM DEBATE

### Round 1: Initial Proposals
- **Grok**: Exhaustive enumeration on Fin 12, embedding + lifting
- **Gemini**: Intersection matrix, constructive covers, edge saturation

### Round 2: Cross-Critique
- **Critical finding**: Vertex saturation FAILED before (database evidence)
- **Gemini defended**: Edge saturation is fundamentally different (operates on edges, not vertices)
- **Grok refined**: Proposed hybrid with matrices for pruning

### Round 3: Convergence
- Both agreed on InteractionGraph approach
- Both proposed inductive classification (Bridge vs Private)
- Discovered existing slot64 infrastructure could be reused

### Round 4: Final Synthesis
- Unified action plan with 4 files, 12 theorems
- Clear dependency chain
- Estimated 2 total sorries (target: fill within 1 submission each)

---

## WHAT THIS ACHIEVES

**Before debate**: 273 theorems on concrete Fin 12 instances
**After debate**: Clear path to general theorem via:
1. Abstract InteractionGraph (not tied to Fin 12)
2. Structural lemmas that work for any finite V
3. Pattern-agnostic cover construction

**The key insight**: We don't need to formalize pattern exhaustiveness separately. The InteractionGraph approach bounds τ directly from the interaction structure, which exists regardless of which of the 6 patterns the packing has.

---

## NEXT STEPS

1. **Immediate**: Write slot455_interaction_foundation.lean
2. **Validate**: Submit to Aristotle for Tier 1-2 verification
3. **Iterate**: Fill any sorries based on Aristotle feedback
4. **Complete**: Chain through slot456 → slot457 → slot458

**Estimated total effort**: 4-6 submissions, ~50 new theorems, ~2 weeks
