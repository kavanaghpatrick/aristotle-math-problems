# FINAL SUBMISSION PLAN: Tuza ν=4 in 12 Slots
## January 1, 2026 - Multi-Agent Consensus

---

## WHY THIS PLAN EXISTS

### The Problem We Discovered
After 140+ Aristotle submissions, we realized our approach was flawed:

| What We Did | Why It's Not Novel |
|-------------|-------------------|
| Proved τ ≤ 2ν* (Krivelevich) | This is a KNOWN weaker bound |
| Used ν* ≤ 4 | Had `sorry` - never actually proved |
| Relied on LP axiom | Not machine-verified |

**Tuza claims τ ≤ 2ν, not τ ≤ 2ν***. The integrality gap (ν*/ν up to 3/2) means our approach was fundamentally insufficient.

### The New Strategy
**"Safe Discard + Interaction Graph"** - a direct combinatorial approach:

1. **Interaction Graph (IG)**: Vertices = M's 12 edges; edges connect if they share an external triangle
2. **Safe Discard**: Find 4-edge independent set in IG → discard them → cover remaining 8
3. **Bridge Absorption**: Triangles bridging disjoint M-elements are covered "for free"

---

## MULTI-AGENT CONSENSUS (Grok + Gemini + Codex)

### All Three Agree On:
1. Krivelevich/LP approach is **DEAD** for novel Tuza work
2. Need **DIRECT** combinatorial construction
3. `safe_discard_soundness` is the critical foundation lemma
4. `bridge_absorption` is key for matching_2/two_two_vw
5. **cycle_4 is hardest** (all rate difficulty 5/5)
6. **τ ≤ 12 is safe fallback** (95%+ success probability)

### Disagreements Resolved:
| Issue | Resolution |
|-------|------------|
| Slot numbering | Start at 64 (continues from slot63) |
| Trivial cases explicit? | NO - cite existing proofs |
| LP vs Direct first? | BOTH in parallel (hedged bet) |

---

## THE 12-SLOT PLAN

### Phase 1: Definitions & Soundness (Slots 64-67)

| Slot | Name | Target Lemma | Deps | Diff |
|------|------|--------------|------|------|
| **64** | `interaction_graph_def` | Define IG on M's 12 edges | None | 2 |
| **65** | `singleton_conflict_def` | `SingletonEdge`, `ConflictPair` predicates | 64 | 2 |
| **66** | `safe_discard_soundness` | 4-indep set → τ ≤ 8 | 65 | 3 |
| **67** | `bridge_absorption` | Bridging triangles are free | 64 | 3 |

**Why This Order**: Can't prove anything without IG definition. Soundness before existence proofs.

### Phase 2: Independent Set Existence (Slots 68-71)

| Slot | Name | Target Lemma | Deps | Diff |
|------|------|--------------|------|------|
| **68** | `ig_max_degree_bound` | IG has Δ ≤ 3 | 64 | 3 |
| **69** | `ig_scattered_empty` | Scattered case: IG is empty | 64 | 2 |
| **70** | `ig_path4_sparse` | Path_4 case: IG is path-like | 64,68 | 4 |
| **71** | `ig_cycle4_bounded` | Cycle_4 case: IG is cycle-like | 64,68 | 5 |

**Why This Order**: Degree bound enables Turán-style arguments. Easy cases first (scattered), hard last (cycle).

### Phase 3: Case Completion (Slots 72-75)

| Slot | Name | Target Lemma | Deps | Diff |
|------|------|--------------|------|------|
| **72** | `tau_le_8_scattered` | τ ≤ 8 when M is scattered | 66,69 | 2 |
| **73** | `tau_le_8_path4` | τ ≤ 8 for path_4 config | 66,67,70 | 4 |
| **74** | `tau_le_8_cycle4` | τ ≤ 8 for cycle_4 config | 66,67,71 | 5 |
| **75** | `tau_le_8_matching2` | τ ≤ 8 for matching_2/two_two_vw | 66,67 | 3 |

**Why This Order**: Use proven infrastructure, complete cases in difficulty order.

### Phase 4: Synthesis (Slot 76)

| Slot | Name | Target Lemma | Deps | Diff |
|------|------|--------------|------|------|
| **76** | `tuza_nu4_complete` | ∀ G, ν(G)=4 → τ(G) ≤ 8 | 72-75 | 4 |

**Why Last**: Combines all cases with case exhaustion.

---

## DEPENDENCY GRAPH

```
                    [64: IG_def]
                    /    |    \
                   /     |     \
              [65]     [67]    [68]
               |        |       |
              [66]      |      / \
               |        |    [70] [71]
               |        |     |     |
              [69]     [67]   |     |
               |        \     |     |
              [72]      [73] [74]  [75]
                \         \   |   /
                 \         \  |  /
                  \------→ [76] ←------
```

---

## RATIONALE FOR EACH SLOT

### Slot 64: interaction_graph_def
**What**: Define `InteractionGraph G M : SimpleGraph (Sym2 V)`
**Why**: Everything else depends on this. Without it, we can't talk about "safe" edges.
**Key Definition**:
```lean
def InteractionGraph (G : SimpleGraph V) (M : Finset (Finset V)) :
    SimpleGraph (Sym2 V) where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ ∃ t ∈ G.cliqueFinset 3, t ∉ M ∧ e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2
```

### Slot 65: singleton_conflict_def
**What**: Define when an edge is "dangerous" to discard
**Why**: These predicates structure the safe discard argument
**Key Definitions**:
```lean
def SingletonEdge (e : Sym2 V) (M : Finset (Finset V)) : Prop :=
  ∃ t ∈ G.cliqueFinset 3, t ∉ M ∧ (t.sym2 ∩ M_edges M) = {e}

def ConflictPair (e₁ e₂ : Sym2 V) (M : Finset (Finset V)) : Prop :=
  ∃ t ∈ G.cliqueFinset 3, t ∉ M ∧ (t.sym2 ∩ M_edges M) = {e₁, e₂}
```

### Slot 66: safe_discard_soundness
**What**: The core theorem - if we find 4 independent edges, τ ≤ 8
**Why**: This is THE key lemma. Everything else feeds into this.
**Statement**:
```lean
theorem safe_discard_soundness (D : Finset (Sym2 V)) (hD : D.card = 4)
    (h_indep : ∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → ¬(InteractionGraph G M).Adj d d')
    (h_no_single : ∀ d ∈ D, ¬SingletonEdge d M) :
    triangleCoveringNumber G ≤ 8
```

### Slot 67: bridge_absorption
**What**: Triangles that bridge disjoint M-elements don't add to τ
**Why**: Critical for matching_2/two_two_vw where M-elements don't share vertices
**Statement**:
```lean
theorem bridge_absorption (A B : Finset V) (hAB : A ∈ M) (hBA : B ∈ M)
    (h_disj : Disjoint A B) (t : Finset V) (ht : t.sym2 ∩ A.sym2 ≠ ∅)
    (ht' : t.sym2 ∩ B.sym2 ≠ ∅) :
    ∃ e ∈ local_cover A, e ∈ t.sym2
```

### Slot 68: ig_max_degree_bound
**What**: Each edge in M is adjacent to at most 3 others in IG
**Why**: Enables Turán-style independent set bounds
**Statement**:
```lean
theorem ig_max_degree_bound :
    ∀ e ∈ M_edges M, (InteractionGraph G M).degree e ≤ 3
```

### Slots 69-71: Case-specific IG structure
**What**: For each packing configuration, analyze IG structure
**Why**: Different configs have different IG shapes, enabling tailored arguments

### Slots 72-75: Case completion
**What**: Apply safe_discard_soundness to each case
**Why**: Once IG structure is known, finding 4-indep set is mechanical

### Slot 76: Final synthesis
**What**: Combine all cases
**Why**: The actual theorem we want

---

## SUBMISSION SCHEDULE

### Batch 1 (Parallel, No Dependencies)
Submit immediately:
- **Slot 64**: interaction_graph_def
- **Slot 68**: ig_max_degree_bound (can work in parallel)

### Batch 2 (After Batch 1)
- **Slot 65**: singleton_conflict_def
- **Slot 67**: bridge_absorption
- **Slot 69**: ig_scattered_empty

### Batch 3 (After Batch 2)
- **Slot 66**: safe_discard_soundness
- **Slot 70**: ig_path4_sparse
- **Slot 71**: ig_cycle4_bounded

### Batch 4 (After Batch 3)
- **Slots 72-75**: All case completions (parallel)

### Batch 5 (Final)
- **Slot 76**: tuza_nu4_complete

---

## RISK MITIGATION

### If Slot 71 (cycle_4) Fails:
- **Fallback A**: Accept τ ≤ 10 for cycle_4 (4 shared vertex edges + 6 M-edges)
- **Fallback B**: Use Krivelevich axiom for cycle_4 only (mixed proof)
- **Fallback C**: Prove τ ≤ 12 (guaranteed, uses all 12 M-edges)

### If Safe Discard Approach Fails Entirely:
- **Alternative 1**: Return to Krivelevich and prove the axiom in Lean
- **Alternative 2**: Prove τ ≤ 12 and document blocking pattern
- **Alternative 3**: Seek structural insight from counterexamples

---

## FALSE LEMMAS TO AVOID

| Pattern | Why False | Slots Affected |
|---------|-----------|----------------|
| local_cover_le_2 | 4 M-edges needed at shared vertex | 66, 74 |
| external_share_common_vertex | Counterexample found | 71, 74 |
| bridges_partition | X_ef symmetry | 67 |
| link_graph_bipartite | Odd cycles exist | None (avoided) |

**Check failed_approaches before each submission!**

---

## SUCCESS METRICS

| Level | Definition | Slots Required |
|-------|------------|----------------|
| **Bronze** | τ ≤ 12 for all ν=4 | 64 only (trivial) |
| **Silver** | τ ≤ 8 for 4/7 cases | 64-67, 72-73, 75 |
| **Gold** | τ ≤ 8 for all ν=4 | All 12 slots |
| **Platinum** | Gold + no axioms | Gold + prove Krivelevich |

---

## IMMEDIATE NEXT ACTIONS

1. **Create slot64_interaction_graph_def.lean** with IG definition
2. **Submit to Aristotle** (UUID will be tracked)
3. **Create slot65 in parallel** while 64 processes
4. **Update database** with new submission IDs
5. **Monitor for false lemma patterns** in outputs

---

## DOCUMENT HISTORY

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | Jan 1, 2026 | Initial synthesis from 3-AI debate |
| 1.1 | Jan 1, 2026 | Added rationale and risk mitigation |
