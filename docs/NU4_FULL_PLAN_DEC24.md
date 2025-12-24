# Tuza ν=4: Full Attack Plan
*Generated: 2024-12-24 from AI Consultation Synthesis*

## Executive Summary

Based on 94 proven lemmas, 12 negated approaches, and consultation with Grok/Gemini/Codex, we have a clear path forward. The key insight is that **the proof reduces to showing we can always remove elements at cost ≤2 per element**.

---

## PHASE 1: IMMEDIATE ACTIONS

### 1.1 Cancel/Deprioritize Slot 37 (LLL)
**Rationale**: All three AIs agree probabilistic methods fail for finite ν=4.
```bash
# Don't download output - low value
# Focus resources elsewhere
```

### 1.2 Monitor Running Slots (34, 35, 36)
These target different sharing graph types:
- **Slot 34**: ∃ pair with τ(T_pair) ≤ 4 (attacks all types)
- **Slot 35**: V-decomposition overlap (attacks dense types)
- **Slot 36**: Leaf removal τ(T_leaf) ≤ 2 (attacks Path/Star)

---

## PHASE 2: NOVEL APPROACH SUBMISSIONS

### 2.1 Hypergraph Transfer Attack (Codex's Insight)

**The Idea**: We have a PROVEN bridge lemma for 4-uniform hypergraphs that's underused. Reinterpret the triangle problem in hypergraph terms.

**Submission: slot38_hypergraph_transfer.lean**
```
Target Lemma: hypergraph_bridge_transfer

For ν=4 packing M = {e₁, e₂, e₃, e₄}:
- View each packing element eᵢ as a "hypervertex"
- A bridge triangle t ∈ X(eᵢ, eⱼ) becomes a "hyperedge" connecting hypervertices i,j
- The proven r=4 bridge lemma bounds the hyperedge structure
- Transfer back: τ(all bridges) ≤ 4

Combined with τ(∪S_eᵢ) ≤ 8 (union of 4 disjoint sets each ≤2), get τ(G) ≤ 8.
```

**Why Novel**: Nobody has used the hypergraph results as direct scaffolding for the triangle case.

**Scaffolding Needed**:
- `bridge_lemma` from `aristotle_hypergraph_r4_COMPLETE.lean`
- `tau_S_le_2` (proven slot 6)
- `tau_union_le_sum` (proven slot 16)

---

### 2.2 Heavy Edge Forcing (Gemini's Insight)

**The Idea**: If τ(T_e) > 2 for some packing element e, what structure does this FORCE? Gemini hypothesizes it forces e to share EDGES (not just vertices) with other packing members.

**Submission: slot39_heavy_edge_forcing.lean**
```
Target Lemma: heavy_implies_edge_sharing

If τ(T_e) ≥ 3 for packing element e ∈ M, then:
∃ f ∈ M, f ≠ e, such that (e ∩ f).card ≥ 2

English: A "heavy" element (needing 3+ edges to cover its triangles)
must share an EDGE with another packing element.

Contrapositive: If e shares only vertices (no edges) with all other
elements, then τ(T_e) ≤ 2.
```

**Why Novel**: All our analysis focused on vertex-sharing. Edge-sharing is strictly stronger and might force better bounds.

**Strategic Implication**: If proven, then:
- Elements with τ(T_e) ≥ 3 form edge-sharing pairs
- Edge-sharing pairs have constrained bridge structure
- Could reduce to the τ(T_pair) ≤ 4 case

---

### 2.3 Bridge Counting Bound (Grok's Insight)

**The Idea**: The bridge absorption counterexample showed covers of S_e don't absorb bridges. But Grok notes: use that counterexample to BOUND total bridges instead.

**Submission: slot40_bridge_counting.lean**
```
Target Lemma: total_bridges_bounded

For ν=4 packing M:
|bridges(M)| ≤ 12  (total bridge triangles across all pairs)

Combined with:
- τ(bridges) ≤ |bridges| / 2 (each edge hits ≤2 triangles)
- τ(bridges) ≤ 6

Plus τ(∪S_eᵢ) ≤ 4 (overlapping S_e sets), get τ(G) ≤ 10.
Not tight, but provides upper bound framework.
```

**Refinement Target**:
```
Refined Lemma: bridge_per_pair_bounded

For any pair (e,f) in ν=4 packing:
|X(e,f)| ≤ 3  (at most 3 bridge triangles per pair)

Since there are C(4,2) = 6 pairs:
Total bridges ≤ 18, but with overlap through shared vertex v,
actual distinct bridges ≤ 12.
```

---

### 2.4 C₄ Sharing Graph Attack (All Three Agree)

**The Idea**: C₄ is the hardest case - no leaves, opposite pairs not disjoint. Create a dedicated submission.

**Submission: slot41_cycle_sharing_graph.lean**
```
Target Lemma: cycle_sharing_graph_bound

If sharing graph of M = {e₁, e₂, e₃, e₄} is a 4-cycle C₄
(i.e., e₁-e₂-e₃-e₄-e₁ with no other edges), then:
τ(G) ≤ 8

Approach: Use the cycle structure explicitly.
- Adjacent pairs: (e₁,e₂), (e₂,e₃), (e₃,e₄), (e₄,e₁)
- Each adjacent pair shares exactly one vertex
- Non-adjacent pairs (e₁,e₃), (e₂,e₄) may or may not share vertices
  (Negation #8 shows they CAN share - don't assume disjoint)

Strategy: Cover with 4 pairs of edges:
- 2 edges for T_{e₁} ∩ T_{e₂} (triangles touching both)
- 2 edges for T_{e₃} ∩ T_{e₄}
- Remaining triangles in S_eᵢ (already covered or ≤4 more edges)
```

---

### 2.5 Local Reduction Lemma (Gemini's Key Insight)

**The Idea**: Don't prove τ(G) ≤ 8 globally. Prove we can always make a "good move".

**Submission: slot42_local_reduction.lean**
```
Target Lemma: good_reduction_exists

For any ν=4 graph G, at least one of the following holds:
(A) ∃ e ∈ M: τ(T_e) ≤ 2  (can remove 1 element for cost 2)
(B) ∃ e,f ∈ M: τ(T_e ∪ T_f) ≤ 4  (can remove 2 elements for cost 4)

Either way: Cost ≤ 2 × (elements removed)

Then by induction:
- If (A): τ(G) ≤ 2 + τ(G', ν=3) ≤ 2 + 6 = 8
- If (B): τ(G) ≤ 4 + τ(G', ν=2) ≤ 4 + 4 = 8
```

**Why Powerful**: This is the MINIMAL statement needed. We don't need τ(T_e) ≤ 2 for ALL e, just existence of a good move.

---

### 2.6 Adjacent Pair Bound for Dense Types (Codex's Target)

**Submission: slot43_adjacent_pair_dense.lean**
```
Target Lemma: adjacent_pair_bound_dense

For ν=4 packing M with sharing graph having min-degree ≥ 2,
∃ adjacent pair (e,f) with τ(T_e ∪ T_f) ≤ 4.

Key insight: T_{e,f} lives on ≤ 6 vertices (because every bridge
contains the shared vertex v, and e,f each have 3 vertices).

On ≤6 vertices, explicit case analysis is tractable.
```

---

## PHASE 3: SHARING GRAPH EXHAUSTION STRATEGY

### Complete Proof Structure

```
THEOREM: Tuza ν=4
  By case analysis on sharing graph type:

  CASE 1: Empty (K̄₄)
    All elements disjoint
    τ(G) = Σ τ(T_eᵢ) ≤ Σ τ(S_eᵢ) ≤ 4×2 = 8  ✓
    [TRIVIAL - no submission needed]

  CASE 2: Path (P₄)
    Has 2 leaves
    Apply Slot 36: τ(T_leaf) ≤ 2
    Remove leaf, residual ν=3
    τ(G) ≤ 2 + 6 = 8  ✓

  CASE 3: Star (K₁,₃)
    Has 3 leaves
    Apply Slot 36: τ(T_leaf) ≤ 2
    Remove any leaf, residual ν=3
    τ(G) ≤ 2 + 6 = 8  ✓

  CASE 4: Cycle (C₄) [HARDEST]
    No leaves, all degree 2
    Apply Slot 41: dedicated C₄ analysis
    OR apply Slot 43: adjacent pair bound
    τ(G) ≤ 8  ✓

  CASE 5: K₄-e (almost complete)
    No leaves, degrees (2,2,3,3)
    Two high-degree vertices must be adjacent
    Apply Slot 43: adjacent pair bound for that pair
    τ(G) ≤ 8  ✓

  CASE 6: Complete (K₄)
    No leaves, all degree 3
    Maximum overlap - triangles heavily constrained
    Apply Slot 35: V-decomposition
    OR apply Slot 43: any adjacent pair
    τ(G) ≤ 8  ✓
```

---

## PHASE 4: SUBMISSION PRIORITY ORDER

### Tier 1: Highest Impact (Submit First)
| Slot | Name | Targets | Why First |
|------|------|---------|-----------|
| 42 | Local Reduction | ALL types | Minimal statement, maximum impact |
| 41 | C₄ Attack | Cycle only | Hardest case, cracks the bottleneck |
| 38 | Hypergraph Transfer | ALL types | Novel approach, uses proven scaffolding |

### Tier 2: Type-Specific (Submit After Tier 1)
| Slot | Name | Targets | Dependency |
|------|------|---------|------------|
| 43 | Adjacent Pair Dense | C₄, K₄-e, K₄ | Complements Slot 41 |
| 39 | Heavy Edge Forcing | Heavy T_e cases | Novel structural insight |

### Tier 3: Refinement (Submit If Tier 1-2 Partial)
| Slot | Name | Targets | Purpose |
|------|------|---------|---------|
| 40 | Bridge Counting | ALL types | Provides upper bound framework |

---

## PHASE 5: SCAFFOLDING REQUIREMENTS

### For All New Submissions, Include:

```lean
-- PROVEN SCAFFOLDING (copy full proofs, not axioms)

-- From slot6: S_e structure
lemma tau_S_le_2 : τ(S_e) ≤ 2 := [full proof]

-- From slot16: Union bound
lemma tau_union_le_sum : τ(A ∪ B) ≤ τ(A) + τ(B) := [full proof]

-- From slot24: Bridge bounds
lemma tau_X_le_2 : τ(X(e,f)) ≤ 2 := [full proof]
lemma mem_X_implies_v_in_t : t ∈ X(e,f) → v ∈ t := [full proof]

-- From slot6: Partition
lemma Te_eq_Se_union_bridges : T_e = S_e ∪ bridges := [full proof]
```

### For Hypergraph Transfer (Slot 38), Additionally:
```lean
-- From aristotle_hypergraph_r4_COMPLETE.lean
lemma bridge_lemma_r4 : [hypergraph bridge structure] := [full proof]
lemma union_size_pair_r4 : [4-edges sharing 3 vertices have union ≤5] := [full proof]
```

---

## PHASE 6: SUCCESS CRITERIA

### Primary Success (Full Proof)
Any ONE of these proves Tuza ν=4:
- Slot 42 (Local Reduction) succeeds
- Slot 38 (Hypergraph Transfer) + Slot 41 (C₄) both succeed
- All 6 sharing graph cases proven individually

### Partial Success (Progress)
- τ(T_pair) ≤ 4 proven for ANY pair type
- C₄ case cracked (unlocks other dense types)
- Bridge counting gives τ ≤ 9 (tightens Haxell's 2.87ν)

### Failure Indicators
- Aristotle finds counterexample to τ(T_pair) ≤ 4
- Heavy edge forcing is FALSE
- All novel approaches hit structural barriers

---

## PHASE 7: CONTINGENCY PLANS

### If All Fail: Pivot to Counterexample Hunt
The constraints are tight:
- mad(G) ≥ 7, χ(G) ≥ 5, treewidth ≥ 7
- Contains K₃,₃, NOT tripartite/threshold/planar/random/4-partite

Search space: Non-abelian Cayley graphs, Kneser graphs, polarity graphs.

### If Partial Success: Iteration
- Use Aristotle output to identify exactly WHERE proof breaks
- Create refined submission targeting that specific gap
- Rinse and repeat

---

## IMPLEMENTATION CHECKLIST

### Today (Dec 24):
- [ ] Monitor slots 34, 35, 36 (already running)
- [ ] Create slot38_hypergraph_transfer.lean
- [ ] Create slot41_cycle_sharing_graph.lean
- [ ] Create slot42_local_reduction.lean

### Next Session:
- [ ] Download and analyze slot 34-36 outputs
- [ ] Submit slots 38, 41, 42
- [ ] Create slots 39, 40, 43 based on results

### Success Verification:
```bash
# After each download:
./scripts/verify_output.sh output.lean
./scripts/post_result.sh <uuid> output.lean

# Check sorry count - 0 means proven
grep -c "sorry" output.lean
```

---

## APPENDIX: Novel Approach Details

### A. Hypergraph Transfer (Full Strategy)

The key insight is that our bridge structure maps to a hypergraph:

```
Triangle World           Hypergraph World
─────────────────────    ─────────────────────
Packing element eᵢ   →   Hypervertex i
Bridge t ∈ X(eᵢ,eⱼ)  →   Hyperedge {i,j}
Shared vertex v      →   Hyperedge label
```

The PROVEN lemma for r=4 hypergraphs says:
> If two 4-edges share a 3-face, their union has ≤5 vertices.

Translating back:
> If two packing elements share a vertex, all bridges between them lie on ≤5 vertices.

This CONSTRAINS bridge structure far more than our current analysis exploits.

### B. Heavy Edge Forcing (Full Strategy)

Consider: Why would τ(T_e) ≥ 3?

T_e = S_e ∪ bridges. We know τ(S_e) ≤ 2. So τ(T_e) ≥ 3 requires bridges that ESCAPE the S_e cover.

But every bridge contains the shared vertex v. If e shares vertex v with f, then bridges X(e,f) all pass through v.

**Hypothesis**: If τ(T_e) ≥ 3, then e must share vertices with ≥3 other elements (otherwise all bridges go through ≤2 vertices, coverable by ≤2 edges).

**Refined Hypothesis**: Sharing with ≥3 elements in ν=4 means sharing with ALL other elements → complete sharing graph K₄ → maximum structure → probably τ ≤ 8 anyway.

### C. Bridge Counting (Full Strategy)

For pair (e,f) sharing vertex v:
- Every bridge t ∈ X(e,f) contains v
- t has 3 vertices, one is v, two others from e∪f minus v
- |e ∪ f| ≤ 5 (since |e ∩ f| ≥ 1)
- Triangles on ≤5 vertices containing fixed v: at most C(4,2) = 6

So |X(e,f)| ≤ 6 per pair, with 6 pairs: total bridges ≤ 36.
But bridges can belong to multiple X(e,f) sets (if they hit 3+ elements).

**Tighter bound**: Each bridge hits exactly 2 packing elements (by definition).
So total distinct bridges ≤ 6×6 / 1 = 36 (loose) or better analysis needed.

If we can show ≤12 distinct bridges and each edge covers ≥1.5 bridges on average, we get τ(bridges) ≤ 8.
