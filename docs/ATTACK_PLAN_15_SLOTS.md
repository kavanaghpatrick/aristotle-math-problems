# Cycle_4 Attack Strategy - 15 Slots (SYNTHESIZED)
## December 26, 2025

---

## CRITICAL FINDING: local_cover_le_2 is FALSE!

**Source**: Codex deep analysis

### The Problem
At shared vertex `v_ab`, the set `M_edges_at G M v_ab` contains FOUR edges:
- `{v_ab, v_da}` (from A)
- `{v_ab, a_priv}` (from A)
- `{v_ab, v_bc}` (from B)
- `{v_ab, b_priv}` (from B)

Nothing in `isCycle4` prevents triangles from using ALL FOUR edges simultaneously.

### Codex Counterexample
Start with packing:
- `A = {v_ab, v_da, a_priv}`
- `B = {v_ab, v_bc, b_priv}`
- `C = {v_bc, v_cd, c_priv}`
- `D = {v_cd, v_da, d_priv}`

Add vertex `x` with edges to create:
- `T₁ = {v_ab, v_da, x}` - shares `e₁ = {v_ab,v_da}` with A
- `T₂ = {v_ab, a_priv, x}` - shares `e₂ = {v_ab,a_priv}` with A
- `T₃ = {v_ab, v_bc, x}` - shares `e₃ = {v_ab,v_bc}` with B
- `T₄ = {v_ab, b_priv, x}` - shares `e₄ = {v_ab,b_priv}` with B

**Result**: All four T_i lie in `trianglesSharingMEdgeAt v_ab`, each using a DIFFERENT M-edge.
- They share `{v_ab, x}`, so mutually edge-overlapping → ν stays 4
- But any hitting set restricted to M_edges_at needs ALL FOUR edges
- Therefore `local_cover_le_2` is **FALSE**

### Impact
- Grok's slots 5, 11, 13 (local_cover_le_2 based) are INVALID
- Need corrected strategy using "support clusters" approach

---

## AI CONSENSUS STATUS

| AI | Finding | Status |
|----|---------|--------|
| **Gemini** | trianglesContainingVertex partition WRONG | ✅ Validated |
| **Grok** | 15-slot plan (but relies on local_cover_le_2) | ⚠️ PARTIAL |
| **Codex** | local_cover_le_2 FALSE + corrected 15-slot plan | ✅ CRITICAL |

---

## SYNTHESIZED 15-SLOT PLAN (Codex Strategy)

### Key Insight
Instead of restricting covering edges to `M_edges_at`, partition supported triangles into
at most 2 "clusters" at each vertex (triangles sharing a non-M edge like `{v,x}`), then
cover each cluster with ONE edge (possibly outside M_edges_at).

### Priority Legend
- ✅ High confidence
- ⚠️ Medium risk
- 🔁 Fallback/redundancy

---

## 15 SUBMISSION SLOTS

### Slot 1: local_cover_counterexample.md (INFORMAL ✅)
**Goal**: Document the 4-active-edges witness, why it satisfies isCycle4 and ν=4
**Scaffolding**: Cycle definition, M_edges_at description, packing-number check
**Why**: CRITICAL - prevents reusing bogus lemma

### Slot 2: slot95_edges_of_cycle4_have_shared_vertex (FORMAL ✅)
**Goal**: Prove every edge of each packing triangle contains at least one shared vertex
**Scaffolding**: `isCycle4`, `cycle4_element_contains_shared`, Finset rewrites
**Why**: Needed to redirect triangles to correct shared vertex

### Slot 3: slot96_h_only_from_diagonal (FORMAL ✅)
**Goal**: Show each shared vertex belongs to exactly its two adjoining elements
**Scaffolding**: `isCycle4`, Finset.card arithmetic
**Why**: Enables `h_only` hypothesis in local lemmas

### Slot 4: slot97_triangles_sharing_edge_pick_vertex (FORMAL ✅)
**Goal**: If triangle shares edge with A, it contains one of A's shared vertices
**Scaffolding**: Slots 2-3, `cycle4_intersection_pigeonhole`
**Why**: Bridges `trianglesSharingEdge` with `trianglesSharingMEdgeAt`

### Slot 5: slot98_cycle4_no_loose_triangles re-proof (FORMAL ✅)
**Goal**: Re-establish maximality lemma WITHOUT self-loop bug
**Scaffolding**: `isMaxPacking`, slot73 logic scrubbed of self-loops
**Why**: Guarantees every triangle shares edge with M

### Slot 6: slot99_every_triangle_shares_M_edge_at_shared (FORMAL ✅)
**Goal**: Every triangle belongs to some `trianglesSharingMEdgeAt v`
**Scaffolding**: Slots 2-5, explicit v_ab/v_bc/v_cd/v_da witnesses
**Why**: Core partition property

### Slot 7: slot100_support_clusters_design.md (INFORMAL ⚠️)
**Goal**: Analyze counterexample, derive extra condition for salvaging local cover
**Key idea**: Partition triangles at v into ≤2 "clusters" sharing non-M edge
**Scaffolding**: Combinatorial reasoning, diagrams
**Why**: Produces corrected local lemma statement

### Slot 8: slot101_support_clusters_exist (FORMAL ⚠️)
**Goal**: Formalize Slot 7 - triangles in `trianglesSharingMEdgeAt v` partition into ≤2 clusters
**Scaffolding**: `cycle4_triangle_at_vertex_supported`, pigeonhole, `S_e_structure`
**Why**: Foundation for corrected local cover

### Slot 9: slot102_local_cover_le_two_edges (FORMAL ⚠️)
**Goal**: Corrected local lemma: ∃ ≤2 edges (NOT restricted to M_edges_at) covering triangles
**Scaffolding**: Slot 8, Sym2 utilities, self-loop guards
**Why**: Replaces bogus local_cover_le_2

### Slot 10: slot103_trianglesSharingMEdgeAt_cover_local (FORMAL ⚠️)
**Goal**: Package Slot 9 with E_v witnesses for downstream use
**Scaffolding**: Slot 9, Finset.subset rewrites
**Why**: Clean interface for union step

### Slot 11: slot104_union_of_local_covers (FORMAL ⚠️)
**Goal**: Four E_v witnesses have union cardinality ≤8, hitting every triangle
**Scaffolding**: `Finset.card_union_le`, deduplication
**Note**: Covering edges may now lie OUTSIDE M_edges_at

### Slot 12: slot105_tau_le_8_cycle4_formal (FORMAL ⚠️)
**Goal**: MAIN THEOREM τ(G) ≤ 8 for cycle_4
**Scaffolding**: Slots 3, 6, 10, 11, `tau_union_le_sum`
**Why**: Capstone assembly

### Slot 13: slot106_counterexample_guard (FORMAL ⚠️)
**Goal**: Prove helper forbidding Sym2.mk(v,v) in local-cover reasoning
**Scaffolding**: SimpleGraph.edgeFinset, Finset filtering
**Why**: Regression prevention

### Slot 14: slot107_cycle4_strategy_report.md (INFORMAL ⚠️)
**Goal**: Summary for humans and database - new approach, trusted lemmas, failures
**Scaffolding**: Slots 1, 7, 12 combined
**Why**: Documentation

### Slot 15: slot108_tau_le_8_cycle4_inline (FORMAL 🔁)
**Goal**: Streamlined variant of Slot 12 with inlined proofs
**Scaffolding**: Slots 8-11 re-proved inline
**Why**: Fallback if Slot 12 times out

---

## TRUSTED LEMMAS (STILL VALID)
| Lemma | Status | Use In |
|-------|--------|--------|
| tau_S_le_2 | ✅ | S_e bounds |
| tau_X_le_2 | ✅ | Bridge bounds |
| tau_union_le_sum | ✅ | Final assembly |
| S_e_structure | ✅ | Cluster analysis |
| triangle_shares_edge_with_packing | ✅ | Slot 5 |
| diagonal_bridges_empty | ✅ | No diagonal bridges |
| cycle4_element_contains_shared | ✅ | Slot 2 |
| cycle4_no_loose_triangles | ✅ | Slot 5 |

## FAILED APPROACHES (AVOID!)
| Approach | Why Wrong |
|----------|-----------|
| bridge_absorption | S_e covers do NOT absorb bridges |
| avoiding_covered_by_spokes | FALSE |
| trianglesContainingVertex | WRONG partition (Gemini) |
| local_cover_le_2 | FALSE - 4 active edges possible (Codex) |
| Sym2.mk(v,v) | Self-loop invalid in SimpleGraph |

---

## IMPLEMENTATION ORDER

**Phase 1 (High Confidence)**: Slots 1-6
- Document counterexample
- Re-prove foundational lemmas without bugs
- Establish partition property

**Phase 2 (Medium Risk)**: Slots 7-12
- Design and prove cluster approach
- Build to main theorem

**Phase 3 (Safety)**: Slots 13-15
- Guards, documentation, fallbacks

---

## KEY DIFFERENCE FROM GROK STRATEGY

| Grok | Codex (Corrected) |
|------|-------------------|
| Assumes local_cover_le_2 is TRUE | Proves it's FALSE |
| Restricts cover to M_edges_at | Allows cover edges OUTSIDE M_edges_at |
| Direct 4×2=8 bound | Cluster-based partition + cover |

**Codex strategy is more robust** - it doesn't rely on the false lemma.
