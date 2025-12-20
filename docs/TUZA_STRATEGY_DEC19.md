# Tuza's Conjecture: Strategic Plan (December 19, 2025)

## Executive Summary

**Critical Discovery**: Alex Parker (arXiv:2406.06501, March 2025) proved Tuza for ν ≤ 3.
**Impact**: Our ν=2 target is now a KNOWN result, but first machine-verification is still valuable.
**Recommendation**: Complete ν=2, then pivot to ν=4 (genuinely open).

---

## Current Status (Updated Dec 19)

### Major Breakthrough: 30 Proven Lemmas

Three Aristotle runs completed with **zero sorry statements**:
- `aristotle_tuza_nu1_infrastructure.lean` - 11 lemmas
- `aristotle_tuza_parker_extended.lean` - 11 lemmas
- `aristotle_tuza_conflict_graph.lean` - 8 lemmas

### Proven Lemma Inventory

**nu1_infrastructure (11 lemmas)**:
- `trivial_bound` - τ ≤ 3ν (weak Tuza bound for ALL graphs)
- `nu_1_implies_intersect` - ν=1 triangles share vertex
- `edge_forced_of_nu_1` - edge constraint for ν=1
- `common_vertex_of_nu_1` - common vertex structure
- `K4_of_nu_1_witnesses` - K₄ structure in ν=1 case
- `exists_K4_of_nu_1_tau_gt_2` - K₄ exists when τ>2, ν=1
- `all_triangles_in_K4_of_nu_1` - triangles contained in K₄
- `K4_covering_number_le_2` - τ ≤ 2 for K₄ subgraphs

**parker_extended (11 lemmas)**:
- `lemma_2_2` - Parker's Lemma 2.2
- `lemma_2_3` - Parker's Lemma 2.3
- `inductive_bound` - Induction step
- `covering_number_le_two_of_subset_four` - τ ≤ 2 if triangles in ≤4 vertices
- `tau_star` - τ* bound
- `intersecting_triples_structure` - Structure of intersecting triples
- `tau_S_le_2` - τ(S) ≤ 2 bound
- `tuza_case_nu_0` - Base case ν=0

**conflict_graph (8 lemmas)**:
- `neighbors_are_packing_of_triangle_free_conflict_graph`
- `degree_le_three_of_triangle_free_conflict_graph`
- `local_covering_of_triangle_free`
- `edge_in_at_most_two_triangles`
- `neighbor_in_conflict_graph_not_in_packing`
- `not_neighbor_implies_edge_disjoint`
- `private_neighbor_is_edge_disjoint_from_rest`
- `private_neighbors_le_one`

### Summary
| Result | Status | Lines | Value |
|--------|--------|-------|-------|
| ν=0 | ✅ | Trivial | Base case |
| ν=1 | ✅ | 400+ | **First machine-verified** |
| τ ≤ 3ν | ✅ | ~120 | All graphs, weak bound |
| K₄, K₅ tight | ✅ | - | Confirmed tightness |
| Parker lemmas | ✅ | ~600 | lemma_2_2, 2_3, inductive_bound |
| ν=2 | 🔶 | 2 gaps | 90% complete - assembly needed |

### Counterexamples Discovered (Publication-worthy)
| Lemma | Counterexample | Insight |
|-------|----------------|---------|
| `TuzaReductionProperty` | 2 triangles sharing edge | Strong induction invalid |
| `two_edges_cover_nearby` | K₄ | "Nearby triangles" approach fails |
| `two_K4_almost_disjoint` | 6-vertex, \|s₁∩s₂\|=2 | K₄s can share edge |

---

## Parker's Paper vs Our Approach

| Aspect | Parker (2025) | Our Work |
|--------|---------------|----------|
| **Method** | Hypergraph (k-1)-matchings | K₄-extension + case analysis |
| **Key Lemma** | ν(S_e) = 1, inductive on T_e | exists_disjoint_in_K4 |
| **Scope** | ν ≤ 3 proven | ν ≤ 1 verified, ν=2 in progress |
| **Verification** | Human proof | **Machine-verified (Lean)** |
| **Counterexamples** | None mentioned | 3 flawed approaches disproved |

**Key Insight**: Methods are complementary, not redundant. Our K₄-extension is more constructive and amenable to formalization.

---

## Strategic Priorities (Grok-4 Analysis)

### Priority 1: Complete ν=2 (70% effort)
**Rationale**:
- Low risk (result now known to be true)
- 90% complete (2 gaps remain)
- Unique value: First machine-verified proof
- Different method from Parker

**Action Items**:
1. Monitor v12-minimal (8a5948f4) - running now
2. Queue v12-minimal.md (informal) when slot frees
3. If gaps remain, queue targeted submissions for each gap
4. Timeline: 1-2 weeks to completion

### Priority 2: Prepare ν=4 Scaffolding (30% effort)
**Rationale**:
- Genuinely open (not covered by Parker)
- Higher risk but higher reward
- Parker's method might extend (via (k-1)-matchings)

**Action Items**:
1. Study Parker's Lemma 2.2/2.3 for extension potential
2. Partially formalize Parker's ν=3 in Lean (~100 lines)
3. Design hybrid approach: Parker's hypergraph + our K₄ cases
4. After ν=2: Queue 2-3 scouting submissions for ν=4

### Fallback: Special Graph Classes (Option D)
If ν=4 stalls after 2-3 submissions:
- Planar graphs (Tuza 1985) - medium effort
- Treewidth ≤ 6 (Botler 2021) - medium effort
- Known results, but first formalizations

---

## Publication Strategy

### Paper 1: Formal Methods (ITP/CPP/JAR)
**Title**: "First Machine-Verified Proofs of Tuza's Conjecture Cases"
**Focus**:
- 400+ lines Lean code for ν=1
- Reusable verification infrastructure
- AI-assisted counterexample discovery (Aristotle)
- Comparison with Parker's human proof

**Target**: Q1 2026, after ν=2 completion

### Paper 2: Combinatorics (EJC/Graphs & Comb)
**Title**: "Alternative Proof of Tuza for ν≤2 via K₄-Extensions"
**Focus**:
- Novel K₄-extension method (different from Parker)
- Counterexamples to prior approaches
- τ ≤ 3ν general bound
- If ν=4 succeeds, include for higher impact

**Target**: Q2 2026

### ArXiv Strategy
- Upload unified preprint after ν=2: claim priority
- Title: "Machine-Verified Alternative Proofs for Tuza's Conjecture"
- Cross-cite both papers for synergy

### Potential Collaboration
- Reach out to Alex Parker for feedback
- "Our method complements yours—interested in co-authoring extension?"

---

## Aristotle Queue Management

With 5 slots available:

| Slot | Current Use | Priority |
|------|-------------|----------|
| 1 | v12-minimal.lean (running) | ν=2 formal |
| 2 | v12-minimal.md (queued) | ν=2 informal |
| 3 | v12-scaffolded (queued) | ν=2 backup |
| 4 | Reserved | ν=4 scout (after ν=2) |
| 5 | Reserved | ν=4 scout or gap target |

**Audit Finding**: Informal mode sometimes outperforms formal (v7 informal proved K₄/K₅ tightness that formal missed). Queue both modes for important results.

---

## Counterexample Publication Value

The 3 counterexamples have **independent publication value**:

1. **For formal methods**: Demonstrates AI/formal verification finding bugs humans missed
2. **For combinatorics**: Reveals which proof strategies DON'T work for Tuza
3. **Framing**: "Lessons from Formalizing Tuza: What Doesn't Work and Why"

Could be:
- Appendix in main paper
- Standalone short paper (e.g., "On Flawed Approaches to Tuza's Conjecture")
- Blog post for visibility

---

## Timeline

| Week | Goal | Submissions |
|------|------|-------------|
| Dec 19-25 | Complete ν=2 | v12-minimal, informal, scaffolded |
| Dec 26-Jan 1 | Polish ν=2, start ν=4 scaffold | Gap-targeted if needed |
| Jan 2-15 | Scout ν=4 | 2-3 hybrid submissions |
| Jan 15-31 | Assess ν=4, draft Paper 1 | - |
| Feb | Submit Paper 1 (formal methods) | - |
| Mar-Apr | Continue ν=4 or pivot to Option D | - |

---

## Key Decisions Made

1. ✅ **Continue ν=2** (first machine-verified, different method)
2. ✅ **Two separate papers** (formal methods + combinatorics)
3. ✅ **Pivot to ν=4 after ν=2** (genuinely open territory)
4. ✅ **Counterexamples have publication value** (include in papers)
5. ✅ **Use hybrid Parker/K₄ approach for ν=4**

---

## References

- Parker, A. (2025). "New bounds on a generalization of Tuza's conjecture." arXiv:2406.06501
- Haxell, P.E. (1999). "Packing and covering triangles in graphs." Discrete Math 195:251-254
- Tuza, Z. (1990). "A conjecture on triangles of graphs." Graphs & Comb 6:373-380
- Botler, F. et al. (2021). "On Tuza's conjecture for graphs with small treewidth."
