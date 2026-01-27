# Multi-Agent Audit: slot473 Tuza ν=4 Proof

**Date**: 2026-01-21
**Submission**: slot473_tuza_nu4_final_aristotle.lean (62 theorems, 0 sorry)

## Audit Status

| Agent | Status | Verdict |
|-------|--------|---------|
| **Gemini** | Complete | INCOMPLETE / FLAWED |
| **Codex** | Complete | Critical Issues - Does NOT prove conjecture |
| **Grok** | Complete | Mathematically unsound - Does NOT establish claim |

## Consensus: PROOF IS INVALID

Both independent audits identified the same fundamental flaws.

### Gap 1: No Actual Graph Modeling

**Codex** (lines 50-77):
> `isTriangle` is "card = 3" and `edgeHitsTriangle` is just set inclusion, with no reference to G's adjacency or to whether the candidate "edge" even belongs to G. It says nothing about covering triangles of a graph by edges of that graph.

**Impact**: The purported τ bounds do not connect to Tuza's conjecture.

### Gap 2: External Triangles Completely Ignored

**Gemini**:
> The "covers" only guard the four triangles in the fixed packing. This contradicts the audit requirement about handling external triangles—PATH_4 never mentions triangles outside the packing, so the slot472 adaptive reasoning is entirely absent here.

**Gemini** also notes:
> The difficulty of Tuza's conjecture lies entirely in covering the *external* triangles that share edges with the packing, which this proof largely ignores or handles incorrectly.

**Impact**: The core challenge of the conjecture is not addressed.

### Gap 3: Transfer Principle Not Proven

**Codex** (lines 449-476):
> The "transfer principle" section is purely informal prose followed by the numerology lemma `four_triangles_fit_in_fin12`. There is no construction of an injection, no statement relating a general graph's packing to one of the Fin 12 witnesses, and no preservation of edges/adjacency.

**Gemini**:
> This assumes that the graph G consists *only* of the vertices involved in the maximal packing M. Tuza's conjecture applies to the *entire* graph. External triangles often involve vertices outside V(M).

**Impact**: Nothing bridges Fin 12 to arbitrary graphs.

### Gap 4: Exhaustiveness Not Proven

**Codex** (lines 363-377):
> `all_edge_counts_exist` shows that for each edge count there exists some packing realizing it, not that every 4‑packing is isomorphic to one of those examples. There is no enumeration of non‑isomorphic intersection graphs.

**Impact**: Case analysis may be incomplete.

### Gap 5: Master Theorem Disconnected

**Codex** (lines 498-507):
> The supposed master theorem does not even mention graphs, ν, τ, or the previously defined packings. The quantified statement `∀ i : Fin 11, ∃ C ...` is discharged by choosing `cover_P1` for every `i`, which is unrelated to the pattern classification.

**Impact**: No part of the file actually proves "if ν(G)=4 then τ(G)≤8".

## What slot473 Actually Proves

> If we have 4 arbitrary 3-element subsets of Fin 12 with pairwise disjoint edges, then some 8-element set of 2-subsets intersects all four 3-subsets.

This is a **combinatorial lemma about sets**, not a graph theory theorem about Tuza's conjecture.

## Required Fixes

1. **Formal Graph Model**: Define `SimpleGraph V`, triangle = 3 vertices all mutually adjacent
2. **External Triangle Coverage**: Integrate slot472 adaptive reasoning
3. **Formal Transfer**: Prove injection preserving adjacency structure
4. **Exhaustiveness**: Formal proof that 11 patterns cover all cases
5. **Connect ν and τ**: Master theorem with proper Mathlib definitions

## Recommendations

**Gemini**:
> Focus on the "Safe Discard" or "S_e" approach: Prove that for every triangle in the packing, there is an edge e such that G - e has strictly smaller packing number, or use the Parker approach (τ(T_e) ≤ 2).

**Codex**:
> If using `native_decide`, the model must include "ghost" edges representing potential external triangles on *every* edge of the packing, not just a few selected ones.

## Grok-4 Analysis (Added 2026-01-21)

**Verdict**: Mathematically unsound, does not establish the claim

### Key Findings

**On `isTriangle`**:
> In graph theory, a triangle is a 3-cycle: a set of 3 vertices where every pair is connected by an edge. The definition only checks cardinality, treating any 3-set as a "triangle" without verifying the presence of edges. This is not a model of a graph at all—it's just set theory on subsets.

**On external triangles**:
> In a graph with ν(G)=4, there can be many triangles beyond the maximum packing. The proof constructs covers for the 11 intersection patterns but only verifies against the 4 in M, ignoring others. τ(G) requires hitting ALL triangles, not just the packing.

**On transfer principle**:
> General graphs can have arbitrary edges and vertices beyond the packing's ≤12, creating triangles not representable in Fin 12. Without a formal reduction proving that τ is determined by the induced subgraph on the packing vertices, the enumeration doesn't generalize.

**On what is actually proven**:
> Weaker property proven: For each of 11 intersection patterns of 4 edge-disjoint 3-sets on ≤12 elements, there exists a set of ≤8 2-sets that subsets into each of the 4. This is verified decidably on Fin 12, but it's just set-covering 4 sets, not hitting all triangles in a graph.

### Grok's Recommendations
> To Salvage: Redefine with actual graph structure (e.g., include an edge relation in Lean). Verify covers hit all possible triangles in the induced graph on the packing vertices, plus argue why external triangles are hit (e.g., via the "every triangle intersects packing edges" property, but prove a hitting set works globally).

## Files Referenced

- `/tmp/claude/-Users-patrickkavanagh-math/tasks/bfd7f98.output` - Gemini audit
- `/tmp/claude/-Users-patrickkavanagh-math/tasks/bd6b256.output` - Codex audit
- `submissions/nu4_final/slot473_tuza_nu4_final_aristotle.lean` - Audited file
