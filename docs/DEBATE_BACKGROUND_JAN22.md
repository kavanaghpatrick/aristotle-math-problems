# Multi-Agent Debate Background: Tuza ν=4 Proof Strategy

**Date**: January 22, 2026
**Participants**: Claude (Opus 4.5), Grok-4, Codex
**Objective**: Validate our approach to proving τ ≤ 8 for graphs with ν = 4

---

## 1. Problem Statement

**Tuza's Conjecture** (1981): For any graph G, τ(G) ≤ 2ν(G), where:
- ν(G) = triangle packing number (max edge-disjoint triangles)
- τ(G) = triangle covering number (min edges to hit all triangles)

**Our Target**: Prove τ(G) ≤ 8 for all graphs G with ν(G) = 4.

**Best Known**: Haxell (1999) proved τ ≤ 3ν - 2 in general. Tuza ν=3 was proven by Haxell (1996).

---

## 2. What We Have Proven (Phase 1 - 108 Files, 0 Sorry)

### Concrete Pattern Verification on Fin n
| Pattern | τ Bound | Key File |
|---------|---------|----------|
| Scattered (E₄) | τ ≤ 4 | slot376 |
| Star (K₁,₃) | τ ≤ 4 | slot375 |
| Three-share-v | τ ≤ 4 | slot378 |
| Two-two-vw | τ ≤ 4 | slot379 |
| Cycle₄ | τ ≤ 4 | slot377 |
| PATH₄ (hardest) | τ ≤ 8 | slot407 |
| Exhaustiveness | 11 patterns | slot466 |

### Critical Proven Lemma (slot412 - 0 sorry, 12 theorems)
```lean
theorem not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) ... :
    ¬((S_e_edge G M a b c).Nonempty ∧
      (S_e_edge G M b c a).Nonempty ∧
      (S_e_edge G M a c b).Nonempty)
```

**Meaning**: For any packing element e = {a,b,c}, at most 2 of its 3 edges can have "private externals" (triangles sharing that specific edge but edge-disjoint from other M-elements).

**Why It's Critical**: If all 3 edges had externals T₁, T₂, T₃, we could form a 6-packing {T₁, T₂, T₃, B, C, D}, contradicting ν=4.

---

## 3. The Gap: Phase 1 ≠ General Theorem

### Multi-Agent Critique (Jan 22, 2026)

**Grok-4 Findings**:
1. Pattern proofs work on specific Fin n constructions, not arbitrary G
2. Fin 12 doesn't generalize to graphs with arbitrarily many vertices
3. No remainder handling for non-packing triangles
4. Edge-sharing between triangles not addressed

**Codex Findings**:
5. No actual graph modeling - triangles treated as size-3 subsets
6. Missing transfer principle from arbitrary graph to Fin 12
7. No ν(G)/τ(G) relation - master theorems quantify over finite index

**Consensus**: "A correct proof must talk about a SimpleGraph V, define ν(G) and τ(G) via packings/covers of actual triangles, and quantify over ALL triangles of G."

---

## 4. Current Approach (slot504)

### Key Definitions
```lean
-- S_e: Triangles sharing edge with e but edge-disjoint from other M-elements
def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t =>
    t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- S_e_edge: S_e elements using specific edge {a,b} (excluding c)
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)
```

### Proof Chain
```
slot412 (PROVEN)           slot504 (3 sorry)           Main Theorem
─────────────────────────────────────────────────────────────────────
not_all_three_edge_types → tau_Se_le_2 → tau_le_8_from_Se_bound
         ↑                       ↑                    ↑
   6-packing             Case analysis:        Union of 4 covers
   contradiction         "pick 2 of 3 edges"   |E'| ≤ 4×2 = 8
```

### slot504 Remaining Sorries (3)

1. **tau_Se_le_2**: Given `not_all_three_edge_types`, construct 2-edge cover for S_e
   - WLOG edges {a,b} and {b,c} have externals, {a,c} doesn't
   - Cover = {s(a,b), s(b,c)} hits all of S_e
   - Difficulty: Tier 1-2 (case analysis)

2. **triangle_in_some_Se_or_M**: Every triangle T is in M or in some S_e
   - Follows from maximality of M
   - If T ∉ M, T shares edge with some e ∈ M
   - Need: T shares with exactly one (or handle bridges)
   - Difficulty: Tier 2 (pigeonhole)

3. **tau_le_8_from_Se_bound**: Assemble union of covers
   - For each e ∈ M, get E_e with |E_e| ≤ 2 covering S_e
   - E' = ⋃ E_e has |E'| ≤ 8
   - Every triangle hit by some E_e
   - Difficulty: Tier 2 (union construction)

---

## 5. FALSE LEMMAS (Critical to Avoid!)

| # | Lemma | Evidence | Why False |
|---|-------|----------|-----------|
| 1 | `local_cover_le_2` | AI | 4 M-edges at v, each Tᵢ uses unique edge → 2 edges miss 2 triangles |
| 6 | `external_share_common_vertex` | AI | Externals from different M-elements A,B don't share apex |
| 8 | `link_graph_bipartite` | AI | König approach invalid |
| 11 | `self_loop_cover` | trivial | s(v,v) not a graph edge |
| 14 | `bridge_auto_covered_by_pigeonhole` | AI | Covering vertex v ≠ covering triangles containing v |
| 29 | `sym2_cover_cardinality` | ARISTOTLE | A.sym2 includes self-loops! Never use for edge enumeration |

### Key Anti-Patterns
- **Never** use `Finset.sym2` for edge enumeration (includes s(v,v))
- **Never** claim 2 edges cover ALL triangles at a vertex
- **Never** assume bridges are automatically covered
- **Always** require `E ⊆ G.edgeFinset` in cover definitions

---

## 6. Alternative Approaches Considered

### A. Transfer Principle (slot463)
- Embed any 4-packing into Fin 12 (preserves structure)
- Apply verified Fin 12 results
- **Problem**: Doesn't handle triangles outside the packing

### B. InteractionGraph (slot458)
- Define graph on M-edges where edge = shared by external
- Find 4-edge independent set (one per M-element)
- Discard those 4, cover with remaining 8
- **Problem**: Complex degree bounds, bridge handling unclear

### C. Direct S_e Decomposition (slot474/504) ← CURRENT
- Partition non-M triangles into S_e sets
- Use 6-packing constraint for τ(S_e) ≤ 2
- Combine: 4 × 2 = 8
- **Advantage**: Directly uses proven slot412 lemma

---

## 7. Open Questions for Debate

### Q1: Is the S_e decomposition complete?
Does every non-M triangle belong to exactly one S_e, or can triangles share edges with multiple M-elements (bridges)?

**Current assumption**: The maximality argument assigns T to some e, but T might share edges with multiple M-elements.

### Q2: How to handle bridges?
A bridge T shares edges with 2+ M-elements. Options:
- (a) Bridges are covered by M-edges (any edge from shared M-elements hits T)
- (b) Count bridges separately with τ(bridges) ≤ k for some k
- (c) Prove bridges don't exist under ν=4 (seems false)

### Q3: Is tau_Se_le_2 actually true?
The proof assumes:
- At most 2 edge-types have externals (proven by slot412)
- Therefore 2 edges suffice

**Concern**: What if T uses edge {a,b} but our cover picks {b,c} and {a,c}?

**Answer**: T ∈ S_e_edge(a,b,c) means T uses {a,b}. If we pick cover = {s(a,b), s(b,c)}, then s(a,b) ∈ T.sym2. The case analysis must align cover choice with non-empty edge-types.

### Q4: Does the union double-count?
If E_e and E_f both contain the same edge (e.g., shared vertex), the union might have fewer than 8 edges. This is fine (helps us), but need to ensure coverage.

### Q5: Is SimpleGraph V the right abstraction?
Our proofs use:
- `G.cliqueFinset 3` for triangles
- `G.edgeFinset` for cover edges
- `(t ∩ e).card ≥ 2` for edge-sharing

Is this equivalent to the standard graph-theoretic definition?

---

## 8. Key Insight Summary

The **6-packing constraint** is the linchpin:

```
ν(G) = 4
    ↓
Any packing M has |M| = 4
    ↓
For any e ∈ M, if all 3 edges had externals T₁, T₂, T₃:
  {T₁, T₂, T₃} ∪ (M \ {e}) would be a 6-packing
    ↓
Contradiction! So at most 2 edges have externals.
    ↓
2 edges from e cover all of S_e
    ↓
4 × 2 = 8 edges total
```

---

## 9. Requested Debate Focus

1. **Validate the S_e decomposition approach** - Is it sound?
2. **Identify any gaps in the tau_Se_le_2 argument**
3. **Propose concrete fixes for bridge handling**
4. **Assess: Can Aristotle close the 3 remaining sorries?**
5. **Alternative: Is there a simpler path we're missing?**

---

## 10. Files for Reference

| File | Status | Content |
|------|--------|---------|
| `slot412_6packing_proof_aristotle.lean` | 0 sorry | `not_all_three_edge_types` PROVEN |
| `slot504_tau_Se_le_2.lean` | 3 sorry | Bridging file (submitted to Aristotle) |
| `slot474_tuza_nu4_general.lean` | 6 sorry | Earlier attempt, overlaps with slot412 |
| `docs/FALSE_LEMMAS.md` | Reference | All known false lemmas |
| `submissions/tracking.db` | Database | Full submission history |

---

*Prepared for multi-agent debate by Claude Opus 4.5*
