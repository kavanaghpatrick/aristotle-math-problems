# FALSE LEMMAS - DO NOT USE

> **⚠️ AUTO-GENERATED FILE** - Do not edit directly!
> Source of truth: `submissions/tracking.db` table `false_lemmas`

**Last generated**: 2026-01-01 22:22:07

This document lists lemmas that have been PROVEN FALSE. Do not use these in any proof attempts.

---

## Quick Reference

| Evidence | Meaning | Count |
|----------|---------|-------|
| 🔴 ARISTOTLE-VERIFIED | Actual Aristotle counterexample/bug | 8 |
| 🟠 AI-VERIFIED | AI agents verified the math | 10 |
| 🟡 REASONING-BASED | Sound reasoning, no formal verification | 3 |
| ⚪ TRIVIALLY FALSE | Obvious logical error | 2 |

**Total**: 23 FALSE lemmas documented

---

## Summary Table

| # | Lemma | Evidence | Source |
|---|-------|----------|--------|
| 1 | `local_cover_le_2` | 🟠 | Codex 2025-12-26 |
| 2 | `avoiding_covered_by_spokes` | ⚪ | Logical analysis 2025-12-26 |
| 3 | `bridge_absorption` | 🔴 | Aristotle 2025-12-25 |
| 4 | `trianglesContainingVertex_partition` | 🟡 | Gemini 2025-12-26 |
| 5 | `support_sunflower_tau_2` | 🟡 | Definition analysis 2025-12-28 |
| 6 | `external_share_common_vertex` | 🟠 | AI debate 2025-12-29 |
| 7 | `sunflower_cover_at_vertex_2edges` | 🟠 | Gemini + Codex 2025-12-29 |
| 8 | `tau_pair_le_4` | ⚪ | Multi-agent consensus (6 agents) 2024-12-30 |
| 9 | `fixed_8_edge_M_subset` | 🟡 | Grok 2025-12-31 |
| 10 | `krivelevich_bound_forall_w` | 🔴 | Aristotle 2025-12-31 |
| 11 | `nu_star_equals_nu_automatic` | 🟠 | Gemini literature search 2026-01-01 |
| 12 | `externals_sum_le_totalSlack` | 🔴 | Aristotle 2026-01-01 |
| 13 | `covering_selection_exists` | 🔴 | Aristotle 2026-01-01 |
| 14 | `proof_by_type_escape` | 🔴 | Aristotle bug 2026-01-02 |
| 15 | `self_loop_witness` | 🔴 | Aristotle bug 2026-01-02 |
| 16 | `helly_three_triangles` | 🟠 | Codex debate 2026-01-02 |
| 17 | `externals_partition_by_M_element` | 🟠 | Multi-agent 2026-01-03 |
| 18 | `common_edge_in_cluster` | 🟠 | Multi-agent 2026-01-03 |
| 19 | `cluster_weight_decomposition` | 🟠 | Multi-agent 2026-01-03 |
| 20 | `four_vertex_cover` | 🔴 | Aristotle 2026-01-03 |
| 21 | `trianglesThroughVinS domain` | 🟠 | Multi-agent 2026-01-03 |
| 22 | `bridge_externals_share_apex` | 🔴 | **ARISTOTLE COUNTEREXAMPLE** slot227 2026-01-04 |
| 23 | `tau_le_8_scattered` | 🔴 | Propeller counterexample 2026-01-04 |
| 24 | `same_edge_share_external_vertex` | 🟠 | Manual counterexample 2026-01-04 |
| 25 | `all_externals_share_apex` | 🟠 | Depends on FALSE lemma #24 2026-01-04 |

---

## Pattern 1: local_cover_le_2

**Status**: ❌ FALSE | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
2 edges from M_edges_at suffice to cover all triangles sharing an M-edge at vertex v
```

**Counterexample**:
```
At v_ab: Add vertex x with triangles T₁={v_ab,v_da,x}, T₂={v_ab,a_priv,x}, T₃={v_ab,v_bc,x}, T₄={v_ab,b_priv,x}. Each uses different M-edge, all share {v_ab,x} so ν stays 4. Need 4 M-edges to hit all.
```

**Why False**:
M_edges_at contains 4 edges at v_ab. Each Tᵢ uses a unique M-edge. Any 2-edge subset misses at least 2 triangles.

**Impact**: Breaks 4×2=8 sunflower covering approach. Need 4 edges per vertex, not 2.

**Avoid Pattern**: Never assume 2 M-edges suffice at shared vertex. Check how many distinct M-edges triangles use.

**Correct Approach**: Use adaptive cover with non-M-edges, or accept τ ≤ 12 (3 per vertex).

**Source**: Codex (2025-12-26) | Slot: N/A

---

## Pattern 2: avoiding_covered_by_spokes

**Status**: ❌ FALSE | ⚪ TRIVIALLY FALSE

**Statement** (FALSE):
```
Triangles avoiding vertex v can be covered by spokes from v
```

**Counterexample**:
```
Triangle {a,b,x} shares base edge {a,b} with e={v,a,b}. t avoids v, so v ∉ t. No spoke {v,*} can be in t.
```

**Why False**:
If t avoids v, then v ∉ t. Spokes by definition contain v. Therefore spokes ∉ t.sym2. This is basic set theory.

**Impact**: Cannot use spokes to cover avoiding triangles.

**Avoid Pattern**: Never claim spokes cover triangles that avoid the spoke vertex.

**Correct Approach**: Use BASE EDGES {a,b},{c,d} for avoiding triangles, not spokes.

**Source**: Logical analysis (2025-12-26) | Slot: N/A

---

## Pattern 3: bridge_absorption

**Status**: ❌ FALSE | 🔴 ARISTOTLE-VERIFIED

**Statement** (FALSE):
```
A cover that hits all triangles in S_e and S_f also hits bridges between e and f
```

**Counterexample**:
```
Aristotle 5-vertex: e={0,1,2}, f={0,3,4}, bridge t={0,1,3}, cover C={{1,2},{3,4}} covers S_e∪S_f but NOT bridge t.
```

**Why False**:
Bridges share vertices with e,f but may not share edges with S_e or S_f triangles. The cover hits triangles ONLY sharing edge with one element.

**Impact**: Cannot assume S_e∪S_f cover handles bridges. Must handle bridges separately.

**Avoid Pattern**: Never assume bridge coverage comes free from S covers.

**Correct Approach**: Handle bridges separately with tau_X_le_2. Total: τ(S_e) + τ(S_f) + τ(X_ef).

**Source**: Aristotle (2025-12-25) | Slot: N/A

---

## Pattern 4: trianglesContainingVertex_partition

**Status**: ❌ FALSE | 🟡 REASONING-BASED

**Statement** (FALSE):
```
Partitioning triangles by which shared vertex they contain gives correct bounds
```

**Counterexample**:
```
Triangle t={v_ab, v_cd, c3} contains v_ab but shares M-edge only at v_cd (with C). local_cover_le_2 at v_ab cannot cover t.
```

**Why False**:
A triangle can contain shared vertex v but share its M-edge at a DIFFERENT shared vertex. The partition by containment doesnt match M-edge sharing.

**Impact**: Wrong partition leads to incorrect coverage analysis.

**Avoid Pattern**: Dont partition by vertex containment.

**Correct Approach**: Use trianglesSharingMEdgeAt v (partition by which vertex the M-edge is incident to).

**Source**: Gemini (2025-12-26) | Slot: N/A

---

## Pattern 5: support_sunflower_tau_2

**Status**: ❌ FALSE | 🟡 REASONING-BASED

**Statement** (FALSE):
```
At shared vertex v, 2 edges suffice to cover all triangles sharing an M-edge at v
```

**Counterexample**:
```
At v_ab: trianglesSharingMEdgeAt contains {A, B, T1, T2, T3, T4}. {v_ab,x} covers T1-T4 but NOT A,B (x is external, x ∉ A, x ∉ B). Need 3+ edges.
```

**Why False**:
trianglesSharingMEdgeAt INCLUDES the M-elements A and B, not just external triangles! M-elements dont contain external vertices, so {v,x} cant hit them.

**Impact**: The 4×2=8 approach is invalid. Need to separately cover M-elements and externals.

**Avoid Pattern**: Dont confuse trianglesSharingMEdgeAt (includes M) with external triangles only.

**Correct Approach**: Separate M-coverage from external-coverage. But see Pattern 6 - externals dont share common vertex either!

**Source**: Definition analysis (2025-12-28) | Slot: N/A

---

## Pattern 6: external_share_common_vertex

**Status**: ❌ FALSE | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
All external triangles at shared vertex v share a common external vertex x
```

**Counterexample**:
```
CounterexampleG: M={A,B,C,D} with A={0,1,2}, B={0,3,4}, C={3,7,8}, D={7,1,9}. At v_ab=0: T1={0,1,5} uses {0,1} from A, T2={0,3,6} uses {0,3} from B. T1∩T2={0} only!
```

**Why False**:
External triangles can use edges from DIFFERENT M-triangles (A vs B) at the same shared vertex. Each M-triangle contributes different M-edges, so externals borrowing from different M-triangles share only v.

**Impact**: The 4+4 covering approach (4 M-edges + 4 external-via-{v,x}) is INVALID. Need multiple edges for externals.

**Avoid Pattern**: Never assume external triangles share common vertex. They can independently use edges from different M-triangles.

**Correct Approach**: Unknown - this is a major blocker. May need LP relaxation or accept τ ≤ 12.

**Source**: AI debate (2025-12-29) | Slot: slot131_v2

---

## Pattern 7: sunflower_cover_at_vertex_2edges

**Status**: ❌ FALSE | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
At each shared vertex v, 2 edges suffice to cover all triangles containing v
```

**Counterexample**:
```
At v_ab: A={v_ab,v_da,a_priv}, B={v_ab,v_bc,b_priv}. Externals T1-T4 all share {v_ab,x}. Edge {v_ab,x} covers T1-T4 but NOT A,B (x∉A, x∉B). A.sym2 ∩ B.sym2 = ∅. Minimum 3 edges needed. slot152 claims 2 - IMPOSSIBLE.
```

**Why False**:
At v_ab, triangles come from TWO M-elements (A and B). Even if externals share x, A and B dont contain x. Need: edge for A + edge for B + edge for externals = 3+ edges.

**Impact**: The 4×2=8 sunflower approach is INVALID. Actual bound: 4×3=12 (matches slot113).

**Avoid Pattern**: Dont assume 2 edges per shared vertex suffice.

**Correct Approach**: Accept τ ≤ 12 or find adaptive approach. M-elements require separate coverage from externals.

**Source**: Gemini + Codex (2025-12-29) | Slot: N/A

---

## Pattern 8: tau_pair_le_4

**Status**: ❌ FALSE | ⚪ TRIVIALLY FALSE

**Statement** (FALSE):
```
τ(T_pair) ≤ 4: 4 edges suffice to cover all triangles sharing edge with A or B
```

**Counterexample**:
```
Avoiding triangles cannot be covered by spokes. Spokes contain v, avoiding triangles do not contain v.
```

**Why False**:
T_pair splits into containing(v) and avoiding(v). Containing needs 4 spokes. Avoiding needs 2 base edges. Total = 6, not 4. The lemma avoiding_covered_by_spokes is TRIVIALLY FALSE.

**Impact**: N/A

**Avoid Pattern**: N/A

**Correct Approach**: Unknown

**Source**: Multi-agent consensus (6 agents) (2024-12-30) | Slot: N/A

---

## Pattern 9: fixed_8_edge_M_subset

**Status**: ❌ FALSE | 🟡 REASONING-BASED

**Statement** (FALSE):
```
A specific fixed 8-edge subset of M-edges covers all triangles in Cycle_4
```

**Counterexample**:
```
Triangle T={a_priv, v_da, z} shares edge {a_priv, v_da} with A. Check: v_ab∉T, v_bc∉T, v_cd∉T, b_priv∉T, c_priv∉T, d_priv∉T. NONE of the 8 edges hit T!
```

**Why False**:
Any 8-subset of 12 M-edges must omit 4 edges. The omitted edges are {v_da,a_priv}, {v_ab,b_priv}, {v_bc,c_priv}, {v_cd,d_priv}. External triangles sharing those edges are uncovered.

**Impact**: NO fixed 8-edge subset of M-edges works universally. τ ≤ 8 requires ADAPTIVE cover or non-M-edges.

**Avoid Pattern**: Dont pick a fixed 8-edge subset of M-edges.

**Correct Approach**: Either use all 12 M-edges (τ ≤ 12) or use adaptive selection that includes non-M-edges when needed.

**Source**: Grok (2025-12-31) | Slot: N/A

---

## Pattern 10: krivelevich_bound_forall_w

**Status**: ❌ FALSE | 🔴 ARISTOTLE-VERIFIED

**Statement** (FALSE):
```
For any fractional packing w, τ ≤ 2 × weight(w)
```

**Counterexample**:
```
K₃ with w=0: τ(K₃)=1 but 2×packingWeight(0)=0. So τ=1 > 0.
```

**Why False**:
The bound τ ≤ 2ν* uses the SUPREMUM over all fractional packings, not any particular packing. With w=0, the bound becomes τ ≤ 0 which is false for any graph with triangles.

**Impact**: slot55 LP approach gave wrong bound direction

**Avoid Pattern**: Never state Krivelevich as ∀w. τ ≤ 2*packingWeight(w)

**Correct Approach**: Use τ ≤ 2*ν* where ν* = sSup{packingWeight(w) : isFractionalPacking(w)}

**Source**: Aristotle (2025-12-31) | Slot: N/A

---

## Pattern 11: nu_star_equals_nu_automatic

**Status**: ❌ FALSE | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
The fractional packing number equals the integer packing number for any graph
```

**Counterexample**:
```
Yuster (1996): Exists infinite family with nu*(G) - nu(G) = Omega(n^1.5). Haxell-Rodl: gap can be o(n^2).
```

**Why False**:
Fractional LP relaxation can achieve MORE than integer optimum. LP duality shows nu* = tau* (fractional cover), but tau* can exceed nu in general. For nu=4, need SPECIFIC proof that nu* <= 4.

**Impact**: Breaks all approaches assuming nu* = nu without proof. Cannot just say indicator achieves 4 therefore nu* = 4.

**Avoid Pattern**: Never assume nu* = nu. Always construct explicit dual certificate.

**Correct Approach**: Use CoveringSelection: select |M| M-edges covering all triangles. Prove covering_selection_exists. Then weak duality gives nu* <= |M|.

**Source**: Gemini literature search (2026-01-01) | Slot: N/A

---

## Pattern 12: externals_sum_le_totalSlack

**Status**: ❌ FALSE | 🔴 ARISTOTLE-VERIFIED

**Statement** (FALSE):
```
External triangles weight sum is bounded by total slack (M.card - M.sum w)
```

**Counterexample**:
```
G6: Central triangle {0,1,2} in M, externals {0,1,3}, {1,2,4}, {2,0,5} each with w=1. externals.sum=3 > totalSlack=1
```

**Why False**:
Externals can share DIFFERENT M-edges, each consuming slack independently. 3 externals can each use a different M-edge, summing to 3 while slack is only 1.

**Impact**: Breaks the direct exchange argument for ν* ≤ 4

**Avoid Pattern**: Never assume externals sum ≤ totalSlack. Correct bound is ≤ 3×totalSlack.

**Correct Approach**: Use corrected bound externals_sum_le_three_totalSlack or try CoveringSelection approach

**Source**: Aristotle (2026-01-01) | Slot: slot172

---

## Pattern 13: covering_selection_exists

**Status**: ❌ FALSE | 🔴 ARISTOTLE-VERIFIED

**Statement** (FALSE):
```
There exists a selection of |M| edges from M-edges that covers all triangles
```

**Counterexample**:
```
G_ex on Fin 5: edges {0,1},{1,2},{2,0},{0,3},{1,3},{1,4},{2,4}. M={{0,1,2}}. Triangles: {0,1,2},{0,1,3},{1,2,4}. Need 1 edge to cover 3 triangles - impossible.
```

**Why False**:
Different triangles may require DIFFERENT M-edges to be covered. When externals at shared vertices use edges from different parts of the M-triangle, no single edge covers all.

**Impact**: CoveringSelection approach for ν* ≤ 4 is INVALID

**Avoid Pattern**: Never assume |M| edges suffice. The weak duality argument requires a valid covering selection which may not exist.

**Correct Approach**: Need weaker bound: |S| ≤ 2|M| (gives τ ≤ 8 directly) or case-by-case analysis

**Source**: Aristotle (2026-01-01) | Slot: slot174

---

## Pattern 14: proof_by_type_escape

**Status**: ❌ FALSE PROOF TECHNIQUE | 🔴 ARISTOTLE BUG

**Statement** (FALSE TECHNIQUE):
```
Using `contrapose! + specialize @this (Fin n) + simp +decide` to "prove" a theorem
```

**Counterexample**:
```lean
-- slot179 "proof" of tau_externals_le_2:
have := @no_bridge_disjoint;
specialize @this ( Fin 6 );
contrapose! this;
simp +decide [ sharesEdgeWith ];
refine' ⟨ ⟨ inferInstance ⟩, _ ⟩;
exists { 0, 1, 2 }, by decide, { 3, 4, 5 }, by decide, { 0, 1, 3 }, by decide;
```

**Why False**:
This escapes the proof obligation by:
1. Taking `contrapose!` which negates the goal
2. Specializing a helper lemma to a FINITE TYPE (Fin 6)
3. Using `simp +decide` which can decide finite computations
4. Constructing a concrete counterexample in the FINITE TYPE

The "proof" only shows something about Fin 6, NOT about arbitrary V. The original theorem quantifies over all V but the proof escapes to a specific finite type.

**Impact**: Aristotle may CLAIM theorems are proven when they are NOT. Must verify proofs manually.

**Avoid Pattern**: NEVER trust Aristotle's "PROVEN" header. Read the FULL proof. Check for:
- `contrapose!` followed by `simp +decide`
- Specialization to `Fin n` types
- `decide` tactics on goals with type variables

**Correct Approach**: Manually verify every "proven" theorem. Look for proof-by-type-escape pattern.

**Source**: Aristotle bug (2026-01-02) | Slot: slot179, slot177

---

## Pattern 15: self_loop_witness

**Status**: ❌ FALSE PROOF TECHNIQUE | 🔴 ARISTOTLE BUG

**Statement** (FALSE TECHNIQUE):
```
Using Sym2.mk(x,x) as witness for shared edge existence
```

**Counterexample**:
```lean
-- slot180 "proof" of two_externals_share_edge:
obtain ⟨ x, hx ⟩ := Finset.card_pos.mp hT₁_inter_T₂;
specialize h_no_common ( Sym2.mk ( x, x ) ) ;
simp_all +decide ;
```

**Why False**:
`Sym2.mk(x,x)` represents a SELF-LOOP `s(x,x)`. In a SimpleGraph:
1. `G.Adj x x = False` (no self-loops in simple graphs)
2. `s(x,x) ∉ G.edgeFinset`
3. Downstream proofs like `shares_edge_implies_two_vertices` require `u ≠ v`

The witness is technically in `T.sym2` (Finset.sym2 includes self-loops) but:
- NOT a valid graph edge
- Breaks edge-sharing lemmas that require distinct vertices

**Impact**: Proofs that use self-loop witnesses are UNSOUND for graph-theoretic conclusions.

**Avoid Pattern**: Check Aristotle outputs for `Sym2.mk(x,x)` patterns. Any shared "edge" must have `u ≠ v`.

**Correct Approach**: Strengthen theorem statements to require proper edges:
```lean
∃ e ∈ G.edgeFinset, e ∈ T₁.sym2 ∧ e ∈ T₂.sym2  -- NOT just ∃ e, e ∈ T₁.sym2 ∧ e ∈ T₂.sym2
```

**Source**: Aristotle bug (2026-01-02) | Slot: slot180

---

## Pattern 16: helly_three_triangles

**Status**: ❌ FALSE | 🟠 AI-VERIFIED (Codex)

**Statement** (FALSE):
```
If T₁, T₂, T₃ are triangles where every pair shares an edge, then all three share a common edge.
(Helly property for triangles with edge-sharing)
```

**Counterexample**:
```
T₁ = {a, b, x}
T₂ = {b, c, x}
T₃ = {a, c, x}

Pairwise edge-sharing:
- T₁ ∩ T₂ share edge {b, x}
- T₁ ∩ T₃ share edge {a, x}
- T₂ ∩ T₃ share edge {c, x}

BUT: T₁ ∩ T₂ ∩ T₃ = {x} (just vertex x, NO common edge)
```

**Why False**:
A triangle has 3 edges. Three triangles can have pairwise edge-sharing using DIFFERENT edges of each triangle. The Helly property requires that pairwise intersection implies total intersection - this is TRUE for convex sets but FALSE for edges of triangles.

**Impact**: slot184_helly_external_common_edge is INVALID. Cannot use Helly to get τ(externals) ≤ 1.

**Avoid Pattern**: Never assume pairwise edge-sharing implies a common edge for ≥3 triangles.

**Correct Approach**: Use VERTEX intersection instead:
- **FAN STRUCTURE INSIGHT**: Even though externals of A don't share a common edge, they share a common VERTEX (the fan apex x).
- This gives τ(Ext(A)) ≤ 3 via spoke edges {a,x}, {b,x}, {c,x}.

**Source**: Codex multi-agent debate (2026-01-02) | Slot: slot184

---

## KEY INSIGHT: Fan Structure of Externals

**Status**: ✅ TRUE INSIGHT (not a false lemma)

**Statement**:
```
All externals of the SAME M-element A share a common VERTEX x (the "fan apex").
They form a "fan" structure centered at x, using different edges of A but all containing x.
```

**Proof**:
1. By slot182: Two externals of A share an edge (5-packing contradiction)
2. If T₁ = {a,b,x₁} uses edge {a,b} of A, and T₂ = {b,c,x₂} uses edge {b,c} of A
3. T₁, T₂ must share an edge. The only possibilities lead to x₁ = x₂ (analysis in slot182 debate)
4. So all externals using different A-edges share the same external vertex x

**Implication**:
- τ(Ext(A)) ≤ 3 (spoke edges {a,x}, {b,x}, {c,x} cover all externals)
- NOT τ ≤ 1 as hoped (Helly fails)
- For cycle_4: 4 M-edges + 4×3 = 16 edges worst case, but overlap gives τ ≤ 12

**Source**: Multi-agent consensus (2026-01-02)

---

## Pattern 17: externals_partition_by_M_element

**Status**: ❌ FALSE | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
In cycle_4, every external triangle shares a 2-edge with EXACTLY ONE M-element.
```

**Counterexample**:
```
M = {A, B, C, D} with A ∩ B = {v_ab}
A = {v_ab, v_da, a_priv}
B = {v_ab, v_bc, b_priv}

External t = {v_ab, a_priv, b_priv}

Check:
- t ∩ A = {v_ab, a_priv} → shares edge {v_ab, a_priv} with A
- t ∩ B = {v_ab, b_priv} → shares edge {v_ab, b_priv} with B

t shares edges with BOTH A and B!
```

**Why False**:
Triangles at shared vertices can use vertices from BOTH adjacent M-elements. If a' ∈ A \ B and b' ∈ B \ A, then {v_ab, a', b'} is a valid triangle (if edges exist) that shares distinct edges with both A and B.

**Impact**: The 4+4 approach is INVALID. Externals do NOT partition cleanly across M-elements. The sum decomposition in slot222 is wrong.

**Avoid Pattern**: Never assume externals partition by M-element. Adjacent M-elements share a vertex, allowing triangles to straddle both.

**Correct Approach**: Unknown. May need entirely different approach to cycle_4.

**Source**: Multi-agent review (2026-01-03) | Slot: slot222

---

## Pattern 18: common_edge_in_cluster

**Status**: ❌ FALSE | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
All triangles in {X} ∪ externalsOf(X) share a common edge e ∈ X.
```

**Counterexample**:
```
X = {a, b, c} (M-element)
T₁ = {a, b, x} (external sharing edge {a,b})
T₂ = {b, c, x} (external sharing edge {b,c})
T₃ = {a, c, x} (external sharing edge {a,c})

Pairwise edge-sharing (slot182 satisfied):
- T₁ and T₂ share edge {b, x}
- T₁ and T₃ share edge {a, x}
- T₂ and T₃ share edge {c, x}

Common edges:
- X ∩ T₁ edges = {{a,b}}
- X ∩ T₂ edges = {{b,c}}
- X ∩ T₃ edges = {{a,c}}

NO common edge among {X, T₁, T₂, T₃}!
```

**Why False**:
This is the same issue as Pattern 16 (helly_three_triangles). Pairwise edge-sharing does NOT imply a common edge. The "sunflower center" exists as a VERTEX (x), not an edge. Each external uses a DIFFERENT edge of X.

**Impact**: The cluster_weight_le_1 lemma in slot222 is FALSE. Cannot bound cluster weight via single edge constraint.

**Avoid Pattern**: Never assume externals of X share a common edge. They share a common VERTEX (the fan apex), but use different edges of X.

**Correct Approach**: Use fan structure: externals of X form a fan around apex vertex x. Cover requires up to 3 edges {a,x}, {b,x}, {c,x} - NOT 1 edge.

**Source**: Multi-agent review (2026-01-03) | Slot: slot222

---

## Pattern 19: cluster_weight_decomposition

**Status**: ❌ FALSE | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
M.sum w + externals.sum w ≤ Σ_X (w(X) + externalsOf(X).sum w)
```

**Counterexample**:
```
Let E = externals, E_X = externalsOf(X), E_multi = externals sharing edges with 2+ M-elements

By Pattern 17: E_multi is NON-EMPTY (triangles like {v_ab, a', b'})

E = E_A ⊔ E_B ⊔ E_C ⊔ E_D ⊔ E_multi (disjoint union)

LHS = M.sum w + E.sum w
    = M.sum w + E_A.sum w + E_B.sum w + E_C.sum w + E_D.sum w + E_multi.sum w

RHS = (w(A) + E_A.sum w) + (w(B) + E_B.sum w) + (w(C) + E_C.sum w) + (w(D) + E_D.sum w)
    = M.sum w + E_A.sum w + E_B.sum w + E_C.sum w + E_D.sum w

LHS - RHS = E_multi.sum w ≥ 0

Therefore LHS ≥ RHS, which means the inequality LHS ≤ RHS is FALSE.
```

**Why False**:
Externals sharing edges with multiple M-elements (E_multi) are NOT captured by the sum Σ_X externalsOf(X). The RHS misses these triangles entirely, making it SMALLER than LHS.

**Impact**: The proof of nu_star_le_4_cycle4 in slot222 is invalid. The final calc chain has the wrong direction.

**Avoid Pattern**: Never assume externals partition perfectly. Account for "bridge" externals that straddle multiple M-elements.

**Correct Approach**: Unknown. The LP approach may need fundamentally different structure for cycle_4.

**Source**: Multi-agent review (2026-01-03) | Slot: slot222

---

## Pattern 20: four_vertex_cover (Link Graph König approach)

**Status**: ❌ FALSE | 🔴 ARISTOTLE-VERIFIED

**Statement** (FALSE):
```lean
theorem four_vertex_cover (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (hS : S.card ≤ 4)
    (h_ind : ∃ u w, u ∈ S ∧ w ∈ S ∧ u ≠ w ∧ ¬H.Adj u w) :
    ∃ C : Finset V, C.card ≤ 2 ∧ C ⊆ S ∧
      ∀ e : Sym2 V, e ∈ H.edgeFinset → (∃ v ∈ e, v ∈ S) → ∃ v ∈ C, v ∈ e
```
"A 4-vertex graph with α ≥ 2 has a 2-vertex cover C ⊆ S that covers all edges touching S"

**Counterexample (Aristotle)**:
```lean
-- Star graph centered at vertex 0
V = ULift (Fin 4)  -- {0, 1, 2, 3}
H = SimpleGraph.mk (fun u v => u ≠ v ∧ (u.down = 0 ∨ v.down = 0))
-- Edges: {0,1}, {0,2}, {0,3} (star centered at 0)

S = {1, 2, 3}  -- Vertices excluding the center

-- Independence check:
-- {1, 2} is independent: ¬H.Adj 1 2 since neither is 0 ✓

-- But NO C ⊆ S with |C| ≤ 2 covers all edges touching S:
-- Edge {0,1} needs 0 or 1 in cover. Since C ⊆ S, need 1 ∈ C
-- Edge {0,2} needs 0 or 2 in cover. Since C ⊆ S, need 2 ∈ C
-- Edge {0,3} needs 0 or 3 in cover. Since C ⊆ S, need 3 ∈ C
-- So need C ⊇ {1, 2, 3}, but |C| ≤ 2, CONTRADICTION!
```

**Why False**:
The proof idea "take C = S \ {u,w}" assumes edges within S. But edges can have ONE endpoint in S and ONE endpoint OUTSIDE S. Such edges require cover vertices that may not exist in S.

The star graph counterexample: center 0 ∉ S, but all edges incident to 0 touch S. No subset of S can cover them without including the center.

**Impact**: The entire "Link Graph + König" approach from the 3-round debate (ROUND8_CONSENSUS) is INVALID for proving τ ≤ 8.

**Avoid Pattern**: Never assume that vertex cover of induced subgraph covers edges that CROSS the boundary of the vertex set.

**Correct Approach**: UNKNOWN. Need to reconsider the entire cycle_4 strategy. Options:
1. Modify lemma to only cover edges WITHIN S (not edges touching S)
2. Find different approach for τ ≤ 8
3. Prove ν* = 4 via LP instead of constructive cover

**Source**: Aristotle (2026-01-03) | Slot: slot223c | UUID: 9794f0d1-6790-4025-97c8-9a31749d589a

---

## Pattern 21: trianglesThroughVinS domain incompleteness

**Status**: ❌ FALSE ASSUMPTION | 🟠 AI-VERIFIED

**Statement** (FALSE):
```
trianglesThroughVinS(v, M_neighbors(v)) captures ALL triangles through v that need covering
```

**Counterexample**:
```
At v_ab with S = M_neighbors(v_ab) = {v_da, a', v_bc, b'}

External triangle T = {v_ab, a', x} where:
- x is an external vertex (x ∉ A ∪ B ∪ C ∪ D)
- G.Adj v_ab x and G.Adj a' x exist
- T shares edge {v_ab, a'} with A (maximality satisfied)

Check domain:
- a' ∈ S ✓
- x ∉ S ✗ (x not in any M-element containing v_ab)

Therefore T ∉ trianglesThroughVinS(v_ab, S) but T still needs covering!
```

**Why False**:
The Link Graph L_v at shared vertex v only models triangles where BOTH other vertices are in M_neighbors(v). Triangles with ONE vertex in M_neighbors(v) and ONE external vertex are NOT captured. These "half-external" triangles exist when:
1. The external vertex x is adjacent to both v and some private vertex a'
2. The resulting triangle {v, a', x} shares edge {v, a'} with an M-element

**Impact**: The entire Link Graph + König approach for τ ≤ 8 is INCOMPLETE. It only handles Type 1 triangles (both vertices in S), missing Type 2 triangles (one in S, one external).

**Avoid Pattern**: Never assume trianglesThroughVinS covers all triangles. The Link Graph approach fundamentally only handles triangles where all non-center vertices are M-neighbors.

**Correct Approach**: UNKNOWN. Options:
1. Prove Type 2 triangles don't exist in cycle_4 (unlikely)
2. Handle Type 2 triangles with separate covering mechanism
3. Use entirely different approach (not Link Graph based)

**Source**: Multi-agent analysis (2026-01-03) | Slot: slot223e

---

## Pattern 22: bridge_externals_share_apex (CRITICAL - Jan 4, 2026)

**Status**: ❌ FALSE | 🟠 AI-VERIFIED (Grok+Gemini+Codex unanimous)

**Statement** (FALSE):
```lean
theorem bridge_externals_share_apex ...
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hAB : A ≠ B) (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂
```
"Externals of DIFFERENT M-elements A, B at shared vertex v share a common external apex x"

**Counterexample**:
```
M = {A={0,1,2}, B={0,3,4}, C={3,7,8}, D={7,1,9}}  (cycle_4 structure)

At shared vertex v = 0:
  T₁ = {0,1,5}  - external of A (uses edge {0,1})
  T₂ = {0,3,6}  - external of B (uses edge {0,3})

Verification:
- T₁ ∩ A = {0,1} → shares edge ✓
- T₁ ∩ B = {0} → no edge ✓  (isExternalOf A satisfied)
- T₂ ∩ B = {0,3} → shares edge ✓
- T₂ ∩ A = {0} → no edge ✓  (isExternalOf B satisfied)

Result: T₁ ∩ T₂ = {0}  (only the shared vertex!)
        External vertices: 5 (in T₁) ≠ 6 (in T₂)
        NO x satisfies x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂

Minimal graph has ν = 4:
- {T₁, T₂, C, D} is a valid 4-packing (replaces A, B)
- No 5-packing exists in minimal construction
```

**Why False**:
The 5-packing contradiction argument (slot182) ONLY works for externals of the SAME M-element.

| Scenario | Packing Attempt | Result |
|----------|-----------------|--------|
| Same-A externals | {T₁, T₂, B, C, D} | 5 elements → contradicts ν=4 unless T₁, T₂ share edge |
| Different-A,B externals | {T₁, T₂, C, D} | 4 elements (REPLACES A,B) → no contradiction! |

When T₁ is external of A and T₂ is external of B, they can coexist in a 4-packing by replacing both A and B. No structural constraint forces them to share an external apex.

**Impact**:
- The "4+4 cover" approach for cycle_4 is **FUNDAMENTALLY INVALID**
- Cannot assume τ ≤ 8 via sunflower covering at shared vertices
- The τ ≤ 12 bound (slot139) may be optimal for cycle_4

**Avoid Pattern**:
- Never assume externals of DIFFERENT M-elements share an apex
- slot182's result ONLY applies to externals of the SAME M-element A
- The "bridge" structure at shared vertices creates independent channels

**Correct Approach**: UNKNOWN. Options:
1. Accept τ ≤ 12 for cycle_4 (currently proven)
2. Find LP/fractional approach that doesn't rely on sunflower structure
3. Prove ν* ≤ 4 via different method (not constructive cover)
4. Case-by-case analysis based on actual graph structure

**Source**: Multi-agent verification (Grok+Gemini+Codex unanimous) (2026-01-04) | Slot: slot227

---

## Pattern 23: tau_le_8_scattered (CRITICAL - Jan 4, 2026)

**Status**: ❌ FALSE | 🔴 ARISTOTLE-VERIFIED (Concrete counterexample!)

**Statement** (FALSE):
```lean
theorem tau_le_8_scattered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) :
    triangleCoveringNumber G ≤ 8
```
"When all 4 M-elements are pairwise vertex-disjoint (scattered), τ ≤ 8"

**Counterexample (Aristotle - PROVEN)**:
```lean
-- G_counter: 4 disjoint "Propeller" graphs
-- Each Propeller: central triangle + 3 petal triangles

def propeller_edges : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(1, 3), s(1, 4), s(2, 4), s(2, 5), s(0, 5)}

-- M_prop: The central triangle {0,1,2}
-- Triangles in Propeller: {0,1,2}, {0,1,3}, {1,2,4}, {2,0,5}
-- τ(Propeller) = 3 (Aristotle PROVEN: propeller_tau_eq_3)

-- G_counter: 4 copies (on Fin 4 × Fin 6)
-- M_counter: 4 central triangles (vertex-disjoint!)

-- THEOREM (Aristotle PROVEN):
theorem G_counter_tau_ge_12 : triangleCoveringNumber G_counter ≥ 12

-- DISPROOF (Aristotle PROVEN):
theorem disproof_of_tau_le_8_scattered :
    ∃ (V : Type) ... (M : Finset (Finset V)),
      isMaxPacking G M ∧ M.card = 4 ∧
      (∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) ∧
      ¬ (triangleCoveringNumber G ≤ 8)
```

**Why False**:
The key false assumption was `tau_S_le_2` - that 2 edges per M-element suffice to cover all triangles sharing an edge with that element.

In the Propeller:
- M-element A = {0,1,2}
- Externals: T₁={0,1,3}, T₂={1,2,4}, T₃={2,0,5}
- Each external uses a DIFFERENT edge of A
- τ(triangles sharing edge with A) = τ({A, T₁, T₂, T₃}) = 3, NOT 2!

The 3 petals of each Propeller independently require 3 edges (one per petal).
4 Propellers × 3 edges = 12 minimum. τ ≤ 8 is impossible.

**Implication**: τ ≤ 2ν is **TIGHT** for scattered case!

**Impact**:
- Scattered case is NOT the "easiest" - it's actually where Tuza's bound is tight!
- The entire "4×2=8" approach for scattered is INVALID
- Slots 228-230 in attack plan are CANCELLED
- Must find cases with structural constraints that limit externals

**Avoid Pattern**:
- Never assume 2 edges per M-element suffice (tau_S_le_2 is FALSE)
- Never assume scattered is "easiest" - it allows maximum external proliferation
- Never trust "PROVEN" headers without checking for sorry statements

**Correct Approach**: For τ ≤ 8, need cases where externals are constrained:
1. Star case with bounded external vertices
2. Cycle_4 or path_4 where vertex sharing limits independence
3. Prove τ ≤ 12 for scattered and accept this is tight

**Source**: Aristotle (2026-01-04) | Slot: slot148_scattered_tau_le_8_aristotle.lean | UUID: e0e15ef4-4856-4b41-a55e-99c678ad5a58

---

