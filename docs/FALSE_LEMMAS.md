# FALSE LEMMAS - DO NOT USE

**Last updated**: December 31, 2025

This document lists lemmas that have been PROVEN FALSE. Do not use these in any proof attempts.

---

## local_cover_le_2

**Status**: ❌ **FALSE** (not just unproven - mathematically false)

**Statement** (FALSE):
```lean
lemma local_cover_le_2 :
  ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ M_edges_at G M v ∧
  ∀ t ∈ trianglesSharingMEdgeAt v, (∃ e ∈ E', e ∈ t.sym2)
```

**Why it's FALSE** (Codex counterexample, Dec 26 2025):

At shared vertex `v_ab`, `M_edges_at` contains FOUR edges:
- `{v_ab, v_da}` from A
- `{v_ab, a_priv}` from A
- `{v_ab, v_bc}` from B
- `{v_ab, b_priv}` from B

**Counterexample construction**:
```
Packing M = {A, B, C, D} where:
  A = {v_ab, v_da, a_priv}
  B = {v_ab, v_bc, b_priv}
  C = {v_bc, v_cd, c_priv}
  D = {v_cd, v_da, d_priv}

Add vertex x and edges to create:
  T₁ = {v_ab, v_da, x}   -- uses {v_ab, v_da}
  T₂ = {v_ab, a_priv, x} -- uses {v_ab, a_priv}
  T₃ = {v_ab, v_bc, x}   -- uses {v_ab, v_bc}
  T₄ = {v_ab, b_priv, x} -- uses {v_ab, b_priv}
```

All four triangles:
- Are in `trianglesSharingMEdgeAt v_ab`
- Each uses a DIFFERENT M-edge
- Share edge `{v_ab, x}` so mutually overlapping (ν stays 4)
- Require ALL FOUR M-edges to hit

**Database entries**: #22 (self-loop bug), #24 (mathematically false)

**Do not confuse with** (these ARE valid):
- `tau_S_le_2` - τ(S_e) ≤ 2 ✅
- `tau_X_le_2` - τ bridges ≤ 2 ✅
- `tau_containing_v_in_pair_le_4` ✅
- `tau_avoiding_v_in_pair_le_2` ✅

---

## avoiding_covered_by_spokes

**Status**: ❌ **FALSE**

**Statement** (FALSE): If t avoids v, then ∃ spoke {v,x} ∈ t.sym2

**Why FALSE**: If t avoids v, then v ∉ t. Spokes contain v. So spokes ∉ t.sym2.

**Correct approach**: Use BASE EDGES {a,b},{c,d} for avoiding triangles.

---

## bridge_absorption

**Status**: ❌ **FALSE**

**Statement** (FALSE): Cover of S_e ∪ S_f covers bridges X(e,f)

**Why FALSE**: Bridges share vertices with e,f but may not share edges with S_e or S_f triangles.

---

## trianglesContainingVertex partition

**Status**: ❌ **WRONG PARTITION**

**Statement** (FALSE): Partition triangles by "contains vertex v"

**Counterexample** (Gemini, Dec 26 2025):
Triangle t = {v_ab, v_cd, c3} contains v_ab but shares M-edge only at v_cd (with C).
So `local_cover_le_2` at v_ab cannot cover t.

**Correct partition**: `trianglesSharingMEdgeAt v` (partition by which vertex the M-edge is incident to)

---

## support_sunflower (τ ≤ 2 version)

**Status**: ❌ **FALSE** (Dec 28, 2025)

**Statement** (FALSE):
```lean
lemma support_sunflower :
  τ(trianglesSharingMEdgeAt G M v) ≤ 2
```

**Why it's FALSE**: `trianglesSharingMEdgeAt G M v` INCLUDES the M-elements containing v!

At `v = v_ab`:
- `trianglesSharingMEdgeAt v_ab` contains A, B (M-elements) PLUS external triangles T1-T4
- To cover {A, B, T1, T2, T3, T4}:
  - `{v_ab, x}` covers T1-T4 (all contain edge {v_ab, x}) ✓
  - `{v_ab, x}` does NOT cover A because x ∉ A (x is external) ✗
  - `{v_ab, x}` does NOT cover B for the same reason ✗
- Need 3 edges minimum: one hitting A, one hitting B, one for externals

**Correct approach**: Unknown - needs new strategy after external_share_common_vertex was disproved.

---

## external_share_common_vertex

**Status**: ❌ **FALSE** (Dec 29, 2025 - slot131_v2 counterexample)

**Statement** (FALSE):
```lean
-- CLAIMED: External triangles at shared vertex v share a common external vertex x
lemma external_share_common_vertex :
  ∀ T1 T2 ∈ (trianglesSharingMEdgeAt G M v \ M), T1 ≠ T2 →
  ∃ x, x ∈ T1 ∧ x ∈ T2 ∧ x ≠ v
```

**Why it's FALSE** (Aristotle counterexample, slot131_v2 UUID 7039b275):

At shared vertex `v_ab = 0`, external triangles can use edges from DIFFERENT M-triangles:

```
CounterexampleG (10 vertices):
  M_cex = {A, B, C, D} where:
    A = {0, 1, 2}
    B = {0, 3, 4}
    C = {3, 7, 8}
    D = {7, 1, 9}

  Shared vertices: v_ab=0, v_bc=3, v_cd=7, v_da=1

  External triangles at v_ab = 0:
    T1 = {0, 1, 5}  -- uses edge {0,1} from A, external vertex 5
    T2 = {0, 3, 6}  -- uses edge {0,3} from B, external vertex 6

  T1 ∩ T2 = {0} only!  5 ≠ 6, no common external vertex!
```

**Why this works as a counterexample**:
- T1 uses edge {0,1} from A (the edge A shares with D via v_da=1)
- T2 uses edge {0,3} from B (the edge B shares with C via v_bc=3)
- {T1, T2, C, D} is also a valid packing of size 4, so M_cex is maximum
- The external triangles are "independent" - they draw from different M-triangle edges

**Impact**: The 4+4 edge cover approach (4 M-edges + 4 external-vertex edges) is INVALID.
Each shared vertex may need MULTIPLE edges to cover external triangles from different M-sources.

**Avoid pattern**: Never assume external triangles share common vertex. At v_ab, externals can independently use edges from A or from B.

---

## sunflower_cover_at_vertex (2 edges per shared vertex)

**Status**: ❌ **FALSE** (Dec 29, 2025 - Gemini + Codex audit)

**Statement** (FALSE):
```lean
-- CLAIMED: At each shared vertex v, 2 edges suffice to cover all triangles containing v
lemma sunflower_cover_at_vertex :
  ∃ E_v ⊆ G.edgeFinset, E_v.card ≤ 2 ∧
  ∀ t ∈ trianglesContaining G v, ∃ e ∈ E_v, e ∈ t.sym2
```

**Why it's FALSE** (Gemini counterexample):

At shared vertex v_ab, there can be 3+ disjoint triangle clusters:
```
T_A = {v_ab, a_priv, x1}  -- uses M-edge {v_ab, a_priv}
T_B = {v_ab, b_priv, x2}  -- uses M-edge {v_ab, b_priv}
T_C = {v_ab, v_cd, c_priv} -- uses diagonal edge {v_ab, v_cd}
```

These require 3 DISTINCT edges:
- {v_ab, a_priv} for T_A cluster
- {v_ab, b_priv} for T_B cluster
- {v_ab, v_cd} for T_C cluster

**Why this works as counterexample** (Codex analysis):

The fundamental issue: at v_ab, triangles come from TWO M-elements (A and B).
- M-element A = {v_ab, v_da, a_priv}
- M-element B = {v_ab, v_bc, b_priv}
- Externals using A-edges or B-edges

Even if externals share common vertex x, A and B don't contain x.
So we need: edge for A + edge for B + edge for externals = 3+ edges minimum.

**Impact**: The 4×2=8 sunflower approach is INVALID.
Actual bound: 4×3=12 (matches proven slot113).

**Avoid pattern**: Don't assume 2 edges per shared vertex suffice.
The M-elements themselves require separate coverage from externals.

---

## link_graph_bipartite

**Status**: ❌ **FALSE** (Dec 31, 2025 - AI Debate Rounds 1-4)

**Statement** (FALSE):
```lean
-- CLAIMED: Link graph at shared vertex is bipartite
lemma link_graph_bipartite (v : V) (hv : v ∈ shared_vertices) :
  IsBipartite (linkGraph G v)
```

**Why it's FALSE** (Grok + Codex counterexamples):

The checkpoint (Dec 30) incorrectly claimed "Link graphs are bipartite (external vertices isolated)".

**Counterexample construction** (Grok):
```
In Cycle_4, add edges to G:
  - {v_da, b_priv}
  - {a_priv, b_priv}

This creates triangle {v_da, a_priv, b_priv} IN the link graph L_{v_ab}!

Triangle in L_v = 3-cycle = odd cycle → NOT bipartite

Graph has 14 edges, ν still = 4 (extra triangles share edges with M).
```

**Counterexample construction** (Codex):
```
At v_ab, if G additionally has:
  - Edge {a_priv, b_priv}
  - Edge {b_priv, v_da}

Then L_{v_ab} contains 3-cycle: v_da - a_priv - b_priv - v_da
```

**Why the checkpoint was wrong**:
- Round 5 correctly proved "external vertices cannot be adjacent to each other in L_v"
- But INCORRECTLY concluded bipartiteness
- The M-neighbors (v_da, a_priv, v_bc, b_priv) can form additional edges creating odd cycles

**Impact**: König's theorem CANNOT be applied. The proof that τ(L_v) = ν(L_v) is INVALID.

**Avoid pattern**: Never assume link graphs are bipartite. The ν=4 constraint prevents external-external edges but NOT odd cycles among M-neighbors.

---

## fixed_8_edge_cover (any specific 8-edge subset)

**Status**: ❌ **FALSE** (Dec 31, 2025 - AI Debate Round 4)

**Statement** (FALSE):
```lean
-- CLAIMED: A specific fixed 8-edge subset of M-edges covers all triangles
def cycle4_cover_8 (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc),
   s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da),
   s(cfg.v_ab, cfg.a_priv), s(cfg.v_bc, cfg.b_priv),
   s(cfg.v_cd, cfg.c_priv), s(cfg.v_da, cfg.d_priv)}

lemma cycle4_cover_8_covers_all :
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ cycle4_cover_8 cfg, e ∈ t.sym2
```

**Why it's FALSE** (Grok counterexample):

The 8-edge cover above misses {v_da, a_priv} (the "other" private edge of A).

**Counterexample**:
```
External triangle T = {a_priv, v_da, z} where z is external:
  - T shares edge {a_priv, v_da} with A (satisfies maximality)
  - Check each of the 8 cover edges:
    - {v_ab, v_da}: v_ab ∉ T ❌
    - {v_ab, v_bc}: v_ab, v_bc ∉ T ❌
    - {v_bc, v_cd}: v_bc, v_cd ∉ T ❌
    - {v_cd, v_da}: v_cd ∉ T ❌
    - {v_ab, a_priv}: v_ab ∉ T ❌
    - {v_bc, b_priv}: v_bc, b_priv ∉ T ❌
    - {v_cd, c_priv}: v_cd, c_priv ∉ T ❌
    - {v_da, d_priv}: d_priv ≠ z (external) ❌

  NONE of the 8 edges are in T.sym2!
```

**Why this generalizes**:
- Any 8-edge subset of the 12 M-edges must omit 4 edges
- The omitted edges are: {v_da, a_priv}, {v_ab, b_priv}, {v_bc, c_priv}, {v_cd, d_priv}
- If an external triangle shares one of these 4 edges, it's uncovered

**Impact**: NO fixed 8-edge subset of M-edges works universally.
τ ≤ 8 requires ADAPTIVE cover that may include non-M-edges.

**Avoid pattern**: Don't pick a fixed 8-edge subset of M-edges. Either use all 12 M-edges (τ ≤ 12) or use adaptive selection.

---

## How to check before using a lemma

1. Check this file first
2. Query database: `SELECT * FROM failed_approaches WHERE approach_name LIKE '%lemma_name%';`
3. Check `validated_true` in literature_lemmas: `SELECT * FROM literature_lemmas WHERE name = 'lemma_name' AND validated_true = 1;`
4. If lemma is in `proven/` directory, check the file header for "crashed" or "sorry"
