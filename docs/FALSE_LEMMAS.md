# FALSE LEMMAS - DO NOT USE

**Last updated**: December 26, 2025

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

**Correct approach**: Separate the cover into:
1. Cover M with 4 edges (one per element)
2. Cover external triangles at each shared vertex with 1 edge each
3. Total: 4 + 4 = 8 edges

**Key lemma that IS true**:
```lean
-- External triangles (trianglesSharingMEdgeAt \ M) share a common external vertex x
lemma external_share_common_vertex :
  ∀ T1 T2 ∈ (trianglesSharingMEdgeAt G M v \ M), T1 ≠ T2 →
  ∃ x, x ∈ T1 ∧ x ∈ T2 ∧ x ≠ v
```

This is true because if two external triangles had different external vertices and were edge-disjoint, {T1, T2, C, D} or similar would form a packing of size 5 when combined with parts of {A, B, C, D}, contradicting ν = 4.

---

## How to check before using a lemma

1. Check this file first
2. Query database: `SELECT * FROM failed_approaches WHERE approach_name LIKE '%lemma_name%';`
3. Check `validated_true` in literature_lemmas: `SELECT * FROM literature_lemmas WHERE name = 'lemma_name' AND validated_true = 1;`
4. If lemma is in `proven/` directory, check the file header for "crashed" or "sorry"
