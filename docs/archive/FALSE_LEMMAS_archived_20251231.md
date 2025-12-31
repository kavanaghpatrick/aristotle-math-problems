# FALSE LEMMAS - DO NOT USE

> **⚠️ AUTO-GENERATED FILE** - Do not edit directly!
> Source of truth: `submissions/tracking.db` table `false_lemmas`
> Regenerate with: `./scripts/generate_false_lemmas_md.sh`

**Last generated**: 2025-12-31 09:05:42

This document lists lemmas that have been PROVEN FALSE. Do not use these in any proof attempts.

---

## Quick Reference

| Evidence | Meaning | Count |
|----------|---------|-------|
| 🔴 ARISTOTLE-VERIFIED | Actual Aristotle counterexample | 1 |
| 🟠 AI-VERIFIED | AI agents verified the math | 4 |
| 🟡 REASONING-BASED | Sound reasoning, no formal verification | 3 |
| ⚪ TRIVIALLY FALSE | Obvious logical error | 1 |

---

## Summary Table

| # | Lemma | Evidence | Source |
|---|-------|----------|--------|

| 1 | `local_cover_le_2` | 🟠 AI-VERIFIED | Codex 2025-12-26 |
| 2 | `avoiding_covered_by_spokes` | ⚪ TRIVIAL | Logical analysis 2025-12-26 |
| 3 | `bridge_absorption` | 🔴 ARISTOTLE | Aristotle 2025-12-25 |
| 4 | `trianglesContainingVertex_partition` | 🟡 REASONING | Gemini 2025-12-26 |
| 5 | `support_sunflower_tau_2` | 🟡 REASONING | Definition analysis 2025-12-28 |
| 6 | `external_share_common_vertex` | 🟠 AI-VERIFIED | AI debate 2025-12-29 |
| 7 | `sunflower_cover_at_vertex_2edges` | 🟠 AI-VERIFIED | Gemini + Codex 2025-12-29 |
| 8 | `link_graph_bipartite` | 🟠 AI-VERIFIED | Grok + Codex 2025-12-31 |
| 9 | `fixed_8_edge_M_subset` | 🟡 REASONING | Grok 2025-12-31 |

---

## Pattern 1: local_cover_le_2

**Status**: ❌ FALSE | 🟠 **AI-VERIFIED**

**Statement** (FALSE):
```
2 edges from M_edges_at suffice to cover all triangles sharing an M-edge at vertex v
```

**Counterexample**:
```
At v_ab: Add vertex x with triangles T₁={v_ab,v_da,x}, T₂={v_ab,a_priv,x}, T₃={v_ab,v_bc,x}, T₄={v_ab,b_priv,x}. Each uses different M-edge, all share {v_ab,x} so ν stays 4. Need 4 M-edges to hit all.
```

**Why it's FALSE**: M_edges_at contains 4 edges at v_ab. Each Tᵢ uses a unique M-edge. Any 2-edge subset misses at least 2 triangles.

**Verified by**: Grok agent (2025-12-31)

**Impact**: Breaks 4×2=8 sunflower covering approach. Need 4 edges per vertex, not 2.

**Avoid**: Never assume 2 M-edges suffice at shared vertex. Check how many distinct M-edges triangles use.

**Correct approach**: Use adaptive cover with non-M-edges, or accept τ ≤ 12 (3 per vertex).

**Notes**: Verified mathematically correct by Grok agent on Dec 31. Minimum M-edge cover at v_ab is 4, not 2.

---

## Pattern 2: avoiding_covered_by_spokes

**Status**: ❌ FALSE | ⚪ **TRIVIALLY FALSE**

**Statement** (FALSE):
```
Triangles avoiding vertex v can be covered by spokes from v
```

**Counterexample**:
```
Triangle {a,b,x} shares base edge {a,b} with e={v,a,b}. t avoids v, so v ∉ t. No spoke {v,*} can be in t.
```

**Why it's FALSE**: If t avoids v, then v ∉ t. Spokes by definition contain v. Therefore spokes ∉ t.sym2. This is basic set theory.

**Impact**: Cannot use spokes to cover avoiding triangles.

**Avoid**: Never claim spokes cover triangles that avoid the spoke vertex.

**Correct approach**: Use BASE EDGES {a,b},{c,d} for avoiding triangles, not spokes.

---

## Pattern 3: bridge_absorption

**Status**: ❌ FALSE | 🔴 **ARISTOTLE-VERIFIED**

**Statement** (FALSE):
```
A cover that hits all triangles in S_e and S_f also hits bridges between e and f
```

**Counterexample**:
```
Aristotle 5-vertex: e={0,1,2}, f={0,3,4}, bridge t={0,1,3}, cover C={{1,2},{3,4}} covers S_e∪S_f but NOT bridge t.
```

**Why it's FALSE**: Bridges share vertices with e,f but may not share edges with S_e or S_f triangles. The cover hits triangles ONLY sharing edge with one element.

**Impact**: Cannot assume S_e∪S_f cover handles bridges. Must handle bridges separately.

**Avoid**: Never assume bridge coverage comes free from S covers.

**Correct approach**: Handle bridges separately with tau_X_le_2. Total: τ(S_e) + τ(S_f) + τ(X_ef).

---

## Pattern 4: trianglesContainingVertex_partition

**Status**: ❌ FALSE | 🟡 **REASONING-BASED**

**Statement** (FALSE):
```
Partitioning triangles by which shared vertex they contain gives correct bounds
```

**Counterexample**:
```
Triangle t={v_ab, v_cd, c3} contains v_ab but shares M-edge only at v_cd (with C). local_cover_le_2 at v_ab cannot cover t.
```

**Why it's FALSE**: A triangle can contain shared vertex v but share its M-edge at a DIFFERENT shared vertex. The partition by containment doesnt match M-edge sharing.

**Impact**: Wrong partition leads to incorrect coverage analysis.

**Avoid**: Dont partition by vertex containment.

**Correct approach**: Use trianglesSharingMEdgeAt v (partition by which vertex the M-edge is incident to).

---

## Pattern 5: support_sunflower_tau_2

**Status**: ❌ FALSE | 🟡 **REASONING-BASED**

**Statement** (FALSE):
```
At shared vertex v, 2 edges suffice to cover all triangles sharing an M-edge at v
```

**Counterexample**:
```
At v_ab: trianglesSharingMEdgeAt contains {A, B, T1, T2, T3, T4}. {v_ab,x} covers T1-T4 but NOT A,B (x is external, x ∉ A, x ∉ B). Need 3+ edges.
```

**Why it's FALSE**: trianglesSharingMEdgeAt INCLUDES the M-elements A and B, not just external triangles! M-elements dont contain external vertices, so {v,x} cant hit them.

**Impact**: The 4×2=8 approach is invalid. Need to separately cover M-elements and externals.

**Avoid**: Dont confuse trianglesSharingMEdgeAt (includes M) with external triangles only.

**Correct approach**: Separate M-coverage from external-coverage. But see Pattern 6 - externals dont share common vertex either!

---

## Pattern 6: external_share_common_vertex

**Status**: ❌ FALSE | 🟠 **AI-VERIFIED**

**Statement** (FALSE):
```
All external triangles at shared vertex v share a common external vertex x
```

**Counterexample**:
```
CounterexampleG: M={A,B,C,D} with A={0,1,2}, B={0,3,4}, C={3,7,8}, D={7,1,9}. At v_ab=0: T1={0,1,5} uses {0,1} from A, T2={0,3,6} uses {0,3} from B. T1∩T2={0} only!
```

**Why it's FALSE**: External triangles can use edges from DIFFERENT M-triangles (A vs B) at the same shared vertex. Each M-triangle contributes different M-edges, so externals borrowing from different M-triangles share only v.

**Verified by**: Gemini agent (2025-12-31)

**Impact**: The 4+4 covering approach (4 M-edges + 4 external-via-{v,x}) is INVALID. Need multiple edges for externals.

**Avoid**: Never assume external triangles share common vertex. They can independently use edges from different M-triangles.

**Correct approach**: Unknown - this is a major blocker. May need LP relaxation or accept τ ≤ 12.

**Notes**: Originally attributed to Aristotle UUID 7039b275 but NO output file exists. Counterexample is from AI debate, verified correct by Gemini agent.

---

## Pattern 7: sunflower_cover_at_vertex_2edges

**Status**: ❌ FALSE | 🟠 **AI-VERIFIED**

**Statement** (FALSE):
```
At each shared vertex v, 2 edges suffice to cover all triangles containing v
```

**Counterexample**:
```
At v_ab: T_A={v_ab,a_priv,x1}, T_B={v_ab,b_priv,x2}, T_C={v_ab,v_cd,c_priv}. These 3 triangle clusters require 3 distinct edges: {v_ab,a_priv}, {v_ab,b_priv}, {v_ab,v_cd}.
```

**Why it's FALSE**: At v_ab, triangles come from TWO M-elements (A and B). Even if externals share x, A and B dont contain x. Need: edge for A + edge for B + edge for externals = 3+ edges.

**Verified by**: Same analysis as Pattern 1 (2025-12-31)

**Impact**: The 4×2=8 sunflower approach is INVALID. Actual bound: 4×3=12 (matches slot113).

**Avoid**: Dont assume 2 edges per shared vertex suffice.

**Correct approach**: Accept τ ≤ 12 or find adaptive approach. M-elements require separate coverage from externals.

---

## Pattern 8: link_graph_bipartite

**Status**: ❌ FALSE | 🟠 **AI-VERIFIED**

**Statement** (FALSE):
```
The link graph L_v at a shared vertex v in Cycle_4 is bipartite
```

**Counterexample**:
```
Add edges {v_da, b_priv} and {a_priv, b_priv} to G. Creates triangles {v_ab,v_da,b_priv} and {v_ab,a_priv,b_priv}. In L_{v_ab}: 3-cycle v_da--a_priv--b_priv--v_da.
```

**Why it's FALSE**: Dec 30 checkpoint incorrectly claimed bipartiteness. M-neighbors (v_da, a_priv, v_bc, b_priv) CAN form odd cycles through added edges. ν=4 blocks external-external edges but NOT odd cycles among M-neighbors.

**Verified by**: Codex agent (2025-12-31)

**Impact**: König theorem CANNOT be applied. The proof that τ(L_v) = ν(L_v) is INVALID. The entire König-based τ ≤ 8 approach fails.

**Avoid**: Never assume link graphs are bipartite. The ν=4 constraint prevents external-external edges but NOT odd cycles among M-neighbors.

**Correct approach**: LP relaxation (Krivelevich τ ≤ 2ν*) may bypass bipartiteness requirement entirely.

**Notes**: This was a critical Dec 31 discovery that overturned Dec 30 checkpoint claims. Verified by Codex agent with rigorous 3-cycle analysis.

---

## Pattern 9: fixed_8_edge_M_subset

**Status**: ❌ FALSE | 🟡 **REASONING-BASED**

**Statement** (FALSE):
```
A specific fixed 8-edge subset of M-edges covers all triangles in Cycle_4
```

**Counterexample**:
```
Triangle T={a_priv, v_da, z} shares edge {a_priv, v_da} with A. Check: v_ab∉T, v_bc∉T, v_cd∉T, b_priv∉T, c_priv∉T, d_priv∉T. NONE of the 8 edges hit T!
```

**Why it's FALSE**: Any 8-subset of 12 M-edges must omit 4 edges. The omitted edges are {v_da,a_priv}, {v_ab,b_priv}, {v_bc,c_priv}, {v_cd,d_priv}. External triangles sharing those edges are uncovered.

**Impact**: NO fixed 8-edge subset of M-edges works universally. τ ≤ 8 requires ADAPTIVE cover or non-M-edges.

**Avoid**: Dont pick a fixed 8-edge subset of M-edges.

**Correct approach**: Either use all 12 M-edges (τ ≤ 12) or use adaptive selection that includes non-M-edges when needed.

**Notes**: The key insight (any 8 of 12 omits 4) is combinatorially obvious. Sound reasoning but no formal Aristotle verification.

---

## Database Queries

```sql
-- Quick summary
SELECT * FROM v_false_lemmas_summary;

-- Full details for a pattern
SELECT * FROM false_lemmas WHERE pattern_number = 1;

-- Find by lemma name
SELECT * FROM false_lemmas WHERE lemma_name LIKE '%cover%';

-- All AI-verified patterns
SELECT lemma_name, counterexample FROM false_lemmas
WHERE evidence_level = 'ai_verified';
```
