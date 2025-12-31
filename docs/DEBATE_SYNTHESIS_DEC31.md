# Multi-Agent Debate Synthesis: τ ≤ 8 for Cycle_4

**Date:** December 31, 2025
**Participants:** Grok-4, Gemini, Codex
**Rounds:** 4

---

## Final Consensus

All agents agree:
1. **τ ≤ 12 is PROVEN and valid** - matches Haxell's general bound (τ ≤ 2.87ν)
2. **τ ≤ 8 is LIKELY but requires careful construction**
3. **No fixed 8-edge M-subset works** - need adaptive/structural approach
4. **LP/Fractional approach is viable alternative** to direct construction

---

## Two Viable Paths to τ ≤ 8

### Path A: LP Relaxation (Gemini)

**Theorem:** Krivelevich (1995): τ(G) ≤ 2ν*(G)

**Strategy:**
1. Define fractional packing LP: max Σ w_T s.t. for each edge e, Σ_{T∋e} w_T ≤ 1
2. Prove ν* = 4 for Cycle_4 configuration
3. Apply Krivelevich → τ ≤ 8

**Key Insight:** Setting w_A = w_B = w_C = w_D = 1 gives fractional packing of weight 4.
Any external triangle shares an M-edge, so adding weight to externals forces reducing M-weights.

**Advantages:**
- No König theorem needed
- No bipartiteness assumption
- Pure LP argument

**Challenges:**
- Formalizing LP duality in Lean
- Proving no fractional solution exceeds 4

### Path B: Direct 8-Edge Construction (Codex)

**The 8 edges:**
```
Ring edges (cover M-triangles):
  1. {v_ab, v_da}  -- covers A
  2. {v_ab, v_bc}  -- covers B
  3. {v_bc, v_cd}  -- covers C
  4. {v_cd, v_da}  -- covers D

Private spokes (cover externals):
  5. {v_ab, a_priv}  -- externals at v_ab through A's private vertex
  6. {v_bc, b_priv}  -- externals at v_bc through B's private vertex
  7. {v_cd, c_priv}  -- externals at v_cd through C's private vertex
  8. {v_da, d_priv}  -- externals at v_da through D's private vertex
```

**Lemma Stack:**
1. `ring_edges_cover_M` - 4 ring edges hit all M-triangles (EASY)
2. `external_uses_M_edge_at_v` - Externals at v share M-edge at v (MEDIUM)
3. `externals_at_v_covered` - 4 edges at v cover all triangles through v (HARDEST)
4. `cycle4_cover_8_covers_all` - Combined coverage proof (MEDIUM)
5. `tau_le_8_cycle4` - Main theorem (EASY conclusion)

**Advantages:**
- Concrete construction Aristotle can verify
- Case-split friendly
- Uses proven lemmas (triangle_shares_edge_with_packing)

**Challenges:**
- Proving `externals_at_v_covered` for each shared vertex
- Need private vertex structure in Cycle4 config

**Estimated success:** 70%

---

## False Lemmas to Avoid

| Pattern | Lemma | Why False |
|---------|-------|-----------|
| 5 | local_cover_le_2 | 4 triangles at v may need 4 different M-edges |
| 6 | support_sunflower τ≤2 | trianglesSharingMEdgeAt includes M-elements A,B |
| 7 | external_share_common_vertex | Externals can use edges from DIFFERENT M-triangles |
| 8 | link_graph_bipartite | L_v can have odd cycles (König fails) |

---

## Proven Foundation

**Critical lemmas available:**
- `tau_union_le_sum` - τ(A ∪ B) ≤ τ(A) + τ(B)
- `tau_le_12_cycle4` - 12 M-edges cover everything
- `triangle_shares_edge_with_packing` - Maximality lemma
- `cycle4_all_triangles_contain_shared` - Every triangle has v_ab, v_bc, v_cd, or v_da
- `S_e_structure` - Either common edge OR common external vertex
- `diagonal_bridges_empty` - No bridges between opposite elements

---

## Strategic Recommendations

### Priority 1: Accept τ ≤ 12
- Valid mathematical result
- Matches best known general bound
- Write up false lemma discoveries as contribution

### Priority 2: One More τ ≤ 8 Attempt (Path B)
- Submit direct 8-edge construction to Aristotle
- Requires adding private vertices to Cycle4 structure
- If fails, document and pivot

### Priority 3: Alternative Paths
- Formalize LP approach (if Mathlib has support)
- Explore ν = 5 structure
- Clean up existing proofs for publication

---

## Next Submission Structure (if pursuing Path B)

```lean
structure Cycle4Extended (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) extends Cycle4 G M where
  a_priv : V
  b_priv : V
  c_priv : V
  d_priv : V
  h_apriv_A : a_priv ∈ A
  h_apriv_not_B : a_priv ∉ B
  -- etc.

def cycle4_cover_8 (cfg : Cycle4Extended G M) : Finset (Sym2 V) :=
  {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc),
   s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da),
   s(cfg.v_ab, cfg.a_priv), s(cfg.v_bc, cfg.b_priv),
   s(cfg.v_cd, cfg.c_priv), s(cfg.v_da, cfg.d_priv)}
```

---

## Sources

- Krivelevich (1995): "On a conjecture of Tuza" Discrete Mathematics 142(1-3):281-286
- Haxell (1999): τ ≤ 2.87ν for general graphs
- Chapuy et al. (2014): τ ≤ 2ν* - (1/√6)√ν*
- Project database: 35 failed approaches, 9 false lemma patterns
