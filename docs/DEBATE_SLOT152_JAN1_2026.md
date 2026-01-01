# AI Debate: slot152_cycle4_tau8_fixed.lean

**Date:** January 1, 2026
**Participants:** Grok-4, Gemini, Codex
**Verdict:** UNANIMOUS INVALID

---

## The Claim Under Review

```lean
lemma adaptiveCoverAt_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    ∃ E_v : Finset (Sym2 V), E_v ⊆ G.edgeFinset ∧ E_v.card ≤ 2 ∧
      ∀ t ∈ trianglesAt G v, ∃ e ∈ E_v, e ∈ t.sym2
```

**Translation:** At each shared vertex v in cycle_4, there exist 2 edges that cover ALL triangles containing v.

**Proposed τ ≤ 8 proof:** 4 vertices × 2 edges = 8 edges total.

---

## Verdict: FALSE (Pattern 7)

All three AIs independently identified this as **Pattern 7** (`sunflower_cover_at_vertex_2edges`), a documented false lemma.

---

## The Counterexample

### Setup at v_ab

M-elements meeting at v_ab:
- **A** = {v_ab, v_da, a_priv}
- **B** = {v_ab, v_bc, b_priv}

### Triangles to Cover

| Triangle | Type | Edges (sym2) |
|----------|------|--------------|
| A | M-element | {v_ab, v_da}, {v_ab, a_priv}, {v_da, a_priv} |
| B | M-element | {v_ab, v_bc}, {v_ab, b_priv}, {v_bc, b_priv} |
| T1 = {v_ab, v_da, x} | External | {v_ab, v_da}, {v_ab, x}, {v_da, x} |
| T2 = {v_ab, a_priv, x} | External | {v_ab, a_priv}, {v_ab, x}, {a_priv, x} |
| T3 = {v_ab, v_bc, x} | External | {v_ab, v_bc}, {v_ab, x}, {v_bc, x} |
| T4 = {v_ab, b_priv, x} | External | {v_ab, b_priv}, {v_ab, x}, {b_priv, x} |

### Why 2 Edges Fail

**Case 1: E_v contains {v_ab, x}**
- Covers: T1, T2, T3, T4 (all externals share {v_ab, x})
- Does NOT cover: A, B (because x ∉ A and x ∉ B)
- A.sym2 ∩ B.sym2 = ∅ (no common edge)
- Need 2 more edges (one for A, one for B)
- **Total: 3 edges minimum**

**Case 2: E_v does NOT contain {v_ab, x}**
- Each external Ti must be covered by its unique M-edge
- T1 needs {v_ab, v_da}, T2 needs {v_ab, a_priv}, etc.
- **Total: 4 edges minimum**

### Minimum Cover

**3 edges suffice:**
1. {v_ab, x} - covers all externals
2. {v_ab, a_priv} - covers A (and T2)
3. {v_ab, v_bc} - covers B (and T3)

---

## Why τ ≤ 8 Is Impossible via Vertex Approach

| Vertex | Triangles | Min Edges |
|--------|-----------|-----------|
| v_ab | A, B, externals | 3 |
| v_bc | B, C, externals | 3 |
| v_cd | C, D, externals | 3 |
| v_da | D, A, externals | 3 |
| **Total** | | **12** |

The vertex-centric approach gives τ ≤ 12, NOT τ ≤ 8.

---

## Individual AI Analyses

### Grok-4

> "This is **exactly** the false claim from **Pattern 7** (`sunflower_cover_at_vertex_2edges`). At v_ab: T_A={v_ab,a_priv,x1}, T_B={v_ab,b_priv,x2}, T_C={v_ab,v_cd,c_priv}. These 3 triangle clusters require 3 distinct edges. No 2-edge subset covers all three. QED."

**Recommendation:** Do NOT submit slot152.

### Gemini

> "The slot152 approach is FUNDAMENTALLY FLAWED and cannot be salvaged. The sorry at line 185 is NOT a minor gap - it IS the false claim... Could add hypothesis 'No external triangles exist at v' - but this would make the lemma trivially useless."

**Recommendation:** Pursue LP relaxation (τ ≤ 2ν*) or accept τ ≤ 12.

### Codex

> "**VERDICT: INVALID.** Any 2-edge subset misses at least one of {A, B, T1, T2, T3, T4}. Minimum cover requires 3 edges... Could state `E_v.card ≤ 3` instead of `≤ 2`. This would be TRUE and would give τ ≤ 12."

**Recommendation:** Fix bound to 3 edges/vertex for τ ≤ 12.

---

## Salvage Options Evaluated

| Option | Viable? | Reasoning |
|--------|---------|-----------|
| Use non-M-edges | NO | Pattern 6: externals use different M-triangle edges |
| Prove common external vertex | NO | Pattern 7: no such x exists |
| Weaken to 3 edges/vertex | YES | Gives τ ≤ 12 (already proven) |
| LP relaxation (ν* = 4) | MAYBE | Bypasses vertex-centric counting |

---

## Conclusion

The slot152 approach **cannot** achieve τ ≤ 8. The mathematical structure of cycle_4 requires minimum 3 edges per shared vertex.

**Proven:** τ ≤ 12 (slot139)
**Open:** τ ≤ 8 (requires LP/fractional approach or novel insight)

---

## Related False Lemma Patterns

| Pattern | Name | Status |
|---------|------|--------|
| 1 | local_cover_le_2 | FALSE |
| 5 | support_sunflower_tau_2 | FALSE |
| 6 | external_share_common_vertex | FALSE |
| 7 | sunflower_cover_at_vertex_2edges | FALSE |
| 9 | fixed_8_edge_M_subset | FALSE |

All vertex-centric τ ≤ 8 approaches fail due to these patterns.

---

*Document generated from parallel AI debate, January 1, 2026*
