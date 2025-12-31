# CYCLE_4 ROUND 7 - FINAL SUBMISSION PLAN
## December 30, 2025

---

## AI CONSENSUS (Gemini + Codex)

### Slot 139 (τ ≤ 12 Fallback)
- **Success probability**: 90-95%
- **Sorries**: 6 (all trivial arithmetic like `Nat.choose 3 2 = 3`)
- **Structure**: Sound, no circular dependencies
- **Recommendation**: **SUBMIT IMMEDIATELY**

### Slot 140 (τ ≤ 8 Greedy)
- **Success probability**: 40-50%
- **Critical flaw found by Gemini**: Diagonal spokes {v_da, v_ab}, {v_da, v_cd} do NOT cover triangle T = {v_da, a_priv, v_bc}
- **Codex issues**: Line 335 syntax error, `no_external_edge_at_v` unproven
- **Recommendation**: **DEFER - needs fundamental rework**

---

## COUNTEREXAMPLE TO τ ≤ 8 GREEDY APPROACH

**Triangle**: T = {v_da, a_priv, v_bc}

**At v_da**, cover is {s(v_da, v_cd), s(v_da, v_ab)}

**T's edges**:
- s(v_da, a_priv) - NOT in cover
- s(v_da, v_bc) - NOT in cover
- s(a_priv, v_bc) - NOT in cover

**Conclusion**: The "diagonal spokes" strategy fails because it doesn't cover triangles containing private vertices from different M-triangles.

---

## CORRECTED APPROACH FOR τ ≤ 8

The issue is that {v_da, v_ab} and {v_da, v_cd} don't cover triangles like {v_da, a_priv, v_bc}.

**What WOULD work**:
- At v_da, need to cover ALL edges in link graph L_{v_da}
- Link graph L_{v_da} has vertex set = neighbors of v_da
- The 2-vertex cover of L_{v_da} might NOT be {v_ab, v_cd}!
- It could be {a_priv, d_priv} or some other pair

**The correct claim**: τ(L_v) ≤ 2 by König's theorem on bipartite L_v
**The incorrect claim**: {v_ab, v_cd} is that vertex cover

---

## SUBMISSION STRATEGY

1. **Submit slot139 (τ ≤ 12)** - Secure baseline result
2. **Record slot140 flaw** in `failed_approaches` table
3. **Future work**: Properly implement link graph with König's theorem scaffolding

---

## SLOT 139 EXPECTED BEHAVIOR

Aristotle should:
1. Prove `Nat.choose 3 2 = 3` using `decide` or `omega`
2. Fill in `shared_vertices_implies_shared_edge` (extract 2 from card ≥ 2)
3. Complete cardinality bounds

All are within Aristotle's 6-hour capability.

---

## SLOT 140 STATUS

**DO NOT SUBMIT** - mathematical flaw in cover construction.

The claim "diagonal spokes from each corner cover all triangles" is FALSE.

Counter-example proves this: T = {v_da, a_priv, v_bc} exists and is not covered.
