# Tuza ν=4 Debate Round 2 Summary
## January 31, 2026

## Key Finding: Octahedron τ ≤ 8 VERIFIED

The octahedron counterexample does NOT break Tuza's conjecture:
```
Cover (8 edges): {0,1}, {0,2}, {0,3}, {0,5}, {1,4}, {2,4}, {3,4}, {4,5}
All 8 triangles: ✓ covered
```

The K4-free split strategy failed, but the conjecture holds.

---

## Agent Recommendations

### Grok-4: Fix 2-Sorry Cases
- Focus on star_all_4 and three_share_v (each has 2 sorries)
- Apply tau_pair_le_6 to pairs and subtract overlaps
- Octahedron fits into scattered/two_two_vw naturally

### Gemini: Weaken Fan Apex Lemma
- Current fan_apex_exists is FALSE (forbids apex in A)
- New formulation: `∃ x : V, ∀ T ∈ externalsOf G M A, x ∈ T`
- Allows "book" case where apex is edge vertex of A
- Gives τ(externals) ≤ 3 in all cases

### Codex: Explicit Octahedron Proof
- Create `slotXXX_octahedron_tau_le_8.lean`
- Use `native_decide` with explicit 8-edge cover
- Validates the bound constructively

---

## Consensus Strategy

1. **Immediate**: Prove octahedron τ≤8 via `native_decide` (Codex)
2. **Short-term**: Implement weakened Fan Apex lemma (Gemini)
3. **Medium-term**: Fix 2-sorry cases in star_all_4, three_share_v (Grok)
4. **Final**: Tighten scattered/two_two_vw from τ≤12 to τ≤8

---

## Action Items

### Priority 1: Octahedron Explicit Proof
Create Lean file with:
- V6 := Fin 6
- Octahedron edges (12 total)
- Packing M = {{0,1,2}, {1,3,4}, {2,4,5}, {0,3,5}}
- Cover C = {s(0,1), s(0,2), s(0,3), s(0,5), s(1,4), s(2,4), s(3,4), s(4,5)}
- Prove via native_decide

### Priority 2: Weak Fan Apex
```lean
theorem fan_apex_exists_weak
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ x : V, ∀ T ∈ externalsOf G M A, x ∈ T
```

### Priority 3: Star/Three_share_v
- Locate the 2 sorries in tau_le_8_triple_apex
- Apply proven lemmas (tau_S_le_2, tau_X_le_2, tau_pair_le_6)
- Complete proofs

---

## False Strategies to Avoid

1. ❌ K4 vs K4-free split (octahedron breaks this)
2. ❌ tau_pair_le_4 (correct bound is 6)
3. ❌ fan_apex_outside_A (book case has apex in A)
4. ❌ link_graph_bipartite (can have odd cycles)
5. ❌ local_cover_le_2 (can need 4+ edges)
