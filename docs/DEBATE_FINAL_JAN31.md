# Tuza ν=4 Three-Round Debate - Final Summary
## January 31, 2026

## PARTICIPANTS
- **Grok-4** (xAI)
- **Gemini** (Google)
- **Codex** (OpenAI)

---

## LP DISPUTE RESOLUTION

### Question: Does edge-counting prove ν* ≤ 4?

**VERDICT: NO (Codex was correct)**

All three agents agreed by Round 3:
- Edge-counting proves ν* ≥ 4 (lower bound)
- It does NOT prove ν* ≤ 4 (upper bound)

**Mathematical Proof (K4 counterexample)**:
- K4 (complete graph on 4 vertices) has ν(K4) = 1
- But ν*(K4) = 4/3 (assign weight 1/3 to each triangle)
- Relaxation can EXCEED integer packing: ν* > ν

**Implication**: Cannot use Krivelevich's τ ≤ 2ν* directly without proving ν* ≤ 4 separately.

---

## FINAL STRATEGY: Local Structure + Overlap

### Abandoned Approaches
1. ❌ LP-based (ν* ≤ 4 → τ ≤ 8) - Mathematically unsound
2. ❌ K4-free split - Octahedron counterexample
3. ❌ fan_apex_outside_A - FALSE (book case)
4. ❌ two_externals_share_edge - FALSE (share 1 vertex only)

### Adopted Approach
1. ✅ Fix concrete cases with `native_decide` first
2. ✅ Prove general spoke/base lemmas
3. ✅ Find 4 edges of overlap between pair covers
4. ✅ Allow internal fan apex (x ∈ A for book case)

---

## IMPLEMENTATION PLAN

### Phase 1: Concrete Cases (Decidable)

**File: slot49_star_all_4_clean.lean**
```lean
-- τ ≤ 4 for star configuration where v ∈ all 4 elements
-- Cover: 4 spoke edges from central vertex
theorem tau_le_4_star_all_4 :
    triangleCoveringNumber star_all_4_graph ≤ 4 := by
  native_decide
```

**File: slot50_three_share_v_clean.lean**
```lean
-- τ ≤ 5 for 3-star + isolated configuration
-- Cover: 4 spokes for 3-star + 1 edge for isolated
theorem tau_le_5_three_share_v :
    triangleCoveringNumber three_share_v_graph ≤ 5 := by
  native_decide
```

### Phase 2: General Lemmas

**File: slot51_spoke_cover_lemma.lean**
```lean
-- Spoke edges cover all triangles containing v
lemma spoke_edges_cover_containing (v : V) (hv : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumberOn G (trianglesContaining G v) ≤ 4 := by
  -- Proof: Each triangle shares edge with some e ∈ M
  -- Since v ∈ e and v ∈ t, shared edge is a spoke
  sorry
```

**File: slot52_base_cover_lemma.lean**
```lean
-- Base edges cover all triangles avoiding v
lemma base_edges_cover_avoiding (v : V) :
    triangleCoveringNumberOn G (trianglesAvoiding G v) ≤ 4 := by
  -- Proof: By avoiding_contains_base_edge
  sorry
```

### Phase 3: Assembly

**File: slot53_triple_apex_fixed.lean**
```lean
theorem tau_le_8_triple_apex :
    triangleCoveringNumber G ≤ 8 := by
  by_cases h : (packingElementsContaining M v).card = 4
  · -- STAR_ALL_4
    calc τ ≤ τ(containing) + τ(avoiding) := tau_union_le_sum
         _ ≤ 4 + 4 := by apply spoke + base lemmas
         _ = 8 := rfl
  · -- THREE_SHARE_V
    -- Use τ_S_le_2 for isolated element
    sorry
```

---

## VALIDATED TRUE LEMMAS (Safe)

| Lemma | Status |
|-------|--------|
| tau_S_le_2 | ✅ PROVEN |
| tau_X_le_2 | ✅ PROVEN |
| tau_pair_le_6 | ✅ PROVEN |
| tau_union_le_sum | ✅ PROVEN |
| bridges_contain_v | ✅ PROVEN |
| avoiding_contains_base_edge | ✅ PROVEN |

## FALSE LEMMAS (Do Not Use)

| Lemma | Evidence |
|-------|----------|
| two_externals_share_edge | 🔴 Aristotle |
| fan_apex_outside_A | 🟠 AI |
| tau_pair_le_4 | ⚪ Trivial |
| bridge_absorption | 🔴 Aristotle |
| sym2_cover_cardinality | 🔴 Aristotle |
| ν* ≤ 4 via edge-counting | 🔴 K4 counterexample |

---

## NEXT STEPS

1. Create `slot49_star_all_4_clean.lean` with explicit Fin 9 graph
2. Submit to Aristotle with `native_decide`
3. If successful, create slot50 for three_share_v
4. Then create general lemmas (slot51, slot52)
5. Finally assemble in slot53

---

## DEBATE STATISTICS

| Round | Topics | Key Resolution |
|-------|--------|----------------|
| 1 | Strategy selection | Hybrid approach preferred |
| 2 | Technical details | Fan apex must allow internal |
| 3 | Implementation | LP approach abandoned, concrete cases first |

**Total API calls**: 9 (3 rounds × 3 agents)
**Consensus achieved**: Yes, all agree on implementation plan
