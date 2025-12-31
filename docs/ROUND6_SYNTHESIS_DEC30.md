# CYCLE_4 ROUND 6 SYNTHESIS - FINAL FORMALIZATION STRATEGY
## December 30, 2025

---

## AI CONSENSUS ON LEAN TACTICS

### All Three AIs Agree On:

| Component | Recommended Approach | Difficulty |
|-----------|---------------------|------------|
| `cycle4_triangle_contains_shared` | Pigeonhole via Finset.card_sdiff | **EASY** |
| `sunflower_cover_at_vertex` | Direct explicit construction | **HARD** |
| König's theorem | **SKIP** - not in Mathlib, too complex | N/A |
| Fallback τ ≤ 12 | Use all M-edges | **TRIVIAL** |

---

## KEY TACTICS FOR EACH LEMMA

### 1. Pigeonhole (`cycle4_triangle_contains_shared`)

**Strategy:** If `t ∩ A` has ≥2 elements and `t` avoids shared vertices, then `t ∩ A ⊆ {a_priv}`, so `|t ∩ A| ≤ 1`. Contradiction.

```lean
-- Key tactic sequence:
by_contra h_none
push_neg at h_none
have h_sub : t ∩ cfg.A ⊆ cfg.A \ {cfg.v_ab, cfg.v_da} := by aesop
have h_card : (cfg.A \ {cfg.v_ab, cfg.v_da}).card = 1 := by
  simp [Finset.card_sdiff]; omega
calc (t ∩ cfg.A).card ≤ 1 := Finset.card_le_card h_sub ▸ h_card
omega  -- contradicts |t ∩ A| ≥ 2
```

**Missing Ingredient:** Distinctness axioms (v_ab ≠ v_da, etc.)

### 2. Two-Edge Cover (`sunflower_cover_at_vertex`)

**Strategy:** At v_ab, use diagonal spokes `{v_ab, v_da}` and `{v_ab, v_bc}`.

```lean
-- At v_ab:
use {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc)}

-- Coverage argument:
-- 1. M-elements A, B are covered by their internal edges
-- 2. External triangles share edge with M (by triangle_shares_edge_with_packing)
-- 3. If external t contains v_ab and shares edge with A or B, covered!
-- 4. If shares edge with C or D (doesn't contain v_ab)... contradiction!
```

**Key insight (Codex):** This is where the Round 5 analysis matters:
- External triangles at v_ab MUST share edge with A or B (not C or D)
- Because C and D don't contain v_ab!

### 3. Final Min Extraction (`tau_le_8_cycle4`)

```lean
have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨E_total, h_in⟩
obtain ⟨n, hn⟩ := Finset.Nonempty.min_eq_some (h_nonempty.image Finset.card)
calc n ≤ E_total.card := Finset.min_le ...
     _ ≤ 8 := h_card
```

---

## RECOMMENDED EXECUTION PLAN

### Step 1: Add Distinctness to Cycle4 Structure

```lean
structure Cycle4 ... where
  ...
  h_distinct_ab_bc : v_ab ≠ v_bc
  h_distinct_ab_cd : v_ab ≠ v_cd
  h_distinct_ab_da : v_ab ≠ v_da
  h_distinct_bc_cd : v_bc ≠ v_cd
  h_distinct_bc_da : v_bc ≠ v_da
  h_distinct_cd_da : v_cd ≠ v_da
```

**This makes ALL the pigeonhole proofs trivial!**

### Step 2: Submit τ ≤ 12 First (Fallback)

```lean
theorem tau_le_12_cycle4 ... :
    triangleCoveringNumber G ≤ 12 := by
  let E_M := cfg.A.sym2 ∪ cfg.B.sym2 ∪ cfg.C.sym2 ∪ cfg.D.sym2
  -- |E_M| ≤ 12 (4 triangles × 3 edges)
  -- Every triangle shares edge with M → covered
  sorry
```

### Step 3: Attempt τ ≤ 8 with Greedy Spokes

Focus on ONE shared vertex first (v_ab), then copy pattern.

---

## MATHLIB LEMMA CHEAT SHEET

### Finset Cardinality
```lean
Finset.card_le_card : s ⊆ t → s.card ≤ t.card
Finset.card_sdiff : s ⊆ t → (t \ s).card = t.card - s.card
Finset.card_insert_of_not_mem : a ∉ s → (insert a s).card = s.card + 1
Finset.card_union_le : (s ∪ t).card ≤ s.card + t.card
```

### Finset Min/Max
```lean
Finset.Nonempty.min_eq_some : s.Nonempty → ∃ n, s.min = some n
Finset.min_le : x ∈ s → s.min.getD default ≤ x
```

### Tactics
```lean
omega      -- Linear arithmetic on Nat
by_contra  -- Proof by contradiction
push_neg   -- Negate and push through quantifiers
aesop      -- Automated reasoning
rcases     -- Pattern matching
obtain     -- Extract existentials
calc       -- Calculation chains
```

---

## SUCCESS PROBABILITY ESTIMATES

| Target | Success Rate | Aristotle Time |
|--------|--------------|----------------|
| τ ≤ 12 (fallback) | **95%** | 2-3 hours |
| τ ≤ 8 (greedy spokes) | **70%** | 5-6 hours |
| τ ≤ 8 (optimal/König) | **40%** | >6 hours (timeout risk) |

---

## FINAL RECOMMENDATION

1. **Submit τ ≤ 12 immediately** - secure baseline
2. **Add distinctness axioms** - unlocks cleaner proofs
3. **Attempt τ ≤ 8 greedy** - one vertex at a time
4. **Skip König approach** - too complex for timeout

**The diagonal spokes strategy from Round 5 is correct and feasible!**

Key insight: External triangles at shared vertex v MUST share edge with M-elements containing v (not the others), so 2 spokes from v suffice.
