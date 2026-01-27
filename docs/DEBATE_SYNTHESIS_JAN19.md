# Debate Synthesis: Closing the General Theorem Gap

## Date: January 19, 2026

## Gemini's Approach: "Maximal Compatible Hypergraph" Strategy

### Core Insight
Instead of proving over abstract `V : Type*`, we:
1. Work entirely on `Fin 12` (any 4-packing uses ≤12 vertices)
2. Prove the result computationally via `native_decide`
3. Use a transfer principle to lift to arbitrary types

### Key Components

#### 1. Finite Domain Reformulation
```lean
-- Work on Fin 12 instead of abstract V
abbrev V12 := Fin 12

-- A computable check for whether a specific packing has τ ≤ 8
def check_tuza_packing (P : Finset (Finset V12)) : Bool :=
  -- Check if there exists an 8-edge cover hitting all triangles
  ...
```

#### 2. Pattern-Based Verification
Since we already have all 6 patterns verified:
- star_all_4, scattered, path_4, cycle_4, three_share_v, two_two_vw

We can reformulate as:
```lean
-- Every 4-packing on Fin 12 has one of 6 intersection patterns
theorem packing_pattern_exhaustive (M : Finset (Finset V12))
    (hM : is_4_packing M) :
    isStarAll4 M ∨ isScattered M ∨ isPath4 M ∨
    isCycle4 M ∨ isThreeShareV M ∨ isTwoTwoVW M := by
  native_decide  -- If formulated correctly on Fin 12
```

#### 3. Transfer Principle (Manual Proof)
```lean
-- The key insight: any abstract 4-packing embeds into Fin 12
theorem embedding_exists {V : Type*} [Fintype V] [DecidableEq V]
    (M : Finset (Finset V)) (hM : M.card = 4)
    (hTriangles : ∀ T ∈ M, T.card = 3) :
    ∃ (f : V → Fin 12), Function.Injective f ∧
      (∀ T ∈ M, (T.map f).card = 3) := by
  -- 4 triangles × 3 vertices = 12 max vertices
  -- This is a standard cardinality argument
  sorry -- Manual proof needed
```

### The Winning Formulation

Instead of one abstract theorem, we prove:

**Theorem A (Computational - Aristotle):**
"For every labeled 4-packing on Fin 12, there exists an 8-edge cover"

**Theorem B (Transfer - Manual):**
"Any 4-packing on arbitrary V embeds into Fin 12"

**Corollary (Combines A + B):**
"For any graph with ν = 4, τ ≤ 8"

### Implementation Plan

#### Phase 1: Pattern Exhaustiveness on Fin 12
Create `slot462_pattern_exhaustive_fin12.lean`:
- Enumerate ALL valid 4-packings on Fin 12 (or use symmetry)
- Prove each falls into one of 6 patterns
- Use `native_decide`

#### Phase 2: Universal Cover Construction
Create `slot463_universal_cover.lean`:
- For each pattern, define the cover construction function
- Prove it produces a valid cover of size ≤ 8
- Use our existing cover constructions

#### Phase 3: Main Theorem Assembly
Create `slot464_main_theorem.lean`:
- Combine pattern exhaustiveness + cover constructions
- State: "For any 4-packing on Fin 12, τ ≤ 8"
- This should be `native_decide`-able

#### Phase 4: Transfer (Manual)
Create `slot465_transfer.lean`:
- Prove the embedding lemma (manual)
- Combine with Fin 12 result
- Get the general theorem

### Why This Works for Aristotle

1. **No Abstract Types**: Everything is on `Fin 12`
2. **Decidable Predicates**: Pattern checks are `Bool`-returning
3. **Finite Search Space**: All 4-packings on Fin 12 are enumerable
4. **Leverages Existing Work**: Uses our 215+ proven theorems

### Estimated New Theorems
- slot462: ~30 theorems (pattern exhaustiveness)
- slot463: ~20 theorems (universal cover)
- slot464: ~10 theorems (assembly)
- slot465: ~5 theorems (transfer, manual)
- **Total**: ~65 new theorems

### Risk Assessment
- **High confidence**: Phases 1-3 (Aristotle Tier 1-2)
- **Medium confidence**: Phase 4 transfer (may need manual proof)
- **Fallback**: If transfer is hard, the Fin 12 result is still mathematically meaningful
