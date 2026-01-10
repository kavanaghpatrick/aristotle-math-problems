# ARISTOTLE 15-SLOT ATTACK PLAN (REVISED)
## Date: January 4, 2026
## Goal: 15 Single-Sorry Breakthrough Submissions
## Synthesized From: Grok-4, Gemini, Codex + Comprehensive Snapshot
## REVISION: Incorporates critical discovery that scattered τ ≤ 8 is FALSE

---

## ⚠️ CRITICAL DISCOVERY: SCATTERED τ ≤ 8 IS FALSE!

**Aristotle proved this counterexample in `slot148_scattered_tau_le_8_aristotle.lean`:**

```lean
theorem disproof_of_tau_le_8_scattered :
    ∃ (V : Type) ... (M : Finset (Finset V)),
      isMaxPacking G M ∧ M.card = 4 ∧
      (∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) ∧
      ¬ (triangleCoveringNumber G ≤ 8)
```

**The Counterexample**: 4 disjoint "Propeller" graphs
- Each Propeller: central triangle + 3 "petal" triangles
- τ(Propeller) = 3 (Aristotle proved this!)
- G_counter: 4 disjoint Propellers → τ(G_counter) ≥ 12
- M_counter: 4 central triangles (vertex-disjoint)

**Implication**: τ ≤ 2ν is **TIGHT** for scattered case when ν=4!

---

## EXECUTIVE SUMMARY (REVISED)

The discovery that scattered τ ≤ 8 is FALSE fundamentally changes our strategy:

| Slot Range | Strategy | Expected Breakthroughs |
|------------|----------|----------------------|
| 243-245 | Constrained Cases (star, three_share with restrictions) | 1-2 |
| 246-248 | Novel Mathematical Approaches (LP, etc.) | 1-2 |
| 249-251 | Structural Lemmas (building blocks) | 2-3 |
| 252-254 | Cycle_4 with New Insights | 0-1 |
| 255-257 | Alternative Bounds (τ ≤ 10, τ ≤ 6 for special cases) | 2-3 |

**Total Expected**: 6-11 proofs from 15 submissions = 40-73% success rate

---

## PROJECT STATE (UPDATED)

### What We KNOW
- **τ ≤ 12 PROVEN** for all ν=4 cases (slot139)
- **τ = 12 ACHIEVABLE** for scattered (4 propellers counterexample)
- **τ ≤ 8 is FALSE** for scattered case
- **Max τ = 6 observed** computationally for "natural" graphs
- **120 validated lemmas** to build on
- **22 false lemmas** to avoid (Pattern 22 added!)

### Case Difficulty Ranking (REVISED)
1. **star_all_4 (with hub externals bounded)** - POSSIBLE (τ ≤ 8)
2. **three_share_v (D isolated from hub)** - POSSIBLE (τ ≤ 8)
3. **matching_2 (no cross-pair externals)** - POSSIBLE (τ ≤ 8)
4. **scattered** - τ = 12 IS TIGHT (τ ≤ 8 FALSE!)
5. **path_4** - VERY HARD
6. **cycle_4** - HARDEST (22 false lemmas!)

### The Key Insight
Scattered case fails because each M-element can have MANY independent externals.
In the Propeller, each M-element (central triangle) has 3 petals requiring 3 edges!

For τ ≤ 8 to work, we need **structural constraints** that limit externals.

---

## THE 15 BREAKTHROUGH SUBMISSIONS

### ❌ TIER 1: SCATTERED CASE - **INVALIDATED**

**Slots 228-230 are CANCELLED** - Aristotle proved τ ≤ 8 is FALSE for scattered!

The Propeller counterexample shows τ = 12 is achievable when ν = 4 with disjoint M-elements.

---

### TIER 1 (REVISED): STAR CASE WITH BOUNDED EXTERNALS (slots 243-245)

The key insight: τ ≤ 8 might work when externals are STRUCTURALLY CONSTRAINED.

#### Slot 243: tau_le_8_star_bounded_externals
**Target**: τ ≤ 8 for star case when externals share common hub vertex

**Approach**: When all 4 M-elements share vertex v (star configuration):
- All externals at v form a "fan" - they all contain v
- Fan triangles at v can be covered by edges incident to v
- Key: Bound the number of distinct non-v vertices used

**Key Lemma** (1 sorry):
```lean
lemma tau_le_8_star_bounded (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ A ∈ M, v ∈ A)
    (h_bounded : {x : V | x ≠ v ∧ ∃ t ∈ G.cliqueFinset 3, v ∈ t ∧ x ∈ t ∧ t ∉ M}.toFinset.card ≤ 8) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Why It Works**: If externals at v use ≤ 8 distinct non-v vertices, then 8 spokes suffice.

**Confidence**: 65%

---

#### Slot 244: tau_le_6_special_star
**Target**: τ ≤ 6 for star case with very tight constraints

**Approach**: When the 4 M-elements share v and have exactly 8 vertices total:
- M uses vertices {v, a, b, c, d, e, f, g} where v is hub
- Each external uses v plus one M-vertex plus one NEW vertex
- But with only 8 M-vertices, externals are severely constrained

**Key Lemma** (1 sorry):
```lean
lemma tau_le_6_tight_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ A ∈ M, v ∈ A)
    (h_tight : (M.biUnion id).card = 9) -- exactly v + 8 other vertices
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    triangleCoveringNumber G ≤ 6 := by
  sorry
```

**Confidence**: 50%

---

#### Slot 245: externals_per_M_element_bounded_by_nu
**Target**: Prove externals per M-element is bounded when ν is fixed

**Approach**: Use the 5-packing argument (slot182 style):
- If M-element A has k externals T1, ..., Tk that are pairwise edge-disjoint
- Then {T1, ..., Tk} ∪ (M \ {A}) would be a packing of size k + 3
- So k ≤ ν - 3 = 1 for ν = 4
- But overlapping externals share common structure!

**Key Lemma** (1 sorry):
```lean
lemma externals_per_element_bounded (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (externals : Finset (Finset V))
    (h_ext : ∀ t ∈ externals, t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ (t ∩ A).card ≥ 2)
    (h_disjoint : Set.Pairwise (externals : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)) :
    externals.card ≤ 1 := by
  sorry
```

**Why It Works**: Pairwise edge-disjoint externals plus M \ {A} form a larger packing.

**Confidence**: 75%

---

### TIER 2: OTHER EASY CASES (slots 231-233)

#### Slot 231: tau_le_8_star_all_4
**Target**: τ ≤ 8 for star configuration (all 4 share vertex v)

**Approach**: All M-elements share center v:
- Every triangle passes through v (proven)
- 8 spokes from v cover all triangles
- But need to prove 8 edges suffice, not 12

**Key Lemma** (1 sorry):
```lean
lemma tau_le_8_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ A ∈ M, v ∈ A) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Why It Works**: In star case, v is in every M-element. Spokes from v hit most triangles. Need only 8 carefully chosen spokes (2 per M-element touching v).

**Confidence**: 70%

---

#### Slot 232: tau_le_8_three_share
**Target**: τ ≤ 8 for three_share_v (3 share vertex, 1 isolated)

**Approach**: Decomposition:
- Let M' = {A, B, C} share v, D isolated
- τ(M') ≤ 6 (spokes from v cover containing, bases cover avoiding)
- τ({D}) ≤ 2 (isolated = 2 edges)
- Total: 6 + 2 = 8

**Key Lemma** (1 sorry):
```lean
lemma tau_le_8_three_share (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hM_eq : M = {A, B, C, D})
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B) (hv_C : v ∈ C) (hv_D : v ∉ D)
    (h_D_isolated : ∀ X ∈ M, X ≠ D → D ∩ X = ∅) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Confidence**: 65%

---

#### Slot 233: tau_le_8_matching_2
**Target**: τ ≤ 8 for matching_2 (two disjoint vertex-sharing pairs)

**Approach**:
- Pair 1: A, B share v (like 2-element star)
- Pair 2: C, D share w (independent of pair 1)
- Each pair needs ≤ 4 edges
- Total: 4 + 4 = 8

**Key Lemma** (1 sorry):
```lean
lemma tau_le_8_matching (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hM_eq : M = {A, B, C, D})
    (v w : V) (hv_AB : v ∈ A ∧ v ∈ B) (hw_CD : w ∈ C ∧ w ∈ D)
    (h_disjoint : v ≠ w ∧ A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ C = ∅ ∧ B ∩ D = ∅) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Confidence**: 60%

---

### TIER 3: NOVEL MATHEMATICAL APPROACHES (slots 234-237)

#### Slot 234: LP_dual_witness_construction
**Target**: τ ≤ 8 via LP duality (Gemini + Grok approach)

**Approach**: Construct explicit fractional cover with weight ≤ 8:
- Define w : E → [0,1] on edges
- Prove ∀ triangle t, Σ_{e ∈ t} w(e) ≥ 1
- Prove Σ_e w(e) ≤ 8

**Key Lemma** (1 sorry):
```lean
lemma lp_dual_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    ∃ w : Sym2 V → ℝ,
      (∀ e, 0 ≤ w e ∧ w e ≤ 1) ∧
      (∀ t ∈ G.cliqueFinset 3, ∑ e in t.sym2, w e ≥ 1) ∧
      (∑ e in G.edgeFinset, w e ≤ 8) := by
  sorry
```

**Why It Works**: LP duality is bulletproof. If such a w exists, τ* ≤ 8, and integrality gap ≤ 0 for this structure would give τ ≤ 8.

**Confidence**: 55%

---

#### Slot 235: greedy_amortized_analysis
**Target**: τ ≤ 8 via greedy with amortized analysis (Gemini approach)

**Approach**: Track "potential function" during greedy:
- Φ(k) = unhit triangles after k edges selected
- Prove: Φ(k) ≤ Φ(k-1) × (1 - 1/(8-k+1))
- Telescoping: Φ(8) = 0

**Key Lemma** (1 sorry):
```lean
lemma greedy_amortized (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    ∃ greedy_selection : Fin 8 → Sym2 V,
      ∀ t ∈ G.cliqueFinset 3, ∃ i : Fin 8, greedy_selection i ∈ t.sym2 := by
  sorry
```

**Confidence**: 50%

---

#### Slot 236: induction_on_triangles
**Target**: τ ≤ 8 via strong induction on |T| (Gemini approach)

**Approach**:
- Base: |T| ≤ 8 → trivially τ ≤ 8
- Inductive: Remove triangle t, prove τ(G\t) ≤ 8 by IH
- Add back: Show t is covered by existing 8 edges OR add 0-1 edges

**Key Lemma** (1 sorry):
```lean
lemma induction_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_ind : ∀ G' : SimpleGraph V, ∀ M' : Finset (Finset V),
      isMaxPacking G' M' → M'.card = 4 →
      (G'.cliqueFinset 3).card < (G.cliqueFinset 3).card →
      triangleCoveringNumber G' ≤ 8) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Confidence**: 45%

---

#### Slot 237: discharging_method
**Target**: τ ≤ 8 via discharging (Codex approach, like 4-color proof)

**Approach**:
- Assign initial charge c(t) = 1 to each triangle
- Redistribute charge via edges
- Prove total charge ≤ 8 after redistribution

**Key Lemma** (1 sorry):
```lean
lemma discharging_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (discharge : Finset V → Sym2 V → ℝ)
    (h_conservation : ∀ t ∈ G.cliqueFinset 3, ∑ e in t.sym2, discharge t e = 1)
    (h_capacity : ∀ e ∈ G.edgeFinset, ∑ t in G.cliqueFinset 3,
      if e ∈ t.sym2 then discharge t e else 0 ≤ 1) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Confidence**: 40%

---

### TIER 4: CYCLE_4 DIRECT ATTACKS (slots 238-240)

#### Slot 238: cycle4_adaptive_cover
**Target**: τ ≤ 8 for cycle_4 via adaptive edge selection

**Approach**: Instead of fixed 8-edge subset (Pattern 9), select ADAPTIVELY:
1. For each shared vertex v, select 2 edges based on local structure
2. Total: 4 vertices × 2 = 8
3. Key: Selection depends on which externals exist

**Key Lemma** (1 sorry):
```lean
lemma adaptive_8_cover_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    ∃ selection : Fin 4 → Finset (Sym2 V),
      (∀ i, (selection i).card ≤ 2) ∧
      isTriangleCover G (Finset.univ.biUnion selection) := by
  sorry
```

**Confidence**: 30%

---

#### Slot 239: cycle4_lovasz_local_lemma
**Target**: τ ≤ 8 via Lovász Local Lemma (Grok approach)

**Approach**: Probabilistic method:
- Randomly select 8 edges with appropriate probabilities
- Use LLL to show Pr[all triangles covered] > 0
- Dependency structure of cycle_4 is bounded

**Key Lemma** (1 sorry):
```lean
lemma lll_8_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_dependency : ∀ t ∈ G.cliqueFinset 3,
      {t' ∈ G.cliqueFinset 3 | t ≠ t' ∧ (t ∩ t').card ≥ 2}.card ≤ 10) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Confidence**: 25%

---

#### Slot 240: cycle4_spectral_bound
**Target**: τ ≤ 8 via spectral graph theory (Grok approach)

**Approach**: Use triangle-adjacency graph spectral properties:
- Build adjacency matrix of triangle intersection graph
- Apply Hoffman bound for independence number
- Derive τ ≤ 8 from spectral gap

**Key Lemma** (1 sorry):
```lean
lemma spectral_8_cover (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (triangle_adj : Finset V → Finset V → Bool)
    (h_adj : ∀ t1 t2 : Finset V, triangle_adj t1 t2 = decide ((t1 ∩ t2).card ≥ 2))
    (h_spectral : ∀ eigenvalue λ of triangle_adj_matrix, |λ| ≤ 4) :
    triangleCoveringNumber G ≤ 8 := by
  sorry
```

**Confidence**: 20%

---

### TIER 5: STRUCTURAL BUILDING BLOCKS (slots 241-242)

#### Slot 241: nu_star_le_4_for_cycle4
**Target**: Prove ν* ≤ 4 for cycle_4 (enables Krivelevich bound)

**Approach**: Show fractional packing number equals integer packing number:
- Construct explicit feasible dual solution
- Use structure of cycle_4 to bound ν*

**Key Lemma** (1 sorry):
```lean
lemma nu_star_le_4_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (w : Finset V → ℝ) (hw_pos : ∀ t, w t ≥ 0)
    (hw_packing : ∀ e ∈ G.edgeFinset, ∑ t in G.cliqueFinset 3,
      if e ∈ t.sym2 then w t else 0 ≤ 1) :
    ∑ t in G.cliqueFinset 3, w t ≤ 4 := by
  sorry
```

**Why It Works**: If ν* ≤ 4, then by LP duality τ* ≤ 8, and integrality gap analysis could give τ ≤ 8.

**Confidence**: 50%

---

#### Slot 242: externals_bounded_per_vertex
**Target**: Bound on externals per shared vertex

**Approach**: Prove at most 4 externals can exist at any shared vertex:
- Each external uses one of 4 M-edges at v
- Fan structure forces sharing
- This limits the covering problem

**Key Lemma** (1 sorry):
```lean
lemma externals_at_vertex_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M) (v : V)
    (hv : v ∈ cfg.A ∧ v ∈ cfg.B) :
    {t ∈ G.cliqueFinset 3 | t ∉ M ∧ v ∈ t ∧
      ∃ A ∈ M, (t ∩ A).card ≥ 2}.card ≤ 4 := by
  sorry
```

**Confidence**: 60%

---

## PRIORITY RANKING (REVISED)

| Rank | Slot | Lemma | Confidence | Impact |
|------|------|-------|------------|--------|
| 1 | 245 | externals_per_element_bounded | 75% | Key structural lemma (enables τ ≤ 8 strategies) |
| 2 | 231 | tau_le_8_star_all_4 | 70% | First valid τ ≤ 8 case |
| 3 | 243 | tau_le_8_star_bounded | 65% | Star with constraints |
| 4 | 232 | tau_le_8_three_share | 65% | 3+1 decomposition |
| 5 | 242 | externals_bounded_per_vertex | 60% | Vertex-local bound |
| 6 | 233 | tau_le_8_matching | 60% | Disjoint pairs |
| 7 | 234 | LP_dual_witness | 55% | Novel approach |
| 8 | 244 | tau_le_6_tight_star | 50% | Stronger bound! |
| 9 | 241 | nu_star_le_4 | 50% | Enables Krivelevich |
| 10 | 235 | greedy_amortized | 50% | Algorithmic proof |
| 11 | 236 | induction_triangles | 45% | Inductive approach |
| 12 | 237 | discharging_method | 40% | 4-color style |
| 13 | 238 | cycle4_adaptive | 30% | Direct cycle_4 |
| 14 | 239 | cycle4_LLL | 25% | Probabilistic |
| 15 | 240 | cycle4_spectral | 20% | Spectral methods |

**NOTE**: Scattered case τ ≤ 8 (slots 228-230) has been REMOVED - Aristotle proved it FALSE!

---

## SUCCESS PROBABILITY ANALYSIS

**Expected proofs by confidence tier:**
- Tier 1 (80%+): 2.4 expected from 3 submissions
- Tier 2 (60-70%): 2.0 expected from 3 submissions
- Tier 3 (45-55%): 2.0 expected from 4 submissions
- Tier 4 (20-30%): 0.75 expected from 3 submissions
- Tier 5 (50-60%): 1.1 expected from 2 submissions

**Total expected proofs: 8.25 from 15 submissions = 55%**

**Best case (optimistic)**: 12-13 proofs
**Worst case (pessimistic)**: 4-5 proofs

---

## WHAT EACH PROOF WOULD MEAN

| If Proven | Significance |
|-----------|-------------|
| Any scattered τ ≤ 8 | First case of Tuza at ν=4! |
| star_all_4 τ ≤ 8 | Simplest cycle-free case |
| three_share τ ≤ 8 | 3+1 decomposition works |
| matching τ ≤ 8 | Disjoint pairs independent |
| ν* ≤ 4 | Enables LP-based τ ≤ 8 |
| Any cycle_4 τ ≤ 8 | **MAJOR BREAKTHROUGH** |

---

## IMPLEMENTATION NOTES

Each submission should have:
1. **Exactly 1 sorry** - the key lemma
2. **Full scaffolding** - proven infrastructure from slot139, slot182, slot224f
3. **Clear proof sketch** - guide Aristotle
4. **Avoid all 21 false patterns** - especially Patterns 6, 9, 17, 20, 22

---

## FILES TO CREATE

```
submissions/nu4_final/slot228_scattered_disjoint.lean
submissions/nu4_final/slot229_scattered_greedy.lean
submissions/nu4_final/slot230_scattered_explicit.lean
submissions/nu4_final/slot231_star_tau_le_8.lean
submissions/nu4_final/slot232_three_share_tau_le_8.lean
submissions/nu4_final/slot233_matching_tau_le_8.lean
submissions/nu4_final/slot234_lp_dual_witness.lean
submissions/nu4_final/slot235_greedy_amortized.lean
submissions/nu4_final/slot236_induction_triangles.lean
submissions/nu4_final/slot237_discharging.lean
submissions/nu4_final/slot238_cycle4_adaptive.lean
submissions/nu4_final/slot239_cycle4_lll.lean
submissions/nu4_final/slot240_cycle4_spectral.lean
submissions/nu4_final/slot241_nu_star_le_4.lean
submissions/nu4_final/slot242_externals_bounded.lean
```

---

## AGENT CREDITS

- **Grok-4**: LP dual, spectral methods, LLL, matroid theory
- **Gemini**: Greedy amortized, induction, clique cover, entropy
- **Codex**: Discharging, computational hybrid, structural stability
- **Comprehensive Snapshot**: Case ranking, false lemma avoidance, infrastructure

*Attack plan synthesized January 4, 2026*
