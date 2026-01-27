/-
  slot444_tau_le_8_coordinated.lean

  MAIN THEOREM: τ ≤ 8 for PATH_4 (ν = 4) with COORDINATED COVER

  DEBATE SYNTHESIS (Jan 16, 2026):
  - False Lemma #31: "Vertex coverage ≠ triangle coverage"
  - Grok counterexample: Bridge {v1, a1, v2} can be missed by naive selection
  - Solution: COORDINATED selection that ensures bridges are covered

  STRATEGY: Spine-Priority with B-C Coordination
  - Middle elements (B, C) prioritize spines to cover most bridges
  - If B-C bridge exists, at least one must include the shared-facing leg
  - Endpoints (A, D) use adaptive selection (slot422)

  KEY INSIGHT: If middle element has S_e on BOTH spine AND away-leg,
  it's forced to use those two edges. The B-C conflict scenario
  (both B and C forced to away-legs) is handled by hypothesis.

  TIER: 2 (uses proven scaffolding, case analysis)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (with explicit type class parameters)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglesSharingEdge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def S_e_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A bridge between E and F is a triangle sharing edge with both -/
def isBridge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T E F : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ 2 ≤ (T ∩ E).card ∧ 2 ≤ (T ∩ F).card

def bridgesBetween {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ E).card ∧ 2 ≤ (T ∩ F).card)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Bridge contains shared vertex (from slot441)
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    ext x; simp only [mem_inter, mem_singleton]; constructor
    · intro ⟨⟨hxT, hxE⟩, _, hxF⟩
      have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE, hxF⟩
      rw [hEF] at hx_both
      exact ⟨hxT, mem_singleton.mp hx_both⟩
    · intro ⟨hxT, hxv⟩
      have hv_mem : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      rw [hxv]
      exact ⟨⟨hxT, (mem_inter.mp hv_mem).1⟩, hxT, (mem_inter.mp hv_mem).2⟩
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx; simp only [mem_union, mem_inter] at hx
    cases hx with | inl h => exact h.1 | inr h => exact h.1
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
      calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
        _ = 3 := hT_card
    omega
  rw [card_pos] at h_pos
  obtain ⟨x, hx⟩ := h_pos
  simp only [mem_inter, mem_singleton] at hx
  exact hx.2 ▸ hx.1

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge edge structure
-- ══════════════════════════════════════════════════════════════════════════════

/--
For a bridge T between E and F with shared vertex v:
- T = {v, x, y} where x ∈ E, y ∈ F
- T's edges are: s(v,x), s(v,y), s(x,y)
- s(v,x) is an edge of E
- s(v,y) is an edge of F
- s(x,y) is a "bridge edge" (not in E or F unless x=y, impossible)
-/
lemma bridge_edge_structure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hE_card : E.card = 3) (hF_card : F.card = 3)
    (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    ∃ x y : V, x ∈ E ∧ x ≠ v ∧ y ∈ F ∧ y ≠ v ∧ T = {v, x, y} := by
  have hv_T := bridge_contains_shared G E F v hEF T hT hTE hTF
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  -- T ∩ E has size ≥ 2 and contains v, so there's x ∈ T ∩ E with x ≠ v
  have h_TE_v : v ∈ T ∩ E := by
    rw [mem_inter]
    constructor
    · exact hv_T
    · have hv_EF : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      exact (mem_inter.mp hv_EF).1
  have h_exists_x : ∃ x ∈ T ∩ E, x ≠ v := by
    by_contra h_all
    push_neg at h_all
    have h_sub : T ∩ E ⊆ {v} := by
      intro z hz
      rw [mem_singleton]
      exact h_all z hz
    have h_card_le : (T ∩ E).card ≤ 1 := by
      calc (T ∩ E).card ≤ ({v} : Finset V).card := card_le_card h_sub
        _ = 1 := card_singleton v
    omega
  obtain ⟨x, hx_TE, hx_ne⟩ := h_exists_x
  -- Similarly for F
  have h_TF_v : v ∈ T ∩ F := by
    rw [mem_inter]
    constructor
    · exact hv_T
    · have hv_EF : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      exact (mem_inter.mp hv_EF).2
  have h_exists_y : ∃ y ∈ T ∩ F, y ≠ v := by
    by_contra h_all
    push_neg at h_all
    have h_sub : T ∩ F ⊆ {v} := by
      intro z hz
      rw [mem_singleton]
      exact h_all z hz
    have h_card_le : (T ∩ F).card ≤ 1 := by
      calc (T ∩ F).card ≤ ({v} : Finset V).card := card_le_card h_sub
        _ = 1 := card_singleton v
    omega
  obtain ⟨y, hy_TF, hy_ne⟩ := h_exists_y
  use x, y
  simp only [mem_inter] at hx_TE hy_TF
  refine ⟨hx_TE.2, hx_ne, hy_TF.2, hy_ne, ?_⟩
  -- Show T = {v, x, y}
  ext z
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hz
    -- z ∈ T, T has 3 elements: v, x, y
    -- Show z = v ∨ z = x ∨ z = y
    by_contra h_none
    push_neg at h_none
    -- T contains v, x, y, z with z ≠ v, x, y
    have h_four : 4 ≤ ({v, x, y, z} : Finset V).card := by
      rw [card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
      · simp [h_none.2.2]
      · simp [h_none.2.1, hx_ne.symm]
      · simp [h_none.1, hy_ne.symm, ?_]
        -- x ≠ y: x ∈ E\{v}, y ∈ F\{v}, and E ∩ F = {v}
        intro hxy
        rw [hxy] at hx_TE
        have : y ∈ E ∩ F := mem_inter.mpr ⟨hx_TE.2, hy_TF.2⟩
        rw [hEF] at this
        exact hy_ne (mem_singleton.mp this)
    have h_sub : {v, x, y, z} ⊆ T := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hv_T
      · exact hx_TE.1
      · exact hy_TF.1
      · exact hz
    have : ({v, x, y, z} : Finset V).card ≤ T.card := card_le_card h_sub
    omega
  · intro hz
    rcases hz with rfl | rfl | rfl
    · exact hv_T
    · exact hx_TE.1
    · exact hy_TF.1

-- ══════════════════════════════════════════════════════════════════════════════
-- COORDINATION PREDICATE
-- ══════════════════════════════════════════════════════════════════════════════

/--
A cover assignment for an element E is "coordinated" if:
1. It uses exactly 2 edges from E
2. It covers all S_e externals of E
3. It covers its share of bridges (or the neighbor covers them)
-/
def coordinatedCoverFor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (E : Finset V) (cover : Finset (Sym2 V)) : Prop :=
  cover.card = 2 ∧
  cover ⊆ E.sym2 ∩ G.edgeFinset ∧
  ∀ T ∈ S_e G M E, ∃ e ∈ cover, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4 with coordination hypothesis
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (COORDINATED ASSEMBLY):

PATH_4 structure: A—v1—B—v2—C—v3—D where:
  A = {a1, a2, v1}, B = {v1, b, v2}, C = {v2, c, v3}, D = {v3, d1, d2}
  A ∩ B = {v1}, B ∩ C = {v2}, C ∩ D = {v3}

CONSTRUCTION:
1. For each element, choose 2 edges adaptively:
   - Cover all S_e externals (slot422 guarantees possible)
   - If bridge requires specific edge, prioritize it

2. For bridges between adjacent pairs:
   - By bridge_contains_shared, bridge T contains shared vertex v
   - T = {v, x, y} with x from E, y from F
   - T's edges are s(v,x) ∈ E, s(v,y) ∈ F, s(x,y) bridge edge
   - At least one of E's cover or F's cover must include s(v,x) or s(v,y)

3. Coordination guarantee:
   - If E can't cover bridge (both edges needed for S_e), F must cover it
   - By slot412, E has at most 2 nonempty S_e types, so one edge type is "free"
   - Use free edge type for bridges when needed

HYPOTHESIS: We assume no "conflict scenario" where both adjacent middles
are forced to use away-legs while a B-C bridge exists. (To be proven separately)

CARDINALITY: |Cover| = 2+2+2+2 = 8
-/

theorem tau_le_8_path4_coordinated {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    -- PATH_4 elements
    (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    -- Triangle definitions
    (hA_eq : A = {a1, a2, v1})
    (hB_eq : B = {v1, b, v2})
    (hC_eq : C = {v2, c, v3})
    (hD_eq : D = {v3, d1, d2})
    -- All are cliques
    (hA_clq : A ∈ G.cliqueFinset 3)
    (hB_clq : B ∈ G.cliqueFinset 3)
    (hC_clq : C ∈ G.cliqueFinset 3)
    (hD_clq : D ∈ G.cliqueFinset 3)
    -- PATH structure
    (hAB : A ∩ B = {v1})
    (hBC : B ∩ C = {v2})
    (hCD : C ∩ D = {v3})
    (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hBD : Disjoint B D)
    -- Distinctness
    (h_all_distinct : [a1, a2, v1, b, v2, c, v3, d1, d2].Nodup)
    -- Packing
    (M : Finset (Finset V)) (hM : M = {A, B, C, D})
    (hPacking : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, 2 ≤ (T ∩ E).card)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    -- 6-packing constraint (slot412)
    (h_6pack : ∀ E ∈ M, ∀ x y z : V, E = {x, y, z} →
      ¬((S_e_edge G M x y z).Nonempty ∧ (S_e_edge G M y z x).Nonempty ∧ (S_e_edge G M x z y).Nonempty))
    -- COORDINATION HYPOTHESIS: No conflict scenario for B-C bridges
    -- (If B-C bridge exists, at least one of B or C can include the shared-facing leg)
    (h_BC_coord : ∀ T ∈ bridgesBetween G B C,
      -- Either B's S_e allows using {b, v2}
      (¬((S_e_edge G M v1 v2 b).Nonempty ∧ (S_e_edge G M v1 b v2).Nonempty)) ∨
      -- Or C's S_e allows using {v2, c}
      (¬((S_e_edge G M v2 v3 c).Nonempty ∧ (S_e_edge G M c v3 v2).Nonempty))) :
    ∃ Cover : Finset (Sym2 V),
      Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE: τ ≤ 8 without coordination hypothesis (for Fin 9 testing)
-- ══════════════════════════════════════════════════════════════════════════════

/--
Simpler version: Prove on Fin 9 with explicit cover construction.
This helps verify the coordination hypothesis is achievable.
-/
theorem tau_le_8_path4_fin9 :
    ∀ G : SimpleGraph (Fin 9), ∀ [DecidableRel G.Adj],
    ∀ A B C D : Finset (Fin 9),
    A = {0, 1, 2} → B = {2, 3, 4} → C = {4, 5, 6} → D = {6, 7, 8} →
    A ∈ G.cliqueFinset 3 → B ∈ G.cliqueFinset 3 →
    C ∈ G.cliqueFinset 3 → D ∈ G.cliqueFinset 3 →
    (∀ T ∈ G.cliqueFinset 3, T ∉ {A, B, C, D} →
      ∃ E ∈ ({A, B, C, D} : Finset (Finset (Fin 9))), 2 ≤ (T ∩ E).card) →
    ∃ Cover : Finset (Sym2 (Fin 9)),
      Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  sorry

end
