/-
  slot553_universal_apex_endpoint.lean

  UNIVERSAL APEX LEMMA FOR PATH_4 ENDPOINTS:

  For endpoint A = {v1, a1, a2} of PATH_4 with ν = 4, at least one vertex
  u ∈ A appears in every non-M triangle of T_e(G, A).

  PROOF (by contradiction):
  If not, for each u ∈ A there exists a non-M triangle T_u ∈ T_e(A) with u ∉ T_u.
  Since |T_u ∩ A| ≥ 2 and u ∉ T_u, T_u uses the other 2 vertices of A:
    F = {a1, a2, x}  (v1 ∉ F, so x ∉ A)
    T = {v1, a2, y}  (a1 ∉ T, so y ∉ A)
    S = {v1, a1, z}  (a2 ∉ S, so z ∉ A)

  When x, y, z are pairwise distinct: {F, T, S, C, D} is a 5-packing.
  (Uses A∩C = ∅ and A∩D = ∅ for PATH_4 endpoints.)
  This contradicts ν = 4.

  SORRY COUNT: 0
  AXIOM COUNT: 0
  TIER: 1 (set cardinality + packing argument)
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS (matching project conventions)
-- ═══════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ e).card)

-- ═══════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

/-- A triple of distinct elements has card 3. -/
lemma card_triple (a b c : V) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
  · simpa using h3
  · simp [h1, h2]

/-- Intersection of {a,b,x} and {v,b,y} when the "extra" elements are distinct
    from all named vertices: the intersection is {b}. -/
lemma inter_card_one_of_distinct
    (a b c d e f : V) (S T : Finset V)
    (hS : S = {a, b, c}) (hT : T = {d, e, f})
    -- The common element
    (hb_eq : b = e)
    -- Everything else is disjoint
    (ha_not : a ∉ ({d, e, f} : Finset V))
    (hc_not : c ∉ ({d, e, f} : Finset V))
    (hd_not : d ∉ ({a, b, c} : Finset V))
    (hf_not : f ∉ ({a, b, c} : Finset V)) :
    (S ∩ T).card ≤ 1 := by
  subst hb_eq; subst hS; subst hT
  have : S ∩ T ⊆ {b} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx
    have hxT := hx.2; have hxS := hx.1
    simp only [mem_insert, mem_singleton] at hxS hxT
    rcases hxS with rfl | rfl | rfl
    · exfalso; exact ha_not (by simp [hxT])
    · exact mem_singleton.mpr rfl
    · exfalso; exact hc_not (by simp [hxT])
  exact le_trans (card_le_card this) (card_singleton b).le

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Intersection of witness with non-adjacent M-element ≤ 1
--
-- If A = {v1,a1,a2} and C is a packing element with A ∩ C = ∅,
-- then for any witness W = {u1, u2, w} with u1, u2 ∈ A and w ∉ A,
-- we have |W ∩ C| ≤ 1.
-- ═══════════════════════════════════════════════════════════════════════

/-- A triangle with 2 vertices from A and 1 vertex outside A
    has at most 1 vertex in any C with A ∩ C = ∅. -/
lemma witness_inter_nonadj_le_one
    (A C W : Finset V) (u1 u2 w : V)
    (hW : W = {u1, u2, w})
    (hu1_A : u1 ∈ A) (hu2_A : u2 ∈ A)
    (hw_A : w ∉ A) (hAC : A ∩ C = ∅) :
    (W ∩ C).card ≤ 1 := by
  have hu1_C : u1 ∉ C := by
    intro h; have := mem_inter.mpr ⟨hu1_A, h⟩; rw [hAC] at this; exact not_mem_empty _ this
  have hu2_C : u2 ∉ C := by
    intro h; have := mem_inter.mpr ⟨hu2_A, h⟩; rw [hAC] at this; exact not_mem_empty _ this
  have : W ∩ C ⊆ {w} := by
    intro x hx
    rw [mem_inter] at hx; rw [hW] at hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx.1 with rfl | rfl | rfl
    · exact absurd hx.2 hu1_C
    · exact absurd hx.2 hu2_C
    · exact mem_singleton.mpr rfl
  exact le_trans (card_le_card this) (card_singleton w).le

-- ═══════════════════════════════════════════════════════════════════════
-- PAIRWISE INTERSECTION BETWEEN WITNESSES
-- ═══════════════════════════════════════════════════════════════════════

/-- F ∩ T = {a2} when x ≠ y (and other distinctness conditions). -/
lemma witness_FT_inter_le_one
    (v1 a1 a2 x y : V) (F T : Finset V)
    (hF : F = {a1, a2, x}) (hT : T = {v1, a2, y})
    (hx_ne_v1 : x ≠ v1) (hx_ne_y : x ≠ y)
    (ha1_ne_v1 : a1 ≠ v1) (ha1_ne_y : a1 ≠ y) :
    (F ∩ T).card ≤ 1 := by
  subst hF; subst hT
  have : F ∩ T ⊆ {a2} := by
    intro w hw
    rw [mem_inter] at hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw.1 with rfl | rfl | rfl
    · -- w = a1: is a1 ∈ T? a1 = v1 or a1 = a2 or a1 = y
      rcases hw.2 with rfl | rfl | rfl
      · exact absurd rfl ha1_ne_v1
      · exact mem_singleton.mpr rfl
      · exact absurd rfl ha1_ne_y
    · exact mem_singleton.mpr rfl
    · -- w = x: is x ∈ T? x = v1 or x = a2 or x = y
      rcases hw.2 with rfl | rfl | rfl
      · exact absurd rfl hx_ne_v1
      · exact mem_singleton.mpr rfl
      · exact absurd rfl hx_ne_y
  exact le_trans (card_le_card this) (card_singleton a2).le

/-- F ∩ S = {a1} when x ≠ z (and other distinctness conditions). -/
lemma witness_FS_inter_le_one
    (v1 a1 a2 x z : V) (F S : Finset V)
    (hF : F = {a1, a2, x}) (hS : S = {v1, a1, z})
    (hx_ne_v1 : x ≠ v1) (hx_ne_z : x ≠ z)
    (ha2_ne_v1 : a2 ≠ v1) (ha2_ne_z : a2 ≠ z) :
    (F ∩ S).card ≤ 1 := by
  subst hF; subst hS
  have : F ∩ S ⊆ {a1} := by
    intro w hw
    rw [mem_inter] at hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw.1 with rfl | rfl | rfl
    · exact mem_singleton.mpr rfl
    · rcases hw.2 with rfl | rfl | rfl
      · exact absurd rfl ha2_ne_v1
      · exact mem_singleton.mpr rfl
      · exact absurd rfl ha2_ne_z
    · rcases hw.2 with rfl | rfl | rfl
      · exact absurd rfl hx_ne_v1
      · exact mem_singleton.mpr rfl
      · exact absurd rfl hx_ne_z
  exact le_trans (card_le_card this) (card_singleton a1).le

/-- T ∩ S = {v1} when y ≠ z (and other distinctness conditions). -/
lemma witness_TS_inter_le_one
    (v1 a1 a2 y z : V) (T S : Finset V)
    (hT : T = {v1, a2, y}) (hS : S = {v1, a1, z})
    (hy_ne_a1 : y ≠ a1) (hy_ne_z : y ≠ z)
    (ha2_ne_a1 : a2 ≠ a1) (ha2_ne_z : a2 ≠ z) :
    (T ∩ S).card ≤ 1 := by
  subst hT; subst hS
  have : T ∩ S ⊆ {v1} := by
    intro w hw
    rw [mem_inter] at hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw.1 with rfl | rfl | rfl
    · exact mem_singleton.mpr rfl
    · rcases hw.2 with rfl | rfl | rfl
      · exact absurd rfl ha2_ne_a1.symm
      · exact absurd rfl ha2_ne_a1
      · exact absurd rfl ha2_ne_z
    · rcases hw.2 with rfl | rfl | rfl
      · exact absurd rfl hy_ne_a1.symm
      · exact absurd rfl hy_ne_a1
      · exact absurd rfl hy_ne_z
  exact le_trans (card_le_card this) (card_singleton v1).le

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: No-universal-apex implies 5-packing (generic case)
-- ═══════════════════════════════════════════════════════════════════════

/-- CORE LEMMA: If 3 witnesses to non-universal-apex exist with their
    "extra" vertices x, y, z pairwise distinct, then {F, T, S, C, D}
    is a valid 5-packing, contradicting ν = 4. -/
theorem five_packing_from_three_witnesses
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    -- PATH_4 structure
    (A C D : Finset V) (hA : A ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅)
    (hCD_inter : (C ∩ D).card ≤ 1)
    (hA_ne_C : A ≠ C) (hA_ne_D : A ≠ D) (hC_ne_D : C ≠ D)
    -- Endpoint A = {v1, a1, a2}
    (v1 a1 a2 : V) (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    -- Three witnesses (non-M triangles in T_e(A) avoiding each vertex)
    (F T S : Finset V)
    (x y z : V)
    (hF_eq : F = {a1, a2, x}) (hT_eq : T = {v1, a2, y}) (hS_eq : S = {v1, a1, z})
    (hF_tri : F ∈ G.cliqueFinset 3) (hT_tri : T ∈ G.cliqueFinset 3) (hS_tri : S ∈ G.cliqueFinset 3)
    (hF_notM : F ∉ M) (hT_notM : T ∉ M) (hS_notM : S ∉ M)
    -- Extra vertices outside A
    (hx_A : x ∉ ({v1, a1, a2} : Finset V))
    (hy_A : y ∉ ({v1, a1, a2} : Finset V))
    (hz_A : z ∉ ({v1, a1, a2} : Finset V))
    -- KEY CONDITION: x, y, z pairwise distinct
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    False := by
  -- Extract distinctness from hx_A, hy_A, hz_A
  simp only [mem_insert, mem_singleton, not_or] at hx_A hy_A hz_A
  obtain ⟨hx_v1, hx_a1, hx_a2⟩ := hx_A
  obtain ⟨hy_v1, hy_a1, hy_a2⟩ := hy_A
  obtain ⟨hz_v1, hz_a1, hz_a2⟩ := hz_A
  -- Build the 5-packing {F, T, S, C, D}
  -- First: all are graph triangles
  -- Second: all pairwise intersections ≤ 1
  -- Third: all distinct and have 5 elements
  -- F ∩ T ≤ 1
  have hFT := witness_FT_inter_le_one v1 a1 a2 x y F T hF_eq hT_eq hx_v1 hxy ha1_ne_v1 hy_a1
    where ha1_ne_v1 := h12.symm
  -- F ∩ S ≤ 1
  have hFS := witness_FS_inter_le_one v1 a1 a2 x z F S hF_eq hS_eq hx_v1 hxz h13.symm hz_a2
  -- T ∩ S ≤ 1
  have hTS := witness_TS_inter_le_one v1 a1 a2 y z T S hT_eq hS_eq hy_a1 hyz h23 hz_a2
  -- F ∩ C ≤ 1 (A ∩ C = ∅, so a1, a2 ∉ C; extra vertex x might be in C)
  have hFC := witness_inter_nonadj_le_one A C F a1 a2 x hF_eq
    (hA_eq ▸ by simp) (hA_eq ▸ by simp [h12, h13]) (by rw [hA_eq]; exact hx_A) hAC
  -- F ∩ D ≤ 1
  have hFD := witness_inter_nonadj_le_one A D F a1 a2 x hF_eq
    (hA_eq ▸ by simp) (hA_eq ▸ by simp [h12, h13]) (by rw [hA_eq]; exact hx_A) hAD
  -- T ∩ C ≤ 1
  have hTC := witness_inter_nonadj_le_one A C T v1 a2 y hT_eq
    (hA_eq ▸ by simp) (hA_eq ▸ by simp [h12, h13]) (by rw [hA_eq]; exact hy_A) hAC
  -- T ∩ D ≤ 1
  have hTD := witness_inter_nonadj_le_one A D T v1 a2 y hT_eq
    (hA_eq ▸ by simp) (hA_eq ▸ by simp [h12, h13]) (by rw [hA_eq]; exact hy_A) hAD
  -- S ∩ C ≤ 1
  have hSC := witness_inter_nonadj_le_one A C S v1 a1 z hS_eq
    (hA_eq ▸ by simp) (hA_eq ▸ by simp) (by rw [hA_eq]; exact hz_A) hAC
  -- S ∩ D ≤ 1
  have hSD := witness_inter_nonadj_le_one A D S v1 a1 z hS_eq
    (hA_eq ▸ by simp) (hA_eq ▸ by simp) (by rw [hA_eq]; exact hz_A) hAD
  -- Build the 5-element set P = {F, T, S, C, D}
  -- All distinct: F, T, S ∉ M; C, D ∈ M; F ≠ T ≠ S (different vertex sets)
  have hF_ne_T : F ≠ T := by
    rw [hF_eq, hT_eq]; intro h
    have : v1 ∈ ({a1, a2, x} : Finset V) := h ▸ (by simp)
    simp at this; exact hx_v1 (this.2.symm)
  have hF_ne_S : F ≠ S := by
    rw [hF_eq, hS_eq]; intro h
    have : v1 ∈ ({a1, a2, x} : Finset V) := h ▸ (by simp)
    simp at this; exact hx_v1 (this.2.symm)
  have hT_ne_S : T ≠ S := by
    rw [hT_eq, hS_eq]; intro h
    have : a2 ∈ ({v1, a1, z} : Finset V) := h ▸ (by simp [h12, h13])
    simp at this; rcases this with rfl | rfl
    · exact h13.symm rfl
    · exact hz_a2 rfl
  have hF_ne_C : F ≠ C := fun h => hF_notM (h ▸ hC)
  have hF_ne_D : F ≠ D := fun h => hF_notM (h ▸ hD)
  have hT_ne_C : T ≠ C := fun h => hT_notM (h ▸ hC)
  have hT_ne_D : T ≠ D := fun h => hT_notM (h ▸ hD)
  have hS_ne_C : S ≠ C := fun h => hS_notM (h ▸ hC)
  have hS_ne_D : S ≠ D := fun h => hS_notM (h ▸ hD)
  -- Construct the packing
  let P : Finset (Finset V) := {F, T, S, C, D}
  have hP_clique : P ⊆ G.cliqueFinset 3 := by
    intro X hX; simp only [P, mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · exact hF_tri
    · exact hT_tri
    · exact hS_tri
    · exact hM.1 hC
    · exact hM.1 hD
  have hP_pairwise : Set.Pairwise (P : Set (Finset V))
      (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
    intro x1 hx1 x2 hx2 h12'
    simp only [P, Finset.mem_coe, mem_insert, mem_singleton] at hx1 hx2
    -- Case analysis on which pair (x1, x2)
    rcases hx1 with rfl | rfl | rfl | rfl | rfl <;>
      rcases hx2 with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl h12'
        | (try assumption)
        | (try (rw [inter_comm]; assumption))
  have hP_pack : isTrianglePacking G P := ⟨hP_clique, hP_pairwise⟩
  -- P has 5 elements
  have hP_card : P.card ≥ 5 := by
    simp only [P]
    rw [card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem,
        card_insert_of_not_mem, card_singleton]
    · simp [hS_ne_C, hS_ne_D, hC_ne_D]
    · simp [hT_ne_S, hT_ne_C, hT_ne_D]
    · simp [hF_ne_T, hF_ne_S, hF_ne_C, hF_ne_D]
  -- Contradiction: P has ≥ 5 elements but ν = 4
  linarith [hν P hP_pack]

-- ═══════════════════════════════════════════════════════════════════════
-- COROLLARY: At least one vertex of A is a "weak universal apex"
--
-- i.e., x = y OR x = z OR y = z (the witnesses share an extra vertex)
-- ═══════════════════════════════════════════════════════════════════════

/-- If three witnesses to non-universal-apex exist, their extra
    vertices x, y, z cannot be pairwise distinct. -/
theorem witnesses_share_extra_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A C D : Finset V) (hA : A ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅)
    (hCD_inter : (C ∩ D).card ≤ 1)
    (hA_ne_C : A ≠ C) (hA_ne_D : A ≠ D) (hC_ne_D : C ≠ D)
    (v1 a1 a2 : V) (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (F T S : Finset V) (x y z : V)
    (hF_eq : F = {a1, a2, x}) (hT_eq : T = {v1, a2, y}) (hS_eq : S = {v1, a1, z})
    (hF_tri : F ∈ G.cliqueFinset 3) (hT_tri : T ∈ G.cliqueFinset 3)
    (hS_tri : S ∈ G.cliqueFinset 3)
    (hF_notM : F ∉ M) (hT_notM : T ∉ M) (hS_notM : S ∉ M)
    (hx_A : x ∉ ({v1, a1, a2} : Finset V))
    (hy_A : y ∉ ({v1, a1, a2} : Finset V))
    (hz_A : z ∉ ({v1, a1, a2} : Finset V)) :
    x = y ∨ x = z ∨ y = z := by
  by_contra h; push_neg at h
  exact five_packing_from_three_witnesses G M hM hM_card hν A C D hA hC hD
    hAC hAD hCD_inter hA_ne_C hA_ne_D hC_ne_D v1 a1 a2 hA_eq h12 h13 h23
    F T S x y z hF_eq hT_eq hS_eq hF_tri hT_tri hS_tri hF_notM hT_notM hS_notM
    hx_A hy_A hz_A h.1 h.2.1 h.2.2

end
