/-
  slot432_bridge_analysis.lean

  CRITICAL ANALYSIS: Do we really need 3 edges for middle elements?

  MULTI-AGENT FINDING (Jan 15, 2026):
  - T₁ = {v₁, b₃, a₂} (A-B bridge using left spoke) and
  - T₂ = {v₂, b₃, c₄} (B-C bridge using right spoke)
  CAN BOTH EXIST in a valid PATH_4 graph.

  The spine edge {v₁, v₂} covers NEITHER of these.

  KEY INSIGHT: Bridges are covered by BOTH adjacent elements!
  - T₁ = {v₁, b₃, a₂} is covered if A's selection includes {v₁, a₂}
  - T₂ = {v₂, b₃, c₄} is covered if C's selection includes {v₂, c₄}

  So even if B's 2-edge selection misses some bridges, the adjacent
  endpoint's selection can cover them!

  REVISED STRATEGY:
  For PATH_4: A—v₁—B—v₂—C—v₃—D

  1. Endpoints A and D: adaptive 2-edge selection (proven in slot426)
     - A covers: A itself, S_e(A) externals, AND A-side of all A-B bridges
     - D covers: D itself, S_e(D) externals, AND D-side of all C-D bridges

  2. Middles B and C: use SPINE + one spoke
     - B uses {s(v₁,v₂), s(v₁,b₃) or s(v₂,b₃)}
     - C uses {s(v₂,v₃), s(v₂,c₄) or s(v₃,c₄)}

  3. Bridge coverage analysis:
     - A-B bridges: share edge with A AND B
       * A's selection covers if A chose the right spoke
       * B's spine covers if bridge uses spine
       * Need to verify ALL A-B bridges hit at least one selection

  TIER: 2 (analysis with proven scaffolding)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ≠ A ∧ T ≠ B ∧ (T ∩ A).card ≥ 2 ∧ (T ∩ B).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge is covered by at least one adjacent element's selection
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
An A-B bridge T shares edges with BOTH A and B.
- T ∩ A ≥ 2 means T shares an edge {x, y} ⊆ A with A
- T ∩ B ≥ 2 means T shares an edge {u, v} ⊆ B with B

If A's adaptive selection includes the edge that T shares with A,
then T is covered by A's selection.

Similarly for B's selection.

The question is: can we guarantee at least one selection hits T?
-/

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

lemma bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (v : V) (hAB : A ∩ B = {v})
    (T : Finset V) (hT : isBridge G A B T) :
    v ∈ T := by
  obtain ⟨hT_clq, hT_ne_A, hT_ne_B, hTA, hTB⟩ := hT
  by_contra hv_not
  have h_disj : Disjoint (T ∩ A) (T ∩ B) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hx_inter : x ∈ A ∩ B := mem_inter.mpr ⟨mem_of_mem_inter_right hxA, mem_of_mem_inter_right hxB⟩
    rw [hAB] at hx_inter
    simp only [mem_singleton] at hx_inter
    rw [hx_inter] at hxA
    exact hv_not (mem_of_mem_inter_left hxA)
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq
    exact hT_clq.1.card_eq
  have h_union : (T ∩ A ∪ T ∩ B) ⊆ T := union_subset inter_subset_left inter_subset_left
  have h_card : (T ∩ A ∪ T ∩ B).card ≤ T.card := card_le_card h_union
  rw [card_union_of_disjoint h_disj] at h_card
  omega

/-
KEY LEMMA: A-B bridge uses exactly one "private" vertex from each element.

For A = {v₁, a₂, a₃} and B = {v₁, v₂, b₃} with A ∩ B = {v₁}:
An A-B bridge T = {v₁, x, y} where:
- x ∈ A \ {v₁} (so x ∈ {a₂, a₃})
- y ∈ B \ {v₁} (so y ∈ {v₂, b₃})

This means T shares edge {v₁, x} with A and edge {v₁, y} with B.
-/
lemma ab_bridge_structure (A B : Finset V) (v₁ a₂ a₃ v₂ b₃ : V)
    (hA : A = {v₁, a₂, a₃}) (hB : B = {v₁, v₂, b₃})
    (hAB : A ∩ B = {v₁})
    (hdist_A : v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hdist_B : v₁ ≠ v₂ ∧ v₁ ≠ b₃ ∧ v₂ ≠ b₃)
    (T : Finset V) (hT_card : T.card = 3)
    (hv₁_T : v₁ ∈ T)
    (hTA : (T ∩ A).card ≥ 2) (hTB : (T ∩ B).card ≥ 2) :
    ∃ (x y : V), x ∈ ({a₂, a₃} : Finset V) ∧ y ∈ ({v₂, b₃} : Finset V) ∧
      T = {v₁, x, y} := by
  -- T ∩ A has ≥2 elements including v₁, so contains some aᵢ
  have hv₁_A : v₁ ∈ A := by rw [hA]; simp
  have hv₁_B : v₁ ∈ B := by rw [hB]; simp
  have hv₁_TA : v₁ ∈ T ∩ A := mem_inter.mpr ⟨hv₁_T, hv₁_A⟩
  have hv₁_TB : v₁ ∈ T ∩ B := mem_inter.mpr ⟨hv₁_T, hv₁_B⟩
  -- Find x ∈ (T ∩ A) \ {v₁}
  have h_exists_x : ∃ x ∈ T ∩ A, x ≠ v₁ := by
    by_contra h; push_neg at h
    have h_sub : T ∩ A ⊆ {v₁} := fun w hw => mem_singleton.mpr (h w hw)
    have h_card : (T ∩ A).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  -- Find y ∈ (T ∩ B) \ {v₁}
  have h_exists_y : ∃ y ∈ T ∩ B, y ≠ v₁ := by
    by_contra h; push_neg at h
    have h_sub : T ∩ B ⊆ {v₁} := fun w hw => mem_singleton.mpr (h w hw)
    have h_card : (T ∩ B).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  obtain ⟨x, hx_TA, hx_ne⟩ := h_exists_x
  obtain ⟨y, hy_TB, hy_ne⟩ := h_exists_y
  have hx_T : x ∈ T := mem_of_mem_inter_left hx_TA
  have hx_A : x ∈ A := mem_of_mem_inter_right hx_TA
  have hy_T : y ∈ T := mem_of_mem_inter_left hy_TB
  have hy_B : y ∈ B := mem_of_mem_inter_right hy_TB
  -- x ∈ A \ {v₁} = {a₂, a₃}
  rw [hA] at hx_A
  simp only [mem_insert, mem_singleton] at hx_A
  have hx_priv : x ∈ ({a₂, a₃} : Finset V) := by
    simp only [mem_insert, mem_singleton]
    rcases hx_A with rfl | rfl | rfl
    · exact absurd rfl hx_ne
    · left; rfl
    · right; rfl
  -- y ∈ B \ {v₁} = {v₂, b₃}
  rw [hB] at hy_B
  simp only [mem_insert, mem_singleton] at hy_B
  have hy_priv : y ∈ ({v₂, b₃} : Finset V) := by
    simp only [mem_insert, mem_singleton]
    rcases hy_B with rfl | rfl | rfl
    · exact absurd rfl hy_ne
    · left; rfl
    · right; rfl
  -- T = {v₁, x, y}
  use x, y, hx_priv, hy_priv
  -- Prove T = {v₁, x, y}
  ext z
  constructor
  · intro hz_T
    simp only [mem_insert, mem_singleton]
    -- z ∈ T, |T| = 3, {v₁, x, y} ⊆ T
    have h_sub : ({v₁, x, y} : Finset V) ⊆ T := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hv₁_T
      · exact hx_T
      · exact hy_T
    -- Need x ≠ y to have |{v₁, x, y}| = 3
    have hx_ne_y : x ≠ y := by
      intro hxy
      rw [hxy] at hx_A
      -- y ∈ A and y ∈ B, so y ∈ A ∩ B = {v₁}
      have hy_AB : y ∈ A ∩ B := mem_inter.mpr ⟨hx_A, hy_B⟩
      rw [hAB] at hy_AB
      simp only [mem_singleton] at hy_AB
      exact hy_ne hy_AB
    have h_sub_card : ({v₁, x, y} : Finset V).card = 3 := by
      rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
      · simp [hx_ne_y]
      · simp [hx_ne, hx_ne_y]
    have h_eq : T = {v₁, x, y} := Finset.eq_of_subset_of_card_le h_sub (by rw [h_sub_card]; exact hT_card.le)
    rw [h_eq] at hz_T
    simp only [mem_insert, mem_singleton] at hz_T
    exact hz_T
  · intro hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv₁_T
    · exact hx_T
    · exact hy_T

/-
CRITICAL LEMMA: Every A-B bridge is covered by A's or B's edge selection.

For bridge T = {v₁, x, y} where x ∈ {a₂, a₃} and y ∈ {v₂, b₃}:
- T shares edge {v₁, x} with A
- T shares edge {v₁, y} with B

A's 2-edge selection covers all A-related triangles using at most 2 of A's 3 edges.
B's 2-edge selection covers all B-related triangles using at most 2 of B's 3 edges.

Case analysis on which edges are selected:
- If A selects {v₁, x}: T is covered by A ✓
- If B selects {v₁, y}: T is covered by B ✓
- If neither: need to verify this can't happen

KEY INSIGHT: The "at most 2 of 3" constraint for A and B together
ensures at least one of {v₁, x} or {v₁, y} is in some selection!
-/

theorem ab_bridge_covered_by_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (v₁ a₂ a₃ v₂ b₃ : V)
    (hA : A = {v₁, a₂, a₃}) (hB : B = {v₁, v₂, b₃})
    (hAB : A ∩ B = {v₁})
    (hdist_A : v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hdist_B : v₁ ≠ v₂ ∧ v₁ ≠ b₃ ∧ v₂ ≠ b₃)
    -- A's selection: 2 edges from A
    (eA₁ eA₂ : Sym2 V) (heA₁ : eA₁ ∈ A.sym2) (heA₂ : eA₂ ∈ A.sym2)
    -- B's selection: 2 edges from B
    (eB₁ eB₂ : Sym2 V) (heB₁ : eB₁ ∈ B.sym2) (heB₂ : eB₂ ∈ B.sym2)
    -- Key constraint: selections include the shared spoke {v₁, ?}
    -- This is where the adaptive selection ensures coverage
    (h_A_covers_spokes : s(v₁, a₂) ∈ ({eA₁, eA₂} : Finset (Sym2 V)) ∨
                         s(v₁, a₃) ∈ ({eA₁, eA₂} : Finset (Sym2 V)))
    (h_B_covers_left : s(v₁, v₂) ∈ ({eB₁, eB₂} : Finset (Sym2 V)) ∨
                       s(v₁, b₃) ∈ ({eB₁, eB₂} : Finset (Sym2 V)))
    (T : Finset V)
    (hT : isBridge G A B T) :
    ∃ e ∈ ({eA₁, eA₂, eB₁, eB₂} : Finset (Sym2 V)), e ∈ T.sym2 := by
  obtain ⟨hT_clq, hT_ne_A, hT_ne_B, hTA, hTB⟩ := hT
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq
    exact hT_clq.1.card_eq
  have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT
  -- Get bridge structure: T = {v₁, x, y}
  obtain ⟨x, y, hx_priv, hy_priv, hT_eq⟩ := ab_bridge_structure A B v₁ a₂ a₃ v₂ b₃
    hA hB hAB hdist_A hdist_B T hT_card hv₁_T hTA hTB
  -- T shares edge {v₁, x} with A where x ∈ {a₂, a₃}
  -- T shares edge {v₁, y} with B where y ∈ {v₂, b₃}
  simp only [mem_insert, mem_singleton] at hx_priv hy_priv
  rcases hx_priv with rfl | rfl
  · -- x = a₂: T shares {v₁, a₂} with A
    rcases h_A_covers_spokes with h | h
    · -- A selected s(v₁, a₂)
      simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl
      · use eA₁, by simp
        rw [hT_eq]
        exact edge_in_sym2 _ v₁ a₂ (by simp) (by simp [hdist_A.1])
      · use eA₂, by simp
        rw [hT_eq]
        exact edge_in_sym2 _ v₁ a₂ (by simp) (by simp [hdist_A.1])
    · -- A selected s(v₁, a₃), not s(v₁, a₂)
      -- Need B's selection to cover
      rcases hy_priv with rfl | rfl
      · -- y = v₂: T = {v₁, a₂, v₂}, B's spine covers
        rcases h_B_covers_left with hB | hB
        · simp only [mem_insert, mem_singleton] at hB
          rcases hB with rfl | rfl
          · use eB₁, by simp
            rw [hT_eq]
            exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist_A.1, hdist_B.1])
          · use eB₂, by simp
            rw [hT_eq]
            exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist_A.1, hdist_B.1])
        · -- B selected s(v₁, b₃), not spine
          -- T = {v₁, a₂, v₂} doesn't contain b₃, so s(v₁, b₃) doesn't help
          -- But we need A's s(v₁, a₂) which A didn't select
          -- This is the gap! We need stronger constraints
          sorry
      · -- y = b₃: T = {v₁, a₂, b₃}
        rcases h_B_covers_left with hB | hB
        · -- B selected spine: doesn't help (T doesn't contain v₂)
          sorry
        · -- B selected s(v₁, b₃)
          simp only [mem_insert, mem_singleton] at hB
          rcases hB with rfl | rfl
          · use eB₁, by simp
            rw [hT_eq]
            exact edge_in_sym2 _ v₁ b₃ (by simp) (by simp [hdist_A.1, hdist_B.2.1])
          · use eB₂, by simp
            rw [hT_eq]
            exact edge_in_sym2 _ v₁ b₃ (by simp) (by simp [hdist_A.1, hdist_B.2.1])
  · -- x = a₃: similar analysis
    sorry

end
