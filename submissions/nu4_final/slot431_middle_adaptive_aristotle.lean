/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e8e5594d-837f-4dd0-bd28-652a80c850d5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot431_middle_adaptive.lean

  FIX FOR slot426: Middle elements need ADAPTIVE 2-edge selection, not just spine.

  THE PROBLEM (slot426 lines 371-378, 398-401):
  - Bridges like {v₁, b₃, x} (A-B) or {v₂, b₃, y} (B-C) don't contain both spine vertices
  - Claiming s(v₁, v₂) covers ALL bridges is FALSE

  THE FIX (Bridge-External Equivalence for middles):
  - Bridges using edge e from B are e-type externals of B
  - Apply adaptive selection: if spine-type empty, bridges using spine don't exist
  - Middle B uses 2 edges from: {s(v₁,v₂), s(v₁,b₃), s(v₂,b₃)}

  PROOF STRATEGY:
  For middle B = {v₁, v₂, b₃}:
  - At most 2 of 3 edge types have externals (not_all_three_edge_types)
  - Case 1: No spine externals → use {s(v₁,b₃), s(v₂,b₃)}
    * A-B bridges use {v₁,v₂} or {v₁,b₃} - but {v₁,v₂} type empty! → s(v₁,b₃) covers
    * B-C bridges use {v₁,v₂} or {v₂,b₃} - but {v₁,v₂} type empty! → s(v₂,b₃) covers
  - Case 2: Spine type nonempty → one spoke type empty
    * Include spine edge, bridges using empty spoke don't exist

  TIER: 2 (assembly with proven scaffolding)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot426)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- A bridge between A and B is a triangle sharing edge with both -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ≠ A ∧ T ≠ B ∧ (T ∩ A).card ≥ 2 ∧ (T ∩ B).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS (from slot426)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge edge type classification for middle elements
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
For middle B = {v₁, v₂, b₃}:
- A-B bridge T contains v₁ (shared vertex)
- T ∩ B ≥ 2 includes v₁, so T contains v₁ and one of {v₂, b₃}
- Therefore T uses edge {v₁, v₂} or {v₁, b₃}

Similarly B-C bridge uses {v₁, v₂} or {v₂, b₃}.
-/
lemma ab_bridge_uses_left_edges (B : Finset V) (v₁ v₂ b₃ : V)
    (hB : B = {v₁, v₂, b₃}) (hdist : v₁ ≠ v₂ ∧ v₁ ≠ b₃ ∧ v₂ ≠ b₃)
    (T : Finset V) (hv₁_T : v₁ ∈ T)
    (hTB : (T ∩ B).card ≥ 2) :
    (v₁ ∈ T ∧ v₂ ∈ T) ∨ (v₁ ∈ T ∧ b₃ ∈ T) := by
  have hv₁_B : v₁ ∈ B := by rw [hB]; simp
  have hv₁_inter : v₁ ∈ T ∩ B := mem_inter.mpr ⟨hv₁_T, hv₁_B⟩
  -- T ∩ B has ≥2 elements, one is v₁, find another
  have h_exists : ∃ x ∈ T ∩ B, x ≠ v₁ := by
    by_contra h; push_neg at h
    have h_sub : T ∩ B ⊆ {v₁} := fun w hw => mem_singleton.mpr (h w hw)
    have h_card : (T ∩ B).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
  have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
  have hx_B : x ∈ B := mem_of_mem_inter_right hx_inter
  rw [hB] at hx_B
  simp only [mem_insert, mem_singleton] at hx_B
  rcases hx_B with rfl | rfl | rfl
  · exact absurd rfl hx_ne
  · left; exact ⟨hv₁_T, hx_T⟩
  · right; exact ⟨hv₁_T, hx_T⟩

lemma bc_bridge_uses_right_edges (B : Finset V) (v₁ v₂ b₃ : V)
    (hB : B = {v₁, v₂, b₃}) (hdist : v₁ ≠ v₂ ∧ v₁ ≠ b₃ ∧ v₂ ≠ b₃)
    (T : Finset V) (hv₂_T : v₂ ∈ T)
    (hTB : (T ∩ B).card ≥ 2) :
    (v₁ ∈ T ∧ v₂ ∈ T) ∨ (v₂ ∈ T ∧ b₃ ∈ T) := by
  have hv₂_B : v₂ ∈ B := by rw [hB]; simp [hdist.1]
  have hv₂_inter : v₂ ∈ T ∩ B := mem_inter.mpr ⟨hv₂_T, hv₂_B⟩
  have h_exists : ∃ x ∈ T ∩ B, x ≠ v₂ := by
    by_contra h; push_neg at h
    have h_sub : T ∩ B ⊆ {v₂} := fun w hw => mem_singleton.mpr (h w hw)
    have h_card : (T ∩ B).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
  have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
  have hx_B : x ∈ B := mem_of_mem_inter_right hx_inter
  rw [hB] at hx_B
  simp only [mem_insert, mem_singleton] at hx_B
  rcases hx_B with rfl | rfl | rfl
  · left; exact ⟨hx_T, hv₂_T⟩
  · exact absurd rfl hx_ne
  · right; exact ⟨hv₂_T, hx_T⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Adaptive 2-edge selection for middle elements
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (Bridge-External Equivalence for middles):

For middle B = {v₁, v₂, b₃} between A and C:
- Edge types: {v₁,v₂} (spine), {v₁,b₃} (left spoke), {v₂,b₃} (right spoke)
- At most 2 types have externals (not_all_three_edge_types constraint)

KEY INSIGHT: Bridges using edge e ARE e-type externals of B!
- A-B bridge using {v₁,v₂} → {v₁,v₂}-type external of B
- A-B bridge using {v₁,b₃} → {v₁,b₃}-type external of B
- B-C bridge using {v₁,v₂} → {v₁,v₂}-type external of B
- B-C bridge using {v₂,b₃} → {v₂,b₃}-type external of B

Case analysis:
1. No spine externals: use {s(v₁,b₃), s(v₂,b₃)}
   - A-B bridges must use {v₁,b₃} (spine type empty!) → covered by s(v₁,b₃)
   - B-C bridges must use {v₂,b₃} (spine type empty!) → covered by s(v₂,b₃)

2. Spine type nonempty, {v₁,b₃} empty: use {s(v₁,v₂), s(v₂,b₃)}
   - A-B bridges using {v₁,b₃} don't exist! → s(v₁,v₂) covers
   - B-C bridges: covered by s(v₁,v₂) or s(v₂,b₃)

3. Spine type nonempty, {v₂,b₃} empty: use {s(v₁,v₂), s(v₁,b₃)}
   - A-B bridges: covered by s(v₁,v₂) or s(v₁,b₃)
   - B-C bridges using {v₂,b₃} don't exist! → s(v₁,v₂) covers

Therefore: 2 edges ALWAYS suffice for middle elements!
-/

theorem adaptive_middle_covers_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (v₁ v₂ b₃ : V)
    (hB : B = {v₁, v₂, b₃})
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂})
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ b₃ ∧ v₂ ≠ b₃)
    (hB_clq : B ∈ G.cliqueFinset 3)
    -- External type sets
    (Type_spine : Finset (Finset V))   -- externals using edge {v₁, v₂}
    (Type_left : Finset (Finset V))    -- externals using edge {v₁, b₃}
    (Type_right : Finset (Finset V))   -- externals using edge {v₂, b₃}
    -- At most 2 types nonempty
    (h_not_all_three : ¬(Type_spine.Nonempty ∧ Type_left.Nonempty ∧ Type_right.Nonempty))
    -- Bridges belong to their edge type (key constraint)
    (h_ab_bridge_type : ∀ T, isBridge G A B T →
      (v₁ ∈ T → v₂ ∈ T → T ∈ Type_spine) ∧
      (v₁ ∈ T → b₃ ∈ T → T ∈ Type_left))
    (h_bc_bridge_type : ∀ T, isBridge G B C T →
      (v₁ ∈ T → v₂ ∈ T → T ∈ Type_spine) ∧
      (v₂ ∈ T → b₃ ∈ T → T ∈ Type_right))
    :
    -- There exist 2 edges covering ALL bridges (both A-B and B-C)
    ∃ (e₁ e₂ : Sym2 V),
      e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, isBridge G A B T → e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) ∧
      (∀ T, isBridge G B C T → e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- Case analysis on which type is empty
  by_cases h_spine : Type_spine.Nonempty
  · -- Spine type nonempty: one spoke type must be empty
    by_cases h_left : Type_left.Nonempty
    · -- Spine and left nonempty: right must be empty
      have h_right_empty : ¬Type_right.Nonempty := fun h_right => h_not_all_three ⟨h_spine, h_left, h_right⟩
      -- Select {s(v₁, v₂), s(v₁, b₃)}
      use s(v₁, v₂), s(v₁, b₃)
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- s(v₁, v₂) ∈ G.edgeFinset
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1]) hdist.1
      · -- s(v₁, b₃) ∈ G.edgeFinset
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1, hdist.2.1]) hdist.2.1
      · -- A-B bridges covered
        intro T hT_bridge
        obtain ⟨hT_clq, _, _, hTA, hTB⟩ := hT_bridge
        have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_bridge
        have h_edge := ab_bridge_uses_left_edges B v₁ v₂ b₃ hB hdist T hv₁_T hTB
        rcases h_edge with ⟨_, hv₂_T⟩ | ⟨_, hb₃_T⟩
        · left; exact edge_in_sym2 T v₁ v₂ hv₁_T hv₂_T
        · right; exact edge_in_sym2 T v₁ b₃ hv₁_T hb₃_T
      · -- B-C bridges covered
        intro T hT_bridge
        obtain ⟨hT_clq, _, _, hTB, hTC⟩ := hT_bridge
        have hv₂_T : v₂ ∈ T := bridge_contains_shared G B C v₂ hBC T hT_bridge
        have h_edge := bc_bridge_uses_right_edges B v₁ v₂ b₃ hB hdist T hv₂_T hTB
        rcases h_edge with ⟨hv₁_T, _⟩ | ⟨_, hb₃_T⟩
        · left; exact edge_in_sym2 T v₁ v₂ hv₁_T hv₂_T
        · -- Uses {v₂, b₃} but right type is empty!
          have hT_in_right : T ∈ Type_right := (h_bc_bridge_type T hT_bridge).2 hv₂_T hb₃_T
          exact absurd ⟨T, hT_in_right⟩ h_right_empty
    · -- Spine nonempty, left empty: select {s(v₁, v₂), s(v₂, b₃)}
      use s(v₁, v₂), s(v₂, b₃)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1]) hdist.1
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp [hdist.1]) (by rw [hB]; simp [hdist.2.2]) hdist.2.2
      · -- A-B bridges covered
        intro T hT_bridge
        obtain ⟨hT_clq, _, _, hTA, hTB⟩ := hT_bridge
        have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_bridge
        have h_edge := ab_bridge_uses_left_edges B v₁ v₂ b₃ hB hdist T hv₁_T hTB
        rcases h_edge with ⟨_, hv₂_T⟩ | ⟨_, hb₃_T⟩
        · left; exact edge_in_sym2 T v₁ v₂ hv₁_T hv₂_T
        · -- Uses {v₁, b₃} but left type is empty!
          have hT_in_left : T ∈ Type_left := (h_ab_bridge_type T hT_bridge).2 hv₁_T hb₃_T
          exact absurd ⟨T, hT_in_left⟩ h_left
      · -- B-C bridges covered
        intro T hT_bridge
        obtain ⟨hT_clq, _, _, hTB, hTC⟩ := hT_bridge
        have hv₂_T : v₂ ∈ T := bridge_contains_shared G B C v₂ hBC T hT_bridge
        have h_edge := bc_bridge_uses_right_edges B v₁ v₂ b₃ hB hdist T hv₂_T hTB
        rcases h_edge with ⟨hv₁_T, _⟩ | ⟨_, hb₃_T⟩
        · left; exact edge_in_sym2 T v₁ v₂ hv₁_T hv₂_T
        · right; exact edge_in_sym2 T v₂ b₃ hv₂_T hb₃_T
  · -- Spine type empty: select both spokes {s(v₁, b₃), s(v₂, b₃)}
    use s(v₁, b₃), s(v₂, b₃)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
      exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1, hdist.2.1]) hdist.2.1
    · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
      exact hB_clq.1 (by rw [hB]; simp [hdist.1]) (by rw [hB]; simp [hdist.2.2]) hdist.2.2
    · -- A-B bridges: spine type empty, so must use {v₁, b₃}
      intro T hT_bridge
      obtain ⟨hT_clq, _, _, hTA, hTB⟩ := hT_bridge
      have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_bridge
      have h_edge := ab_bridge_uses_left_edges B v₁ v₂ b₃ hB hdist T hv₁_T hTB
      rcases h_edge with ⟨_, hv₂_T⟩ | ⟨_, hb₃_T⟩
      · -- Uses spine but spine type empty!
        have hT_in_spine : T ∈ Type_spine := (h_ab_bridge_type T hT_bridge).1 hv₁_T hv₂_T
        exact absurd ⟨T, hT_in_spine⟩ h_spine
      · left; exact edge_in_sym2 T v₁ b₃ hv₁_T hb₃_T
    · -- B-C bridges: spine type empty, so must use {v₂, b₃}
      intro T hT_bridge
      obtain ⟨hT_clq, _, _, hTB, hTC⟩ := hT_bridge
      have hv₂_T : v₂ ∈ T := bridge_contains_shared G B C v₂ hBC T hT_bridge
      have h_edge := bc_bridge_uses_right_edges B v₁ v₂ b₃ hB hdist T hv₂_T hTB
      rcases h_edge with ⟨hv₁_T, _⟩ | ⟨_, hb₃_T⟩
      · -- Uses spine but spine type empty!
        have hT_in_spine : T ∈ Type_spine := (h_bc_bridge_type T hT_bridge).1 hv₁_T hv₂_T
        exact absurd ⟨T, hT_in_spine⟩ h_spine
      · right; exact edge_in_sym2 T v₂ b₃ hv₂_T hb₃_T

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- FINAL ASSEMBLY: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
PATH_4: A—v₁—B—v₂—C—v₃—D

Edge budget:
- Endpoint A: 2 edges (adaptive selection from slot426)
- Middle B: 2 edges (adaptive selection from above)
- Middle C: 2 edges (adaptive selection from above)
- Endpoint D: 2 edges (adaptive selection from slot426)
Total: 8 edges

Each element's 2 edges cover:
- The element itself
- All S_e externals
- All bridges to neighbors

Since every triangle is either:
- In M (covered by M-element's edges)
- An external (covered by parent's edges)
- A bridge (covered by both neighbors' edge selections)

All triangles are covered by these 8 edges.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A B C D : Finset V)
    (v₁ v₂ v₃ : V)
    -- PATH_4 structure
    (hA_M : A ∈ M) (hB_M : B ∈ M) (hC_M : C ∈ M) (hD_M : D ∈ M)
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂}) (hCD : C ∩ D = {v₃})
    (hM_card : M.card = 4)
    -- PATH_4 means exactly these 4 elements, connected in path
    (hM_eq : M = {A, B, C, D})
    -- Maximality: every triangle shares edge with some element
    (h_max : ∀ T ∈ G.cliqueFinset 3, ∃ E ∈ M, (T ∩ E).card ≥ 2)
    :
    -- τ(G) ≤ 8: there exists a cover of size at most 8
    ∃ (cover : Finset (Sym2 V)),
      cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2 := by
  -- Apply adaptive_endpoint_covers_bridges (slot426) to A and D
  -- Apply adaptive_middle_covers_bridges (above) to B and C
  -- Combine all 8 edges into final cover
  sorry

end