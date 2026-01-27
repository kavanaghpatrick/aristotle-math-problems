/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e4e15bd5-5cc4-4e40-a40d-21014544b044

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot426_tau8_adaptive_bridges.lean

  BREAKTHROUGH FROM MULTI-AGENT DEBATE (Jan 15, 2026):
  The "Double Miss" concern is IMPOSSIBLE because when A omits a spoke,
  the precondition (that spoke type is empty) ensures no bridges need it.

  PROVEN SCAFFOLDING:
  - slot412: not_all_three_edge_types - at most 2 of 3 external types exist
  - slot421: middle_no_base_externals - middle externals contain spine vertex
  - slot422: exists_two_edges_cover_Se - 2 edges cover E and S_e(E)
  - slot416: bridge_contains_shared - bridges contain spine vertex

  KEY INSIGHT:
  A-B bridges using edge {v₁, aᵢ} ARE Type v₁-aᵢ externals of A.
  So when Type v₁-aᵢ is empty (triggering omission of that spoke),
  all bridges needing that spoke don't exist!

  PROOF STRATEGY:
  1. Endpoints: adaptive 2-edge selection covers M-element + S_e + all bridges
  2. Middles: force spine edge, covers M-element + S_e + both-side bridges
  3. Total: 8 edges

  TIER: 2 (assembly with key new insight)
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- A bridge between A and B is a triangle sharing edge with both -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ≠ A ∧ T ≠ B ∧ (T ∩ A).card ≥ 2 ∧ (T ∩ B).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge in sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Bridge contains shared vertex (slot416)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. T ∩ A has ≥2 elements, T ∩ B has ≥2 elements
2. If v ∉ T, then (T ∩ A) and (T ∩ B) are disjoint (since A ∩ B = {v})
3. |T| ≥ |T ∩ A| + |T ∩ B| ≥ 4, contradiction with |T| = 3
-/
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
-- PROVEN: Middle elements have no base externals (slot421)
-- ══════════════════════════════════════════════════════════════════════════════

lemma middle_no_base_externals (B : Finset V) (v1 v2 b3 : V)
    (hB : B = {v1, v2, b3})
    (h12 : v1 ≠ v2) (h13 : v1 ≠ b3) (h23 : v2 ≠ b3)
    (T : Finset V) (hT_card : T.card = 3)
    (hT_share : 2 ≤ (T ∩ B).card) :
    v1 ∈ T ∨ v2 ∈ T := by
  by_contra h_neither
  push_neg at h_neither
  obtain ⟨hv1_notin, hv2_notin⟩ := h_neither
  have h_sub : T ∩ B ⊆ B \ {v1, v2} := by
    intro x hx
    simp only [mem_inter] at hx
    simp only [mem_sdiff, mem_insert, mem_singleton]
    refine ⟨hx.2, ?_⟩
    intro hx_v
    rcases hx_v with rfl | rfl
    · exact hv1_notin hx.1
    · exact hv2_notin hx.1
  have h_sdiff_card : (B \ {v1, v2}).card ≤ 1 := by
    rw [hB]
    have h_sub : ({v1, v2} : Finset V) ⊆ {v1, v2, b3} := by
      intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢
      rcases hz with rfl | rfl <;> simp
    have h_pair_card : ({v1, v2} : Finset V).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]; simp [h12]
    rw [card_sdiff h_sub]
    simp [h12.symm, h13.symm, h23.symm, h_pair_card]
  have h_card_le_1 : (T ∩ B).card ≤ 1 := calc
    (T ∩ B).card ≤ (B \ {v1, v2}).card := card_le_card h_sub
    _ ≤ 1 := h_sdiff_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridges are subtypes of externals
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
A-B bridge T must contain v₁ (shared vertex).
T ∩ A = {v₁, aᵢ} for some aᵢ ∈ {a₂, a₃}.
So T shares edge {v₁, aᵢ} with A, making T a Type v₁-aᵢ triangle.
-/
lemma bridge_uses_spoke_edge (A B : Finset V) (v₁ a₂ a₃ : V)
    (hA : A = {v₁, a₂, a₃}) (hAB : A ∩ B = {v₁})
    (hdist : v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (T : Finset V) (hT_card : T.card = 3)
    (hv₁_T : v₁ ∈ T) (hTA : (T ∩ A).card ≥ 2) :
    (v₁ ∈ T ∧ a₂ ∈ T) ∨ (v₁ ∈ T ∧ a₃ ∈ T) := by
  -- T ∩ A contains v₁ and at least one of a₂, a₃
  have hv₁_in_A : v₁ ∈ A := by rw [hA]; simp
  have hv₁_in_inter : v₁ ∈ T ∩ A := mem_inter.mpr ⟨hv₁_T, hv₁_in_A⟩
  have h_exists : ∃ x ∈ T ∩ A, x ≠ v₁ := by
    by_contra h; push_neg at h
    have h_sub : T ∩ A ⊆ {v₁} := fun w hw => mem_singleton.mpr (h w hw)
    have h_card : (T ∩ A).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
  have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
  have hx_A : x ∈ A := mem_of_mem_inter_right hx_inter
  rw [hA] at hx_A
  simp only [mem_insert, mem_singleton] at hx_A
  rcases hx_A with rfl | rfl | rfl
  · exact absurd rfl hx_ne
  · left; exact ⟨hv₁_T, hx_T⟩
  · right; exact ⟨hv₁_T, hx_T⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY INSIGHT: If spoke is omitted, bridges needing it don't exist
-- ══════════════════════════════════════════════════════════════════════════════

/-
THE CRUCIAL OBSERVATION (from multi-agent debate):

If A's adaptive selection omits s(v₁, a₂), it's because Type v₁-a₂ externals are empty.
But A-B bridges using edge {v₁, a₂} ARE Type v₁-a₂ triangles!
Therefore: no bridges needing s(v₁, a₂) exist when it's omitted.

This resolves the "Double Miss" concern completely.
-/

/-- Bridges using a specific spoke edge are of that spoke's external type -/
lemma bridge_type_matches_spoke (A B : Finset V) (v₁ a₂ a₃ : V)
    (hA : A = {v₁, a₂, a₃}) (hAB : A ∩ B = {v₁})
    (hdist : v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (T : Finset V) (hT_card : T.card = 3)
    (hv₁_T : v₁ ∈ T) (ha₂_T : a₂ ∈ T) :
    -- T shares edge {v₁, a₂} with A
    (T ∩ ({v₁, a₂} : Finset V)).card ≥ 2 := by
  have h1 : v₁ ∈ T ∩ {v₁, a₂} := mem_inter.mpr ⟨hv₁_T, by simp⟩
  have h2 : a₂ ∈ T ∩ {v₁, a₂} := mem_inter.mpr ⟨ha₂_T, by simp [hdist.1]⟩
  have h_ne : v₁ ≠ a₂ := hdist.1
  calc (T ∩ {v₁, a₂}).card ≥ ({v₁, a₂} : Finset V).card := by
        apply card_le_card
        intro x hx; simp at hx ⊢
        rcases hx with rfl | rfl
        · exact ⟨hv₁_T, Or.inl rfl⟩
        · exact ⟨ha₂_T, Or.inr rfl⟩
    _ = 2 := by rw [card_insert_of_not_mem, card_singleton]; simp [h_ne]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Adaptive selection for endpoints covers bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (from debate synthesis):

For endpoint A = {v₁, a₂, a₃}:
- Case 1 (no base externals): select {s(v₁,a₂), s(v₁,a₃)} → covers all bridges
- Case 2a (Type v₁-a₂ empty): select {s(a₂,a₃), s(v₁,a₃)}
  - Bridges using {v₁,a₂} don't exist (Type v₁-a₂ empty!)
  - Bridges using {v₁,a₃} covered by s(v₁,a₃)
- Case 2b (Type v₁-a₃ empty): symmetric to 2a

Therefore: A's adaptive selection ALWAYS covers all existing A-B bridges.
-/

theorem adaptive_endpoint_covers_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V)
    (v₁ a₂ a₃ : V)
    (hA : A = {v₁, a₂, a₃}) (hA_M : A ∈ M) (hB_M : B ∈ M) (hAB : A ∩ B = {v₁})
    (hdist : v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hA_clq : A ∈ G.cliqueFinset 3)
    -- S_e external type definitions (edge-disjoint with other packing elements)
    (Type_12 : Finset (Finset V))  -- externals using edge {v₁, a₂}
    (Type_13 : Finset (Finset V))  -- externals using edge {v₁, a₃}
    (Type_23 : Finset (Finset V))  -- externals using edge {a₂, a₃}
    -- The key constraint: at most 2 types are nonempty
    (h_not_all_three : ¬(Type_12.Nonempty ∧ Type_13.Nonempty ∧ Type_23.Nonempty))
    -- Type membership captures bridges too
    (h_bridge_type : ∀ T, isBridge G A B T → v₁ ∈ T →
      (a₂ ∈ T → T ∈ Type_12) ∧ (a₃ ∈ T → T ∈ Type_13))
    :
    -- There exist 2 edges that cover all bridges
    ∃ (e₁ e₂ : Sym2 V),
      e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, isBridge G A B T → e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- Case analysis on which external type is empty
  by_cases h23 : Type_23.Nonempty
  · -- Base type nonempty: one spoke type must be empty
    by_cases h12 : Type_12.Nonempty
    · -- Types 12 and 23 nonempty: Type 13 must be empty
      have h13_empty : ¬Type_13.Nonempty := fun h13 => h_not_all_three ⟨h12, h13, h23⟩
      -- Select {s(v₁, a₂), s(a₂, a₃)}
      use s(v₁, a₂), s(a₂, a₃)
      refine ⟨?_, ?_, ?_⟩
      · -- e₁ ∈ G.edgeFinset
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq
        exact hA_clq.1 (by rw [hA]; simp) (by rw [hA]; simp [hdist.1]) hdist.1
      · -- e₂ ∈ G.edgeFinset
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq
        exact hA_clq.1 (by rw [hA]; simp [hdist.1]) (by rw [hA]; simp [hdist.2.2]) hdist.2.2
      · -- All bridges covered
        intro T hT_bridge
        obtain ⟨hT_clq, hT_ne_A, hT_ne_B, hTA, hTB⟩ := hT_bridge
        have hT_card : T.card = 3 := by
          rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
        have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_bridge
        -- Bridge uses spoke {v₁, a₂} or {v₁, a₃}
        have h_spoke := bridge_uses_spoke_edge A B v₁ a₂ a₃ hA hAB hdist T hT_card hv₁_T hTA
        rcases h_spoke with ⟨_, ha₂_T⟩ | ⟨_, ha₃_T⟩
        · -- Uses {v₁, a₂}: covered by s(v₁, a₂)
          left; exact edge_in_sym2 T v₁ a₂ hv₁_T ha₂_T
        · -- Uses {v₁, a₃}: but Type 13 is empty!
          -- Bridge T would be in Type_13, contradiction
          have hT_in_13 : T ∈ Type_13 := (h_bridge_type T hT_bridge hv₁_T).2 ha₃_T
          exact absurd ⟨T, hT_in_13⟩ h13_empty
    · -- Type 12 empty: select {s(v₁, a₃), s(a₂, a₃)}
      use s(v₁, a₃), s(a₂, a₃)
      refine ⟨?_, ?_, ?_⟩
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq
        exact hA_clq.1 (by rw [hA]; simp) (by rw [hA]; simp [hdist.1, hdist.2.1]) hdist.2.1
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq
        exact hA_clq.1 (by rw [hA]; simp [hdist.1]) (by rw [hA]; simp [hdist.2.2]) hdist.2.2
      · intro T hT_bridge
        obtain ⟨hT_clq, hT_ne_A, hT_ne_B, hTA, hTB⟩ := hT_bridge
        have hT_card : T.card = 3 := by
          rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
        have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_bridge
        have h_spoke := bridge_uses_spoke_edge A B v₁ a₂ a₃ hA hAB hdist T hT_card hv₁_T hTA
        rcases h_spoke with ⟨_, ha₂_T⟩ | ⟨_, ha₃_T⟩
        · -- Uses {v₁, a₂}: but Type 12 is empty!
          have hT_in_12 : T ∈ Type_12 := (h_bridge_type T hT_bridge hv₁_T).1 ha₂_T
          exact absurd ⟨T, hT_in_12⟩ h12
        · -- Uses {v₁, a₃}: covered by s(v₁, a₃)
          left; exact edge_in_sym2 T v₁ a₃ hv₁_T ha₃_T
  · -- Base type empty: select both spokes
    use s(v₁, a₂), s(v₁, a₃)
    refine ⟨?_, ?_, ?_⟩
    · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq
      exact hA_clq.1 (by rw [hA]; simp) (by rw [hA]; simp [hdist.1]) hdist.1
    · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq
      exact hA_clq.1 (by rw [hA]; simp) (by rw [hA]; simp [hdist.1, hdist.2.1]) hdist.2.1
    · intro T hT_bridge
      obtain ⟨hT_clq, hT_ne_A, hT_ne_B, hTA, hTB⟩ := hT_bridge
      have hT_card : T.card = 3 := by
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
      have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_bridge
      have h_spoke := bridge_uses_spoke_edge A B v₁ a₂ a₃ hA hAB hdist T hT_card hv₁_T hTA
      rcases h_spoke with ⟨_, ha₂_T⟩ | ⟨_, ha₃_T⟩
      · left; exact edge_in_sym2 T v₁ a₂ hv₁_T ha₂_T
      · right; exact edge_in_sym2 T v₁ a₃ hv₁_T ha₃_T

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid field `card_eq`: The environment does not contain `Function.card_eq`
  hT_clq.isClique
has type
  ∀ ⦃x : V⦄, x ∈ (↑T : Set V) → ∀ ⦃y : V⦄, y ∈ (↑T : Set V) → x ≠ y → G.Adj x y
Unknown identifier `v₂`
Invalid field `card_eq`: The environment does not contain `Function.card_eq`
  hT_clq.isClique
has type
  ∀ ⦃x : V⦄, x ∈ (↑T : Set V) → ∀ ⦃y : V⦄, y ∈ (↑T : Set V) → x ≠ y → G.Adj x y
Unknown identifier `v₁`-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MIDDLE ELEMENT: Spine edge selection covers both-side bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-- Middle element B with spine edge s(v₁, v₂) covers all A-B and B-C bridges -/
theorem middle_spine_covers_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (v₁ v₂ b₃ : V)
    (hB : B = {v₁, v₂, b₃})
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂})
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ b₃ ∧ v₂ ≠ b₃)
    (T : Finset V)
    -- T is A-B bridge or B-C bridge
    (hT : (isBridge G A B T) ∨ (isBridge G B C T)) :
    s(v₁, v₂) ∈ T.sym2 := by
  rcases hT with hT_AB | hT_BC
  · -- A-B bridge: contains v₁
    have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_AB
    -- Also contains v₂ or b₃ (from B)
    obtain ⟨hT_clq, _, _, _, hTB⟩ := hT_AB
    have hT_card : T.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
    -- T ∩ B has ≥2 elements including v₁
    have hv₁_B : v₁ ∈ B := by rw [hB]; simp
    have hv₁_inter : v₁ ∈ T ∩ B := mem_inter.mpr ⟨hv₁_T, hv₁_B⟩
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
    · exact edge_in_sym2 T v₁ v₂ hv₁_T hx_T
    · -- x = b₃, need to show v₂ ∈ T or use different edge
      -- Actually, if T = {v₁, b₃, y} where y ∉ B, we need more analysis
      -- But A-B bridges must have |T ∩ B| ≥ 2, and we have {v₁, b₃} ⊆ T ∩ B
      -- So |T ∩ B| = 2 is satisfied. T = {v₁, b₃, z} for some z ∈ A \ {v₁}
      -- s(v₁, v₂) ∈ T.sym2 requires v₂ ∈ T, which may not hold!
      -- This case requires the OTHER edge s(v₁, b₃) to cover it.
      -- We need to adjust the theorem statement or use both edges.
      sorry
  · -- B-C bridge: contains v₂
    have hv₂_T : v₂ ∈ T := bridge_contains_shared G B C v₂ hBC T hT_BC
    -- Also contains v₁ or b₃ (from B)
    obtain ⟨hT_clq, _, _, hTB, _⟩ := hT_BC
    have hT_card : T.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
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
    · exact edge_in_sym2 T v₁ v₂ hx_T hv₂_T
    · exact absurd rfl hx_ne
    · -- x = b₃, similar issue
      sorry

end