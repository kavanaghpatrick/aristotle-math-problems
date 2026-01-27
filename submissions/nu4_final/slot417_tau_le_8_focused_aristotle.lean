/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7962de25-3893-4f0e-bc53-4fe21a5ce4d1
-/

/-
  slot417_tau_le_8_focused.lean

  FOCUSED PROOF: τ ≤ 8 for PATH_4 with ν = 4

  KEY INSIGHT (proven scaffolding):
  For a triangle {a, b, c} and vertex v ∈ {a, b, c}:
  Any 2-edge selection from the triangle includes at least one edge containing v.

  APPLICATION:
  - For middle element B = {v₁, v₂, b₃}, any 2-edge selection covers both v₁ and v₂
  - This handles bridges at both A-B and B-C junctions
  - Total: 4 elements × 2 edges = 8 edges

  TIER: 2 (pigeonhole + counting)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: PIGEONHOLE FOR TRIANGLE EDGES
-- ══════════════════════════════════════════════════════════════════════════════

/-- For a triangle {a,b,c} and vertex v in it, any 2 of the 3 edges include one containing v -/
lemma two_edges_include_vertex (a b c v : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hv : v = a ∨ v = b ∨ v = c)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    (he₁ : e₁ = s(a, b) ∨ e₁ = s(a, c) ∨ e₁ = s(b, c))
    (he₂ : e₂ = s(a, b) ∨ e₂ = s(a, c) ∨ e₂ = s(b, c)) :
    v ∈ e₁ ∨ v ∈ e₂ := by
  rcases hv with rfl | rfl | rfl
  · -- v = a: opposite edge is s(b,c)
    rcases he₁ with rfl | rfl | rfl
    · left; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]
    · rcases he₂ with rfl | rfl | rfl
      · right; simp [Sym2.mem_iff]
      · right; simp [Sym2.mem_iff]
      · exfalso; exact hne rfl
  · -- v = b: opposite edge is s(a,c)
    rcases he₁ with rfl | rfl | rfl
    · left; simp [Sym2.mem_iff]
    · rcases he₂ with rfl | rfl | rfl
      · right; simp [Sym2.mem_iff]
      · exfalso; exact hne rfl
      · right; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]
  · -- v = c: opposite edge is s(a,b)
    rcases he₁ with rfl | rfl | rfl
    · rcases he₂ with rfl | rfl | rfl
      · exfalso; exact hne rfl
      · right; simp [Sym2.mem_iff]
      · right; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: DOUBLE PIGEONHOLE FOR MIDDLE ELEMENT
-- ══════════════════════════════════════════════════════════════════════════════

/-- For B = {v₁, v₂, b₃}, any 2-edge selection covers both v₁ AND v₂ -/
lemma middle_element_double_cover (v₁ v₂ b₃ : V) (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ b₃) (h23 : v₂ ≠ b₃)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    (he₁ : e₁ = s(v₁, v₂) ∨ e₁ = s(v₁, b₃) ∨ e₁ = s(v₂, b₃))
    (he₂ : e₂ = s(v₁, v₂) ∨ e₂ = s(v₁, b₃) ∨ e₂ = s(v₂, b₃)) :
    (v₁ ∈ e₁ ∨ v₁ ∈ e₂) ∧ (v₂ ∈ e₁ ∨ v₂ ∈ e₂) := by
  constructor
  · exact two_edges_include_vertex v₁ v₂ b₃ v₁ h12 h13 h23 (Or.inl rfl) e₁ e₂ hne he₁ he₂
  · exact two_edges_include_vertex v₁ v₂ b₃ v₂ h12 h13 h23 (Or.inr (Or.inl rfl)) e₁ e₂ hne he₁ he₂

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: BRIDGE CONTAINS SHARED VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- A bridge (triangle sharing edges with both E and F) contains their shared vertex -/
lemma bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : (T ∩ E).card ≥ 2) (hTF : (T ∩ F).card ≥ 2) :
    v ∈ T := by
  by_contra hv_not
  have h_disj : Disjoint (T ∩ E) (T ∩ F) := by
    rw [Finset.disjoint_left]
    intro x hxE hxF
    have hx_inter : x ∈ E ∩ F := mem_inter.mpr ⟨mem_of_mem_inter_right hxE, mem_of_mem_inter_right hxF⟩
    rw [hEF] at hx_inter
    simp only [mem_singleton] at hx_inter
    rw [hx_inter] at hxE
    exact hv_not (mem_of_mem_inter_left hxE)
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT
    exact hT.1.card_eq
  have h_union : (T ∩ E ∪ T ∩ F) ⊆ T := union_subset inter_subset_left inter_subset_left
  have h_card : (T ∩ E ∪ T ∩ F).card ≤ T.card := card_le_card h_union
  rw [card_union_of_disjoint h_disj] at h_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: EDGE MEMBERSHIP IN TRIANGLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- If both endpoints of edge are in a 3-element set, the edge is in its sym2 -/
lemma edge_in_sym2_of_mem (T : Finset V) (hT_card : T.card = 3) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: TRIANGLE CARD FROM CLIQUE
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT
  exact hT.1.card_eq

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: SECOND ELEMENT IN INTERSECTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- If |T ∩ E| ≥ 2 and v ∈ T ∩ E, there exists another element x ∈ T ∩ E with x ≠ v -/
lemma exists_second_in_inter (T E : Finset V) (v : V)
    (hv_inter : v ∈ T ∩ E) (h_card : (T ∩ E).card ≥ 2) :
    ∃ x ∈ T ∩ E, x ≠ v := by
  by_contra h
  push_neg at h
  have h_sub : T ∩ E ⊆ {v} := by
    intro y hy
    simp only [mem_singleton]
    exact h y hy
  have h_card' : (T ∩ E).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: MAXIMALITY IMPLIES EDGE SHARING
-- ══════════════════════════════════════════════════════════════════════════════

/-- For maximal packing, every external triangle shares edge with some packing element -/
lemma external_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_ext : T ∉ M) :
    ∃ E ∈ M, (T ∩ E).card ≥ 2 := hMaximal T hT hT_ext

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: PACKING ELEMENT EDGE COVERS ITSELF
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any edge of a triangle covers that triangle -/
lemma triangle_edge_covers_self (a b c : V) (hab : a ≠ b) :
    s(a, b) ∈ ({a, b, c} : Finset V).sym2 := by
  simp only [Finset.mk_mem_sym2_iff, mem_insert, mem_singleton]
  exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for τ ≤ 8 in PATH_4:
1. For each M-element E = {a,b,c}, select 2 edges adaptively
2. Total: 4 × 2 = 8 edges
3. Coverage of each triangle type:
   a) M-elements: covered by their own edges (trivially)
   b) S_e externals: covered by E's 2-edge selection (by 6-packing constraint)
   c) Bridges at A-B: contain v₁, hit by A's or B's selection (B covers via double pigeonhole)
   d) Bridges at B-C: contain v₂, hit by B's or C's selection (both cover via double pigeonhole)
   e) Bridges at C-D: contain v₃, hit by C's or D's selection (C covers via double pigeonhole)

KEY: Middle elements B and C have the double pigeonhole property:
- B's any 2-edge selection covers v₁ (for A-B bridges) AND v₂ (for B-C bridges)
- C's any 2-edge selection covers v₂ (for B-C bridges) AND v₃ (for C-D bridges)

This means bridges are handled automatically by middle element edge selections!
-/

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    -- PATH_4 structure
    (A B C D : Finset V) (hM_eq : M = {A, B, C, D})
    (hA_card : A.card = 3) (hB_card : B.card = 3) (hC_card : C.card = 3) (hD_card : D.card = 3)
    (v₁ v₂ v₃ : V)
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂}) (hCD : C ∩ D = {v₃})
    -- PATH_4: non-adjacent pairs share no vertices
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅)
    -- Vertex memberships
    (hv1_A : v₁ ∈ A) (hv1_B : v₁ ∈ B)
    (hv2_B : v₂ ∈ B) (hv2_C : v₂ ∈ C)
    (hv3_C : v₃ ∈ C) (hv3_D : v₃ ∈ D)
    -- Distinctness of spine vertices
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃)
    -- M-elements in clique finset
    (hA_clq : A ∈ G.cliqueFinset 3) (hB_clq : B ∈ G.cliqueFinset 3)
    (hC_clq : C ∈ G.cliqueFinset 3) (hD_clq : D ∈ G.cliqueFinset 3) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  -- Construct cover from 2 edges of each M-element
  -- For A = {v₁, a₂, a₃}: use edges {v₁, a₂}, {v₁, a₃} (both contain v₁)
  -- For B = {v₁, v₂, b₃}: use edges {v₁, v₂}, {v₁, b₃} OR {v₁, v₂}, {v₂, b₃}
  --   (any 2 edges cover both v₁ and v₂ by double pigeonhole)
  -- For C = {v₂, v₃, c₃}: similar
  -- For D = {v₃, d₂, d₃}: use edges {v₃, d₂}, {v₃, d₃} (both contain v₃)

  -- Get other vertices of each triangle
  have ⟨a₂, a₃, ha12, ha13, ha23, hA_eq⟩ := card_eq_three.mp hA_card
  have ⟨b₁, b₂, b₃, hb12, hb13, hb23, hB_eq⟩ := card_eq_three.mp hB_card
  have ⟨c₁, c₂, c₃, hc12, hc13, hc23, hC_eq⟩ := card_eq_three.mp hC_card
  have ⟨d₁, d₂, d₃, hd12, hd13, hd23, hD_eq⟩ := card_eq_three.mp hD_card

  -- Since v₁ ∈ B = {b₁, b₂, b₃} and v₂ ∈ B, and v₁ ≠ v₂
  -- We know {v₁, v₂} ⊆ {b₁, b₂, b₃}
  rw [hB_eq] at hv1_B hv2_B
  simp only [mem_insert, mem_singleton] at hv1_B hv2_B

  -- Similarly for C with v₂, v₃
  rw [hC_eq] at hv2_C hv3_C
  simp only [mem_insert, mem_singleton] at hv2_C hv3_C

  -- Construct the 8-edge cover
  -- The cover consists of 2 edges from each of A, B, C, D

  -- For now, construct cover using specific edge selections
  -- A: edges containing v₁ (handles A and A-B bridges)
  -- B: any 2 edges (handles B and all bridges at both ends via double pigeonhole)
  -- C: any 2 edges (handles C and all bridges at both ends via double pigeonhole)
  -- D: edges containing v₃ (handles D and C-D bridges)

  sorry

end