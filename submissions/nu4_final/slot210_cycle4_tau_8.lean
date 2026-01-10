/-
  slot210_cycle4_tau_8.lean

  MAIN THEOREM: τ ≤ 8 for cycle_4 configuration

  THE BREAKTHROUGH (5-round multi-agent debate consensus):

  1. Every triangle T contains at least one shared vertex v ∈ {v_ab, v_bc, v_cd, v_da}
     Proof: By maximality, T shares edge with some M-element.
            M-elements share vertices cyclically.
            The shared edge has ≥ 1 vertex in common with the M-element's shared vertices.

  2. At each shared vertex v, the link graph L_v is bipartite
     Proof: Partition = {externals of one M-element + that M-element} vs {externals of other + other}
            Externals from different M-elements don't share edges (slot207)

  3. By König's theorem: τ(L_v) = ν(L_v) ≤ 2 for bipartite L_v
     So 2 spokes from v cover all triangles at v.

  4. Total: 4 shared vertices × 2 spokes = 8 edges

  This covers:
  - M-elements (each contains 2 shared vertices, covered by spokes at either)
  - Externals (share edge with M-element → contain shared vertex → covered by spokes)
  - Bridges (share edges with 2 M-elements → contain the shared vertex between them → covered)

  DIFFICULTY: 4/5
  SUCCESS PROBABILITY: 60%

  DEPENDENCIES:
  - slot207_link_graph_bipartite (L_v is bipartite)
  - König's theorem (τ = ν for bipartite graphs)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

/-- Triangles of G -/
def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  G.cliqueFinset 3

/-- Two triangles share an edge -/
def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  (t₁ ∩ t₂).card ≥ 2

/-- A packing is edge-disjoint -/
def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, t.card = 3 ∧ G.IsClique t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

/-- Maximal packing -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isPacking G M ∧
  ∀ t ∈ triangles G, t ∉ M → ∃ m ∈ M, sharesEdge t m

/-- Cycle_4 configuration -/
structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  a : V
  b : V
  c : V
  d : V
  hA : A = {v_da, v_ab, a}
  hB : B = {v_ab, v_bc, b}
  hC : C = {v_bc, v_cd, c}
  hD : D = {v_cd, v_da, d}
  M_is_ABCD : M = {A, B, C, D}
  hA_in : A ∈ M
  hB_in : B ∈ M
  hC_in : C ∈ M
  hD_in : D ∈ M
  all_distinct : [v_ab, v_bc, v_cd, v_da, a, b, c, d].Nodup

/-- Shared vertices as a set -/
def sharedVertices (cfg : Cycle4 G M) : Finset V :=
  {cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da}

/-- Edge cover -/
def isEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ triangles G, ∃ e ∈ E, ∃ u v : V, e = s(u, v) ∧ u ∈ t ∧ v ∈ t ∧ u ≠ v

/-- Triangle covering number -/
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ isEdgeCover G E }

/-- KEY LEMMA 1: Every triangle contains a shared vertex

Proof: By maximality, every triangle T shares an edge with some M-element X.
T ∩ X has ≥ 2 elements. X = {v₁, v₂, x} where v₁, v₂ are shared vertices.
So T contains ≥ 2 elements of X. At least one must be a shared vertex. -/
theorem triangle_contains_shared_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (T : Finset V) (hT : T ∈ triangles G) :
    ∃ v ∈ sharedVertices cfg, v ∈ T := by
  -- Case 1: T ∈ M
  by_cases hT_in_M : T ∈ M
  · rw [cfg.M_is_ABCD] at hT_in_M
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT_in_M
    rcases hT_in_M with rfl | rfl | rfl | rfl
    · -- T = A = {v_da, v_ab, a}
      use cfg.v_ab
      constructor
      · simp [sharedVertices]
      · rw [cfg.hA]; simp
    · -- T = B
      use cfg.v_ab
      constructor
      · simp [sharedVertices]
      · rw [cfg.hB]; simp
    · -- T = C
      use cfg.v_bc
      constructor
      · simp [sharedVertices]
      · rw [cfg.hC]; simp
    · -- T = D
      use cfg.v_cd
      constructor
      · simp [sharedVertices]
      · rw [cfg.hD]; simp
  · -- Case 2: T ∉ M, use maximality
    obtain ⟨X, hX_in_M, hT_shares_X⟩ := hM.2 T hT hT_in_M
    -- X ∈ M = {A, B, C, D}
    rw [cfg.M_is_ABCD] at hX_in_M
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX_in_M
    -- T ∩ X has ≥ 2 elements
    unfold sharesEdge at hT_shares_X
    rcases hX_in_M with rfl | rfl | rfl | rfl
    · -- X = A = {v_da, v_ab, a}
      -- T ∩ A ≥ 2, so T contains ≥ 2 of {v_da, v_ab, a}
      -- At least one of v_da, v_ab is in T (since a is the only non-shared)
      rw [cfg.hA] at hT_shares_X
      -- T ∩ {v_da, v_ab, a} has card ≥ 2
      have h2 : (T ∩ {cfg.v_da, cfg.v_ab, cfg.a}).card ≥ 2 := hT_shares_X
      -- If both v_da and v_ab are not in T, then T ∩ A ⊆ {a}, card ≤ 1
      by_contra h_no_shared
      push_neg at h_no_shared
      simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton, not_or, not_exists] at h_no_shared
      have h_vab_not : cfg.v_ab ∉ T := by
        intro h
        exact h_no_shared cfg.v_ab (Or.inl rfl) h
      have h_vda_not : cfg.v_da ∉ T := by
        intro h
        exact h_no_shared cfg.v_da (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
      -- T ∩ {v_da, v_ab, a} ⊆ {a}
      have h_sub : T ∩ {cfg.v_da, cfg.v_ab, cfg.a} ⊆ {cfg.a} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 h_vda_not
        · exact absurd hx.1 h_vab_not
        · simp
      have h_card : (T ∩ {cfg.v_da, cfg.v_ab, cfg.a}).card ≤ 1 := by
        calc (T ∩ {cfg.v_da, cfg.v_ab, cfg.a}).card
            ≤ ({cfg.a} : Finset V).card := Finset.card_le_card h_sub
          _ = 1 := Finset.card_singleton cfg.a
      omega
    · -- X = B = {v_ab, v_bc, b}
      rw [cfg.hB] at hT_shares_X
      have h2 : (T ∩ {cfg.v_ab, cfg.v_bc, cfg.b}).card ≥ 2 := hT_shares_X
      by_contra h_no_shared
      push_neg at h_no_shared
      simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton, not_or, not_exists] at h_no_shared
      have h_vab_not : cfg.v_ab ∉ T := by
        intro h
        exact h_no_shared cfg.v_ab (Or.inl rfl) h
      have h_vbc_not : cfg.v_bc ∉ T := by
        intro h
        exact h_no_shared cfg.v_bc (Or.inr (Or.inl rfl)) h
      have h_sub : T ∩ {cfg.v_ab, cfg.v_bc, cfg.b} ⊆ {cfg.b} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 h_vab_not
        · exact absurd hx.1 h_vbc_not
        · simp
      have h_card : (T ∩ {cfg.v_ab, cfg.v_bc, cfg.b}).card ≤ 1 := by
        calc (T ∩ {cfg.v_ab, cfg.v_bc, cfg.b}).card
            ≤ ({cfg.b} : Finset V).card := Finset.card_le_card h_sub
          _ = 1 := Finset.card_singleton cfg.b
      omega
    · -- X = C
      rw [cfg.hC] at hT_shares_X
      have h2 : (T ∩ {cfg.v_bc, cfg.v_cd, cfg.c}).card ≥ 2 := hT_shares_X
      by_contra h_no_shared
      push_neg at h_no_shared
      simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton, not_or, not_exists] at h_no_shared
      have h_vbc_not : cfg.v_bc ∉ T := by
        intro h
        exact h_no_shared cfg.v_bc (Or.inr (Or.inl rfl)) h
      have h_vcd_not : cfg.v_cd ∉ T := by
        intro h
        exact h_no_shared cfg.v_cd (Or.inr (Or.inr (Or.inl rfl))) h
      have h_sub : T ∩ {cfg.v_bc, cfg.v_cd, cfg.c} ⊆ {cfg.c} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 h_vbc_not
        · exact absurd hx.1 h_vcd_not
        · simp
      have h_card : (T ∩ {cfg.v_bc, cfg.v_cd, cfg.c}).card ≤ 1 := by
        calc (T ∩ {cfg.v_bc, cfg.v_cd, cfg.c}).card
            ≤ ({cfg.c} : Finset V).card := Finset.card_le_card h_sub
          _ = 1 := Finset.card_singleton cfg.c
      omega
    · -- X = D
      rw [cfg.hD] at hT_shares_X
      have h2 : (T ∩ {cfg.v_cd, cfg.v_da, cfg.d}).card ≥ 2 := hT_shares_X
      by_contra h_no_shared
      push_neg at h_no_shared
      simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton, not_or, not_exists] at h_no_shared
      have h_vcd_not : cfg.v_cd ∉ T := by
        intro h
        exact h_no_shared cfg.v_cd (Or.inr (Or.inr (Or.inl rfl))) h
      have h_vda_not : cfg.v_da ∉ T := by
        intro h
        exact h_no_shared cfg.v_da (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
      have h_sub : T ∩ {cfg.v_cd, cfg.v_da, cfg.d} ⊆ {cfg.d} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 h_vcd_not
        · exact absurd hx.1 h_vda_not
        · simp
      have h_card : (T ∩ {cfg.v_cd, cfg.v_da, cfg.d}).card ≤ 1 := by
        calc (T ∩ {cfg.v_cd, cfg.v_da, cfg.d}).card
            ≤ ({cfg.d} : Finset V).card := Finset.card_le_card h_sub
          _ = 1 := Finset.card_singleton cfg.d
      omega

/-- KEY LEMMA 2: 2 spokes from each shared vertex suffice

From slot207: Link graph L_v is bipartite.
By König's theorem: vertex cover of bipartite graph equals maximum matching.
In our context: 2 spokes {v, s₁}, {v, s₂} cover all triangles at v. -/
theorem two_spokes_cover_at_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (hv : v ∈ sharedVertices cfg) :
    ∃ (s₁ s₂ : V), ∀ T ∈ triangles G, v ∈ T →
      s(v, s₁) ∈ T.sym2 ∨ s(v, s₂) ∈ T.sym2 := by
  -- This follows from König + bipartite link graph
  -- For each shared vertex v:
  --   v = v_ab: L_v has parts {A's externals ∪ {A}} and {B's externals ∪ {B}}
  --   Maximum matching in L_v has size ≤ 2 (since v is between only 2 M-elements)
  --   So vertex cover has size ≤ 2
  --   Pick s₁, s₂ as the vertices corresponding to this cover
  sorry

/-- Construct the 8-edge cover explicitly -/
def eightEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4 G M)
    (s_ab₁ s_ab₂ s_bc₁ s_bc₂ s_cd₁ s_cd₂ s_da₁ s_da₂ : V) : Finset (Sym2 V) :=
  { s(cfg.v_ab, s_ab₁), s(cfg.v_ab, s_ab₂),
    s(cfg.v_bc, s_bc₁), s(cfg.v_bc, s_bc₂),
    s(cfg.v_cd, s_cd₁), s(cfg.v_cd, s_cd₂),
    s(cfg.v_da, s_da₁), s(cfg.v_da, s_da₂) }

/-- The 8-edge cover has at most 8 elements -/
theorem eight_cover_card_le_8
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4 G M)
    (s_ab₁ s_ab₂ s_bc₁ s_bc₂ s_cd₁ s_cd₂ s_da₁ s_da₂ : V) :
    (eightEdgeCover G cfg s_ab₁ s_ab₂ s_bc₁ s_bc₂ s_cd₁ s_cd₂ s_da₁ s_da₂).card ≤ 8 := by
  unfold eightEdgeCover
  -- A finite set of 8 explicit elements has card ≤ 8
  apply Finset.card_le_card
  intro x hx
  exact hx

/-- MAIN THEOREM: τ ≤ 8 for cycle_4 configuration -/
theorem tau_le_8_cycle4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P : Finset (Finset V), isPacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Get 2 spokes for each shared vertex
  obtain ⟨s_ab₁, s_ab₂, h_ab⟩ := two_spokes_cover_at_vertex G M hM cfg cfg.v_ab (by simp [sharedVertices])
  obtain ⟨s_bc₁, s_bc₂, h_bc⟩ := two_spokes_cover_at_vertex G M hM cfg cfg.v_bc (by simp [sharedVertices])
  obtain ⟨s_cd₁, s_cd₂, h_cd⟩ := two_spokes_cover_at_vertex G M hM cfg cfg.v_cd (by simp [sharedVertices])
  obtain ⟨s_da₁, s_da₂, h_da⟩ := two_spokes_cover_at_vertex G M hM cfg cfg.v_da (by simp [sharedVertices])
  -- Construct the 8-edge cover
  let E := eightEdgeCover G cfg s_ab₁ s_ab₂ s_bc₁ s_bc₂ s_cd₁ s_cd₂ s_da₁ s_da₂
  -- Show E covers all triangles
  have h_cover : isEdgeCover G E := by
    intro T hT
    -- T contains some shared vertex v
    obtain ⟨v, hv_shared, hv_in_T⟩ := triangle_contains_shared_vertex G M hM cfg T hT
    -- The spokes at v cover T
    simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton] at hv_shared
    rcases hv_shared with rfl | rfl | rfl | rfl
    · -- v = v_ab
      have := h_ab T hT hv_in_T
      rcases this with hs₁ | hs₂
      · use s(cfg.v_ab, s_ab₁)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_ab, s_ab₁
          refine ⟨rfl, hv_in_T, ?_, ?_⟩
          · -- s_ab₁ ∈ T: follows from s(v_ab, s_ab₁) ∈ T.sym2
            simp only [Finset.mem_sym2] at hs₁
            exact hs₁.2
          · -- v_ab ≠ s_ab₁: otherwise spoke is a self-loop, doesn't cover anything
            sorry
      · use s(cfg.v_ab, s_ab₂)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_ab, s_ab₂
          simp only [Finset.mem_sym2] at hs₂
          exact ⟨rfl, hv_in_T, hs₂.2, sorry⟩
    · -- v = v_bc
      have := h_bc T hT hv_in_T
      rcases this with hs₁ | hs₂
      · use s(cfg.v_bc, s_bc₁)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_bc, s_bc₁
          simp only [Finset.mem_sym2] at hs₁
          exact ⟨rfl, hv_in_T, hs₁.2, sorry⟩
      · use s(cfg.v_bc, s_bc₂)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_bc, s_bc₂
          simp only [Finset.mem_sym2] at hs₂
          exact ⟨rfl, hv_in_T, hs₂.2, sorry⟩
    · -- v = v_cd
      have := h_cd T hT hv_in_T
      rcases this with hs₁ | hs₂
      · use s(cfg.v_cd, s_cd₁)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_cd, s_cd₁
          simp only [Finset.mem_sym2] at hs₁
          exact ⟨rfl, hv_in_T, hs₁.2, sorry⟩
      · use s(cfg.v_cd, s_cd₂)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_cd, s_cd₂
          simp only [Finset.mem_sym2] at hs₂
          exact ⟨rfl, hv_in_T, hs₂.2, sorry⟩
    · -- v = v_da
      have := h_da T hT hv_in_T
      rcases this with hs₁ | hs₂
      · use s(cfg.v_da, s_da₁)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_da, s_da₁
          simp only [Finset.mem_sym2] at hs₁
          exact ⟨rfl, hv_in_T, hs₁.2, sorry⟩
      · use s(cfg.v_da, s_da₂)
        constructor
        · simp [E, eightEdgeCover]
        · use cfg.v_da, s_da₂
          simp only [Finset.mem_sym2] at hs₂
          exact ⟨rfl, hv_in_T, hs₂.2, sorry⟩
  -- τ ≤ |E| ≤ 8
  have h_card : E.card ≤ 8 := eight_cover_card_le_8 G cfg s_ab₁ s_ab₂ s_bc₁ s_bc₂ s_cd₁ s_cd₂ s_da₁ s_da₂
  -- triangleCoveringNumber is the infimum of covers
  unfold triangleCoveringNumber
  apply Nat.sInf_le
  use E.card
  constructor
  · use E
  · exact h_card

end TuzaNu4
