/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 72bb0e1a-ee89-4229-9b60-244d623e3091

The following was proved by Aristotle:

- lemma exists_two_covering_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      -- Cover the element E = {a,b,c}
      (e₁ ∈ ({a,b,c} : Finset V).sym2 ∨ e₂ ∈ ({a,b,c} : Finset V).sym2) ∧
      -- Cover all Type 1 externals
      (∀ T ∈ externalsWithEdge G a b c, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) ∧
      -- Cover all Type 2 externals
      (∀ T ∈ externalsWithEdge G b c a, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) ∧
      -- Cover all Type 3 externals
      (∀ T ∈ externalsWithEdge G a c b, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)
-/

/-
  slot410_tau_8_explicit.lean

  EXPLICIT PROOF: τ ≤ 8 for PATH_4 with ν = 4

  Uses case analysis on which external types exist.
  By 6-packing, at most 2 types exist, so we can always choose 2 covering edges.

  For E = {a, b, c} with edge types e₁ = {a,b}, e₂ = {b,c}, e₃ = {a,c}:
  - If type e₃ is empty: use e₁, e₂
  - If type e₂ is empty: use e₁, e₃
  - If type e₁ is empty: use e₂, e₃

  TIER: 2 (uses proven scaffolding from slot406/407)
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
-- EXTERNAL TYPE DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles sharing exactly edge {a,b} with E = {a,b,c} -/
def externalsWithEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ {a, b, c} ∧ a ∈ T ∧ b ∈ T ∧ c ∉ T)

/-- Type 1: {a,b,w} externals -/
def type1Exists (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) : Prop :=
  (externalsWithEdge G a b c).Nonempty

/-- Type 2: {b,c,w} externals -/
def type2Exists (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) : Prop :=
  (externalsWithEdge G b c a).Nonempty

/-- Type 3: {a,c,w} externals -/
def type3Exists (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) : Prop :=
  (externalsWithEdge G a c b).Nonempty

-- ══════════════════════════════════════════════════════════════════════════════
-- 6-PACKING CONTRADICTION (from slot406)
-- ══════════════════════════════════════════════════════════════════════════════

theorem six_triangles_contradict_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T₁ T₂ T₃ B C D : Finset V)
    (hT1 : T₁ ∈ G.cliqueFinset 3) (hT2 : T₂ ∈ G.cliqueFinset 3)
    (hT3 : T₃ ∈ G.cliqueFinset 3) (hB : B ∈ G.cliqueFinset 3)
    (hC : C ∈ G.cliqueFinset 3) (hD : D ∈ G.cliqueFinset 3)
    (h_distinct : T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₁ ≠ B ∧ T₁ ≠ C ∧ T₁ ≠ D ∧
                  T₂ ≠ T₃ ∧ T₂ ≠ B ∧ T₂ ≠ C ∧ T₂ ≠ D ∧
                  T₃ ≠ B ∧ T₃ ≠ C ∧ T₃ ≠ D ∧
                  B ≠ C ∧ B ≠ D ∧ C ≠ D)
    (h12 : (T₁ ∩ T₂).card ≤ 1) (h13 : (T₁ ∩ T₃).card ≤ 1)
    (h1B : (T₁ ∩ B).card ≤ 1) (h1C : (T₁ ∩ C).card ≤ 1) (h1D : (T₁ ∩ D).card ≤ 1)
    (h23 : (T₂ ∩ T₃).card ≤ 1)
    (h2B : (T₂ ∩ B).card ≤ 1) (h2C : (T₂ ∩ C).card ≤ 1) (h2D : (T₂ ∩ D).card ≤ 1)
    (h3B : (T₃ ∩ B).card ≤ 1) (h3C : (T₃ ∩ C).card ≤ 1) (h3D : (T₃ ∩ D).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) (hBD : (B ∩ D).card ≤ 1) (hCD : (C ∩ D).card ≤ 1)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4) :
    False := by
  let S : Finset (Finset V) := {T₁, T₂, T₃, B, C, D}
  have hS_packing : isTrianglePacking G S := by
    constructor
    · intro X hX
      simp only [S, mem_insert, mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · intro X hX Y hY hXY
      simp only [S, mem_insert, mem_singleton, mem_coe] at hX hY
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hY with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hXY | assumption | (rw [inter_comm]; assumption)
  have hS_card : S.card = 6 := by
    simp only [S]
    rw [card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem,
        card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
    · simp [h_distinct.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    · simp [h_distinct.2.2.2.2.2.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    · simp [h_distinct.2.2.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.2.2.2.1]
    · simp [h_distinct.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.1, h_distinct.2.2.2.2.2.2.2.2.1]
    · simp [h_distinct.1, h_distinct.2.1, h_distinct.2.2.1, h_distinct.2.2.2.1, h_distinct.2.2.2.2.1]
  have h_bound := hNu4 S hS_packing
  omega

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Not all 3 types can exist
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If all 3 types exist for E = {a,b,c}, get witness triangles T₁, T₂, T₃.
Together with B, C, D from M, we have 6 edge-disjoint triangles.
This contradicts ν = 4 by six_triangles_contradict_nu4.
-/
lemma not_all_three_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    ¬(type1Exists G a b c ∧ type2Exists G a b c ∧ type3Exists G a b c) := by
  intro ⟨h1, h2, h3⟩
  -- Extract witness triangles
  obtain ⟨T₁, hT1⟩ := h1
  obtain ⟨T₂, hT2⟩ := h2
  obtain ⟨T₃, hT3⟩ := h3
  -- Need to show these 6 triangles form a packing and apply contradiction
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ADAPTIVE EDGE SELECTION
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
By not_all_three_types, at least one type is empty.
Case analysis on which type is missing determines which 2 edges to use.
-/
lemma exists_two_covering_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      -- Cover the element E = {a,b,c}
      (e₁ ∈ ({a,b,c} : Finset V).sym2 ∨ e₂ ∈ ({a,b,c} : Finset V).sym2) ∧
      -- Cover all Type 1 externals
      (∀ T ∈ externalsWithEdge G a b c, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) ∧
      -- Cover all Type 2 externals
      (∀ T ∈ externalsWithEdge G b c a, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) ∧
      -- Cover all Type 3 externals
      (∀ T ∈ externalsWithEdge G a c b, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- By not_all_three_types, at least one type is empty
  have h_not_all := not_all_three_types G M hM hNu4 a b c hE hab hbc hac B C D
    hB hC hD hB_ne hC_ne hD_ne hBC hBD hCD
  push_neg at h_not_all
  -- Case analysis
  by_cases h1 : type1Exists G a b c
  · by_cases h2 : type2Exists G a b c
    · -- Types 1, 2 exist → Type 3 must not exist
      have h3 : ¬type3Exists G a b c := h_not_all h1 h2
      -- Use edges {a,b} and {b,c}
      use s(a, b), s(b, c)
      refine' ⟨ _, _, _, _, _ ⟩;
      · have := hM.1 hE; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
        rw [ SimpleGraph.isNClique_iff ] at this ; aesop;
      · have := hM.1 hE; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
        rw [ SimpleGraph.isNClique_iff ] at this ; aesop;
      · simp +decide [ Sym2.mem_iff ];
      · intro T hT; have := Finset.mem_filter.mp hT; simp_all +decide [ Finset.subset_iff, Sym2.eq ] ;
      · simp_all +decide [ type1Exists, type2Exists, type3Exists, externalsWithEdge ]
    · -- Type 2 doesn't exist
      -- Use edges {a,b} and {a,c}
      use s(a, b), s(a, c)
      unfold type1Exists type2Exists externalsWithEdge at *; simp_all +decide ;
      have := hM.1 hE; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  · -- Type 1 doesn't exist
    -- Use edges {b,c} and {a,c}
    use s(b, c), s(a, c)
    simp_all +decide [ type1Exists, type2Exists, type3Exists, externalsWithEdge ];
    have := hM.1 hE; simp_all +decide [ SimpleGraph.isNClique_iff ] ;

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

def isPath4Labeled (M : Finset (Finset V)) (A B C D : Finset V)
    (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V) : Prop :=
  M = {A, B, C, D} ∧
  A = {v₁, a₂, a₃} ∧ B = {v₁, v₂, b₃} ∧ C = {v₂, v₃, c₃} ∧ D = {v₃, d₂, d₃} ∧
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ v₁ ≠ b₃ ∧ v₁ ≠ c₃ ∧ v₁ ≠ d₂ ∧ v₁ ≠ d₃ ∧
  v₂ ≠ v₃ ∧ v₂ ≠ a₂ ∧ v₂ ≠ a₃ ∧ v₂ ≠ b₃ ∧ v₂ ≠ c₃ ∧ v₂ ≠ d₂ ∧ v₂ ≠ d₃ ∧
  v₃ ≠ a₂ ∧ v₃ ≠ a₃ ∧ v₃ ≠ b₃ ∧ v₃ ≠ c₃ ∧ v₃ ≠ d₂ ∧ v₃ ≠ d₃ ∧
  a₂ ≠ a₃ ∧ a₂ ≠ b₃ ∧ a₂ ≠ c₃ ∧ a₂ ≠ d₂ ∧ a₂ ≠ d₃ ∧
  a₃ ≠ b₃ ∧ a₃ ≠ c₃ ∧ a₃ ≠ d₂ ∧ a₃ ≠ d₃ ∧
  b₃ ≠ c₃ ∧ b₃ ≠ d₂ ∧ b₃ ≠ d₃ ∧
  c₃ ≠ d₂ ∧ c₃ ≠ d₃ ∧
  d₂ ≠ d₃

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_path4_explicit (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  -- For each M-element, get 2 covering edges using exists_two_covering_edges
  -- Then union all 4 × 2 = 8 edges
  sorry

end