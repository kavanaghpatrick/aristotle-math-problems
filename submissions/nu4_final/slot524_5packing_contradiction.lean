/-
  slot524_5packing_contradiction.lean
  TARGET: Prove bridge + 2 externals → 5-packing (contradiction with ν=4)
  FROM slot451: Verified on Fin 10 that {A, D, T, E_B, E_C} form 5-packing
  TIER: 2 (packing construction, proven scaffolding)
-/

import Mathlib

set_option maxHeartbeats 600000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- DEFINITIONS (from slot451)
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ E ∧ 2 ≤ (T ∩ E).card ∧ ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1)

def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (T E F : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ 2 ≤ (T ∩ E).card ∧ 2 ≤ (T ∩ F).card

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  Disjoint A C ∧ Disjoint A D ∧ Disjoint B D

-- HELPER: S_e elements are edge-disjoint from non-adjacent packing elements
lemma Se_edge_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (B A D : Finset V)
    (hA : A ∈ M) (hD : D ∈ M) (hAne : A ≠ B) (hDne : D ≠ B)
    (E_B : Finset V) (hE : E_B ∈ S_e G M B) :
    (E_B ∩ A).card ≤ 1 ∧ (E_B ∩ D).card ≤ 1 := by
  simp only [S_e, mem_filter] at hE
  obtain ⟨_, _, _, hpw⟩ := hE
  exact ⟨hpw A hA hAne, hpw D hD hDne⟩

/-
PROOF SKETCH (5-packing construction):
Given PATH_4 = {A, B, C, D}, bridge T between B,C, and externals E_B ∈ S_e(B), E_C ∈ S_e(C):
1. {A, D, T, E_B, E_C} are all triangles in G
2. Pairwise edge-disjoint:
   - A ∩ D = ∅ (PATH_4 property)
   - A ∩ T ≤ 1 (T shares 2 vertices with B and C; A shares 1 with B, 0 with C)
   - A ∩ E_B, A ∩ E_C ≤ 1 (S_e definition)
   - D similar by symmetry
   - T ∩ E_B, T ∩ E_C ≤ 1 (hypothesis)
   - E_B ∩ E_C ≤ 1 (hypothesis)
3. Card = 5 (all distinct by construction)
-/

lemma five_packing_from_bridge_and_externals
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hM_pack : isTrianglePacking G M)
    (hpath : isPath4 M A B C D)
    (T E_B E_C : Finset V)
    (hT_bridge : isBridge G T B C)
    (hEB : E_B ∈ S_e G M B)
    (hEC : E_C ∈ S_e G M C)
    (hT_EB : (T ∩ E_B).card ≤ 1)
    (hT_EC : (T ∩ E_C).card ≤ 1)
    (hEB_EC : (E_B ∩ E_C).card ≤ 1) :
    ∃ P : Finset (Finset V), isTrianglePacking G P ∧ P.card = 5 := by
  obtain ⟨hMeq, hAB, hBC, hCD, hAC, hAD, hBD⟩ := hpath
  obtain ⟨hM_tri, _⟩ := hM_pack
  simp only [S_e, mem_filter] at hEB hEC
  obtain ⟨hEB_tri, _, _, hEB_pw⟩ := hEB
  obtain ⟨hEC_tri, _, _, hEC_pw⟩ := hEC
  have hA_tri : A ∈ G.cliqueFinset 3 := hM_tri (by simp [hMeq])
  have hD_tri : D ∈ G.cliqueFinset 3 := hM_tri (by simp [hMeq])
  have hA_in : A ∈ M := by simp [hMeq]
  have hD_in : D ∈ M := by simp [hMeq]
  let P : Finset (Finset V) := {A, D, T, E_B, E_C}
  use P
  constructor
  · constructor
    · -- All triangles
      intro t ht
      simp only [P, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact hA_tri
      · exact hD_tri
      · exact hT_bridge.1
      · exact hEB_tri
      · exact hEC_tri
    · -- Pairwise edge-disjoint: prove for all 10 distinct pairs
      sorry
  · -- Card = 5: need distinctness of A, D, T, E_B, E_C
    sorry

/-
PROOF SKETCH (contradiction):
If bridge T and externals E_B, E_C exist with pairwise edge-disjointness,
five_packing_from_bridge_and_externals gives P with |P| = 5.
But ν(G) = 4 means no 5-packing exists → contradiction.
-/

theorem five_packing_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_pack : isTrianglePacking G M)
    (hnu_max : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (T E_B E_C : Finset V)
    (hT_bridge : isBridge G T B C)
    (hEB : E_B ∈ S_e G M B)
    (hEC : E_C ∈ S_e G M C)
    (hT_EB : (T ∩ E_B).card ≤ 1)
    (hT_EC : (T ∩ E_C).card ≤ 1)
    (hEB_EC : (E_B ∩ E_C).card ≤ 1) :
    False := by
  obtain ⟨P, hP_pack, hP_card⟩ := five_packing_from_bridge_and_externals
    G M A B C D hM_pack hpath T E_B E_C hT_bridge hEB hEC hT_EB hT_EC hEB_EC
  have h5 : P.card ≤ 4 := hnu_max P hP_pack
  omega

-- Corollary: In ν=4 graphs, such "bad" configurations cannot exist
theorem no_bad_external_config
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_pack : isTrianglePacking G M)
    (hnu_max : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V)
    (hpath : isPath4 M A B C D) :
    ∀ T E_B E_C,
      isBridge G T B C →
      E_B ∈ S_e G M B →
      E_C ∈ S_e G M C →
      ¬((T ∩ E_B).card ≤ 1 ∧ (T ∩ E_C).card ≤ 1 ∧ (E_B ∩ E_C).card ≤ 1) := by
  intro T E_B E_C hT hEB hEC ⟨h1, h2, h3⟩
  exact five_packing_contradiction G M hM_pack hnu_max A B C D hpath
    T E_B E_C hT hEB hEC h1 h2 h3
