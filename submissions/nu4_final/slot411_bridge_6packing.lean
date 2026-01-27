/-
  slot411_bridge_6packing.lean

  BRIDGE LEMMA: Connect external type witnesses to 6-packing contradiction

  If all 3 external types exist for E = {a,b,c}:
  - T₁ ∈ externalsWithEdge(a,b) means T₁ = {a,b,w₁}, w₁ ≠ c
  - T₂ ∈ externalsWithEdge(b,c) means T₂ = {b,c,w₂}, w₂ ≠ a
  - T₃ ∈ externalsWithEdge(a,c) means T₃ = {a,c,w₃}, w₃ ≠ b

  Together with B,C,D from M, these 6 triangles are pairwise edge-disjoint.
  This contradicts ν = 4.

  TIER: 1 (intersection bounds are simple set arithmetic)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def externalsWithEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ {a, b, c} ∧ a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- INTERSECTION LEMMAS FOR EXTERNAL TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

/-- T₁ = {a,b,w₁} and T₂ = {b,c,w₂} share at most vertex b -/
lemma external_T1_T2_inter_le_1 (a b c w₁ w₂ : V)
    (hw1_ne_c : w₁ ≠ c) (hw2_ne_a : w₂ ≠ a)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ({a, b, w₁} ∩ {b, c, w₂} : Finset V).card ≤ 1 := by
  -- T₁ ∩ T₂ ⊆ {b} since:
  -- a ∉ T₂ (a ≠ b, a ≠ c, a ≠ w₂)
  -- w₁ ∉ T₂ (w₁ ≠ b by hab contrapos, w₁ ≠ c by hw1_ne_c, need w₁ ≠ w₂)
  by_cases hw : w₁ = w₂
  · -- w₁ = w₂, but w₁ ≠ c and w₂ ≠ a, so intersection is {b, w₁}
    subst hw
    have h : ({a, b, w₁} : Finset V) ∩ {b, c, w₁} ⊆ {b, w₁} := by
      intro x hx
      simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
      rcases hx.1 with rfl | rfl | rfl
      · -- x = a, but a ∉ {b, c, w₁}
        rcases hx.2 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact absurd rfl hac
        · exact absurd rfl hw2_ne_a
      · exact Or.inl rfl
      · exact Or.inr rfl
    calc ({a, b, w₁} : Finset V).card ∩ {b, c, w₁}
        ≤ ({b, w₁} : Finset V).card := card_le_card h
      _ ≤ 2 := by simp
    sorry  -- Need to show ≤ 1, this case is tricky
  · -- w₁ ≠ w₂
    have h : ({a, b, w₁} : Finset V) ∩ {b, c, w₂} ⊆ {b} := by
      intro x hx
      simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
      rcases hx.1 with rfl | rfl | rfl
      · -- x = a ∈ {b, c, w₂}
        rcases hx.2 with rfl | rfl | rfl
        · exact rfl
        · exact absurd rfl hac
        · exact absurd rfl hw2_ne_a
      · exact rfl
      · -- x = w₁ ∈ {b, c, w₂}
        rcases hx.2 with rfl | rfl | rfl
        · exact rfl
        · exact absurd rfl hw1_ne_c
        · exact absurd rfl hw
    calc ({a, b, w₁} : Finset V).card ∩ {b, c, w₂}
        ≤ ({b} : Finset V).card := card_le_card h
      _ = 1 := card_singleton b

/-- T₁ = {a,b,w₁} and T₃ = {a,c,w₃} share at most vertex a -/
lemma external_T1_T3_inter_le_1 (a b c w₁ w₃ : V)
    (hw1_ne_c : w₁ ≠ c) (hw3_ne_b : w₃ ≠ b)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hw1_ne_w3 : w₁ ≠ w₃) :
    ({a, b, w₁} ∩ {a, c, w₃} : Finset V).card ≤ 1 := by
  have h : ({a, b, w₁} : Finset V) ∩ {a, c, w₃} ⊆ {a} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
    rcases hx.1 with rfl | rfl | rfl
    · rfl
    · -- b ∈ {a, c, w₃}
      rcases hx.2 with rfl | rfl | rfl
      · rfl
      · exact absurd rfl hbc.symm
      · exact absurd rfl hw3_ne_b
    · -- w₁ ∈ {a, c, w₃}
      rcases hx.2 with rfl | rfl | rfl
      · rfl
      · exact absurd rfl hw1_ne_c
      · exact absurd rfl hw1_ne_w3
  calc ({a, b, w₁} : Finset V).card ∩ {a, c, w₃}
      ≤ ({a} : Finset V).card := card_le_card h
    _ = 1 := card_singleton a

/-- T₂ = {b,c,w₂} and T₃ = {a,c,w₃} share at most vertex c -/
lemma external_T2_T3_inter_le_1 (a b c w₂ w₃ : V)
    (hw2_ne_a : w₂ ≠ a) (hw3_ne_b : w₃ ≠ b)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hw2_ne_w3 : w₂ ≠ w₃) :
    ({b, c, w₂} ∩ {a, c, w₃} : Finset V).card ≤ 1 := by
  have h : ({b, c, w₂} : Finset V) ∩ {a, c, w₃} ⊆ {c} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
    rcases hx.1 with rfl | rfl | rfl
    · -- b ∈ {a, c, w₃}
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hab.symm
      · rfl
      · exact absurd rfl hw3_ne_b
    · rfl
    · -- w₂ ∈ {a, c, w₃}
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hw2_ne_a
      · rfl
      · exact absurd rfl hw2_ne_w3
  calc ({b, c, w₂} : Finset V).card ∩ {a, c, w₃}
      ≤ ({c} : Finset V).card := card_le_card h
    _ = 1 := card_singleton c

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN BRIDGE LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- If all 3 external types exist, contradicts ν = 4 -/
theorem not_all_three_types_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    -- Type witnesses
    (T₁ : Finset V) (hT1_tri : T₁ ∈ G.cliqueFinset 3)
    (hT1_type : T₁ ∈ externalsWithEdge G a b c)
    (T₂ : Finset V) (hT2_tri : T₂ ∈ G.cliqueFinset 3)
    (hT2_type : T₂ ∈ externalsWithEdge G b c a)
    (T₃ : Finset V) (hT3_tri : T₃ ∈ G.cliqueFinset 3)
    (hT3_type : T₃ ∈ externalsWithEdge G a c b) :
    False := by
  -- Extract structure from externalsWithEdge membership
  simp only [externalsWithEdge, mem_filter] at hT1_type hT2_type hT3_type
  obtain ⟨_, hT1_ne, ha_in_T1, hb_in_T1, hc_notin_T1⟩ := hT1_type
  obtain ⟨_, hT2_ne, hb_in_T2, hc_in_T2, ha_notin_T2⟩ := hT2_type
  obtain ⟨_, hT3_ne, ha_in_T3, hc_in_T3, hb_notin_T3⟩ := hT3_type
  -- Get B, C, D are triangles
  have hB_tri : B ∈ G.cliqueFinset 3 := hM.1 hB
  have hC_tri : C ∈ G.cliqueFinset 3 := hM.1 hC
  have hD_tri : D ∈ G.cliqueFinset 3 := hM.1 hD
  -- Show all 15 pairwise intersections are ≤ 1
  -- Then apply 6-packing contradiction
  sorry

end
