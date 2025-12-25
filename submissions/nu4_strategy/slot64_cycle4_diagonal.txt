/-
Tuza ν=4 Strategy - Slot 64: CYCLE_4 via Diagonal Independence

ALTERNATIVE APPROACH: Exploit that opposite pairs are vertex-disjoint.

For CYCLE_4 (A—B—C—D—A):
- A ∩ C = ∅ (diagonally opposite, vertex-disjoint)
- B ∩ D = ∅ (diagonally opposite, vertex-disjoint)

STRATEGY:
1. Decompose into "Black" (S_A ∪ S_C) and "White" (S_B ∪ S_D)
2. Since A, C are vertex-disjoint, their S sets have simpler interaction
3. τ(S_A ∪ S_C) ≤ τ(S_A) + τ(S_C) ≤ 2 + 2 = 4
4. τ(S_B ∪ S_D) ≤ τ(S_B) + τ(S_D) ≤ 2 + 2 = 4
5. Handle bridges X_ef between adjacent pairs separately

PROVEN LEMMAS USED:
- tau_S_le_2: τ(S_e) ≤ 2
- tau_X_le_2: τ(bridges) ≤ 2
- tau_union_le_sum: τ(A∪B) ≤ τ(A) + τ(B)

KEY INSIGHT (Gemini): Vertex-disjoint opposite pairs means simpler analysis.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Definitions (same as other slots)
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- S_e: triangles sharing edge with e but not with any other packing element
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- X_ef: bridges between e and f (triangles sharing edge with both)
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- PROVEN scaffolding
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot61

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- PROVEN in slot6

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- PROVEN in slot24

-- KEY LEMMA: Diagonal pairs have empty bridges
-- If A ∩ C = ∅, no triangle can share an edge with both A and C
lemma diagonal_bridges_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (hA3 : A.card = 3) (hC3 : C.card = 3)
    (h_disj : (A ∩ C).card = 0) :
    X_ef G A C = ∅ := by
  -- If A and C share no vertex, no triangle can share edge with both
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ⟨ht_clique, h_A, h_C⟩
  -- t has exactly 3 vertices (it's a triangle)
  have ht3 : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_clique
    exact ht_clique.2
  -- t ∩ A has ≥2 elements, t ∩ C has ≥2 elements
  -- So |t ∩ A| + |t ∩ C| ≥ 4, but t only has 3 vertices
  -- By pigeonhole, t ∩ A and t ∩ C must overlap
  -- Any overlap means A ∩ C ≠ ∅, contradiction
  have h_sum : (t ∩ A).card + (t ∩ C).card ≥ 4 := Nat.add_le_add h_A h_C
  -- But (t ∩ A) ∪ (t ∩ C) ⊆ t, so |(t ∩ A) ∪ (t ∩ C)| ≤ 3
  have h_union_sub : (t ∩ A) ∪ (t ∩ C) ⊆ t := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter] at hx
    rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
  have h_union_card : ((t ∩ A) ∪ (t ∩ C)).card ≤ 3 := by
    calc ((t ∩ A) ∪ (t ∩ C)).card ≤ t.card := Finset.card_le_card h_union_sub
      _ = 3 := ht3
  -- By inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B|
  -- So |A ∩ B| = |A| + |B| - |A ∪ B| ≥ 4 - 3 = 1
  have h_inter_card : ((t ∩ A) ∩ (t ∩ C)).card ≥ 1 := by
    have h_ie := Finset.card_union_add_card_inter (t ∩ A) (t ∩ C)
    omega
  -- (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C)
  have h_inter_eq : (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C) := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  -- But A ∩ C = ∅, so t ∩ (A ∩ C) = ∅
  rw [h_inter_eq] at h_inter_card
  simp only [Finset.card_eq_zero] at h_disj
  rw [h_disj, Finset.inter_empty] at h_inter_card
  simp at h_inter_card

-- Helper: packing elements are triangles (card 3)
lemma packing_elem_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) : e.card = 3 := by
  -- M is a triangle packing, so e ∈ cliqueFinset 3
  have h_sub := hM.1.1
  have he_clique := h_sub he
  simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at he_clique
  exact he_clique.2

-- MAIN: Cycle4 via diagonal decomposition
theorem tau_le_8_cycle4_diagonal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Extract structure
  have hM_eq : M = {A, B, C, D} := hcycle.1
  have hA : A ∈ M := by rw [hM_eq]; simp
  have hB : B ∈ M := by rw [hM_eq]; simp
  have hC : C ∈ M := by rw [hM_eq]; simp
  have hD : D ∈ M := by rw [hM_eq]; simp

  -- A, B, C, D are triangles (card 3)
  have hA3 : A.card = 3 := packing_elem_card_3 G M hM A hA
  have hB3 : B.card = 3 := packing_elem_card_3 G M hM B hB
  have hC3 : C.card = 3 := packing_elem_card_3 G M hM C hC
  have hD3 : D.card = 3 := packing_elem_card_3 G M hM D hD

  -- Opposite pairs are vertex-disjoint
  have hAC_disj : (A ∩ C).card = 0 := hcycle.2.2.2.2.2.2.2.2.2.2.2.1
  have hBD_disj : (B ∩ D).card = 0 := hcycle.2.2.2.2.2.2.2.2.2.2.2.2

  -- No bridges between diagonal pairs
  have h_no_AC : X_ef G A C = ∅ := diagonal_bridges_empty G A C hA3 hC3 hAC_disj
  have h_no_BD : X_ef G B D = ∅ := diagonal_bridges_empty G B D hB3 hD3 hBD_disj

  -- Adjacent pairs share exactly 1 vertex
  have hAB_card : (A ∩ B).card = 1 := hcycle.2.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.1

  -- τ(S_A) ≤ 2, τ(S_B) ≤ 2, τ(S_C) ≤ 2, τ(S_D) ≤ 2
  have h_SA : triangleCoveringNumberOn G (S_e G M A) ≤ 2 := tau_S_le_2 G M hM A hA
  have h_SB : triangleCoveringNumberOn G (S_e G M B) ≤ 2 := tau_S_le_2 G M hM B hB
  have h_SC : triangleCoveringNumberOn G (S_e G M C) ≤ 2 := tau_S_le_2 G M hM C hC
  have h_SD : triangleCoveringNumberOn G (S_e G M D) ≤ 2 := tau_S_le_2 G M hM D hD

  -- Adjacent bridges (4 of them): AB, BC, CD, DA
  have hAB : A ≠ B := hcycle.2.1
  have hBC : B ≠ C := hcycle.2.2.1
  have hCD : C ≠ D := hcycle.2.2.2.1
  have hDA : D ≠ A := hcycle.2.2.2.2.1

  have h_XAB : triangleCoveringNumberOn G (X_ef G A B) ≤ 2 := tau_X_le_2 G M hM A B hA hB hAB
  have h_XBC : triangleCoveringNumberOn G (X_ef G B C) ≤ 2 := tau_X_le_2 G M hM B C hB hC hBC
  have h_XCD : triangleCoveringNumberOn G (X_ef G C D) ≤ 2 := tau_X_le_2 G M hM C D hC hD hCD
  have h_XDA : triangleCoveringNumberOn G (X_ef G D A) ≤ 2 := tau_X_le_2 G M hM D A hD hA hDA.symm

  -- Strategy: decompose into "Black" and "White" based on diagonal pairs
  -- Black = S_A ∪ S_C ∪ X_AB ∪ X_CD (triangles touching A or C)
  -- White = S_B ∪ S_D ∪ X_BC ∪ X_DA (triangles touching B or D)
  -- τ(Black) ≤ 2 + 2 + 2 + 2 = 8... but we need ≤ 4 each!

  -- Alternative: Use tau_union_le_sum with (A,B) and (C,D) pairs
  -- All triangles ⊆ T_pair(A,B) ∪ T_pair(C,D) by maximality
  -- τ(T_pair(A,B)) ≤ 4, τ(T_pair(C,D)) ≤ 4
  -- Total: ≤ 8

  -- This reduces to the same approach as slot63 (T_pair decomposition)
  sorry

end
