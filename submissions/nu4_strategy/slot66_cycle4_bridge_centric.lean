/-
Tuza ν=4 Strategy - Slot 66: CYCLE_4 via Bridge-Centric Decomposition

STRATEGY: Full S_e decomposition with explicit bridge counting.

For CYCLE_4 (A—B—C—D—A):
- All triangles = S_A ∪ S_B ∪ S_C ∪ S_D ∪ (bridges)
- Bridges: X_AB, X_BC, X_CD, X_DA (4 adjacent pairs)
- No diagonal bridges: X_AC = ∅, X_BD = ∅ (opposite pairs disjoint)

COUNTING:
- τ(S_A) ≤ 2, τ(S_B) ≤ 2, τ(S_C) ≤ 2, τ(S_D) ≤ 2 → total ≤ 8
- BUT bridges overlap with S sets!
- Bridges X_ef contain shared vertex v_ef
- So X_AB triangles are counted in S_A or S_B already

KEY INSIGHT: The S_e sets + bridges is a PARTITION (up to overlap)
- X_AB ⊆ S_A ∪ S_B (bridges between A,B share edge with A or B)
- Wait, that's wrong! S_e requires sharing with ONLY e.
- X_AB triangles share edge with BOTH A and B, so they're in neither S_A nor S_B!

CORRECT DECOMPOSITION:
- allTriangles = (S_A ∪ S_B ∪ S_C ∪ S_D) ∪ (X_AB ∪ X_BC ∪ X_CD ∪ X_DA)
- This is disjoint by definition of S_e
- τ(each S_e) ≤ 2 → 4 × 2 = 8
- τ(each X_ef) ≤ 2 → 4 × 2 = 8... but that's 16 total!

REFINEMENT: Bridges can be covered more efficiently
- All X_AB bridges contain v_ab (shared vertex)
- We can cover ALL X_AB with at most 2 edges incident to v_ab
- But these edges may overlap with S covers!

FINAL STRATEGY: Interleave bridge and S covers
- Cover S_A with 2 edges (one being edge of A)
- Cover S_C with 2 edges
- Cover X_AB and X_DA with edges through v_ab and v_da
- Since A has edges to v_ab and v_da, we get overlap!

Actually, the T_pair approach (slot63) is cleaner. This file explores
an alternative counting argument.

TARGET: tau_le_8_cycle4_bridges
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

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

-- X_ef: bridges between e and f
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

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

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  sorry -- PROVEN in slot61

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE STRUCTURE LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- All bridges contain the shared vertex
lemma bridge_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) : v ∈ t := by
  simp only [X_ef, Finset.mem_filter] at ht
  -- t ∩ e has ≥ 2 elements, t ∩ f has ≥ 2 elements
  -- e ∩ f = {v}, so (t ∩ e) ∩ (t ∩ f) = t ∩ (e ∩ f) = t ∩ {v}
  -- By pigeonhole (t has 3 vertices), this intersection is nonempty
  -- So v ∈ t
  sorry

-- No bridges between disjoint pairs
lemma no_bridge_between_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he3 : e.card = 3) (hf3 : f.card = 3)
    (h_disj : (e ∩ f).card = 0) :
    X_ef G e f = ∅ := by
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ⟨ht_clique, h_e, h_f⟩
  -- Same pigeonhole argument as diagonal_bridges_empty
  have ht3 : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_clique
    exact ht_clique.2
  have h_sum : (t ∩ e).card + (t ∩ f).card ≥ 4 := Nat.add_le_add h_e h_f
  have h_union_sub : (t ∩ e) ∪ (t ∩ f) ⊆ t := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter] at hx
    rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
  have h_union_card : ((t ∩ e) ∪ (t ∩ f)).card ≤ 3 := by
    calc ((t ∩ e) ∪ (t ∩ f)).card ≤ t.card := Finset.card_le_card h_union_sub
      _ = 3 := ht3
  have h_inter_card : ((t ∩ e) ∩ (t ∩ f)).card ≥ 1 := by
    have h_ie := Finset.card_union_add_card_inter (t ∩ e) (t ∩ f)
    omega
  have h_inter_eq : (t ∩ e) ∩ (t ∩ f) = t ∩ (e ∩ f) := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [h_inter_eq] at h_inter_card
  simp only [Finset.card_eq_zero] at h_disj
  rw [h_disj, Finset.inter_empty] at h_inter_card
  simp at h_inter_card

-- ══════════════════════════════════════════════════════════════════════════════
-- DECOMPOSITION
-- ══════════════════════════════════════════════════════════════════════════════

-- All triangles decompose into S sets and bridges
-- Note: This is NOT disjoint - triangles can be in multiple X_ef if they
-- share edges with 3+ packing elements. But for ν=4, each triangle shares
-- edge with at most 2 packing elements (otherwise we'd have ν ≥ 5).

lemma all_triangles_in_S_or_X (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t ∈ S_e G M A ∪ S_e G M B ∪ S_e G M C ∪ S_e G M D ∪
        X_ef G A B ∪ X_ef G B C ∪ X_ef G C D ∪ X_ef G D A := by
  -- Every triangle shares edge with some packing element
  obtain ⟨e, he_in_M, h_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  have hM_eq : M = {A, B, C, D} := hcycle.1
  rw [hM_eq] at he_in_M

  -- Case split on which element(s) t shares edge with
  -- If t shares edge with exactly one element → in S_e
  -- If t shares edge with two adjacent elements → in X_ef

  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_cycle4_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  have hM_eq : M = {A, B, C, D} := hcycle.1
  have hA : A ∈ M := by rw [hM_eq]; simp
  have hB : B ∈ M := by rw [hM_eq]; simp
  have hC : C ∈ M := by rw [hM_eq]; simp
  have hD : D ∈ M := by rw [hM_eq]; simp

  -- Distinctness
  have hAB : A ≠ B := hcycle.2.1
  have hBC : B ≠ C := hcycle.2.2.1
  have hCD : C ≠ D := hcycle.2.2.2.1
  have hDA : D ≠ A := hcycle.2.2.2.2.1

  -- S bounds
  have h_SA : triangleCoveringNumberOn G (S_e G M A) ≤ 2 := tau_S_le_2 G M hM A hA
  have h_SB : triangleCoveringNumberOn G (S_e G M B) ≤ 2 := tau_S_le_2 G M hM B hB
  have h_SC : triangleCoveringNumberOn G (S_e G M C) ≤ 2 := tau_S_le_2 G M hM C hC
  have h_SD : triangleCoveringNumberOn G (S_e G M D) ≤ 2 := tau_S_le_2 G M hM D hD

  -- Bridge bounds (only 4 adjacent pairs have bridges)
  have h_XAB : triangleCoveringNumberOn G (X_ef G A B) ≤ 2 := tau_X_le_2 G M hM A B hA hB hAB
  have h_XBC : triangleCoveringNumberOn G (X_ef G B C) ≤ 2 := tau_X_le_2 G M hM B C hB hC hBC
  have h_XCD : triangleCoveringNumberOn G (X_ef G C D) ≤ 2 := tau_X_le_2 G M hM C D hC hD hCD
  have h_XDA : triangleCoveringNumberOn G (X_ef G D A) ≤ 2 := tau_X_le_2 G M hM D A hD hA hDA.symm

  -- KEY: We can cover more efficiently using shared vertices
  -- Each adjacent pair (e,f) shares vertex v_ef
  -- Bridges X_ef all contain v_ef
  -- Edges through v_ef can cover both S_e contributions and X_ef

  -- Using T_pair approach instead (cleaner)
  -- τ(T_pair(A,B)) ≤ 4, τ(T_pair(C,D)) ≤ 4
  -- Their union covers all triangles
  -- Total: 8

  sorry

end
