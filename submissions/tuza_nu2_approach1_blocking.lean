/-
TUZA ν=2 - APPROACH 1: Enhanced Blocking Number
Strategy: Prove ≤2 edges can hit ALL maximum packings, then extend to cover

KEY INSIGHT: Instead of proving extensions collapse, prove blocking number b(G) ≤ 2
This directly gives the reduction lemma.

IMPROVEMENTS OVER PREVIOUS:
1. Explicit intersection lemma (any triangle hits some packing triangle)
2. Complete case classification (only disjoint or bowtie possible)
3. Helper lemmas to guide Aristotle
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  IsTrianglePacking G P ∧ P.card = trianglePackingNumber G

def maxPackings (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Finset V)) :=
  (G.cliqueFinset 3).powerset.filter (fun P => IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G)

def BlocksAllMaxPackings (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∀ P ∈ maxPackings G, ∃ t ∈ P, ¬ Disjoint (triangleEdges t) S

def blockingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (BlocksAllMaxPackings G)).image Finset.card
    |>.min.getD G.edgeFinset.card

/-! ## Helper Lemmas (Grok's suggestions) -/

/-- Any triangle in G must share an edge with some triangle in any max packing -/
lemma any_triangle_intersects_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) (P : Finset (Finset V)) (hP : IsMaxPacking G P)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ t' ∈ P, ¬ Disjoint (triangleEdges t) (triangleEdges t') := by
  -- If t were edge-disjoint from all P-triangles, P ∪ {t} would be a packing of size 3
  by_contra h_all_disj
  push_neg at h_all_disj
  have h_disj : IsEdgeDisjoint (insert t P) := by
    unfold IsEdgeDisjoint Set.PairwiseDisjoint
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact h_all_disj y hy
    · exact (h_all_disj x hx).symm
    · exact hP.1.2 hx hy hxy
  have h_sub : insert t P ⊆ G.cliqueFinset 3 := by
    intro x hx; simp at hx; rcases hx with rfl | hx
    · exact ht
    · exact hP.1.1 hx
  have ht_notin : t ∉ P := by
    intro ht_in
    have := h_all_disj t ht_in
    simp [Finset.disjoint_self_iff_empty] at this
    have ht_card : t.card = 3 := ht.2
    have : t.offDiag.Nonempty := Finset.offDiag_nonempty.mpr (by omega)
    simp [triangleEdges] at this
    exact this.ne_empty (by simp_all)
  have h_bigger : (insert t P).card = 3 := by
    rw [Finset.card_insert_of_not_mem ht_notin, hP.2, h]
  have h_le : (insert t P).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    apply Finset.le_sup
    simp [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_sub, h_disj⟩
  omega

/-- Classification: When ν=2, two packing triangles are either disjoint or share exactly 1 vertex -/
lemma nu2_overlap_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) (t1 t2 : Finset V)
    (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hne : t1 ≠ t2) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2)) :
    Disjoint t1 t2 ∨ (t1 ∩ t2).card = 1 := by
  -- If they share ≥2 vertices, they share an edge, contradicting edge-disjointness
  by_contra h_contra
  push_neg at h_contra
  have h_inter_ge_2 : (t1 ∩ t2).card ≥ 2 := by
    rcases h_contra with ⟨h_not_disj, h_not_one⟩
    have h_nonempty : (t1 ∩ t2).Nonempty := by
      rw [Finset.not_disjoint_iff] at h_not_disj
      exact h_not_disj
    have h_card_pos : 0 < (t1 ∩ t2).card := Finset.card_pos.mpr h_nonempty
    omega
  -- Two vertices in intersection means shared edge
  obtain ⟨a, ha⟩ : ∃ a, a ∈ t1 ∩ t2 := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ t1 ∩ t2, b ≠ a := by
    have := Finset.exists_ne_of_one_lt_card (by omega : 1 < (t1 ∩ t2).card) a
    exact ⟨this.choose, this.choose_spec.1, this.choose_spec.2⟩
  have h_shared_edge : s(a, b) ∈ triangleEdges t1 ∧ s(a, b) ∈ triangleEdges t2 := by
    constructor <;> simp [triangleEdges, Finset.mem_image, Finset.mem_offDiag]
    · exact ⟨(a, b), ⟨Finset.mem_of_mem_inter_left ha, Finset.mem_of_mem_inter_left hb, hab⟩, rfl⟩
    · exact ⟨(a, b), ⟨Finset.mem_of_mem_inter_right ha, Finset.mem_of_mem_inter_right hb, hab⟩, rfl⟩
  exact Finset.disjoint_left.mp h_edge_disj h_shared_edge.1 h_shared_edge.2

/-- Extract two triangles from a ν=2 packing -/
lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  have h_exists : ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
    have : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
    have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
    obtain ⟨P, hP₁, hP₂⟩ := h_max
    simp [Finset.mem_filter, Finset.mem_powerset] at hP₁
    exact ⟨P, hP₁.1, hP₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := h_exists
  rw [h] at hP_card
  obtain ⟨t1, t2, hne, hP_eq⟩ := Finset.card_eq_two.mp hP_card
  use t1, t2
  have ht1_mem : t1 ∈ P := hP_eq ▸ Finset.mem_insert_self t1 {t2}
  have ht2_mem : t2 ∈ P := hP_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t2)
  exact ⟨hP_sub ht1_mem, hP_sub ht2_mem, hne, hP_disj ht1_mem ht2_mem hne⟩

/-! ## Case 1: Vertex-Disjoint Triangles -/

/-- When vertex-disjoint, one edge from each triangle blocks -/
lemma vertex_disjoint_blocking (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hne : t1 ≠ t2) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (h_vertex_disj : Disjoint t1 t2)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ triangleEdges t1) (he2 : e2 ∈ triangleEdges t2) :
    BlocksAllMaxPackings G {e1, e2} := by
  sorry

/-! ## Case 2: Bowtie (Share 1 Vertex) -/

/-- When sharing one vertex v, the two edges at v block all packings -/
lemma bowtie_blocking (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hne : t1 ≠ t2) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (v : V) (hv : (t1 ∩ t2) = {v}) :
    ∃ (e1 e2 : Sym2 V), e1 ∈ G.edgeFinset ∧ e2 ∈ G.edgeFinset ∧ BlocksAllMaxPackings G {e1, e2} := by
  sorry

/-! ## Main Theorem -/

/-- THE KEY: Blocking number ≤ 2 when ν = 2 -/
theorem blocking_number_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    blockingNumber G ≤ 2 := by
  obtain ⟨t1, t2, ht1, ht2, hne, h_edge_disj⟩ := packing_two_triangles G h
  rcases nu2_overlap_classification G h t1 t2 ht1 ht2 hne h_edge_disj with h_disj | h_bowtie
  · -- Case: vertex-disjoint
    sorry
  · -- Case: bowtie (share 1 vertex)
    sorry

/-- Blocking implies ν decreases -/
lemma blocking_reduces_nu (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) (h_block : BlocksAllMaxPackings G S) :
    trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  sorry

/-- MAIN: τ ≤ 4 when ν = 2 via blocking argument -/
theorem tuza_nu_2_blocking (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    triangleCoveringNumber G ≤ 4 := by
  -- Use blocking_number_le_2 and blocking_reduces_nu
  -- Then apply deletion lemma and ν=1 result
  sorry

end
