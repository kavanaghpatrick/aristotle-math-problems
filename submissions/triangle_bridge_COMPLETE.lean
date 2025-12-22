/-
Triangle Bridge Lemma - Adapted from Hypergraph r=4

This adapts the proven hypergraph bridge_lemma to the triangle/graph setting.
The dimension reduction: 4-edges → triangles, 3-faces → edges, face-disjoint → edge-disjoint.

Key insight: If triangle h shares edges with both e and f (edge-disjoint packing elements),
then h ⊆ e ∪ f, and since |e ∪ f| ≤ 5 and |h| = 3, h must contain the shared vertex v.

Submission: 2025-12-21
Pattern: Scaffolded (includes adapted hypergraph proof structure)
Target: Triangle bridge lemma for Tuza ν=4 proof
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-
A triangle is a 3-element set of vertices forming a clique.
Two triangles are edge-disjoint if they share at most 1 vertex.
-/
def EdgeDisjoint (t₁ t₂ : Finset V) : Prop :=
  (t₁ ∩ t₂).card ≤ 1

def SharesEdge (t₁ t₂ : Finset V) : Prop :=
  (t₁ ∩ t₂).card ≥ 2

/-
SCAFFOLD: Hypergraph union size lemma (proven in aristotle_hypergraph_r4_COMPLETE.lean)
Adapted: If two triangles intersect in exactly 2 vertices (share an edge), their union has size 4.
-/
lemma triangle_union_share_edge (t₁ t₂ : Finset V)
    (h₁ : t₁.card = 3) (h₂ : t₂.card = 3)
    (h_inter : (t₁ ∩ t₂).card = 2) :
    (t₁ ∪ t₂).card = 4 := by
  have := Finset.card_union_add_card_inter t₁ t₂
  omega

/-
SCAFFOLD: If triangles share exactly one vertex, their union has size 5.
-/
lemma triangle_union_share_vertex (t₁ t₂ : Finset V)
    (h₁ : t₁.card = 3) (h₂ : t₂.card = 3)
    (h_inter : (t₁ ∩ t₂).card = 1) :
    (t₁ ∪ t₂).card = 5 := by
  have := Finset.card_union_add_card_inter t₁ t₂
  omega

/-
SCAFFOLD: If triangles are disjoint, their union has size 6.
-/
lemma triangle_union_disjoint (t₁ t₂ : Finset V)
    (h₁ : t₁.card = 3) (h₂ : t₂.card = 3)
    (h_inter : (t₁ ∩ t₂).card = 0) :
    (t₁ ∪ t₂).card = 6 := by
  have := Finset.card_union_add_card_inter t₁ t₂
  omega

/-
KEY LEMMA: If edge-disjoint triangles e, f both share edges with triangle h,
then e and f must share exactly one vertex (the "bridge vertex").

This is the triangle analog of the hypergraph bridge_lemma.
-/
lemma bridge_intersection_eq_one (e f h : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (hh : h.card = 3)
    (h_edge_disjoint : EdgeDisjoint e f)
    (h_share_e : SharesEdge h e)
    (h_share_f : SharesEdge h f) :
    (e ∩ f).card = 1 := by
  unfold EdgeDisjoint at h_edge_disjoint
  unfold SharesEdge at h_share_e h_share_f
  have h_inter_h_e : (h ∩ e).card ≥ 2 := h_share_e
  have h_inter_h_f : (h ∩ f).card ≥ 2 := h_share_f
  have h_inter_e_f_in_h : (e ∩ f ∩ h).card ≥ 1 := by
    have h_union_inters : (h ∩ e ∪ h ∩ f).card ≤ h.card := Finset.card_le_card (by
      intro x hx
      simp only [mem_union, mem_inter] at hx
      exact hx.elim And.left And.left)
    have := Finset.card_union_add_card_inter (h ∩ e) (h ∩ f)
    rw [show h ∩ e ∩ (h ∩ f) = e ∩ f ∩ h by ext; simp only [mem_inter]; tauto] at this
    omega
  have h_inter_e_f : (e ∩ f).card ≥ 1 := by
    have : e ∩ f ∩ h ⊆ e ∩ f := Finset.inter_subset_left
    exact Nat.le_trans h_inter_e_f_in_h (Finset.card_mono this)
  omega

/-
MAIN THEOREM: Triangle Bridge Lemma

If triangle h shares edges with two edge-disjoint triangles e and f,
then:
1. h is contained in e ∪ f
2. e and f share exactly one vertex v
3. v is contained in h

This is the key structural lemma for handling X(e,f) in the Tuza decomposition.
-/
theorem triangle_bridge (e f h : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (hh : h.card = 3)
    (h_edge_disjoint : EdgeDisjoint e f)
    (h_share_e : SharesEdge h e)
    (h_share_f : SharesEdge h f) :
    h ⊆ e ∪ f ∧ (e ∩ f).card = 1 ∧ e ∩ f ⊆ h := by
  have h_inter_one : (e ∩ f).card = 1 := bridge_intersection_eq_one e f h he hf hh h_edge_disjoint h_share_e h_share_f
  constructor
  · unfold SharesEdge at h_share_e h_share_f
    have h_inter_ge_4 : (h ∩ (e ∪ f)).card ≥ 3 := by
      have h1 : (h ∩ e).card ≥ 2 := h_share_e
      have h2 : (h ∩ f).card ≥ 2 := h_share_f
      have h3 : (h ∩ e ∩ (h ∩ f)).card ≤ 1 := by
        have : h ∩ e ∩ (h ∩ f) = h ∩ (e ∩ f) := by ext; simp; tauto
        rw [this]
        have : h ∩ (e ∩ f) ⊆ e ∩ f := Finset.inter_subset_right
        calc (h ∩ (e ∩ f)).card ≤ (e ∩ f).card := Finset.card_mono this
          _ = 1 := h_inter_one
      have := Finset.card_union_add_card_inter (h ∩ e) (h ∩ f)
      have h4 : h ∩ e ∪ h ∩ f = h ∩ (e ∪ f) := by ext; simp; tauto
      rw [h4] at this
      rw [show h ∩ e ∩ (h ∩ f) = h ∩ (e ∩ f) by ext; simp; tauto] at this
      have h5 : (h ∩ (e ∩ f)).card ≤ 1 := by
        have : h ∩ (e ∩ f) ⊆ e ∩ f := Finset.inter_subset_right
        calc (h ∩ (e ∩ f)).card ≤ (e ∩ f).card := Finset.card_mono this
          _ = 1 := h_inter_one
      omega
    have h_subset : h ∩ (e ∪ f) ⊆ h := Finset.inter_subset_left
    have h_eq : h ∩ (e ∪ f) = h := by
      apply Finset.eq_of_subset_of_card_le h_subset
      omega
    rw [← h_eq]
    exact Finset.inter_subset_right
  constructor
  · exact h_inter_one
  · have h_contained : h ⊆ e ∪ f := by
      unfold SharesEdge at h_share_e h_share_f
      have h_inter_ge_4 : (h ∩ (e ∪ f)).card ≥ 3 := by
        have h1 : (h ∩ e).card ≥ 2 := h_share_e
        have h2 : (h ∩ f).card ≥ 2 := h_share_f
        have h3 : (h ∩ e ∩ (h ∩ f)).card ≤ 1 := by
          have : h ∩ e ∩ (h ∩ f) = h ∩ (e ∩ f) := by ext; simp; tauto
          rw [this]
          have : h ∩ (e ∩ f) ⊆ e ∩ f := Finset.inter_subset_right
          calc (h ∩ (e ∩ f)).card ≤ (e ∩ f).card := Finset.card_mono this
            _ = 1 := h_inter_one
        have := Finset.card_union_add_card_inter (h ∩ e) (h ∩ f)
        have h4 : h ∩ e ∪ h ∩ f = h ∩ (e ∪ f) := by ext; simp; tauto
        rw [h4] at this
        rw [show h ∩ e ∩ (h ∩ f) = h ∩ (e ∩ f) by ext; simp; tauto] at this
        have h5 : (h ∩ (e ∩ f)).card ≤ 1 := by
          have : h ∩ (e ∩ f) ⊆ e ∩ f := Finset.inter_subset_right
          calc (h ∩ (e ∩ f)).card ≤ (e ∩ f).card := Finset.card_mono this
            _ = 1 := h_inter_one
        omega
      have h_subset : h ∩ (e ∪ f) ⊆ h := Finset.inter_subset_left
      have h_eq : h ∩ (e ∪ f) = h := by
        apply Finset.eq_of_subset_of_card_le h_subset
        omega
      rw [← h_eq]
      exact Finset.inter_subset_right
    have h_union_5 : (e ∪ f).card = 5 := triangle_union_share_vertex e f he hf h_inter_one
    have h_inter_h_e : (h ∩ e).card ≥ 2 := h_share_e
    have h_inter_h_f : (h ∩ f).card ≥ 2 := h_share_f
    intro v hv
    rw [Finset.card_eq_one] at h_inter_one
    obtain ⟨w, hw⟩ := h_inter_one
    rw [hw] at hv
    exact Finset.mem_singleton.mp hv ▸ (by
      have h_e_inter_f_in_h : (e ∩ f ∩ h).card ≥ 1 := by
        have h_union_inters : (h ∩ e ∪ h ∩ f).card ≤ h.card := Finset.card_le_card (by
          intro x hx
          simp only [mem_union, mem_inter] at hx
          exact hx.elim And.left And.left)
        have := Finset.card_union_add_card_inter (h ∩ e) (h ∩ f)
        rw [show h ∩ e ∩ (h ∩ f) = e ∩ f ∩ h by ext; simp only [mem_inter]; tauto] at this
        omega
      rw [hw] at h_e_inter_f_in_h
      have hwh : w ∈ h := by
        have h_nonempty : ({w} ∩ h).Nonempty := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h_e_inter_f_in_h)
        obtain ⟨x, hx⟩ := h_nonempty
        simp only [mem_inter, mem_singleton] at hx
        rw [← hx.1]; exact hx.2
      exact hwh
    )

/-
COROLLARY: All triangles sharing edges with both e and f contain the bridge vertex v.
This immediately gives τ(X(e,f)) ≤ 2 since all such triangles can be covered by edges at v.
-/
theorem bridge_triangles_contain_v (e f : Finset V) (v : V)
    (he : e.card = 3) (hf : f.card = 3)
    (h_edge_disjoint : EdgeDisjoint e f)
    (h_inter : e ∩ f = {v})
    (X : Finset (Finset V))
    (hX : ∀ h ∈ X, h.card = 3 ∧ SharesEdge h e ∧ SharesEdge h f) :
    ∀ h ∈ X, v ∈ h := by
  intro h hh
  obtain ⟨hh_card, hh_e, hh_f⟩ := hX h hh
  have ⟨_, _, h_v_in⟩ := triangle_bridge e f h he hf hh_card h_edge_disjoint hh_e hh_f
  rw [h_inter] at h_v_in
  exact h_v_in (Finset.mem_singleton_self v)

end
