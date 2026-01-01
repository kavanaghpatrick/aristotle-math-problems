/-
Tuza ν=4 Strategy - Slot 148a: Scattered Partition Theorem

TARGET: In scattered case, every triangle has a UNIQUE owner M-element.

PROVEN SCAFFOLDING (from slot67):
- no_bridge_disjoint: No triangle bridges two disjoint M-elements
- scattered_unique_parent: External triangles have unique parent

THIS FILE proves: triangles partition by owner (M-elements own themselves,
externals owned by unique parent, and NO triangle is ownerless by maximality).

ONE SORRY: scattered_triangles_partition
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING (PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ e, e ∈ t.sym2 ∧ e ∈ S.sym2

def trianglesOwnedBy (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t = A ∨ (t ∉ M ∧ sharesEdgeWith t A))

-- PROVEN by Aristotle (slot67, UUID: c522a35a)
lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  have ha1_A : a₁ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h_a2_ne_b2, h_a2_ne_b1]
    · simp [h_a1_ne_b2, h_a1_ne_b1]
    · simp [ha12]
  have h_sub : ({a₁, a₂, b₁, b₂} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- PROVEN by Aristotle (slot67)
theorem scattered_unique_parent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M)
    (A : Finset V) (hA : A ∈ M) (h_share_A : sharesEdgeWith t A) :
    ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B := by
  intro B hB hBA h_share_B
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hB)).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint A B t hA_card hB_card ht_card (h_scattered A B hA hB hBA.symm) h_share_A h_share_B

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Maximality implies edge-sharing
-- ══════════════════════════════════════════════════════════════════════════════

/-- If two 3-sets share 2+ vertices, they share an edge (PROVEN) -/
lemma two_vertices_implies_edge (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_inter : (t ∩ m).card ≥ 2) :
    sharesEdgeWith t m := by
  have h_two : (t ∩ m).Nonempty := by omega
  obtain ⟨v, hv⟩ := h_two
  have hv_t := (Finset.mem_inter.mp hv).1
  have hv_m := (Finset.mem_inter.mp hv).2
  have h_two' : ((t ∩ m).erase v).Nonempty := by
    rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨w, hw⟩ := h_two'
  have hw' := Finset.mem_erase.mp hw
  have hw_t := (Finset.mem_inter.mp hw'.2).1
  have hw_m := (Finset.mem_inter.mp hw'.2).2
  have hvw : v ≠ w := hw'.1.symm
  use s(v, w)
  constructor
  · rw [Finset.mem_sym2_iff]; exact ⟨v, w, hvw, hv_t, hw_t, rfl⟩
  · rw [Finset.mem_sym2_iff]; exact ⟨v, w, hvw, hv_m, hw_m, rfl⟩

/-- Every external triangle shares edge with some M-element (by maximality) -/
lemma external_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M) :
    ∃ m ∈ M, sharesEdgeWith t m := by
  obtain ⟨m, hm, h_inter⟩ := hM.2 t ht ht_not_M
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have hm_card : m.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hm)).card_eq
  exact ⟨m, hm, two_vertices_implies_edge t m ht_card hm_card h_inter⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET THEOREM: Partition by owner
-- ══════════════════════════════════════════════════════════════════════════════

/-- In scattered case, every triangle has exactly one owner in M.
    This means triangles partition by trianglesOwnedBy. -/
theorem scattered_triangles_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) :
    ∀ t ∈ G.cliqueFinset 3, ∃! A, A ∈ M ∧ t ∈ trianglesOwnedBy G M A := by
  intro t ht
  by_cases ht_M : t ∈ M
  · -- t is itself an M-element, owned by itself
    use t
    constructor
    · constructor
      · exact ht_M
      · simp only [trianglesOwnedBy, Finset.mem_filter]
        exact ⟨ht, Or.inl rfl⟩
    · -- Uniqueness: only t owns t
      intro A ⟨hA, hA_owns⟩
      simp only [trianglesOwnedBy, Finset.mem_filter] at hA_owns
      rcases hA_owns.2 with rfl | ⟨ht_not_M', _⟩
      · rfl
      · exact absurd ht_M ht_not_M'
  · -- t is external; by maximality, has unique parent
    obtain ⟨m, hm, h_share⟩ := external_shares_edge_with_M G M hM t ht ht_M
    use m
    constructor
    · constructor
      · exact hm
      · simp only [trianglesOwnedBy, Finset.mem_filter]
        exact ⟨ht, Or.inr ⟨ht_M, h_share⟩⟩
    · -- Uniqueness: by scattered_unique_parent
      intro A ⟨hA, hA_owns⟩
      simp only [trianglesOwnedBy, Finset.mem_filter] at hA_owns
      rcases hA_owns.2 with rfl | ⟨_, h_share_A⟩
      · exact absurd hA ht_M
      · by_contra hAm
        exact scattered_unique_parent G M hM.1 h_scattered t ht ht_M m hm h_share A hA hAm h_share_A

end
