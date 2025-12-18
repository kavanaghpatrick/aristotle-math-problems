/-
TUZA'S CONJECTURE: τ(G) ≤ 2ν(G)

For any graph G:
- τ(G) = minimum edges to delete to make G triangle-free
- ν(G) = maximum number of edge-disjoint triangles

WHAT TO PROVE: `exists_two_edge_reduction` (line ~240)
Given ν(G) > 0, find ≤2 edges whose removal strictly decreases ν.

Once this is proven, the main theorem follows by strong induction.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions -/

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

/-! ## Proven Lemmas -/

lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h
    refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr
        (Classical.choose_spec (Finset.card_pos.mp (Nat.pos_of_ne_zero h)))), _⟩))) <;> norm_num
    intro x hx y hy; aesop
  unfold triangleCoveringNumber IsTriangleCovering; aesop
  rw [show (Finset.image Finset.card (Finset.filter (fun S => (G.deleteEdges S).CliqueFree 3)
    G.edgeFinset.powerset)).min = some 0 from ?_]
  · rfl
  · refine' le_antisymm _ _
    · refine' Finset.min_le _; aesop
    · simp +decide [Finset.min]
      exact fun _ _ _ => WithTop.coe_le_coe.mpr (Nat.zero_le _)

lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧
    IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop
    have := Finset.min_of_nonempty (show Finset.Nonempty (Finset.image Finset.card
      (Finset.filter (IsTriangleCovering (G.deleteEdges S))
        (G.deleteEdges S).edgeFinset.powerset)) from ?_); aesop
    · have := Finset.mem_of_min h; aesop
    · simp +zetaDelta at *; use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering]
  have h_union : IsTriangleCovering G (S ∪ T) := by unfold IsTriangleCovering at *; aesop
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber
    have h_card : (S ∪ T).card ∈ Finset.image Finset.card
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [Finset.subset_iff, SimpleGraph.deleteEdges]
      exact ⟨S ∪ T, ⟨fun x hx => by aesop, h_union⟩, rfl⟩
    have := Finset.min_le h_card; aesop
    cases h : Finset.min (Finset.image Finset.card
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  exact h_union_card.trans (Finset.card_union_le _ _) |> le_trans <| by rw [hT.2.2]

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_finite : (G.cliqueFinset 3).powerset.Nonempty :=
    ⟨∅, Finset.mem_powerset.mpr <| Finset.empty_subset _⟩
  have h_exists : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧
      ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card :=
    Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      by simp +decide [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_exists; use P; aesop
  exact le_antisymm (Finset.le_sup (f := Finset.card) (by aesop)) (Finset.sup_le fun Q hQ => by aesop)

lemma triangle_shares_edge_with_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (hP_card : P.card = trianglePackingNumber G)
    (hP_sub : P ⊆ G.cliqueFinset 3) (hP_disj : IsEdgeDisjoint P)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ p ∈ P, ¬ Disjoint (triangleEdges t) (triangleEdges p) := by
  by_contra h_all_disj
  push_neg at h_all_disj
  have h_disj' : IsEdgeDisjoint (insert t P) := by
    unfold IsEdgeDisjoint Set.PairwiseDisjoint
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact h_all_disj y hy
    · exact (h_all_disj x hx).symm
    · exact hP_disj hx hy hxy
  have h_sub' : insert t P ⊆ G.cliqueFinset 3 := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ht
    · exact hP_sub hx
  have ht_notin : t ∉ P := by
    intro ht_in
    have := h_all_disj t ht_in
    simp only [Finset.disjoint_self_iff_empty] at this
    unfold triangleEdges at this
    have ht_card : t.card = 3 := ht.2
    have h_nonempty : t.offDiag.Nonempty := by
      rw [Finset.offDiag_nonempty]
      obtain ⟨a, b, c, hab, hac, hbc, ht_eq⟩ := Finset.card_eq_three.mp ht_card
      exact ⟨a, b, by simp [ht_eq], by simp [ht_eq], hab⟩
    simp only [Finset.image_eq_empty] at this
    exact h_nonempty.ne_empty this
  have h_card_bigger : (insert t P).card > trianglePackingNumber G := by
    rw [Finset.card_insert_of_not_mem ht_notin, ← hP_card]
    omega
  have h_card_le : (insert t P).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_sub', h_disj'⟩
  omega

lemma triangle_has_three_edges (t : Finset V) (ht : t.card = 3) :
    (triangleEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, ht_eq⟩ := Finset.card_eq_three.mp ht
  simp only [ht_eq, triangleEdges]
  rw [show (Finset.offDiag {a, b, c} : Finset (V × V)) = {(a, b), (a, c), (b, a), (b, c), (c, a), (c, b)} by ext x; aesop]
  simp +decide [hab, hac, hbc, Sym2.eq]

lemma triangle_destroyed_by_two_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ triangleEdges t) (he2 : e2 ∈ triangleEdges t) (hne : e1 ≠ e2) :
    t ∉ (G.deleteEdges {e1, e2}).cliqueFinset 3 := by
  unfold triangleEdges at *; aesop
  simp_all +decide [SimpleGraph.isNClique_iff, SimpleGraph.deleteEdges]
  have := Finset.card_eq_three.mp ht.2
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := this
  simp_all +decide [SimpleGraph.isClique_iff, SimpleGraph.deleteEdges]
  grind

/-! ## THE GAP: Prove this lemma -/

/--
Key reduction: Removing 2 edges from a max packing triangle strictly decreases ν.

Strategy: Pick p ∈ max packing P, remove 2 of its 3 edges.
- p is destroyed (triangle_destroyed_by_two_edges)
- Any max packing Q in G\S has |Q| ≤ ν(G) (monotonicity)
- But Q cannot include p, and triangles sharing p's removed edges are also gone
- So |Q| < |P| = ν(G)
-/
lemma exists_two_edge_reduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G > 0) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  have hP_nonempty : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hP_empty
    simp only [hP_empty, Finset.card_empty] at hP_card
    omega
  obtain ⟨p, hp_mem⟩ := hP_nonempty
  have hp_tri : p ∈ G.cliqueFinset 3 := hP_sub hp_mem
  have hp_clique : G.IsClique p := hp_tri.1
  have hp_card : p.card = 3 := hp_tri.2
  obtain ⟨a, b, c, hab, hac, hbc, hp_eq⟩ := Finset.card_eq_three.mp hp_card
  have hab' : G.Adj a b := by
    rw [hp_eq] at hp_clique
    exact hp_clique (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)) hab
  have hac' : G.Adj a c := by
    rw [hp_eq] at hp_clique
    exact hp_clique (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))) hac
  let e1 : Sym2 V := s(a, b)
  let e2 : Sym2 V := s(a, c)
  use {e1, e2}
  refine ⟨?_, ?_, ?_⟩
  · by_cases h_eq : e1 = e2
    · simp [h_eq]
    · rw [Finset.card_pair h_eq]
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact G.mem_edgeFinset.mpr hab'
    · exact G.mem_edgeFinset.mpr hac'
  · sorry

/-! ## Main Theorem -/

theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  induction h : trianglePackingNumber G using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    by_cases hk : k = 0
    · subst hk
      have := tuza_base_case G h
      simp [this]
    · have hpos : trianglePackingNumber G > 0 := by omega
      obtain ⟨S, hS_card, hS_sub, hS_reduce⟩ := exists_two_edge_reduction G hpos
      have h_del := triangleCoveringNumber_le_card_add_deleteEdges G S hS_sub
      have h_smaller : trianglePackingNumber (G.deleteEdges S) < k := by
        rw [← h]; exact hS_reduce
      have h_ih := ih (trianglePackingNumber (G.deleteEdges S)) h_smaller (G.deleteEdges S) rfl
      calc triangleCoveringNumber G
          ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := h_del
        _ ≤ 2 + 2 * trianglePackingNumber (G.deleteEdges S) := by omega
        _ ≤ 2 + 2 * (k - 1) := by omega
        _ = 2 * k := by omega

end
