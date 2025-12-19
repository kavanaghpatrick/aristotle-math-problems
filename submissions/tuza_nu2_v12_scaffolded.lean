import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

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

def IsK4 (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Prop :=
  s ∈ G.cliqueFinset 4

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_max
  simp [Finset.mem_filter, Finset.mem_powerset] at hP₁
  exact ⟨P, hP₁.1, hP₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (P : Finset (Finset V)) (hP_sub : P ⊆ G.cliqueFinset 3)
    (hP_disj : IsEdgeDisjoint P) (hP_card : P.card = 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ T' ∈ P, ¬ Disjoint (triangleEdges T) (triangleEdges T') := by
  by_contra h_all_disjoint
  push_neg at h_all_disjoint
  have h_new_packing : IsEdgeDisjoint (insert T P) := by
    intro x hx y hy hxy
    cases Finset.mem_insert.mp hx with
    | inl hxT =>
      cases Finset.mem_insert.mp hy with
      | inl hyT => simp_all
      | inr hyP => subst hxT; exact h_all_disjoint y hyP
    | inr hxP =>
      cases Finset.mem_insert.mp hy with
      | inl hyT => subst hyT; exact (h_all_disjoint x hxP).symm
      | inr hyP => exact hP_disj hxP hyP hxy
  have h_card_3 : (insert T P).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · omega
    · intro hTP
      have := h_all_disjoint T hTP
      simp_all +decide [Finset.disjoint_left]
      unfold triangleEdges at this
      have hT_card := hT.card_eq
      rcases Finset.card_eq_three.mp hT_card with ⟨a, b, c, hab, hac, hbc, rfl⟩
      specialize this (Sym2.mk (a, b)) a b
      simp_all +decide
  have h_contra : trianglePackingNumber G ≥ 3 := by
    refine le_trans (by omega : 3 ≤ (insert T P).card) ?_
    refine Finset.le_sup (f := Finset.card) ?_
    refine Finset.mem_filter.mpr ⟨?_, h_new_packing⟩
    refine Finset.mem_powerset.mpr ?_
    intro x hx
    cases Finset.mem_insert.mp hx with
    | inl h => subst h; exact hT
    | inr h => exact hP_sub h
  omega

lemma k4_avoidance_helper (s : Finset V) (hs : s.card = 4)
    (e : Sym2 V) (he : e ∈ triangleEdges s) :
    ∃ U, U ⊆ s ∧ U.card = 3 ∧ e ∉ triangleEdges U := by
  unfold triangleEdges at *; simp_all +decide [Finset.card_sdiff]
  rcases he with ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩; use s \ {a}; aesop
  rw [Finset.card_sdiff]; aesop

lemma extensions_form_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ s : Finset V, T ⊆ s ∧ IsK4 G s := by
  sorry

lemma two_K4_cover_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s1 s2 : Finset V) (hs1 : IsK4 G s1) (hs2 : IsK4 G s2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 4 ∧
    (∀ T, (T ⊆ s1 ∨ T ⊆ s2) → T ∈ G.cliqueFinset 3 → ¬Disjoint (triangleEdges T) S) := by
  sorry

theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

end
