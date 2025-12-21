/-
Tuza ν ≤ 3: Direct Formalization of Parker's Proof

PARKER'S KEY INSIGHT (arXiv:2406.06501, Theorem 1.1-1.2):
The covering edges for S_e come from the edges of e itself.
Since all triangles in T_e share an edge with e (by definition),
if ≤2 edges of e cover S_e, those same edges cover ALL of T_e.

This is the missing bridge: τ(S_e) ≤ 2 → τ(T_e) ≤ 2

Proven lemmas included as full proofs (not axioms).
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E}

/-! ## Core helper lemmas (proven) -/

lemma share_edge_iff_inter_ge_2 (t1 t2 : Finset V) :
    ¬Disjoint (triangleEdges t1) (triangleEdges t2) ↔ (t1 ∩ t2).card ≥ 2 := by
  unfold triangleEdges
  simp +decide [Finset.disjoint_left, Finset.mem_image]
  constructor
  · rintro ⟨x, u, hu, v, hv, huv, rfl, w, hw, z, hz, hwz, hx⟩
    exact Finset.one_lt_card.2 ⟨u, by aesop, v, by aesop⟩
  · intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h
    exact ⟨_, x, Finset.mem_of_mem_inter_left hx, y, Finset.mem_of_mem_inter_left hy, hxy, rfl,
           x, Finset.mem_of_mem_inter_right hx, y, Finset.mem_of_mem_inter_right hy, hxy, rfl⟩

/-! ## Key structural lemmas -/

-- All triangles in T_e share an edge with e (by definition)
lemma T_e_shares_edge_with_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (t : Finset V) (ht : t ∈ T_e G e) :
    ¬Disjoint (triangleEdges t) (triangleEdges e) := by
  simp only [T_e, Finset.mem_filter] at ht
  exact ht.2

-- S_e is a subset of T_e
lemma S_e_subset_T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    S_e G M e ⊆ T_e G e := by
  exact Finset.filter_subset _ _

-- S_e triangles pairwise share edges (Lemma 2.2 from Parker)
lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e) (hne : t1 ≠ t2) :
    ¬Disjoint (triangleEdges t1) (triangleEdges t2) := by
  intro h
  have h_contradiction : IsTrianglePacking G (insert t1 (insert t2 (M \ {e}))) := by
    constructor
    · have h_subset : t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧ (M \ {e}) ⊆ G.cliqueFinset 3 := by
        exact ⟨Finset.mem_filter.mp (Finset.mem_filter.mp ht1 |>.1) |>.1,
               Finset.mem_filter.mp (Finset.mem_filter.mp ht2 |>.1) |>.1,
               Finset.sdiff_subset.trans (hM.1.1)⟩
      exact Finset.insert_subset_iff.mpr ⟨h_subset.1, Finset.insert_subset_iff.mpr ⟨h_subset.2.1, h_subset.2.2⟩⟩
    · intro x hx y hy hxy
      simp_all +decide [S_e]
      rcases hx with (rfl | rfl | ⟨hx, hx'⟩) <;> rcases hy with (rfl | rfl | ⟨hy, hy'⟩) <;>
        simp_all +decide [Function.onFun]
      · exact h.symm
      · exact ht1.2 x hx hx' |> Disjoint.symm
      · exact ht2.2 x hx hx' |> Disjoint.symm
      · exact hM.1.2 hx hy hxy
  have h_card : (insert t1 (insert t2 (M \ {e}))).card > M.card := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] <;> simp_all +decide [Finset.subset_iff]
    · grind
    · intro ht2M; have := hM.1; simp_all +decide [IsTrianglePacking]
      have := this.2 ht2M he; simp_all +decide [IsEdgeDisjoint]
      contrapose! this; simp_all +decide [S_e]
      unfold T_e at ht2; aesop
    · intro ht1M
      have h_contradiction : ¬Disjoint (triangleEdges t1) (triangleEdges e) := by
        have h_filter : t1 ∈ (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f)) := ht1
        unfold T_e at h_filter; aesop
      have h_contradiction' : IsEdgeDisjoint M := hM.1.2
      have := h_contradiction' ht1M he; aesop
  have h_contradiction' : (insert t1 (insert t2 (M \ {e}))).card ≤ packingNumber G := by
    exact le_csSup ⟨Finset.card (G.cliqueFinset 3), fun n hn => by obtain ⟨M, rfl, hM⟩ := hn; exact Finset.card_le_card hM.1⟩
                   ⟨_, rfl, h_contradiction⟩
  exact h_card.not_le (h_contradiction'.trans (hM.2.ge))

/-! ## PARKER'S KEY INSIGHT: Covering edges come from e itself -/

-- When S_e triangles pairwise share edges AND all share edge with e,
-- the covering edges can be chosen from triangleEdges(e)
lemma S_e_covered_by_edges_of_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) (he_card : e.card = 3) :
    ∃ E ⊆ triangleEdges e, E.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ¬Disjoint (triangleEdges t) E := by
  sorry

-- Since T_e triangles all share edge with e, edges from e cover all of T_e
lemma T_e_covered_by_edges_of_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) (he_card : e.card = 3)
    (E : Finset (Sym2 V)) (hE_sub : E ⊆ triangleEdges e)
    (hE_covers_Se : ∀ t ∈ S_e G M e, ¬Disjoint (triangleEdges t) E) :
    ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) E := by
  sorry

/-! ## Main results -/

lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

end
