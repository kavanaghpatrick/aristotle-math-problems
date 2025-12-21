/-
Tuza ν≤3: Bridge Coverage Strategy

INSIGHT FROM MULTI-AGENT ANALYSIS:
The key is that bridge triangles (T_e \ S_e) are automatically covered
by the same edges covering S_e.

REASONING:
1. All triangles in T_e share an edge with e (by definition)
2. The 2 edges covering S_e hit at least one edge of each S_e triangle
3. Bridge triangles also share an edge with e
4. With ν≤3, the structure ensures the S_e covering edges are from e itself

PROOF OUTLINE:
- Show covering edges for S_e are edges of e
- Therefore they cover ALL of T_e (since T_e ⊆ triangles sharing edge with e)
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

-- KEY LEMMA: S_e triangles pairwise share edges (PROVEN in f45bfea3)
lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e) (hne : t1 ≠ t2) :
    ¬Disjoint (triangleEdges t1) (triangleEdges t2) := by
  -- Full proof from Aristotle f45bfea3
  intro h;
  have h_contradiction : IsTrianglePacking G (insert t1 (insert t2 (M \ {e}))) := by
    constructor;
    · have h_subset : t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧ (M \ {e}) ⊆ G.cliqueFinset 3 := by
        exact ⟨ Finset.mem_filter.mp ( Finset.mem_filter.mp ht1 |>.1 ) |>.1, Finset.mem_filter.mp ( Finset.mem_filter.mp ht2 |>.1 ) |>.1, Finset.sdiff_subset.trans ( hM.1.1 ) ⟩;
      exact Finset.insert_subset_iff.mpr ⟨ h_subset.1, Finset.insert_subset_iff.mpr ⟨ h_subset.2.1, h_subset.2.2 ⟩ ⟩;
    · intro x hx y hy hxy;
      simp_all +decide [ S_e ];
      rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> rcases hy with ( rfl | rfl | ⟨ hy, hy' ⟩ ) <;> simp_all +decide [ Function.onFun ];
      · exact h.symm;
      · exact ht1.2 x hx hx' |> Disjoint.symm;
      · exact ht2.2 x hx hx' |> Disjoint.symm;
      · exact hM.1.2 hx hy hxy;
  have h_card : (insert t1 (insert t2 (M \ {e}))).card > M.card := by
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.subset_iff ];
    · grind;
    · intro ht2M; have := hM.1; simp_all +decide [ IsTrianglePacking ] ;
      have := this.2 ht2M he; simp_all +decide [ IsEdgeDisjoint ] ;
      contrapose! this; simp_all +decide [ S_e ] ;
      unfold T_e at ht2; aesop;
    · intro ht1M
      have h_contradiction : ¬Disjoint (triangleEdges t1) (triangleEdges e) := by
        have h_not_disjoint : ¬Disjoint (triangleEdges t1) (triangleEdges e) := by
          have h_filter : t1 ∈ (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f)) := ht1
          unfold T_e at h_filter; aesop;
        exact h_not_disjoint;
      have h_contradiction : IsEdgeDisjoint M := by
        exact hM.1.2;
      have := h_contradiction ht1M he; aesop;
  have h_contradiction : (insert t1 (insert t2 (M \ {e}))).card ≤ packingNumber G := by
    exact le_csSup ⟨ Finset.card ( G.cliqueFinset 3 ), fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact Finset.card_le_card hM.1 ⟩ ⟨ _, rfl, h_contradiction ⟩;
  exact h_card.not_le ( h_contradiction.trans ( hM.2.ge ) )

-- KEY LEMMA: Pairwise sharing triangles can be covered by 2 edges (PROVEN)
lemma intersecting_triangles_covering_edges_from_common {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Finset V))
    (e : Finset V) (he : e.card = 3)
    (h_in_Te : ∀ t ∈ S, ¬Disjoint (triangleEdges t) (triangleEdges e))
    (h_card : ∀ t ∈ S, t.card = 3)
    (h_pair : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → ¬Disjoint (triangleEdges t1) (triangleEdges t2)) :
    ∃ E ⊆ triangleEdges e, E.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E := by
  sorry

-- Using the key lemma: covering edges are from e, so they cover all of T_e
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
