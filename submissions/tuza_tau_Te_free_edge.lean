/-
Tuza ν ≤ 3: Free Edge Approach (Gemini strategy)

Key insight: If ANY edge of e has no attached triangles (besides e itself),
then τ(T_e) ≤ 2. So we only need to show that with ν ≤ 3, we can't
occupy all 3 edges of e.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3

def shareEdge (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  Set.Pairwise (T : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0

def occupiedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (e.powersetCard 2).filter (fun edge => ∃ t ∈ T_e G e, t ≠ e ∧ edge ⊆ t)

lemma triangle_has_three_edges (e : Finset V) (he : e.card = 3) :
    (e.powersetCard 2).card = 3 := by
  simp [Finset.card_powersetCard, he]

lemma two_edges_cover_if_edge_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (h_free : (occupiedEdges G e).card < 3) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

lemma occupied_edges_bounded_by_Se_and_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (occupiedEdges G e).card ≤ (S_e G M e).card + (M.filter (· ≠ e)).card := by
  sorry

lemma Se_pairwise_share_implies_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_pair : ∀ t1 ∈ S_e G M e, ∀ t2 ∈ S_e G M e, t1 ≠ t2 → shareEdge t1 t2) :
    (S_e G M e).card ≤ 4 := by
  sorry

lemma cant_occupy_all_edges_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    (occupiedEdges G e).card < 3 ∨ coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  rcases cant_occupy_all_edges_nu_le_3 G M hM hnu e he with h_free | h_done
  · exact two_edges_cover_if_edge_free G e (hM.1.1 he) h_free
  · exact h_done

end
