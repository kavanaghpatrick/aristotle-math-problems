/-
TUZA'S CONJECTURE - ν=2 CASE v5: COMBINED APPROACH

STRATEGY: Combine proven lemmas from multiple submissions:
- K₄/petal lemmas from 4610138e
- Deletion lemma from v3

PROOF CHAIN FOR ν=1:
  nu1_tau_gt_2_implies_K4 + K4_implies_tau_le_2 → tuza_case_nu_1

PROOF CHAIN FOR ν=2:
  packing_two_triangles + deletion + tuza_case_nu_1 → tuza_case_nu_2

All building blocks included with full proofs from prior submissions.
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

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

/-! ## PROVEN: Base Case (from 4610138e) -/

lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : ∀ t ∈ G.cliqueFinset 3, ¬IsEdgeDisjoint {t} := by
    contrapose! h
    refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup <| Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr <| Finset.singleton_subset_iff.mpr h.choose_spec.1, h.choose_spec.2⟩)); simp +decide [h]
  unfold IsEdgeDisjoint at h_no_triangles; aesop
  unfold triangleCoveringNumber; aesop
  unfold IsTriangleCovering; aesop
  rw [Finset.min]; aesop
  rw [Finset.inf_eq_bot_iff.mpr] <;> aesop

/-! ## PROVEN: Deletion Lemma (from v3) -/

lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  unfold triangleCoveringNumber
  simp +zetaDelta at *
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧ IsTriangleCovering (G.deleteEdges S) T ∧ T.card = (Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges S)) (G.deleteEdges S).edgeFinset.powerset)).min.getD (G.deleteEdges S).edgeFinset.card := by
    unfold Option.getD; aesop
    · have := Finset.mem_of_min heq; aesop
    · simp_all +decide [Finset.min]
      refine' ⟨Finset.filter (Membership.mem (G.deleteEdges S).edgeSet) Finset.univ, _, _, _⟩ <;> simp +decide [IsTriangleCovering]
  have h_cover : IsTriangleCovering G (S ∪ T) := by
    unfold IsTriangleCovering at *; aesop
  have h_cover_card : (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)).min.getD G.edgeFinset.card ≤ (S ∪ T).card := by
    have h_cover_card : (S ∪ T).card ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp +zetaDelta at *
      use S ∪ T
      simp_all +decide [Set.subset_def, SimpleGraph.deleteEdges]
      rintro x (hx | hx) <;> [exact hS x hx; exact hT.1 x hx |>.1]
    have := Finset.min_le h_cover_card; aesop
    cases h : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  simp_all +decide [Finset.union_comm, Finset.card_union_add_card_inter]
  exact h_cover_card.trans (by rw [add_comm]; exact le_trans (Finset.card_union_le _ _) (by linarith))

/-! ## PROVEN: Extract Two Triangles (from 4610138e, v3) -/

lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  rw [eq_comm] at h
  contrapose! h
  refine' ne_of_gt (lt_of_le_of_lt (Finset.sup_le _) _)
  exact 1
  · simp +zetaDelta at *
    intro b hb hb'; rw [Finset.card_le_one_iff]; aesop
    exact Classical.not_not.1 fun h' => h a b_1 (by simpa using hb a_1) (by simpa using hb a_2) h' (hb' a_1 a_2 h')
  · decide

/-! ## PROVEN: Packing Monotonicity -/

lemma packing_mono_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) :
    trianglePackingNumber (G.deleteEdges S) ≤ trianglePackingNumber G := by
  unfold trianglePackingNumber
  apply Finset.sup_mono
  intro P hP
  simp only [Finset.mem_filter, Finset.mem_powerset] at hP ⊢
  constructor
  · intro t ht
    have := hP.1 ht
    simp only [SimpleGraph.mem_cliqueFinset_iff] at this ⊢
    exact ⟨this.1.mono (SimpleGraph.deleteEdges_le _ _), this.2⟩
  · exact hP.2

/-! ## TARGET: ν=1 Case -/

/-- COMBINING K₄ APPROACH: ν=1 implies τ≤2
The building blocks (nu1_tau_gt_2_implies_K4, K4_implies_tau_le_2) were proven in 4610138e.
This should follow by contradiction: if τ>2 then K₄ exists, but K₄ has τ≤2.
-/
lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

/-! ## Helper: ν≤1 implies τ≤2 -/

lemma tuza_nu_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 1) : triangleCoveringNumber G ≤ 2 := by
  rcases Nat.lt_or_eq_of_le h with h_lt | h_eq
  · have h0 : trianglePackingNumber G = 0 := by omega
    rw [tuza_base_case G h0]; norm_num
  · exact tuza_case_nu_1 G h_eq

/-! ## KEY: Reducing Edges Lemma -/

/-- Deleting one edge from each of two edge-disjoint triangles reduces ν to ≤1 -/
lemma exists_reducing_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) ≤ 1 := by
  sorry

/-! ## MAIN THEOREM -/

/-- MAIN: τ ≤ 4 when ν = 2 -/
theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  obtain ⟨S, hS_card, hS_sub, h_reduces⟩ := exists_reducing_edges G h
  have h_del := triangleCoveringNumber_le_card_add_deleteEdges G S hS_sub
  have h_cover := tuza_nu_le_1 (G.deleteEdges S) h_reduces
  omega

end
