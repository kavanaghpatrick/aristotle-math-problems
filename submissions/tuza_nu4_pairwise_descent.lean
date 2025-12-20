/-
Tuza ν=4: Pairwise Descent Strategy

KEY INSIGHT (from Gemini analysis):
Instead of removing ONE triangle (which fails when τ(T_e) = 3 for all e),
remove a PAIR {e, f} that share a vertex v.

This drops ν by 2, allowing cost of 4 edges.
Need: τ(T_e ∪ T_f) ≤ 4

PROVEN BUILDING BLOCKS:
- tau_X_le_2': τ(T_e ∩ T_f) ≤ 2 when e ∩ f = {v}
- tau_S_le_2: τ(S_e) ≤ 2
- mem_X_implies_v_in_t: triangles in T_e ∩ T_f contain v

DECOMPOSITION:
T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) ∪ (other overlaps)

The key is that covers can share edges at v.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def X (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- PROVEN: τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S G e M) ≤ 2 := by
  sorry -- Proven in e7f11dfc

-- PROVEN: triangles in X(e,f) contain shared vertex
lemma mem_X_implies_v_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v}) :
    ∀ t ∈ X G e f, v ∈ t := by
  sorry -- Proven in e7f11dfc

-- PROVEN: τ(X(e,f)) ≤ 2
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : G.IsNClique 3 e) (hf : G.IsNClique 3 f) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
  sorry -- Proven in e7f11dfc

-- KEY NEW LEMMA: Pairwise union bound
-- When e and f share vertex v, we can cover T_e ∪ T_f with ≤ 4 edges
lemma tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

-- Removing a pair drops packing number by at least 2
lemma packing_minus_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (T_ef : Finset (Finset V)) (hT : T_ef = trianglesSharingEdge G e ∪ trianglesSharingEdge G f) :
    trianglePackingNumber G - 2 ≥ 0 →
    ∃ M' : Finset (Finset V), isTrianglePacking G M' ∧
      M' ⊆ (G.cliqueFinset 3) \ T_ef ∧ M'.card ≥ M.card - 2 := by
  sorry

-- Case: exists isolated triangle (doesn't share vertex with others)
lemma nu4_case_isolated (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card = 4)
    (h_isolated : ∃ e ∈ M, ∀ f ∈ M, f ≠ e → (e ∩ f).card = 0) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

-- Case: every triangle shares vertex with another (K_6-like)
-- Use pairwise descent
lemma nu4_case_pairwise (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card = 4)
    (h_all_share : ∀ e ∈ M, ∃ f ∈ M, f ≠ e ∧ (e ∩ f).card ≥ 1) :
    triangleCoveringNumber G ≤ 8 := by
  -- Pick any pair {e, f} that share a vertex
  -- τ(T_e ∪ T_f) ≤ 4 by tau_union_le_4
  -- Residual has ν ≤ 2, so τ(residual) ≤ 4 by induction
  -- Total: 4 + 4 = 8
  sorry

-- Main theorem: τ ≤ 8 when ν = 4
theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  obtain ⟨M, hM⟩ : ∃ M, isMaxPacking G M ∧ M.card = 4 := by sorry
  by_cases h_isolated : ∃ e ∈ M, ∀ f ∈ M, f ≠ e → (e ∩ f).card = 0
  · exact nu4_case_isolated G M hM.1 hM.2 h_isolated
  · push_neg at h_isolated
    -- h_isolated : ∀ e ∈ M, ∃ f ∈ M, f ≠ e ∧ (e ∩ f).card ≠ 0
    have h_all_share : ∀ e ∈ M, ∃ f ∈ M, f ≠ e ∧ (e ∩ f).card ≥ 1 := by
      intro e he
      obtain ⟨f, hf, hne, hcard⟩ := h_isolated e he
      exact ⟨f, hf, hne, Nat.one_le_iff_ne_zero.mpr hcard⟩
    exact nu4_case_pairwise G M hM.1 hM.2 h_all_share

end
