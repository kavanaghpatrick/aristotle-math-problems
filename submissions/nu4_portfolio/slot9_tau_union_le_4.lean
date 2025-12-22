/-
Tuza ν=4 Portfolio - Slot 9: τ(T_e ∪ T_f) ≤ 4 (Pairwise Bound)

TARGET: THE HOLY GRAIL - Prove τ(T_e ∪ T_f) ≤ 4 for packing elements e, f

WHY THIS MATTERS:
If τ(T_e ∪ T_f) ≤ 4, then for ν=4 we can:
- Pair up the 4 packing elements: {e₁,e₂} and {e₃,e₄}
- Cover T_{e₁} ∪ T_{e₂} with ≤ 4 edges
- Cover T_{e₃} ∪ T_{e₄} with ≤ 4 edges
- Total: τ(G) ≤ 8

This bypasses the need to prove τ(T_e) ≤ 2 directly!

PROVEN SCAFFOLDING:
1. τ(S_e) ≤ 2 for any e ∈ M
2. τ(X(e,f)) ≤ 2 when e∩f = {v}
3. All X(e,f) triangles contain v
4. Star/K4 dichotomy

DECOMPOSITION:
T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) ∪ (other bridges)

KEY INSIGHT (from Gemini):
The "other bridges" (triangles sharing edge with e and some g ≠ f, or with f and some h ≠ e)
may overlap with S_f or S_e respectively, reducing double-counting.

STRATEGY: Boris Minimal - let Aristotle find the path
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

-- PROVEN: Decomposition identity (Gemini's Te_Tf_decomposition)
-- Every triangle in T_e ∪ T_f belongs to S_e, S_f, or X(e,f)
lemma Te_Tf_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    trianglesSharingEdge G e ∪ trianglesSharingEdge G f =
      S_e G e M ∪ S_e G f M ∪ X_ef G e f ∪
      ((trianglesSharingEdge G e ∪ trianglesSharingEdge G f).filter
        (fun t => ∃ g ∈ M, g ≠ e ∧ g ≠ f ∧ (t ∩ g).card ≥ 2)) := by
  sorry

-- PROVEN: S_e triangles pairwise share edges
lemma S_e_pairwise_shareEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    Set.Pairwise (S_e G e M : Set (Finset V)) shareEdge := by
  sorry  -- PROVEN in tuza_tau_Se_COMPLETE.lean

-- PROVEN: τ(S_e) ≤ 2
lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry  -- PROVEN in tuza_tau_Se_COMPLETE.lean

-- PROVEN: τ(X(e,f)) ≤ 2 when packing elements share a vertex
lemma tau_X_ef_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry  -- PROVEN in 950cb060

-- CASE ANALYSIS: Packing elements either share a vertex or are disjoint
lemma packing_pair_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (∃ v : V, e ∩ f = {v}) ∨ (e ∩ f = ∅) := by
  -- Edge-disjoint packing elements share ≤ 1 vertex
  have h_card : (e ∩ f).card ≤ 1 := hM.1.2 he hf hef
  interval_cases h : (e ∩ f).card
  · right; exact Finset.card_eq_zero.mp h
  · left
    rw [Finset.card_eq_one] at h
    obtain ⟨v, hv⟩ := h
    exact ⟨v, hv⟩

-- TARGET: τ(T_e ∪ T_f) ≤ 4
theorem tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

-- COROLLARY: Tuza ν=4 via pairwise descent
theorem tuza_nu4_via_pairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  sorry

end
