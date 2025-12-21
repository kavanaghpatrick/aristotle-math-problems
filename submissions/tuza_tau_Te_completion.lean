/-
Tuza ν ≤ 3: Completion submission targeting tau_Te_le_2_of_nu_le_3

CONTEXT: From 4736da84, we have PROVEN:
- S_e_pairwise_share_edges: triangles in S_e pairwise share edges
- tau_S_le_2: τ(S_e) ≤ 2 for any e ∈ M
- Te_eq_Se_when_nu_1: T_e = S_e when ν = 1
- tuza_nu_le_3 (conditional on tau_Te_le_2_of_nu_le_3)

TARGET: Prove tau_Te_le_2_of_nu_le_3

KEY INSIGHT: For e ∈ M with ν ≤ 3:
- T_e = S_e ∪ (T_e ∩ T_f for f ∈ M, f ≠ e)
- Triangles in T_e \ S_e share edges with both e and some f ≠ e
- These triangles have ≥ 4 vertices total (share 2 with e, share 2 with f)
- The edges covering S_e also cover T_e \ S_e (they share the same edge with e)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Core definitions (same as 4736da84)
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

-- T_e \ S_e characterization
def T_e_minus_S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

-- Key lemma: T_e = S_e ∪ T_e_minus_S_e
lemma T_e_eq_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    T_e G e = S_e G M e ∪ T_e_minus_S_e G M e := by
  ext t
  simp only [Finset.mem_union, S_e, T_e_minus_S_e, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right
      push_neg at h
      obtain ⟨f, hfM, hfne, hcard⟩ := h
      exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h
    rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- Triangles in T_e \ S_e share an edge with some f ∈ M, f ≠ e
lemma T_e_minus_S_e_shares_with_other (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V)
    (t : Finset V) (ht : t ∈ T_e_minus_S_e G M e) :
    ∃ f ∈ M, f ≠ e ∧ shareEdge t f := by
  simp only [T_e_minus_S_e, Finset.mem_filter] at ht
  obtain ⟨_, f, hfM, hfne, hcard⟩ := ht
  exact ⟨f, hfM, hfne, hcard⟩

-- When ν ≤ 3, at most 2 other elements in M besides e
lemma other_packing_elements_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    (M.filter (· ≠ e)).card ≤ 2 := by
  have : (M.filter (· ≠ e)).card = M.card - 1 := by
    rw [Finset.filter_ne']
    simp [Finset.card_erase_of_mem he]
  omega

-- Key structural lemma: triangle sharing edge with both e and f
-- must have the shared edge with e contained in T_f's coverage
lemma shared_triangle_coverage (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (t : Finset V) (ht_Te : t ∈ T_e G e) (ht_Tf : shareEdge t f) :
    t ∈ T_e G f := by
  simp only [T_e, Finset.mem_filter] at ht_Te ⊢
  exact ⟨ht_Te.1, ht_Tf⟩

-- THE TARGET LEMMA
lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

end
