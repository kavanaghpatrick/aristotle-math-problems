/-
Tuza ν=4: τ(T_e ∪ T_f) ≤ 4 - Corrected Approach

GOAL: When e, f ∈ M (max packing) share vertex v, prove τ(T_e ∪ T_f) ≤ 4.

KEY INSIGHT (from Grok analysis):
- The lemma bridges_to_f_in_k4 (bridges fit in 4 vertices) is FALSE
- bridges can use all 5 vertices of e ∪ f
- But we don't need cardinality bounds - we need COVERING NUMBER bounds

CORRECTED APPROACH:
- All bridges X(e,f) contain the shared vertex v (proven in triangle_bridge_COMPLETE)
- Therefore τ(X(e,f)) ≤ 2 (just use 2 edges at v)
- Combined with τ(S_e) ≤ 2 and τ(S_f) ≤ 2

DECOMPOSITION: T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) where:
- S_e = triangles sharing edge ONLY with e
- S_f = triangles sharing edge ONLY with f
- X(e,f) = bridges sharing edges with BOTH

Since X(e,f) ⊆ T_e ∩ T_f, we have:
  τ(T_e ∪ T_f) ≤ τ(T_e) + τ(S_f) or τ(S_e) + τ(T_f)

Pattern: Boris Minimal - let Aristotle find the path
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

-- PROVEN: τ(S_e) ≤ 2 (from tuza_tau_Se_COMPLETE.lean)
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry

-- PROVEN: Triangles sharing edges with both e,f contain their shared vertex
-- (from triangle_bridge_COMPLETE.lean)
lemma X_triangles_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V)
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_disjoint : (e ∩ f).card ≤ 1)
    (h_inter : e ∩ f = {v}) :
    ∀ t ∈ X_ef G e f, v ∈ t := by
  sorry

-- KEY LEMMA: τ(X(e,f)) ≤ 2 when all triangles contain v
-- (star cover at v with 2 edges suffices)
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V)
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : e ∩ f = {v})
    (h_all_contain_v : ∀ t ∈ X_ef G e f, v ∈ t) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry

-- STRUCTURAL: X(e,f) is contained in both T_e and T_f
lemma X_subset_Te (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) : X_ef G e f ⊆ trianglesSharingEdge G e := by
  intro t ht
  simp only [X_ef, Finset.mem_inter] at ht
  exact ht.1

-- STRUCTURAL: T_e = S_e ∪ (triangles sharing with other packing elements)
lemma Te_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M) :
    trianglesSharingEdge G e = S_e G e M ∪
      (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2) := by
  sorry

-- COVERING LEMMA: If A ⊆ B, τ(B) ≤ τ(A) + τ(B \ A)
lemma tau_union_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
      triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

-- TARGET: τ(T_e ∪ T_f) ≤ 4 when e, f share exactly one vertex
theorem tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

end
