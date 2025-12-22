/-
Tuza Key Lemma: τ(T_e) ≤ 2

This is the core lemma needed for the ν=4 proof.

T_e = all triangles sharing an edge with packing element e.

CLAIM: For any e in a maximal packing M, τ(T_e) ≤ 2.

WHY THIS MATTERS:
- If τ(T_e) ≤ 2 for each e ∈ M
- Then τ(T_e ∪ T_f) ≤ τ(T_e) + τ(T_f \ T_e) ≤ τ(T_e) + τ(S_f) ≤ 2 + 2 = 4

STRUCTURAL INSIGHT:
- Every triangle in T_e shares at least one edge with e
- e has exactly 3 edges
- By pigeonhole, 2 edges of e cover all triangles sharing ANY edge with e

But wait - not all triangles in T_e are covered by just edges of e!
A triangle t ∈ T_e might share edge {a,b} of e, but be covered by
an edge like {a,x} where x is the third vertex of t.

The key is: we need 2 edges (from anywhere in G) that cover all of T_e.

Pattern: Boris Minimal
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- STRUCTURAL: Triangles sharing edge with e all intersect e in ≥2 vertices
lemma Te_intersect_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (t : Finset V) (ht : t ∈ trianglesSharingEdge G e) :
    (t ∩ e).card ≥ 2 := by
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  exact ht.2

-- STRUCTURAL: Any two triangles sharing an edge with e share at least one vertex
lemma Te_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (t1 t2 : Finset V) (ht1 : t1 ∈ trianglesSharingEdge G e) (ht2 : t2 ∈ trianglesSharingEdge G e) :
    (t1 ∩ t2).card ≥ 1 := by
  sorry

-- HELPER: If all triangles in a family pairwise intersect, they can be covered efficiently
lemma pairwise_intersecting_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : ∀ s ∈ S, s ∈ G.cliqueFinset 3)
    (h_intersect : ∀ t1 ∈ S, ∀ t2 ∈ S, (t1 ∩ t2).card ≥ 1) :
    triangleCoveringNumberOn G S ≤ 2 := by
  sorry

-- TARGET: τ(T_e) ≤ 2 for any packing element e
theorem tau_Te_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry

-- COROLLARY: τ(T_e ∪ T_f) ≤ 4 when e ≠ f
theorem tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

end
