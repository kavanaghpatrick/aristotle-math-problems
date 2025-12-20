/-
Tuza's Conjecture for ν ≤ 3: Assembly of Proven Lemmas
All helper lemmas are PROVEN in prior Aristotle runs.
Goal: Complete the final theorem.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option linter.mathlibStandardSet false

open scoped BigOperators Classical Pointwise

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

def isStar (S : Finset (Finset V)) : Prop :=
  ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t

def isK4 (S : Finset (Finset V)) : Prop :=
  ∃ s : Finset V, s.card = 4 ∧ ∀ t ∈ S, t ⊆ s

def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglePackingNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  triangles.powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, isMaxPacking G M := by
  sorry

lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S_e G e M → t2 ∈ S_e G e M → shareEdge t1 t2 := by
  sorry

lemma lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = trianglePackingNumber G - 1 := by
  sorry

lemma inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
      triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
  sorry

lemma intersecting_family_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_nonempty : S.Nonempty) (hS : S ⊆ G.cliqueFinset 3)
    (h_pair : Set.Pairwise (S : Set (Finset V)) shareEdge) :
    isStar S ∨ isK4 S := by
  sorry

lemma tau_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h_star : isStar S) :
    triangleCoveringNumberOn G S ≤ 1 := by
  sorry

lemma covering_number_le_two_of_subset_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (s : Finset V) (hs_card : s.card = 4) (hs_contains : ∀ t ∈ S, t ⊆ s) :
    triangleCoveringNumberOn G S ≤ 2 := by
  sorry

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry

lemma tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  sorry

theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end
