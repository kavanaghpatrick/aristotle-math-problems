/-
Parker's Proof of Tuza for ν ≤ 3 (arXiv:2406.06501)
Scaffolded version with key lemmas.

PROOF STRUCTURE:
1. Lemma 2.2: For maximum matching M and e ∈ M, any two triangles in S_e share an edge
   - S_e = {t : t shares edge with e, t doesn't share edge with any other f ∈ M}
   - Proof: If t1, t2 ∈ S_e don't share edge, then (M\{e}) ∪ {t1,t2} is larger matching

2. Lemma 2.3: Removing T_e (all triangles sharing edge with e) leaves graph with ν' = ν - 1
   - T_e = {t : t shares edge with e}
   - Proof: If N is matching in G\T_e with |N| ≥ ν, then N ∪ {e} is larger matching in G

3. Induction: τ(G) ≤ τ(T_e) + τ(G\T_e) ≤ τ(T_e) + 2(ν-1)
   - Need τ(T_e) ≤ 2 for Tuza bound
   - Paper proves this via case analysis for ν ≤ 3
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

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

def sharesEdge (t1 t2 : Finset V) : Prop :=
  ¬ Disjoint (triangleEdges t1) (triangleEdges t2)

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h => sharesEdge h e)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h =>
    sharesEdge h e ∧ ∀ f ∈ M, f ≠ e → ¬ sharesEdge h f)

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M ∧ M.card = trianglePackingNumber G := by
  have h : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
  obtain ⟨M, hM₁, hM₂⟩ := h_max
  simp [Finset.mem_filter, Finset.mem_powerset] at hM₁
  exact ⟨M, hM₁.1, hM₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩

lemma parker_lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (h1 h2 : Finset V) (hh1 : h1 ∈ S_e G M e) (hh2 : h2 ∈ S_e G M e) (hne : h1 ≠ h2) :
    sharesEdge h1 h2 := by
  sorry

lemma parker_lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (hM_pos : M.card ≥ 1)
    (H' : Finset (Finset V)) (hH' : H' = G.cliqueFinset 3 \ T_e G e) :
    ∀ N ⊆ H', IsEdgeDisjoint N → N.card ≤ M.card - 1 := by
  sorry

lemma T_e_cover_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧
    ∀ t ∈ T_e G e, ¬ Disjoint (triangleEdges t) C := by
  sorry

theorem tuza_case_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) : triangleCoveringNumber G ≤ 6 := by
  sorry

theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

end
