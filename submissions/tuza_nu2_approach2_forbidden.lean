/-
TUZA ν=2 - APPROACH 2: Forbidden Structure (K₄/K₅ Extension)
Strategy: When ν=2 and τ>4, derive contradiction via forbidden dense structure

KEY INSIGHT: Generalize the ν=1 K₄ argument
- For ν=1, τ>2 forces K₄ which can be covered by 2 edges
- For ν=2, τ>4 should force two K₄s or denser structure

PROOF OUTLINE:
1. Assume ν=2 and τ>4 (contradiction target)
2. Find two edge-disjoint triangles T1, T2
3. Since τ>4, some triangles avoid any 4-edge cover
4. This forces extensions forming dense subgraph (two K₄s?)
5. Such structure either has ν>2 (contradiction) or τ≤4 (contradiction)
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

/-! ## Structure Definitions -/

/-- A K₄ clique in G -/
def IsK4 (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Prop :=
  s ∈ G.cliqueFinset 4

/-- Two K₄s sharing at most one vertex -/
def HasTwoAlmostDisjointK4 (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (s1 s2 : Finset V), IsK4 G s1 ∧ IsK4 G s2 ∧ s1 ≠ s2 ∧ (s1 ∩ s2).card ≤ 1

/-! ## Building Blocks from ν=1 -/

/-- Extract max packing -/
lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_max
  simp [Finset.mem_filter, Finset.mem_powerset] at hP₁
  exact ⟨P, hP₁.1, hP₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩

/-- When ν=1, any two triangles share an edge -/
lemma packing_one_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  sorry

/-- The ν=1 theorem (proven by Aristotle via K₄) -/
lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

/-! ## The Forbidden Structure Argument -/

/-- KEY LEMMA 1: If ν=2 and τ>4, every 4-edge set misses some triangle -/
lemma tau_gt_4_implies_uncovered (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (S : Finset (Sym2 V)) (hS_card : S.card ≤ 4) (hS_sub : S ⊆ G.edgeFinset) :
    ∃ t ∈ G.cliqueFinset 3, Disjoint (triangleEdges t) S := by
  sorry

/-- KEY LEMMA 2: Extension lemma for ν=2 (analogous to ν=1)
    If ν=2, τ>4, and T is a triangle in max packing, for any edge e of T,
    there exists another triangle sharing exactly e with T -/
lemma extension_triangle_exists_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T) :
    ∃ T', T' ∈ G.cliqueFinset 3 ∧ triangleEdges T ∩ triangleEdges T' = {e} := by
  sorry

/-- KEY LEMMA 3: From extensions, build K₄ around a packing triangle -/
lemma extensions_form_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ s : Finset V, T ⊆ s ∧ IsK4 G s := by
  -- Use extension_triangle_exists_nu2 on each edge of T
  -- Extensions must share vertices (packing constraint)
  -- This forces a 4th vertex adjacent to all of T
  sorry

/-- KEY LEMMA 4: With ν=2 and τ>4, we get two almost-disjoint K₄s -/
lemma tau_gt_4_implies_two_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4) :
    HasTwoAlmostDisjointK4 G := by
  -- Get the two packing triangles T1, T2
  -- Apply extensions_form_K4 to each
  -- They're almost-disjoint because T1, T2 are edge-disjoint
  sorry

/-- KEY LEMMA 5: Two almost-disjoint K₄s can be covered by ≤4 edges -/
lemma two_K4_cover_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s1 s2 : Finset V) (h1 : IsK4 G s1) (h2 : IsK4 G s2)
    (h_disj : (s1 ∩ s2).card ≤ 1) :
    ∃ S : Finset (Sym2 V), S.card ≤ 4 ∧ IsTriangleCovering G S := by
  -- Each K₄ can be covered by 2 opposite edges
  -- If disjoint: 2+2=4 edges suffice
  -- If share 1 vertex: careful choice of 4 edges works
  sorry

/-- ALTERNATIVE: Two almost-disjoint K₄s imply ν > 2 -/
lemma two_K4_implies_nu_gt_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s1 s2 : Finset V) (h1 : IsK4 G s1) (h2 : IsK4 G s2)
    (h_disj : (s1 ∩ s2).card ≤ 1) :
    trianglePackingNumber G > 2 ∨ triangleCoveringNumber G ≤ 4 := by
  -- K₄ contains 4 triangles; two K₄s give many triangles
  -- Either some are edge-disjoint (ν>2) or we can cover with ≤4
  sorry

/-! ## Main Theorem -/

/-- MAIN: τ ≤ 4 when ν = 2 via forbidden structure -/
theorem tuza_nu_2_forbidden (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    triangleCoveringNumber G ≤ 4 := by
  by_contra h_tau
  push_neg at h_tau
  -- τ > 4 implies two almost-disjoint K₄s
  have h_K4 := tau_gt_4_implies_two_K4 G h h_tau
  obtain ⟨s1, s2, hs1, hs2, hne, h_inter⟩ := h_K4
  -- But two K₄s give either ν>2 or τ≤4
  rcases two_K4_implies_nu_gt_2 G s1 s2 hs1 hs2 h_inter with h_nu_gt | h_tau_le
  · -- ν > 2 contradicts h
    omega
  · -- τ ≤ 4 contradicts h_tau
    omega

end
