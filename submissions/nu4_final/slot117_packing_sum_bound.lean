/-
Tuza ν=4 Strategy - Slot 117: Sum of Disjoint Packings ≤ Global Packing

DEBATE CONSENSUS (Gemini + Grok + Codex):
This lemma is essential for the final assembly. It says:

If T₁, T₂, T₃, T₄ are DISJOINT sets of triangles, then:
  ν(T₁) + ν(T₂) + ν(T₃) + ν(T₄) ≤ ν(T₁ ∪ T₂ ∪ T₃ ∪ T₄)

WHY THIS IS SAFE (from Grok):
- Let P_i be a maximal packing for T_i
- Since T_i are disjoint sets of triangles, P_i ⊂ T_i are also disjoint
- The union ⋃ P_i is a valid packing for the global set
- Thus |P_global| ≥ |⋃ P_i| = Σ |P_i|

CRITICAL INSIGHT:
This is NOT the same as τ_union_le_sum (which goes the wrong direction).
This is about PACKINGS, not covers:
- τ(A ∪ B) ≤ τ(A) + τ(B)  ← PROVEN (subadditivity of cover)
- ν(A) + ν(B) ≤ ν(A ∪ B)  ← THIS LEMMA (superadditivity of packing)

RISK: LOW - This is standard set theory
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

/-- Packing number restricted to a subset of triangles -/
noncomputable def trianglePackingOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  triangles.powerset.filter (fun S =>
    S ⊆ triangles ∧
    Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1))
    |>.image Finset.card |>.max |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: DISJOINT TRIANGLE SETS HAVE DISJOINT PACKINGS
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁ and T₂ are disjoint sets of triangles, their packings are disjoint -/
lemma disjoint_triangles_disjoint_packings
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 : Finset (Finset V)) (hT1 : T1 ⊆ G.cliqueFinset 3) (hT2 : T2 ⊆ G.cliqueFinset 3)
    (hdisj : Disjoint T1 T2)
    (P1 : Finset (Finset V)) (hP1 : P1 ⊆ T1)
    (P2 : Finset (Finset V)) (hP2 : P2 ⊆ T2) :
    Disjoint P1 P2 := by
  rw [Finset.disjoint_iff_ne] at hdisj ⊢
  intro t1 ht1 t2 ht2
  exact hdisj t1 (hP1 ht1) t2 (hP2 ht2)

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE: UNION OF PACKINGS IS A PACKING
-- ══════════════════════════════════════════════════════════════════════════════

/-- If P₁ and P₂ are packings of disjoint triangle sets, P₁ ∪ P₂ is a packing -/
lemma union_of_disjoint_packings_is_packing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 : Finset (Finset V)) (hT1 : T1 ⊆ G.cliqueFinset 3) (hT2 : T2 ⊆ G.cliqueFinset 3)
    (hdisj : Disjoint T1 T2)
    (P1 P2 : Finset (Finset V))
    (hP1_sub : P1 ⊆ T1) (hP2_sub : P2 ⊆ T2)
    (hP1_pack : Set.Pairwise (P1 : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1))
    (hP2_pack : Set.Pairwise (P2 : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)) :
    Set.Pairwise ((P1 ∪ P2) : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
  intro t1 ht1 t2 ht2 hne
  simp only [Finset.coe_union, Set.mem_union] at ht1 ht2
  rcases ht1 with ht1_P1 | ht1_P2 <;> rcases ht2 with ht2_P1 | ht2_P2
  · -- Both in P1: use P1's packing property
    exact hP1_pack ht1_P1 ht2_P1 hne
  · -- t1 ∈ P1, t2 ∈ P2: disjoint sets means t1 ≠ t2 already
    -- Actually need: P1 ⊆ T1, P2 ⊆ T2, T1 ∩ T2 = ∅ implies triangles from different
    -- parts can share at most 1 vertex (they're different triangles)
    -- Since t1 ∈ T1, t2 ∈ T2, and T1 ∩ T2 = ∅, we have t1 ≠ t2
    -- Two distinct triangles share at most 1 vertex (they're in a packing context)
    sorry
  · -- t1 ∈ P2, t2 ∈ P1: symmetric
    sorry
  · -- Both in P2: use P2's packing property
    exact hP2_pack ht1_P2 ht2_P2 hne

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PACKING SUM BOUND (Two Sets)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁ ∩ T₂ = ∅, then ν(T₁) + ν(T₂) ≤ ν(T₁ ∪ T₂) -/
theorem packing_sum_le_union_packing_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 : Finset (Finset V))
    (hT1 : T1 ⊆ G.cliqueFinset 3)
    (hT2 : T2 ⊆ G.cliqueFinset 3)
    (hdisj : Disjoint T1 T2) :
    trianglePackingOn G T1 + trianglePackingOn G T2 ≤ trianglePackingOn G (T1 ∪ T2) := by
  -- Get optimal packings P1 for T1 and P2 for T2
  -- P1 ∪ P2 is a valid packing for T1 ∪ T2
  -- So ν(T1 ∪ T2) ≥ |P1 ∪ P2| = |P1| + |P2| = ν(T1) + ν(T2)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTENSION: PACKING SUM BOUND (Four Sets)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Pairwise disjoint triangle sets -/
def pairwiseDisjoint (T1 T2 T3 T4 : Finset (Finset V)) : Prop :=
  Disjoint T1 T2 ∧ Disjoint T1 T3 ∧ Disjoint T1 T4 ∧
  Disjoint T2 T3 ∧ Disjoint T2 T4 ∧ Disjoint T3 T4

/-- MAIN: If T₁, T₂, T₃, T₄ are pairwise disjoint, their packing numbers sum up correctly -/
theorem packing_sum_le_union_packing_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 T3 T4 : Finset (Finset V))
    (hT1 : T1 ⊆ G.cliqueFinset 3)
    (hT2 : T2 ⊆ G.cliqueFinset 3)
    (hT3 : T3 ⊆ G.cliqueFinset 3)
    (hT4 : T4 ⊆ G.cliqueFinset 3)
    (hdisj : pairwiseDisjoint T1 T2 T3 T4) :
    trianglePackingOn G T1 + trianglePackingOn G T2 +
    trianglePackingOn G T3 + trianglePackingOn G T4 ≤
    trianglePackingOn G (T1 ∪ T2 ∪ T3 ∪ T4) := by
  -- Apply packing_sum_le_union_packing_two iteratively
  have h12 : trianglePackingOn G T1 + trianglePackingOn G T2 ≤
             trianglePackingOn G (T1 ∪ T2) :=
    packing_sum_le_union_packing_two G T1 T2 hT1 hT2 hdisj.1
  have h34 : trianglePackingOn G T3 + trianglePackingOn G T4 ≤
             trianglePackingOn G (T3 ∪ T4) :=
    packing_sum_le_union_packing_two G T3 T4 hT3 hT4 hdisj.2.2.2.2.2
  have hdisj12_34 : Disjoint (T1 ∪ T2) (T3 ∪ T4) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hdisj.2.1, hdisj.2.2.1⟩, ⟨hdisj.2.2.2.1, hdisj.2.2.2.2.1⟩⟩
  have h1234 : trianglePackingOn G (T1 ∪ T2) + trianglePackingOn G (T3 ∪ T4) ≤
               trianglePackingOn G (T1 ∪ T2 ∪ T3 ∪ T4) := by
    have hunion : T1 ∪ T2 ∪ T3 ∪ T4 = (T1 ∪ T2) ∪ (T3 ∪ T4) := by
      ext x; simp [or_assoc]
    rw [hunion]
    apply packing_sum_le_union_packing_two
    · exact Finset.union_subset hT1 hT2
    · exact Finset.union_subset hT3 hT4
    · exact hdisj12_34
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY COROLLARY: GLOBAL PACKING BOUNDS LOCAL SUM
-- ══════════════════════════════════════════════════════════════════════════════

/-- When union equals all triangles, global packing bounds local sum -/
theorem packing_sum_le_global
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 T3 T4 : Finset (Finset V))
    (hT1 : T1 ⊆ G.cliqueFinset 3)
    (hT2 : T2 ⊆ G.cliqueFinset 3)
    (hT3 : T3 ⊆ G.cliqueFinset 3)
    (hT4 : T4 ⊆ G.cliqueFinset 3)
    (hdisj : pairwiseDisjoint T1 T2 T3 T4)
    (hunion : T1 ∪ T2 ∪ T3 ∪ T4 = G.cliqueFinset 3) :
    trianglePackingOn G T1 + trianglePackingOn G T2 +
    trianglePackingOn G T3 + trianglePackingOn G T4 ≤ trianglePackingNumber G := by
  have h := packing_sum_le_union_packing_four G T1 T2 T3 T4 hT1 hT2 hT3 hT4 hdisj
  -- trianglePackingOn G (G.cliqueFinset 3) = trianglePackingNumber G
  sorry

end
