/-
  slot278: Fan Apex Existence for ν=4 Packings (Single Lemma Focus)

  KEY LEMMA: All externals of a single M-element share a common vertex (fan apex)

  This is the foundational lemma for the 8-edge cover construction.

  PROOF SKETCH:
  1. For M-element A, externals are triangles that share an edge only with A
  2. If there's only one external T, its third vertex (not in A) is the apex
  3. If there are multiple externals T₁, T₂, ...:
     - By slot182 (PROVEN): Any two externals share an edge
     - Each external has form {u, v, x} where {u,v} ⊆ A and x ∉ A
     - If T₁ = {a,b,x₁} and T₂ = {a,b,x₂} share same A-edge, and T₁,T₂ share edge
       → Must have x₁ = x₂ (detailed case analysis)
     - If T₁ = {a,b,x₁} and T₂ = {b,c,x₂} use different A-edges:
       → T₁ ∩ T₂ = {b} or T₁ ∩ T₂ = {b, x₁} (if x₁ = x₂)
       → For edge sharing: need |T₁ ∩ T₂| ≥ 2, so x₁ = x₂ = y for some y
  4. Therefore all externals share a common vertex

  DIFFICULTY: 2/5 (finite case analysis with arithmetic)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Basic definitions
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- Two triangles share an edge (≥2 common vertices) -/
def sharesEdgeWith (t S : Finset V) : Prop :=
  (t ∩ S).card ≥ 2

/-- External of A: triangle not in M, shares edge with A, not with others -/
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: Two externals share an edge (from slot182 PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN (slot182): Two externals of same M-element share an edge -/
axiom two_externals_share_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS (for Aristotle scaffolding)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle has exactly 3 vertices -/
lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp ht).2

/-- External shares exactly 2 vertices with A (not 3, since t ∉ M and t ≠ A) -/
lemma external_inter_card_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M)
    (T : Finset V) (hT : isExternalOf G M A T) :
    (T ∩ A).card = 2 := by
  have h_ge : (T ∩ A).card ≥ 2 := hT.2.2.1
  have hT_card : T.card = 3 := triangle_card_eq_3 G T hT.1
  have hA_card : A.card = 3 := triangle_card_eq_3 G A (hM.1.1 hA)
  -- If |T ∩ A| ≥ 3, then T ⊆ A (since |T| = 3)
  -- But T is a 3-clique and A is a 3-clique, so T = A
  -- This contradicts T ∉ M (since A ∈ M)
  by_contra h_ne
  push_neg at h_ne
  have h_eq_3 : (T ∩ A).card = 3 := by omega
  have h_sub : T ⊆ A := by
    have h_inter_eq : T ∩ A = T := by
      apply eq_of_subset_of_card_le (inter_subset_left)
      rw [h_eq_3, hT_card]
    exact h_inter_eq ▸ inter_subset_right
  have h_eq : T = A := by
    apply eq_of_subset_of_card_le h_sub
    rw [hT_card, hA_card]
  exact hT.2.1 (h_eq ▸ hA)

/-- External has exactly 1 vertex not in A -/
lemma external_sdiff_card_eq_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M)
    (T : Finset V) (hT : isExternalOf G M A T) :
    (T \ A).card = 1 := by
  have hT_card : T.card = 3 := triangle_card_eq_3 G T hT.1
  have h_inter : (T ∩ A).card = 2 := external_inter_card_eq_2 G M hM A hA T hT
  have := card_sdiff_add_card_inter T A
  omega

/-- The unique vertex of T \ A -/
noncomputable def externalApexVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M)
    (T : Finset V) (hT : isExternalOf G M A T) : V :=
  (T \ A).toList.head (by
    have h := external_sdiff_card_eq_1 G M hM A hA T hT
    simp only [← card_pos, h]
    omega)

lemma externalApexVertex_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M)
    (T : Finset V) (hT : isExternalOf G M A T) :
    externalApexVertex G M hM A hA T hT ∈ T ∧
    externalApexVertex G M hM A hA T hT ∉ A := by
  unfold externalApexVertex
  have h_mem : (T \ A).toList.head _ ∈ T \ A := by
    apply List.head_mem
  exact mem_sdiff.mp h_mem

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Fan Apex Exists
-- ══════════════════════════════════════════════════════════════════════════════

/-!
PROOF SKETCH:
1. If externals are empty, statement is vacuously true
2. If there's exactly one external T, its apex vertex x = T \ A works
3. If there are multiple externals T₁, T₂:
   - T₁ = {a, b, x₁} with {a,b} ⊆ A, x₁ ∉ A
   - T₂ = {c, d, x₂} with {c,d} ⊆ A, x₂ ∉ A
   - By slot182: sharesEdgeWith T₁ T₂, so |T₁ ∩ T₂| ≥ 2
   - Case analysis on the shared edge:
     - If {a,b} = {c,d}: Same A-edge, T₁ ∩ T₂ = {a,b,x₁} ∩ {a,b,x₂}
       For |∩| ≥ 2: Either x₁ = x₂ (done) or {a,b} provides 2 common
       But T₁, T₂ both external means T₁ ≠ T₂, so if {a,b} = {c,d}, must have x₁ ≠ x₂
       Then T₁ ∩ T₂ = {a, b}, |∩| = 2 ✓ BUT we need MORE analysis...
   - Key insight: If all externals share a common apex vertex, we're done
   - Otherwise, find T₁, T₂ with different apex vertices but sharing an edge
     This constrains them to share A-vertices, leading to geometric contradiction
-/

/-- Fan apex: vertex in all externals of A, not in A itself -/
def isFanApex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (x : V) : Prop :=
  x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T

/-- Main theorem: Fan apex exists if externals are nonempty -/
theorem fan_apex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (h_nonempty : (externalsOf G M A).Nonempty) :
    ∃ x : V, isFanApex G M A x := by
  -- Get some external T₀
  obtain ⟨T₀, hT₀⟩ := h_nonempty
  have hT₀_ext : isExternalOf G M A T₀ := by
    simp only [externalsOf, mem_filter] at hT₀
    exact hT₀.2
  -- Get T₀'s apex vertex
  let x₀ := externalApexVertex G M hM A hA T₀ hT₀_ext
  -- Claim: x₀ is the fan apex for all externals
  use x₀
  constructor
  · -- x₀ ∉ A
    exact (externalApexVertex_mem G M hM A hA T₀ hT₀_ext).2
  · -- x₀ ∈ T for all externals T
    intro T hT
    have hT_ext : isExternalOf G M A T := by
      simp only [externalsOf, mem_filter] at hT
      exact hT.2
    by_cases h_eq : T = T₀
    · -- T = T₀: x₀ ∈ T₀ by construction
      rw [h_eq]
      exact (externalApexVertex_mem G M hM A hA T₀ hT₀_ext).1
    · -- T ≠ T₀: Use edge-sharing property
      -- T and T₀ share an edge (by slot182)
      have h_share := two_externals_share_edge G M hM hM_card hν A hA T T₀ hT_ext hT₀_ext h_eq
      -- T = {a', b', xT} where {a',b'} ⊆ A, xT ∉ A
      -- T₀ = {a, b, x₀} where {a,b} ⊆ A, x₀ ∉ A
      -- |T ∩ T₀| ≥ 2
      -- T ∩ T₀ ⊆ (T ∩ A) ∪ {xT} and T ∩ T₀ ⊆ (T₀ ∩ A) ∪ {x₀}
      -- Since xT ∉ A and x₀ ∉ A:
      --   If xT ∈ T₀, then xT ∈ T₀ \ A = {x₀}, so xT = x₀
      --   If x₀ ∈ T, then x₀ ∈ T \ A = {xT}, so x₀ = xT
      -- So either xT = x₀ (and x₀ ∈ T), or both xT, x₀ are in T ∩ T₀ only via A
      -- But xT ∉ A and x₀ ∉ A, so if xT ≠ x₀:
      --   T ∩ T₀ = (T ∩ T₀ ∩ A) since neither xT nor x₀ can be in intersection
      --   And |T ∩ T₀ ∩ A| ≤ |T ∩ A| = 2
      -- For |T ∩ T₀| ≥ 2, we need |T ∩ T₀ ∩ A| = 2, i.e., T and T₀ share same A-edge
      -- But then T = {a,b,xT} and T₀ = {a,b,x₀} for some {a,b} ⊆ A
      -- Since xT ≠ x₀, T ∩ T₀ = {a,b} with |∩| = 2 ✓
      -- So this case is POSSIBLE with xT ≠ x₀!
      -- Wait... this means x₀ might NOT be in T!
      -- The proof needs more care...
      --
      -- KEY INSIGHT: We need to show that across ALL externals, there's a COMMON vertex
      -- Not that every external contains x₀ specifically
      --
      -- Refined approach:
      -- Consider the "apex graph": vertices are apex vertices of externals,
      -- edges connect apices of externals that share different A-edges
      -- If two externals share the same A-edge, their apices must be equal (triangle uniqueness)
      -- If two externals share different A-edges and share an edge, their apices must be equal
      --
      -- Actually, let's think more carefully:
      -- T₁ = {a,b,x₁}, T₂ = {b,c,x₂} (different A-edges {a,b} vs {b,c})
      -- T₁ ∩ T₂ = {b} ∪ ({a} ∩ {c}) ∪ ({a,b} ∩ {x₂}) ∪ ({x₁} ∩ {b,c}) ∪ ({x₁} ∩ {x₂})
      -- = {b} ∪ ∅ ∪ ∅ ∪ ∅ ∪ ({x₁} ∩ {x₂})
      -- = {b} if x₁ ≠ x₂, or {b, x₁} if x₁ = x₂
      -- For |T₁ ∩ T₂| ≥ 2, we need x₁ = x₂
      -- So externals using different A-edges MUST have same apex!
      --
      -- Case: T, T₀ use same A-edge {a,b}
      -- T = {a,b,xT}, T₀ = {a,b,x₀}
      -- Both are distinct triangles, so xT ≠ x₀... wait no
      -- If they're distinct, xT could equal x₀ (then T = T₀ contradiction) or differ
      -- If xT ≠ x₀: T ∩ T₀ = {a,b}, |∩| = 2, edge-sharing satisfied
      -- So two externals using same A-edge CAN have different apices!
      --
      -- BUT: We assumed x₀ is THE apex. If some external T has xT ≠ x₀,
      -- then x₀ ∉ T (since T \ A = {xT} and xT ≠ x₀)
      -- This contradicts our goal!
      --
      -- RESOLUTION: The fan apex theorem only holds when there's at most one external
      -- per A-edge, OR when we carefully choose which vertex to call the apex
      --
      -- Actually wait - the original paper/proof uses a DIFFERENT definition of "fan apex"
      -- The apex is a vertex v ∈ A such that all externals contain v
      -- Not a vertex OUTSIDE A!
      --
      -- Let me reconsider...
      -- If A = {a,b,c}, externals share edges with A, so each external contains
      -- exactly 2 vertices of A. If all externals share a common A-vertex v,
      -- then v is in all externals, and we can use edges incident to v.
      --
      -- This is different from what I was proving!
      sorry

end
