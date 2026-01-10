/-
  slot279: Correct Fan Apex Formulation for ν=4 PATH_4

  CRITICAL CORRECTION:
  The fan apex u_A is a vertex IN A (not outside A) such that:
  - All externals of A contain u_A
  - Cover = 2 edges of A incident to u_A

  This works because:
  1. u_A ∈ A and u_A ∈ T for all externals T
  2. External T shares edge {u_A, v} with A for some v ∈ A
  3. Edge {u_A, v} is in our cover (edges of A incident to u_A)
  4. So T is covered!

  PROOF SKETCH for apex existence:
  1. A = {a, b, c} has 3 vertices
  2. Each external uses exactly one edge of A: {a,b}, {b,c}, or {a,c}
  3. If two externals use different edges of A, they share at most 1 A-vertex
  4. But by slot182, externals share an edge (≥2 common vertices)
  5. So if externals use different A-edges, their extra vertices must be equal
  6. Case analysis shows all externals share a common A-vertex (the apex)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Basic definitions (from proven files)
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

def sharesEdgeWith (t S : Finset V) : Prop := (t ∩ S).card ≥ 2

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

-- AXIOM from slot182 (PROVEN)
axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hne : T₁ ≠ T₂) : sharesEdgeWith T₁ T₂

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp ht).2

lemma external_inter_card_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M)
    (T : Finset V) (hT : isExternalOf G M A T) :
    (T ∩ A).card = 2 := by
  have h_ge : (T ∩ A).card ≥ 2 := hT.2.2.1
  have hT_card : T.card = 3 := triangle_card_eq_3 G T hT.1
  by_contra h_ne
  push_neg at h_ne
  have h_eq_3 : (T ∩ A).card = 3 := by omega
  have h_sub : T ⊆ A := by
    have h_inter_eq : T ∩ A = T := eq_of_subset_of_card_le (inter_subset_left) (by rw [h_eq_3, hT_card])
    exact h_inter_eq ▸ inter_subset_right
  have hA_card : A.card = 3 := triangle_card_eq_3 G A (hM.1.1 hA)
  have h_eq : T = A := eq_of_subset_of_card_le h_sub (by rw [hT_card, hA_card])
  exact hT.2.1 (h_eq ▸ hA)

-- ══════════════════════════════════════════════════════════════════════════════
-- CORRECTED FAN APEX DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Fan apex: vertex u IN A such that all externals of A contain u -/
def isFanApex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (u : V) : Prop :=
  u ∈ A ∧ ∀ T ∈ externalsOf G M A, u ∈ T

/-!
## Key Lemma: Fan Apex Exists

PROOF SKETCH:
A = {a, b, c} (3 vertices).
Each external T shares exactly one edge with A, so T ∩ A ∈ {{a,b}, {b,c}, {a,c}}.

Case 1: All externals use the same A-edge {a,b}.
  Then every external contains both a and b.
  Pick u = a (or b). u ∈ A and u ∈ T for all externals.

Case 2: Two externals T₁, T₂ use different A-edges.
  WLOG T₁ uses {a,b}, T₂ uses {b,c}.
  T₁ = {a, b, x₁} for some x₁ ∉ A.
  T₂ = {b, c, x₂} for some x₂ ∉ A.
  By slot182: |T₁ ∩ T₂| ≥ 2.
  T₁ ∩ T₂ = {b} ∪ ({x₁} ∩ {x₂}).
  If x₁ ≠ x₂: T₁ ∩ T₂ = {b}, |∩| = 1. Contradiction!
  So x₁ = x₂ =: x, and T₁ ∩ T₂ = {b, x}, |∩| = 2. ✓

  Now consider any other external T₃.
  If T₃ uses {a,b}: T₃ = {a, b, y}. Compare with T₂ = {b, c, x}.
    T₃ ∩ T₂ = {b} ∪ ({y} ∩ {x}). For |∩| ≥ 2, need y = x.
    So T₃ = {a, b, x}, and b ∈ T₃. ✓
  If T₃ uses {b,c}: T₃ = {b, c, y}. Compare with T₁ = {a, b, x}.
    T₃ ∩ T₁ = {b} ∪ ({y} ∩ {x}). For |∩| ≥ 2, need y = x.
    So T₃ = {b, c, x}, and b ∈ T₃. ✓
  If T₃ uses {a,c}: T₃ = {a, c, y}. Compare with T₁ = {a, b, x}.
    T₃ ∩ T₁ = {a} ∪ ({y} ∩ {x}). For |∩| ≥ 2, need y = x.
    Now compare T₃ = {a, c, x} with T₂ = {b, c, x}.
    T₃ ∩ T₂ = {c, x}, |∩| = 2. ✓
    But wait: what vertex is in ALL of T₁, T₂, T₃?
    T₁ = {a, b, x}, T₂ = {b, c, x}, T₃ = {a, c, x}.
    Common vertex: x! But x ∉ A...

  ISSUE: In Case 2 with T₃ using {a,c}, the common vertex is x ∉ A, not b.
  So the apex might be OUTSIDE A after all!

CORRECTED UNDERSTANDING:
The fan apex can be EITHER in A or outside A. What matters is that it's common to all externals.
For the cover construction:
- If apex u ∈ A: Use 2 edges of A incident to u. These are A-edges.
- If apex x ∉ A: Use 2 edges from A-vertices to x. These are spoke edges.

Either way, we need 2 edges to cover A and all its externals.
-/

/-- Generalized fan apex: vertex common to all externals (may or may not be in A) -/
def isGeneralizedFanApex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (x : V) : Prop :=
  ∀ T ∈ externalsOf G M A, x ∈ T

/-- Fan apex exists (generalized version) -/
theorem generalized_fan_apex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (h_nonempty : (externalsOf G M A).Nonempty) :
    ∃ x : V, isGeneralizedFanApex G M A x := by
  -- The proof follows the sketch above
  -- Key insight: By slot182, any two externals share ≥2 vertices
  -- Since each external has exactly 1 vertex outside A, and shares 2 with A,
  -- the intersection constraint forces a common vertex

  -- If there's only one external, any vertex in it works
  obtain ⟨T₀, hT₀⟩ := h_nonempty
  by_cases h_single : (externalsOf G M A).card ≤ 1
  · -- Single external case
    have hT₀_ext : isExternalOf G M A T₀ := by
      simp only [externalsOf, mem_filter] at hT₀
      exact hT₀.2
    have hT₀_card : T₀.card = 3 := triangle_card_eq_3 G T₀ hT₀_ext.1
    obtain ⟨v, hv⟩ := card_pos.mp (by omega : T₀.card > 0)
    use v
    intro T hT
    have hT₀_unique : T = T₀ := by
      have h1 : (externalsOf G M A).card = 1 := by
        have h_pos : 0 < (externalsOf G M A).card := card_pos.mpr h_nonempty
        omega
      exact card_eq_one.mp h1 ▸ mem_singleton.mp (by
        rw [card_eq_one.mp h1] at hT hT₀
        simp only [mem_singleton] at hT hT₀
        rw [hT, hT₀])
    rw [hT₀_unique]
    exact hv
  · -- Multiple externals case
    push_neg at h_single
    -- Get two distinct externals
    have h_ge_2 : 2 ≤ (externalsOf G M A).card := by omega
    obtain ⟨T₁, hT₁, T₂, hT₂, h_ne⟩ : ∃ T₁ ∈ externalsOf G M A,
        ∃ T₂ ∈ externalsOf G M A, T₁ ≠ T₂ := by
      rcases one_lt_card.mp (by omega : 1 < (externalsOf G M A).card) with ⟨T₁, hT₁, T₂, hT₂, hne⟩
      exact ⟨T₁, hT₁, T₂, hT₂, hne⟩
    have hT₁_ext : isExternalOf G M A T₁ := by simp only [externalsOf, mem_filter] at hT₁; exact hT₁.2
    have hT₂_ext : isExternalOf G M A T₂ := by simp only [externalsOf, mem_filter] at hT₂; exact hT₂.2

    -- T₁ and T₂ share ≥2 vertices
    have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁_ext hT₂_ext h_ne
    -- Each external has 2 vertices in A and 1 outside
    have hT₁_inter : (T₁ ∩ A).card = 2 := external_inter_card_eq_2 G M hM A hA T₁ hT₁_ext
    have hT₂_inter : (T₂ ∩ A).card = 2 := external_inter_card_eq_2 G M hM A hA T₂ hT₂_ext
    have hT₁_card : T₁.card = 3 := triangle_card_eq_3 G T₁ hT₁_ext.1
    have hT₂_card : T₂.card = 3 := triangle_card_eq_3 G T₂ hT₂_ext.1

    -- |T₁ ∩ T₂| ≥ 2
    -- T₁ = (T₁ ∩ A) ∪ (T₁ \ A), |T₁ \ A| = 1
    -- T₂ = (T₂ ∩ A) ∪ (T₂ \ A), |T₂ \ A| = 1

    -- Get the common vertices
    have h_inter_pos : 2 ≤ (T₁ ∩ T₂).card := h_share
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (by omega : 1 < (T₁ ∩ T₂).card)
    -- u and v are in both T₁ and T₂
    use u
    -- Show u is in all externals
    intro T hT
    have hT_ext : isExternalOf G M A T := by simp only [externalsOf, mem_filter] at hT; exact hT.2
    by_cases hT_eq1 : T = T₁
    · rw [hT_eq1]; exact (mem_inter.mp hu).1
    by_cases hT_eq2 : T = T₂
    · rw [hT_eq2]; exact (mem_inter.mp hu).2
    -- T is a third distinct external
    -- T shares edge with T₁ and with T₂
    have h_share_T_T₁ := two_externals_share_edge G M hM hM_card hν A hA T T₁ hT_ext hT₁_ext hT_eq1
    have h_share_T_T₂ := two_externals_share_edge G M hM hM_card hν A hA T T₂ hT_ext hT₂_ext hT_eq2
    -- T ∩ T₁ ≥ 2 and T ∩ T₂ ≥ 2
    -- Combined with triangle structure, this forces u ∈ T
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER CONSTRUCTION WITH GENERALIZED APEX
-- ══════════════════════════════════════════════════════════════════════════════

/-!
## Cover Construction

For M-element A with generalized apex x:
- If x ∈ A: Cover = 2 edges of A incident to x
  - Covers A: obviously (A is a triangle containing x, so has 2 edges at x)
  - Covers externals: External T contains x and shares edge with A,
    so T = {x, a, y} where a ∈ A. Edge {x,a} is in our cover and in T.

- If x ∉ A: Cover = 2 spoke edges from A to x (if they exist in G)
  - Covers A: Need at least one spoke {a, x} where a ∈ A is in A's edge... wait, no
  - This doesn't cover A itself! A might not contain x.

ISSUE: If apex x ∉ A, we need different edges to cover A vs externals.
- 1 edge of A (any edge) covers A itself
- 2 spoke edges {a,x}, {b,x} cover externals (each external contains x and some a∈A)

So: Cover = 1 A-edge + 2 spoke edges = 3 edges when apex is external?
That's too many for 8-total budget!

RESOLUTION: The apex should always be constructible IN A.
Let me re-examine the proof sketch...

Actually, looking at the Case 2 analysis:
- If T₁ = {a,b,x}, T₂ = {b,c,x}, T₃ = {a,c,x}, then x is common
- But A = {a,b,c}, so A ∩ {T₁, T₂, T₃} = {b} ∩ {c} ∩ {a} = ∅... wait that's wrong
- b ∈ T₁ ∩ T₂, c ∈ T₂ ∩ T₃, a ∈ T₁ ∩ T₃
- All of T₁, T₂, T₃ contain x, but x ∉ A

So in this case, the common vertex is x ∉ A.
But we can ALSO note that:
- T₁ contains b (from A)
- T₂ contains b and c (from A)
- T₃ contains c and a (from A)
No single A-vertex is in all three!

So when there are externals using all 3 edges of A, the common vertex must be outside A.
This is a problem for the 2-edge cover construction...

WAIT: Actually we need to cover not just A's externals, but A itself too!
- If x ∉ A, we still need to cover A with edges of A
- We also need to cover externals, which all contain x

Cover = 1 A-edge (covers A) + 1 spoke edge {a, x} (covers externals containing x and a)
But externals might use different A-edges, so one spoke might not cover all...

Actually: External T contains x. T shares edge {u,v} with A where u,v ∈ A.
T = {u, v, x}. If we have edge {u, x} in cover, T is covered.
But different externals might have different {u,v} pairs!

To cover all externals with ONE spoke, we need all externals to share
a common A-vertex u, so that {u, x} is in all of them.

In the Case 2 scenario:
T₁ = {a, b, x}: contains {a,x} and {b,x}
T₂ = {b, c, x}: contains {b,x} and {c,x}
T₃ = {a, c, x}: contains {a,x} and {c,x}

No single spoke covers all three! We'd need 2 spokes: {b,x} covers T₁, T₂; {a,x} or {c,x} covers T₃.
That's 2 spokes + 1 A-edge = 3 edges per M-element = 12 total!

CONCLUSION: The naive 2-edge-per-M-element approach fails when all 3 A-edges have externals.

However, by slot182 (5-packing bound), maybe we can prove this case is IMPOSSIBLE?
If T₁, T₂, T₃ all exist and use different A-edges, perhaps this contradicts ν=4?

Let me investigate...
-/

/-- If A has externals on all 3 edges, we get a 5-packing contradiction -/
theorem externals_use_at_most_2_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (hA_eq : ∃ a b c : V, A = {a, b, c} ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (T₁ T₂ T₃ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂) (hT₃ : isExternalOf G M A T₃)
    (h_distinct : T₁ ≠ T₂ ∧ T₂ ≠ T₃ ∧ T₁ ≠ T₃)
    -- T₁ uses edge {a,b}, T₂ uses {b,c}, T₃ uses {a,c}
    (hT₁_edge : ∃ a b, {a, b} ⊆ T₁ ∩ A)
    (hT₂_edge : ∃ b c, {b, c} ⊆ T₂ ∩ A)
    (hT₃_edge : ∃ a c, {a, c} ⊆ T₃ ∩ A)
    (h_diff_edges : True) -- placeholder for "uses different edges"
    : False := by
  -- If T₁, T₂, T₃ use different A-edges and exist, we can form 5-packing:
  -- M' = (M \ {A}) ∪ {T₁, T₂, T₃}
  -- This has |M'| = 3 + 3 = 6? No wait...
  -- Actually M' = (M \ {A}) ∪ {T₁, T₂} might work if T₁, T₂ don't share edge
  -- But by slot182, T₁, T₂ DO share an edge! So can't add both to packing.
  -- Need different approach...
  sorry

end
