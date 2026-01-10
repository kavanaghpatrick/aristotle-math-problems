/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9f0fac6d-c1bd-4db3-964d-9121f8914b59

The following was proved by Aristotle:

- lemma pairwise_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ X, x ∈ T₁ ∧ x ∈ T₂

- lemma fanCover_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X) :
    (fanCover G X hX_clique x hx).card = 2
-/

/-
  slot308: Adaptive Fan Cover for PATH_4 τ ≤ 8

  CRITICAL INSIGHT FROM AI ANALYSIS (Jan 8, 2026):
  The fixed cover8 = {a1a2, d1d2, v1v2, v2v3, v1a1, v1b, v3c, v3d1} is WRONG!

  It doesn't cover v2-externals like {v2,b,c}:
  - Triangle {v2,b,c} has edges {v2b, v2c, bc}
  - NONE of these are in cover8!

  CORRECT APPROACH: Adaptive Fan Cover

  For each X ∈ M, use the fan apex x_X from proven results:
  - slot301: All A-externals share a vertex in A
  - slot303: All B-externals share a vertex in B

  The cover is constructed as:
  For each X = {x, y, z} with fan apex x:
    Include edges {xy, xz} (the 2 spokes from apex)

  This covers:
  - X itself (by {xy, xz})
  - All X-externals (they all contain x, hence contain spoke edge)

  Total: 4 elements × 2 edges = 8 edges

  KEY LEMMA NEEDED: Universal fan apex (all externals share common vertex)
-/

import Mathlib


set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) ∧ E.card = n }

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING FROM PROVEN RESULTS
-- ══════════════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu_t, hu_m⟩,
                                 v, Finset.mem_inter.mpr ⟨hv_t, hv_m⟩, huv⟩

lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact h_not_share ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

-- From slot301/303: Two externals share edge containing X-vertex
lemma pairwise_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ X, x ∈ T₁ ∧ x ∈ T₂ := by
  -- This is proven in slot301 (for endpoints) and slot303 (for middles)
  -- Since T₁ and T₂ are externals of X, they must share an edge with X. Therefore, there must be at least two vertices in T₁ that are in X, and similarly for T₂.
  have h_share_edge_X : ∃ u v, u ≠ v ∧ u ∈ T₁ ∧ v ∈ T₁ ∧ u ∈ X ∧ v ∈ X := by
    exact hT₁.2.2.1
  have h_share_edge_X_T₂ : ∃ u v, u ≠ v ∧ u ∈ T₂ ∧ v ∈ T₂ ∧ u ∈ X ∧ v ∈ X := by
    cases hT₂ ; aesop;
  obtain ⟨ u₁, v₁, hne₁, hu₁, hv₁, hx₁, hx₂ ⟩ := h_share_edge_X
  obtain ⟨ u₂, v₂, hne₂, hu₂, hv₂, hy₁, hy₂ ⟩ := h_share_edge_X_T₂
  by_cases h_cases : u₁ = u₂ ∨ u₁ = v₂ ∨ v₁ = u₂ ∨ v₁ = v₂;
  · grind;
  · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hx₁ ( Finset.insert_subset hx₂ ( Finset.insert_subset hy₁ ( Finset.singleton_subset_iff.mpr hy₂ ) ) ) ) ; simp_all +decide ;
    aesop

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Universal Fan Apex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Given pairwise sharing, prove universal sharing by pigeonhole on X = {x₁, x₂, x₃}.

Case k ≤ 2 externals: Trivial (use the pairwise shared vertex)

Case k ≥ 3 externals: Let T₁, T₂, T₃ be three externals.
- v₁₂ ∈ X ∩ T₁ ∩ T₂ (pairwise)
- v₁₃ ∈ X ∩ T₁ ∩ T₃ (pairwise)
- v₂₃ ∈ X ∩ T₂ ∩ T₃ (pairwise)

Since |Tᵢ ∩ X| = 2 for each external Tᵢ:
- T₁ ∩ X contains both v₁₂ and v₁₃
- If v₁₂ = v₁₃, that's the common vertex
- If v₁₂ ≠ v₁₃, then T₁ ∩ X = {v₁₂, v₁₃}

In the second case:
- v₂₃ ∈ T₂ ∩ X and v₁₂ ∈ T₂ ∩ X
- Since |T₂ ∩ X| = 2, either v₂₃ = v₁₂ or T₂ ∩ X = {v₁₂, v₂₃}
- But v₂₃ ∈ T₃ and v₁₃ ∈ T₃, so if v₂₃ ≠ v₁₃ and v₂₃ ≠ v₁₂...

The constraints force a common vertex by pigeonhole on |X| = 3.
-/
lemma universal_fan_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ x ∈ X, ∀ T ∈ externals, x ∈ T := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ADAPTIVE COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Given fan apex x in X = {x, y, z}, the 2-edge cover {xy, xz} -/
def fanCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (x : V) (hx : x ∈ X) : Finset (Sym2 V) :=
  -- Get the other two vertices
  let others := X.erase x
  -- Create edges from x to each other vertex
  others.image (fun y => s(x, y))

/-- The fan cover has exactly 2 edges -/
lemma fanCover_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X) :
    (fanCover G X hX_clique x hx).card = 2 := by
  unfold fanCover
  have h_others_card : (X.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx, hX_3]
  -- Image of 2-element set under injective function has 2 elements
  rw [ Finset.card_image_of_injOn, h_others_card ] ; intro y hy ; aesop;

/-- Fan cover edges are graph edges -/
lemma fanCover_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3)
    (x : V) (hx : x ∈ X) :
    fanCover G X hX_clique x hx ⊆ G.edgeFinset := by
  unfold fanCover
  intro e he
  simp only [Finset.mem_image, Finset.mem_erase] at he
  obtain ⟨y, ⟨hy_ne, hy_X⟩, rfl⟩ := he
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hX_clique
  exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hx hy_X hy_ne.symm)

/-- Fan cover covers X -/
lemma fanCover_covers_X (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X) :
    ∃ e ∈ fanCover G X hX_clique x hx, e ∈ X.sym2 := by
  unfold fanCover
  -- X has 3 vertices: x, y, z. Fan cover has {xy, xz}.
  -- xy ∈ X.sym2 since x, y ∈ X
  obtain ⟨y, hy_X, hy_ne⟩ : ∃ y ∈ X, y ≠ x := by
    have : 1 < X.card := by rw [hX_3]; norm_num
    exact Finset.exists_ne_of_one_lt_card this x hx
  use s(x, y)
  constructor
  · simp only [Finset.mem_image, Finset.mem_erase]
    exact ⟨y, ⟨hy_ne, hy_X⟩, rfl⟩
  · simp only [Finset.mem_sym2_iff]
    exact ⟨hx, hy_X⟩

/-- Fan cover covers any triangle containing the apex -/
lemma fanCover_covers_apex_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_3 : t.card = 3)
    (hx_t : x ∈ t) (h_share : sharesEdgeWith t X) :
    ∃ e ∈ fanCover G X hX_clique x hx, e ∈ t.sym2 := by
  -- t shares edge with X, and x ∈ t ∩ X
  -- So t contains edge {x, w} for some w ∈ X
  have h_two : (t ∩ X).card ≥ 2 := shares_edge_implies_two_vertices t X h_share
  -- Get another vertex in t ∩ X besides x
  have hx_inter : x ∈ t ∩ X := Finset.mem_inter.mpr ⟨hx_t, hx⟩
  obtain ⟨w, hw_inter, hw_ne⟩ : ∃ w ∈ t ∩ X, w ≠ x := by
    have h_card : 1 < (t ∩ X).card := h_two
    exact Finset.exists_ne_of_one_lt_card h_card x hx_inter
  have hw_t : w ∈ t := (Finset.mem_inter.mp hw_inter).1
  have hw_X : w ∈ X := (Finset.mem_inter.mp hw_inter).2
  -- Edge {x, w} is in fanCover (since w ∈ X.erase x) and in t.sym2
  use s(x, w)
  constructor
  · unfold fanCover
    simp only [Finset.mem_image, Finset.mem_erase]
    exact ⟨w, ⟨hw_ne, hw_X⟩, rfl⟩
  · simp only [Finset.mem_sym2_iff]
    exact ⟨hx_t, hw_t⟩

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. For each X ∈ M = {A, B, C, D}:
   - Get fan apex x_X by universal_fan_apex
   - Include fanCover(X, x_X) = 2 edges
2. Total cover has ≤ 8 edges (4 × 2, minus overlaps)
3. Every triangle t is covered:
   - If t ∈ M: t = X for some X, covered by fanCover(X, x_X)
   - If t ∉ M: t is external to some X, so x_X ∈ t (by universal_fan_apex)
     → t shares edge with X and contains x_X
     → covered by fanCover_covers_apex_triangle
-/
theorem tau_le_8_adaptive (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅) :
    triangleCoveringNumber G ≤ 8 := by
  -- Get fan apexes for each element
  -- Note: We use the spine vertices as natural apexes
  -- A-apex = v1, B-apex = v1 or v2, C-apex = v2 or v3, D-apex = v3
  sorry

end