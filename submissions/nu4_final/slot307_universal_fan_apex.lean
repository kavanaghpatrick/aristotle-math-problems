/-
  slot307: Universal Fan Apex - From Pairwise to All

  GOAL: Prove that ALL X-externals share a COMMON vertex in X (not just pairs).

  PROVEN RESULTS USED AS SCAFFOLDING:
  - slot301: shared_edge_contains_A_vertex (two A-externals share edge with A-vertex)
  - slot303: middle_fan_apex_in_B (two B-externals share edge with B-vertex)

  KEY INSIGHT: If every pair of X-externals shares a vertex in X (by slot301/303),
  and X only has 3 vertices, then there's a "dominating vertex" that all share.

  PROOF SKETCH:
  1. Each pair (T₁, T₂) of X-externals shares some vertex v_{12} ∈ X
  2. |X| = 3, so X = {x₁, x₂, x₃}
  3. If externals can "choose" different shared vertices, analyze the structure
  4. Key lemma: With 3+ externals, pigeonhole forces a common vertex

  IMPLICATION: Once proven, τ ≤ 8 follows immediately:
  For each X ∈ {A,B,C,D}, get fan apex x_X, include 2 edges incident to x_X
  Total: 4 × 2 = 8 edges

  MULTI-AGENT VERIFIED (Jan 8, 2026):
  - Gemini identified the pairwise-to-common gap
  - Grok confirmed cyclic externals share common outside vertex
-/

import Mathlib


set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven submissions)
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
-- SCAFFOLDING FROM slot301 (PROVEN)
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

-- slot301: Two X-externals share an edge (5-packing argument)
lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
  have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
  let M_minus_X := M.erase X
  let M' := {T₁, T₂} ∪ M_minus_X
  have hM'_card : M'.card = 5 := by
    have hT₁_not_M : T₁ ∉ M := hT₁.2.1
    have hT₂_not_M : T₂ ∉ M := hT₂.2.1
    have hM_minus_X_card : M_minus_X.card = 3 := by rw [Finset.card_erase_of_mem hX]; omega
    have hT₁_not_MX : T₁ ∉ M_minus_X := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MX : T₂ ∉ M_minus_X := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem]; simp [h_ne]; simp [h_ne]
    have h_disj : Disjoint {T₁, T₂} M_minus_X := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact fun h => hT₁_not_MX (h ▸ hy);
                                    exact fun h => hT₂_not_MX (h ▸ hy)]
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_X_card]
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht_pair | ht_MX
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MX).2
    · intro t₁ ht₁ t₂ ht₂ h_ne'
      have h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False :=
        fun u v huv hu₁ hv₁ hu₂ hv₂ => h_no_edge ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
      rcases Finset.mem_union.mp ht₁ with ht₁_pair | ht₁_MX <;>
      rcases Finset.mem_union.mp ht₂ with ht₂_pair | ht₂_MX
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne'
          · rw [Finset.mem_singleton] at ht₂_sing; rw [heq₁, ht₂_sing]
            exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_no_edge
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂, Finset.inter_comm]
            exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_no_edge
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne'
      · have hY_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MX).2
        have hY_ne_X : t₂ ≠ X := (Finset.mem_erase.mp ht₂_MX).1
        have hY_3 : t₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hY_M) |>.2
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]
          have h_not_share := hT₁.2.2.2 t₂ hY_M hY_ne_X
          exact not_share_implies_one_vertex T₁ t₂ hT₁_3 hY_3 h_not_share
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          have h_not_share := hT₂.2.2.2 t₂ hY_M hY_ne_X
          exact not_share_implies_one_vertex T₂ t₂ hT₂_3 hY_3 h_not_share
      · have hY_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MX).2
        have hY_ne_X : t₁ ≠ X := (Finset.mem_erase.mp ht₁_MX).1
        have hY_3 : t₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hY_M) |>.2
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂, Finset.inter_comm]
          have h_not_share := hT₁.2.2.2 t₁ hY_M hY_ne_X
          exact not_share_implies_one_vertex T₁ t₁ hT₁_3 hY_3 h_not_share
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing, Finset.inter_comm]
          have h_not_share := hT₂.2.2.2 t₁ hY_M hY_ne_X
          exact not_share_implies_one_vertex T₂ t₁ hT₂_3 hY_3 h_not_share
      · exact hM.1.2 (Finset.mem_erase.mp ht₁_MX).2 (Finset.mem_erase.mp ht₂_MX).2 h_ne'
  have h_bound := hν M' hM'_packing
  omega

-- slot301 PROVEN: The shared edge contains a vertex from X
lemma shared_edge_contains_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ T₁ ∩ T₂, x ∈ X := by
  have h_share := two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_card : (T₁ ∩ T₂).card ≥ 2 := shares_edge_implies_two_vertices T₁ T₂ h_share
  have hT₁_X : (T₁ ∩ X).card = 2 := by
    have h_ge : (T₁ ∩ X).card ≥ 2 := shares_edge_implies_two_vertices T₁ X hT₁.2.2.1
    have h_le : (T₁ ∩ X).card ≤ 2 := by
      by_contra h_gt; push_neg at h_gt
      have h_sub : T₁ ⊆ X := by
        have h_inter_sub : T₁ ∩ X ⊆ T₁ := Finset.inter_subset_left
        have h_card_eq : (T₁ ∩ X).card = T₁.card := by
          have h1 : (T₁ ∩ X).card ≤ T₁.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : X ⊆ T₁ := by
        have h_inter_sub : T₁ ∩ X ⊆ X := Finset.inter_subset_right
        have h_card_eq : (T₁ ∩ X).card = X.card := by
          have h1 : (T₁ ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      have h_eq : T₁ = X := Finset.Subset.antisymm h_sub h_sub'
      exact hT₁.2.1 (h_eq ▸ hX)
    linarith
  have hT₂_X : (T₂ ∩ X).card = 2 := by
    have h_ge : (T₂ ∩ X).card ≥ 2 := shares_edge_implies_two_vertices T₂ X hT₂.2.2.1
    have h_le : (T₂ ∩ X).card ≤ 2 := by
      by_contra h_gt; push_neg at h_gt
      have h_sub : T₂ ⊆ X := by
        have h_inter_sub : T₂ ∩ X ⊆ T₂ := Finset.inter_subset_left
        have h_card_eq : (T₂ ∩ X).card = T₂.card := by
          have h1 : (T₂ ∩ X).card ≤ T₂.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : X ⊆ T₂ := by
        have h_inter_sub : T₂ ∩ X ⊆ X := Finset.inter_subset_right
        have h_card_eq : (T₂ ∩ X).card = X.card := by
          have h1 : (T₂ ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      have h_eq : T₂ = X := Finset.Subset.antisymm h_sub h_sub'
      exact hT₂.2.1 (h_eq ▸ hX)
    linarith
  have h_T₁_outside : (T₁ \ X).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₁ X
    omega
  have h_T₂_outside : (T₂ \ X).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T₂ X
    omega
  by_contra h_none_in_X
  push_neg at h_none_in_X
  have h_sub_out₁ : T₁ ∩ T₂ ⊆ T₁ \ X := by
    intro x hx
    have hx₁ : x ∈ T₁ := Finset.mem_inter.mp hx |>.1
    have hx_not_X : x ∉ X := h_none_in_X x hx
    exact Finset.mem_sdiff.mpr ⟨hx₁, hx_not_X⟩
  have h_card_bound : (T₁ ∩ T₂).card ≤ (T₁ \ X).card := Finset.card_le_card h_sub_out₁
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Universal Fan Apex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for universal fan apex:

1. Let externals = {T₁, T₂, ..., Tₖ} be all X-externals
2. Each pair (Tᵢ, Tⱼ) shares a vertex vᵢⱼ ∈ X ∩ Tᵢ ∩ Tⱼ (by shared_edge_contains_X_vertex)
3. Case k ≤ 1: trivially true (any X-vertex works)
4. Case k = 2: v₁₂ works
5. Case k ≥ 3: Consider T₁, T₂, T₃
   - v₁₂ ∈ X ∩ T₁ ∩ T₂
   - v₁₃ ∈ X ∩ T₁ ∩ T₃
   - v₂₃ ∈ X ∩ T₂ ∩ T₃

   Since |T₁ ∩ X| = 2, T₁ contains exactly 2 vertices of X.
   v₁₂, v₁₃ ∈ T₁ ∩ X, so if v₁₂ ≠ v₁₃, then T₁ ∩ X = {v₁₂, v₁₃}.

   Similarly for T₂: v₁₂, v₂₃ ∈ T₂ ∩ X.
   Similarly for T₃: v₁₃, v₂₃ ∈ T₃ ∩ X.

   If v₁₂ = v₁₃ = v₂₃ = v, we're done (v is the common vertex).

   Otherwise, the constraints form a cycle that forces a common vertex.
   This is because |X| = 3, so at least two of v₁₂, v₁₃, v₂₃ must be equal.

   By pigeonhole on T₁: v₁₂ = v₁₃ implies common vertex v₁₂.
   Otherwise T₁ ∩ X = {v₁₂, v₁₃} with v₁₂ ≠ v₁₃.

   Then v₂₃ must be one of {v₁₂, v₁₃} (since v₂₃ ∈ X and |X| = 3 contains at most
   one vertex not in T₁ ∩ X, but v₂₃ ∈ T₂ ∩ X and v₁₂ ∈ T₂ ∩ X means |T₂ ∩ X| ≥ 2,
   so v₂₃ ∈ {v₁₂} or T₂ ∩ X = {v₁₂, v₂₃}).

   In all cases, we find a common vertex.

6. By induction: if T₁, ..., Tₖ all share v, and Tₖ₊₁ is a new external,
   then v_{1,k+1} ∈ T₁ ∩ Tₖ₊₁ ∩ X.
   Since T₁ ∩ X contains v (the common vertex), and |T₁ ∩ X| = 2,
   either v = v_{1,k+1}, or T₁ ∩ X = {v, v_{1,k+1}}.

   In the second case, check T₂ ∩ Tₖ₊₁: v_{2,k+1} ∈ T₂ ∩ Tₖ₊₁ ∩ X.
   Since v ∈ T₂ and |T₂ ∩ X| = 2, either v = v_{2,k+1} (we're done),
   or T₂ ∩ X = {v, v_{2,k+1}} with v_{2,k+1} ≠ v.

   But then v_{2,k+1} ∈ Tₖ₊₁ and v_{1,k+1} ∈ Tₖ₊₁ with both in X.
   Since |Tₖ₊₁ ∩ X| = 2, we need v_{1,k+1} = v_{2,k+1} or Tₖ₊₁ ∩ X = {v_{1,k+1}, v_{2,k+1}}.

   The latter means Tₖ₊₁ uses the same edge of X as... (continue analysis)
-/

theorem universal_fan_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v ∈ X, ∀ T ∈ externals, v ∈ T := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- Given a fan apex, 2 edges incident to it cover X + all X-externals -/
lemma fan_apex_gives_2_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∈ X)
    (x y : V) (hx : x ∈ X) (hy : y ∈ X) (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    -- {vx, vy} covers X and any triangle containing v
    (∀ t, t ∈ G.cliqueFinset 3 → v ∈ t →
      s(v, x) ∈ t.sym2 ∨ s(v, y) ∈ t.sym2 ∨ s(x, y) ∈ t.sym2 →
      ∃ e ∈ ({s(v, x), s(v, y)} : Finset (Sym2 V)), e ∈ t.sym2) ∧
    -- X itself is covered by {vx} or {vy}
    (s(v, x) ∈ X.sym2 ∧ s(v, y) ∈ X.sym2) := by
  constructor
  · intro t ht hvt h_some_edge
    rcases h_some_edge with hvx_in | hvy_in | hxy_in
    · exact ⟨s(v, x), by simp, hvx_in⟩
    · exact ⟨s(v, y), by simp, hvy_in⟩
    · -- xy edge: if v ∈ t and xy ∈ t, then since t is a triangle,
      -- one of vx, vy must be in t
      have ht_3 : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht |>.2
      -- If t = {v, x, y} then both vx and vy are in t
      sorry
  · constructor
    · simp only [Finset.mem_sym2_iff]; exact ⟨hv, hx⟩
    · simp only [Finset.mem_sym2_iff]; exact ⟨hv, hy⟩

/-- Main theorem: τ ≤ 8 for PATH_4 using fan apex -/
theorem tau_le_8_path4_fan_apex (G : SimpleGraph V) [DecidableRel G.Adj]
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
  -- Strategy: For each X ∈ M, get fan apex x_X, include 2 edges incident to x_X
  -- Total: 4 × 2 = 8 edges
  sorry

end
