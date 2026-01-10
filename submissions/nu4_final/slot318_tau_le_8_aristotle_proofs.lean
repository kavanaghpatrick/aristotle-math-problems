/-
  slot318: τ ≤ 8 for ν = 4 - Using EXACT Aristotle-proven code

  This file contains VERBATIM proofs from Aristotle outputs:
  - slot307: two_externals_share_edge, shared_edge_contains_X_vertex
  - slot308: pairwise_externals_share_X_vertex, fanCover_card, fanCover_covers_apex_triangle
  - slot309: bridge_triangle_contains_shared_vertex, bridge_covered_if_shared_is_common

  SINGLE SORRY: main tau_le_8 theorem
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
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

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: Basic helpers (slot307)
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

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.2 ⟨u, by aesop, v, by aesop⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: two_externals_share_edge (slot307)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: pairwise_externals_share_X_vertex (slot308)
-- ══════════════════════════════════════════════════════════════════════════════

lemma pairwise_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ x ∈ X, x ∈ T₁ ∧ x ∈ T₂ := by
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

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: fanCover (slot308)
-- ══════════════════════════════════════════════════════════════════════════════

def fanCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (x : V) (hx : x ∈ X) : Finset (Sym2 V) :=
  let others := X.erase x
  others.image (fun y => s(x, y))

lemma fanCover_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X) :
    (fanCover G X hX_clique x hx).card = 2 := by
  unfold fanCover
  have h_others_card : (X.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx, hX_3]
  rw [ Finset.card_image_of_injOn, h_others_card ] ; intro y hy ; aesop;

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

lemma fanCover_covers_apex_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (x : V) (hx : x ∈ X)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_3 : t.card = 3)
    (hx_t : x ∈ t) (h_share : sharesEdgeWith t X) :
    ∃ e ∈ fanCover G X hX_clique x hx, e ∈ t.sym2 := by
  have h_two : (t ∩ X).card ≥ 2 := shares_edge_implies_two_vertices t X h_share
  have hx_inter : x ∈ t ∩ X := Finset.mem_inter.mpr ⟨hx_t, hx⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h_two
  have hw_inter : ∃ w ∈ t ∩ X, w ≠ x := by
    by_cases hax : a = x
    · exact ⟨b, hb, fun h => hab (hax ▸ h.symm)⟩
    · exact ⟨a, ha, hax⟩
  obtain ⟨w, hw_mem, hw_ne⟩ := hw_inter
  have hw_t : w ∈ t := (Finset.mem_inter.mp hw_mem).1
  have hw_X : w ∈ X := (Finset.mem_inter.mp hw_mem).2
  use s(x, w)
  constructor
  · unfold fanCover
    simp only [Finset.mem_image, Finset.mem_erase]
    exact ⟨w, ⟨hw_ne, hw_X⟩, rfl⟩
  · rw [Finset.mem_sym2_iff]
    intro z hz
    simp only [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl <;> assumption

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: bridge_triangle_contains_shared_vertex (slot309)
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hX_card : X.card = 3) (hY_card : Y.card = 3)
    (h_inter : (X ∩ Y).card = 1)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_X : sharesEdgeWith T X) (hT_share_Y : sharesEdgeWith T Y) :
    ∃ c, c ∈ X ∧ c ∈ Y ∧ c ∈ T := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h_inter
  use c
  have hc_X : c ∈ X := Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.1
  have hc_Y : c ∈ Y := Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.2
  refine ⟨hc_X, hc_Y, ?_⟩
  by_contra hc_notin_T
  have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp hT_share_X
  have h_TY : (T ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T Y |>.mp hT_share_Y
  have hT_card : T.card = 3 := by
    simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT_tri
    exact hT_tri.2.2
  have h1 : T ∩ X ⊆ X \ {c} := by
    intro v hv
    simp only [Finset.mem_inter] at hv
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hv.2, fun hvc => hc_notin_T (hvc ▸ hv.1)⟩
  have h2 : T ∩ Y ⊆ Y \ {c} := by
    intro v hv
    simp only [Finset.mem_inter] at hv
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hv.2, fun hvc => hc_notin_T (hvc ▸ hv.1)⟩
  have h3 : (X \ {c}) ∩ (Y \ {c}) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro v hv
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton] at hv
    obtain ⟨⟨hvX, hvc⟩, hvY, _⟩ := hv
    have hv_inter : v ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hvX, hvY⟩
    rw [hc] at hv_inter
    exact hvc (Finset.mem_singleton.mp hv_inter)
  have h4 : Disjoint (T ∩ X) (T ∩ Y) := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_not_mem]
    intro v hv
    simp only [Finset.mem_inter] at hv
    have hv1 : v ∈ X \ {c} := h1 (Finset.mem_inter.mpr ⟨hv.1.1, hv.1.2⟩)
    have hv2 : v ∈ Y \ {c} := h2 (Finset.mem_inter.mpr ⟨hv.2.1, hv.2.2⟩)
    have hv3 : v ∈ (X \ {c}) ∩ (Y \ {c}) := Finset.mem_inter.mpr ⟨hv1, hv2⟩
    rw [h3] at hv3
    exact Finset.not_mem_empty v hv3
  have h5 : (T ∩ X).card + (T ∩ Y).card ≤ T.card := by
    have hunion : (T ∩ X) ∪ (T ∩ Y) ⊆ T := by
      intro v hv
      cases Finset.mem_union.mp hv with
      | inl h => exact Finset.mem_inter.mp h |>.1
      | inr h => exact Finset.mem_inter.mp h |>.1
    have := Finset.card_union_of_disjoint h4
    calc (T ∩ X).card + (T ∩ Y).card
        = ((T ∩ X) ∪ (T ∩ Y)).card := this.symm
      _ ≤ T.card := Finset.card_le_card hunion
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- ARISTOTLE-PROVEN: bridge_covered_if_shared_is_common (slot309)
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_covered_if_shared_is_common (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (c : V) (hc : c ∈ X)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ G.edgeFinset) (he₂ : e₂ ∈ G.edgeFinset)
    (h_incident : ∃ u w : V, u ∈ X ∧ w ∈ X ∧ u ≠ c ∧ w ≠ c ∧ u ≠ w ∧
                  e₁ = Sym2.mk (c, u) ∧ e₂ = Sym2.mk (c, w))
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hT_share_X : sharesEdgeWith T X) (hc_in_T : c ∈ T) :
    e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  obtain ⟨u, w, hu_X, hw_X, hu_ne_c, hw_ne_c, huw, he₁_eq, he₂_eq⟩ := h_incident
  have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp hT_share_X
  have hc_inter : c ∈ T ∩ X := Finset.mem_inter.mpr ⟨hc_in_T, hc⟩
  obtain ⟨v, hv_inter, hv_ne_c⟩ : ∃ v ∈ T ∩ X, v ≠ c := by
    have : 1 < (T ∩ X).card := by linarith
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases hac : a = c
    · exact ⟨b, hb, fun h => hab (hac ▸ h.symm)⟩
    · exact ⟨a, ha, hac⟩
  have hv_T : v ∈ T := Finset.mem_inter.mp hv_inter |>.1
  have hv_X : v ∈ X := Finset.mem_inter.mp hv_inter |>.2
  have hX_form : X = {c, u, w} := by
    -- c, u, w are 3 distinct elements of 3-element set X
    have h_sub : {c, u, w} ⊆ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h_card : ({c, u, w} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; exact huw
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨hu_ne_c.symm, hw_ne_c.symm⟩
    exact (Finset.eq_of_subset_of_card_le h_sub (by rw [h_card, hX_card])).symm
  have hv_uw : v = u ∨ v = w := by
    rw [hX_form] at hv_X
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_X
    rcases hv_X with rfl | rfl | rfl
    · exact absurd rfl hv_ne_c
    · left; rfl
    · right; rfl
  have hT_card : T.card = 3 := by
    simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT
    exact hT.2.2
  have hcv_edge : Sym2.mk (c, v) ∈ T.sym2 := by
    rw [Finset.mem_sym2_iff]
    intro a ha
    simp only [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl <;> assumption
  cases hv_uw with
  | inl hvu =>
    left
    rw [he₁_eq, ← hvu]
    exact hcv_edge
  | inr hvw =>
    right
    rw [he₂_eq, ← hvw]
    exact hcv_edge

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 (SINGLE SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

Every triangle T in G falls into one of three categories:
1. T ∈ M (one of the 4 packing elements)
2. T is external to exactly one X ∈ M (shares edge with X, not with others)
3. T is a bridge triangle (shares edges with multiple M-elements)

Coverage strategy using proven lemmas:

For each X ∈ M:
- Use pairwise_externals_share_X_vertex: any two X-externals share a vertex in X
- Use fanCover: 2 edges from the "common vertex" cover X and its externals
- Use fanCover_covers_apex_triangle: if apex is in T and T shares edge with X, covered

For bridge triangles:
- Use bridge_triangle_contains_shared_vertex: bridge T contains shared vertex c
- Use bridge_covered_if_shared_is_common: if c is fanCover apex, T is covered

Total: 4 elements × 2 edges = 8 edges

The key remaining step: prove that for each pair X,Y sharing vertex c, we can
choose c as the fanCover apex for at least one of X or Y, ensuring all bridge
triangles at c are covered.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
