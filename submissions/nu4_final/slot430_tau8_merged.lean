/-
  slot430_tau8_merged.lean

  MERGED: slot427 goals + slot429 proven scaffolding

  This combines:
  - The τ ≤ 8 assembly structure from slot427
  - The 12 proven lemmas from slot429 (Aristotle output aa115d86)

  KEY PROVEN LEMMAS FROM slot429:
  ✅ triangle_classification - every triangle is M, S_e, or bridge
  ✅ exists_two_edges_cover_Se - 2 edges cover element + S_e externals
  ✅ bridge_contains_shared - bridges contain shared vertex
  ✅ middle_no_base_externals - middle externals contain spine
  ✅ active_triangle_disjoint_from_disjoint_member - no cross-contamination
  ✅ triangle_ne_implies_inter_card_le_2 - distinct triangles share ≤2 vertices

  TIER: 2 (assembly with proven scaffolding)
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.mathlibStandardSet false

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot429)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def Bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (E : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G E).filter (fun T => T ≠ E ∧ ∃ F ∈ M, F ≠ E ∧ (T ∩ F).card ≥ 2)

def ActiveTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (E : Finset V) : Finset (Finset V) :=
  S_e G M E ∪ Bridges G M E

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS FROM slot429 (Aristotle aa115d86)
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

lemma bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : (T ∩ E).card ≥ 2) (hTF : (T ∩ F).card ≥ 2) :
    v ∈ T := by
  contrapose! hTE; simp_all +decide [Finset.ext_iff]
  have h_inter : #(T ∩ E) + #(T ∩ F) ≤ 3 := by
    rw [← Finset.card_union_add_card_inter]
    exact le_trans (add_le_add (Finset.card_le_card (show T ∩ E ∪ T ∩ F ⊆ T from Finset.union_subset (Finset.inter_subset_left) (Finset.inter_subset_left))) (Finset.card_le_card (show T ∩ E ∩ (T ∩ F) ⊆ ∅ from by aesop))) (by simp +decide [hT.card_eq])
  linarith

lemma middle_no_base_externals (B : Finset V) (v1 v2 b3 : V)
    (hB : B = {v1, v2, b3})
    (h12 : v1 ≠ v2) (h13 : v1 ≠ b3) (h23 : v2 ≠ b3)
    (T : Finset V) (hT_card : T.card = 3)
    (hT_share : 2 ≤ (T ∩ B).card) :
    v1 ∈ T ∨ v2 ∈ T := by
  by_contra h_contra
  have h_inter : T ∩ B ⊆ {b3} := by intros x hx; aesop
  exact hT_share.not_lt (lt_of_le_of_lt (Finset.card_le_card h_inter) (by simp +decide [*]))

lemma triangle_ne_implies_inter_card_le_2 (A B : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (h_ne : A ≠ B) :
    (A ∩ B).card ≤ 2 := by
  have h_inter_lt_3 : (A ∩ B).card < 3 := by
    have h_inter_lt_3 : A ∩ B ⊂ A := by
      simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
      exact Finset.not_subset.mp fun h => h_ne <| Finset.eq_of_subset_of_card_le h (by linarith)
    exact lt_of_lt_of_le (Finset.card_lt_card h_inter_lt_3) hA.le
  apply Nat.le_of_lt_succ h_inter_lt_3

lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨
    (∃ E ∈ M, T ∈ S_e G M E) ∨
    (∃ E F : Finset V, E ∈ M ∧ F ∈ M ∧ E ≠ F ∧ (T ∩ E).card ≥ 2 ∧ (T ∩ F).card ≥ 2) := by
  by_cases hT_in_M : T ∈ M <;> simp_all +decide [S_e]
  obtain ⟨E, hE₁, hE₂⟩ := hMaximal T hT hT_in_M
  by_cases hE₃ : ∃ F ∈ M, F ≠ E ∧ 2 ≤ #(T ∩ F)
  · exact Or.inr ⟨E, hE₁, hE₃.choose, hE₃.choose_spec.1, Ne.symm hE₃.choose_spec.2.1, hE₂, hE₃.choose_spec.2.2⟩
  · refine' Or.inl ⟨E, hE₁, _, _, _⟩ <;> simp_all +decide [trianglesSharingEdge]
    · aesop_cat
    · exact fun f hf hfE => Nat.le_of_lt_succ (hE₃ f hf hfE)

/-- KEY LEMMA: 2 edges cover element + all S_e externals -/
lemma exists_two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (E : Finset V) (hE : E ∈ M) :
    ∃ C ⊆ E.sym2, C.card ≤ 2 ∧ (∀ T ∈ insert E (S_e G M E), ∃ e ∈ C, e ∈ T.sym2) := by
  have := hM.1 hE; simp_all +decide [SimpleGraph.cliqueFinset]
  rcases this with ⟨hE₁, hE₂⟩; rcases Finset.card_eq_three.mp hE₂ with ⟨u, v, w, hu, hv, hw, h⟩; simp_all +decide [Finset.subset_iff]
  refine' ⟨{s(u, v), s(w, w)}, _, _, _, _⟩ <;> simp +decide [*]
  intro a ha
  have h_inter : (a ∩ {u, v, w}).card ≥ 2 := by
    exact Finset.mem_filter.mp ha |>.2.2 |> fun h => Finset.mem_filter.mp (Finset.mem_filter.mp ha |>.1) |>.2 |> fun h' => by aesop
  generalize_proofs at *
  contrapose! h_inter; simp_all +decide [Finset.ext_iff]
  exact lt_of_le_of_lt (Finset.card_le_one.mpr (by aesop)) (by decide)

lemma active_triangle_disjoint_from_disjoint_member (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A F : Finset V) (hA : A ∈ M) (hF : F ∈ M) (h_disj : Disjoint A F)
    (T : Finset V) (hT : T ∈ ActiveTriangles G M A) :
    (T ∩ F).card ≤ 1 := by
  have h_inter_le_two : (T ∩ F).card ≤ 2 := by
    have h_inter_le_two : T.card = 3 ∧ F.card = 3 := by
      unfold ActiveTriangles at hT
      have hT_clique : T ∈ G.cliqueFinset 3 := by
        have hT_clique : T ∈ trianglesSharingEdge G A := by
          unfold S_e Bridges at hT; aesop
        exact Finset.mem_filter.mp hT_clique |>.1
      exact ⟨Finset.mem_filter.mp hT_clique |>.2.2, hM.1 hF |> fun h => Finset.mem_filter.mp h |>.2.2⟩
    apply triangle_ne_implies_inter_card_le_2 T F h_inter_le_two.left h_inter_le_two.right
    rintro rfl
    unfold ActiveTriangles at hT; simp_all +decide [Finset.disjoint_left]
    unfold S_e Bridges at hT; simp_all +decide [Finset.disjoint_left]
    cases hT <;> simp_all +decide [trianglesSharingEdge]
    · grind
    · exact absurd (Finset.card_le_card (show T ∩ A ⊆ ∅ from fun x hx => by aesop)) (by aesop)
  interval_cases _ : #(T ∩ F) <;> simp_all +decide
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.1 (by linarith); simp_all +decide [Finset.disjoint_left]
  unfold ActiveTriangles at hT; simp_all +decide [Finset.disjoint_left]
  unfold S_e Bridges at hT; simp_all +decide [Finset.disjoint_left]
  obtain h | h := hT <;> simp_all +decide [trianglesSharingEdge]
  · exact absurd (h.2.2 F hF (by aesop)) (by linarith)
  · have h_card_inter : T ∩ A ⊆ T \ ({v, w} : Finset V) := by grind
    have := Finset.card_le_card h_card_inter; simp_all +decide [Finset.card_sdiff]
    have := h.1.1.2; simp_all +decide [Finset.card_sdiff]
    linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 SPECIFIC LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- PATH_4 configuration -/
def isPATH4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V) : Prop :=
  A = {v₁, a₂, a₃} ∧
  B = {v₁, v₂, b₃} ∧
  C = {v₂, v₃, c₃} ∧
  D = {v₃, d₂, d₃} ∧
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
  v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
  v₁ ≠ b₃ ∧ v₂ ≠ b₃ ∧
  v₂ ≠ c₃ ∧ v₃ ≠ c₃ ∧
  v₃ ≠ d₂ ∧ v₃ ≠ d₃ ∧ d₂ ≠ d₃ ∧
  A ∩ B = {v₁} ∧
  B ∩ C = {v₂} ∧
  C ∩ D = {v₃} ∧
  A ∈ G.cliqueFinset 3 ∧
  B ∈ G.cliqueFinset 3 ∧
  C ∈ G.cliqueFinset 3 ∧
  D ∈ G.cliqueFinset 3

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE COVERAGE (from multi-agent debate insight)
-- ══════════════════════════════════════════════════════════════════════════════

/-
KEY INSIGHT (Bridge-External Equivalence):
Bridges using spoke edge {v₁, aᵢ} ARE Type v₁-aᵢ externals of A.
When endpoint's selection omits that spoke (because Type is empty),
NO bridges need that spoke - they don't exist!
-/

/-- For adjacent elements E, F sharing vertex v, any bridge T contains v -/
lemma bridge_in_active_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E F : Finset V) (v : V)
    (hE : E ∈ M) (hF : F ∈ M) (hEF : E ∩ F = {v})
    (T : Finset V) (hT_bridge : T ∈ Bridges G M E)
    (hT_to_F : (T ∩ F).card ≥ 2) :
    v ∈ T := by
  have hT_clq : T ∈ G.cliqueFinset 3 := by
    unfold Bridges trianglesSharingEdge at hT_bridge
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hT_bridge).1).1
  have hTE : (T ∩ E).card ≥ 2 := by
    unfold Bridges trianglesSharingEdge at hT_bridge
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hT_bridge).1).2
  exact bridge_contains_shared G E F v hEF T hT_clq hTE hT_to_F

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF STRUCTURE:
1. By triangle_classification, every triangle is: in M, S_e external, or bridge
2. By exists_two_edges_cover_Se, 2 edges cover each element + its S_e externals
3. By bridge_contains_shared + middle_no_base_externals, bridges are covered
4. Total: 4 elements × 2 edges = 8 edges
-/

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hPath : isPATH4 G A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : M = {A, B, C, D})
    (hPacking : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2) :
    ∃ (cover : Finset (Sym2 V)),
      isTriangleCover G cover ∧
      cover.card ≤ 8 := by
  -- Extract PATH_4 structure
  obtain ⟨hA, hB, hC, hD, hv12, hv13, hv23, hv1a2, hv1a3, ha23, hv1b3, hv2b3,
          hv2c3, hv3c3, hv3d2, hv3d3, hd23, hAB, hBC, hCD, hA_clq, hB_clq, hC_clq, hD_clq⟩ := hPath

  -- Get 2-edge covers for each element using exists_two_edges_cover_Se
  obtain ⟨CA, hCA_sub, hCA_card, hCA_covers⟩ := exists_two_edges_cover_Se G M hPacking A (by rw [hM]; simp)
  obtain ⟨CB, hCB_sub, hCB_card, hCB_covers⟩ := exists_two_edges_cover_Se G M hPacking B (by rw [hM]; simp)
  obtain ⟨CC, hCC_sub, hCC_card, hCC_covers⟩ := exists_two_edges_cover_Se G M hPacking C (by rw [hM]; simp)
  obtain ⟨CD', hCD_sub, hCD_card, hCD_covers⟩ := exists_two_edges_cover_Se G M hPacking D (by rw [hM]; simp)

  -- Build the cover as union of all selections
  let cover := CA ∪ CB ∪ CC ∪ CD'

  use cover
  constructor
  · -- isTriangleCover
    constructor
    · -- cover ⊆ G.edgeFinset
      intro e he
      simp only [cover, mem_union] at he
      rcases he with (((he | he) | he) | he)
      · have := hCA_sub he
        simp only [Finset.mem_sym2_iff] at this
        obtain ⟨a, ha, b, hb, hab⟩ := this
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hA_clq
        rw [hA] at ha hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
          try exact hA_clq.1 (by rw [hA]; simp) (by rw [hA]; simp [hv1a2, hv1a3, ha23]) (by assumption)
        all_goals { rw [Sym2.eq_swap] at hab; exact hA_clq.1 (by rw [hA]; simp [hv1a2, hv1a3, ha23]) (by rw [hA]; simp) hab }
      · have := hCB_sub he
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        simp only [Finset.mem_sym2_iff] at this
        obtain ⟨a, ha, b, hb, hab⟩ := this
        rw [hB] at ha hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
          try exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hv12, hv1b3, hv2b3]) (by assumption)
        all_goals { rw [Sym2.eq_swap] at hab; exact hB_clq.1 (by rw [hB]; simp [hv12, hv1b3, hv2b3]) (by rw [hB]; simp) hab }
      · have := hCC_sub he
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hC_clq
        simp only [Finset.mem_sym2_iff] at this
        obtain ⟨a, ha, b, hb, hab⟩ := this
        rw [hC] at ha hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
          try exact hC_clq.1 (by rw [hC]; simp) (by rw [hC]; simp [hv23, hv2c3, hv3c3]) (by assumption)
        all_goals { rw [Sym2.eq_swap] at hab; exact hC_clq.1 (by rw [hC]; simp [hv23, hv2c3, hv3c3]) (by rw [hC]; simp) hab }
      · have := hCD_sub he
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hD_clq
        simp only [Finset.mem_sym2_iff] at this
        obtain ⟨a, ha, b, hb, hab⟩ := this
        rw [hD] at ha hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
          try exact hD_clq.1 (by rw [hD]; simp) (by rw [hD]; simp [hv3d2, hv3d3, hd23]) (by assumption)
        all_goals { rw [Sym2.eq_swap] at hab; exact hD_clq.1 (by rw [hD]; simp [hv3d2, hv3d3, hd23]) (by rw [hD]; simp) hab }
    · -- Every triangle is covered
      intro T hT
      -- Use triangle_classification
      rcases triangle_classification G M hPacking hMaximal T hT with hT_M | ⟨E, hE_M, hT_Se⟩ | ⟨E, F, hE_M, hF_M, hEF_ne, hTE, hTF⟩
      · -- T ∈ M: covered by that element's selection
        rw [hM] at hT_M
        simp only [mem_insert, mem_singleton] at hT_M
        rcases hT_M with rfl | rfl | rfl | rfl
        · obtain ⟨e, he_CA, he_T⟩ := hCA_covers A (mem_insert_self A _)
          use e, (by simp [cover, he_CA]), he_T
        · obtain ⟨e, he_CB, he_T⟩ := hCB_covers B (mem_insert_self B _)
          use e, (by simp [cover, he_CB]), he_T
        · obtain ⟨e, he_CC, he_T⟩ := hCC_covers C (mem_insert_self C _)
          use e, (by simp [cover, he_CC]), he_T
        · obtain ⟨e, he_CD, he_T⟩ := hCD_covers D (mem_insert_self D _)
          use e, (by simp [cover, he_CD]), he_T
      · -- T ∈ S_e(E): covered by E's selection
        rw [hM] at hE_M
        simp only [mem_insert, mem_singleton] at hE_M
        rcases hE_M with rfl | rfl | rfl | rfl
        · obtain ⟨e, he_CA, he_T⟩ := hCA_covers T (mem_insert_of_mem hT_Se)
          use e, (by simp [cover, he_CA]), he_T
        · obtain ⟨e, he_CB, he_T⟩ := hCB_covers T (mem_insert_of_mem hT_Se)
          use e, (by simp [cover, he_CB]), he_T
        · obtain ⟨e, he_CC, he_T⟩ := hCC_covers T (mem_insert_of_mem hT_Se)
          use e, (by simp [cover, he_CC]), he_T
        · obtain ⟨e, he_CD, he_T⟩ := hCD_covers T (mem_insert_of_mem hT_Se)
          use e, (by simp [cover, he_CD]), he_T
      · -- T is a bridge between E and F
        -- By PATH_4 structure, E and F must be adjacent
        -- Bridge contains shared vertex, so covered by spine edge selection
        -- This is the key insight from the multi-agent debate
        rw [hM] at hE_M hF_M
        simp only [mem_insert, mem_singleton] at hE_M hF_M
        -- Case analysis on which pair (E, F) is
        -- Adjacent pairs: (A,B), (B,C), (C,D)
        -- Non-adjacent pairs can't have bridges (would share edge with middle element)
        sorry
  · -- cover.card ≤ 8
    calc cover.card = (CA ∪ CB ∪ CC ∪ CD').card := rfl
      _ ≤ CA.card + CB.card + CC.card + CD'.card := by
          calc (CA ∪ CB ∪ CC ∪ CD').card
              ≤ (CA ∪ CB ∪ CC).card + CD'.card := card_union_le _ _
            _ ≤ (CA ∪ CB).card + CC.card + CD'.card := by linarith [card_union_le (CA ∪ CB) CC]
            _ ≤ CA.card + CB.card + CC.card + CD'.card := by linarith [card_union_le CA CB]
      _ ≤ 2 + 2 + 2 + 2 := by linarith
      _ = 8 := by norm_num

end
