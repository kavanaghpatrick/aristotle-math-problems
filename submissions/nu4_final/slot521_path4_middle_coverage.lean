/-
PATH_4 gap: endpoint coverage (T_A ∪ T_D) propagates to middle (S_B ∪ X_BC ∪ S_C).

PROOF SKETCH for path4_middle_coverage:
1. Spine vertices: v1 = A∩B, v2 = B∩C, v3 = C∩D are distinct
2. X_BC triangles contain v2 (proven: X_BC_contains_v2)
3. Triangles in S_B not containing v1 or v2 use "external" vertex x ∉ M
4. At most 2 such externals per base edge (else 5-packing contradiction)
5. The 8-edge cover for T_A ∪ T_D includes edges incident to v1, v3
6. These plus base edges cover S_B ∪ X_BC ∪ S_C
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- Proven: cover bound
lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E' : Finset (Sym2 V)) (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2⟩
  have := Finset.min_le (Finset.mem_image_of_mem Finset.card h_mem)
  rw [WithTop.le_coe_iff] at this; aesop

-- Proven: cover union
lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  constructor
  · exact Finset.union_subset hA.1 hB.1
  · intro t ht; simp only [Finset.mem_union] at ht
    rcases ht with htA | htB
    · obtain ⟨e, heEA, het⟩ := hA.2 t htA; exact ⟨e, Finset.mem_union_left EB heEA, het⟩
    · obtain ⟨e, heEB, het⟩ := hB.2 t htB; exact ⟨e, Finset.mem_union_right EA heEB, het⟩

-- Proven: spine vertex extraction
lemma path4_spine_vertices (M : Finset (Finset V)) (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    ∃ v1 v2 v3 : V, A ∩ B = {v1} ∧ B ∩ C = {v2} ∧ C ∩ D = {v3} ∧ v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3 := by
  obtain ⟨_, _, _, _, _, _, _, hAB, hBC, hCD, hAC, hAD, hBD⟩ := hpath
  obtain ⟨v1, hv1⟩ := Finset.card_eq_one.mp hAB
  obtain ⟨v2, hv2⟩ := Finset.card_eq_one.mp hBC
  obtain ⟨v3, hv3⟩ := Finset.card_eq_one.mp hCD
  refine ⟨v1, v2, v3, hv1, hv2, hv3, ?_, ?_, ?_⟩
  all_goals { intro heq; have h1 : _ ∈ _ := by simp [← hv1, ← hv2, ← hv3, heq]
              have h2 : _ ∈ _ := by simp [← hv1, ← hv2, ← hv3, heq]
              simp_all [Finset.card_eq_zero] }

-- Proven: X_BC contains v2
lemma X_BC_contains_v2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C : Finset V) (v2 : V) (hv2 : B ∩ C = {v2}) (t : Finset V) (ht : t ∈ X_ef G B C) : v2 ∈ t := by
  simp only [X_ef, Finset.mem_filter] at ht
  by_contra hv2_not
  have h_disj : Disjoint (t ∩ B) (t ∩ C) := by
    rw [Finset.disjoint_left]; intro x hxB hxC
    have hxBC : x ∈ B ∩ C := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxB).2, (Finset.mem_inter.mp hxC).2⟩
    rw [hv2] at hxBC; simp only [Finset.mem_singleton] at hxBC
    exact hv2_not (hxBC ▸ (Finset.mem_inter.mp hxB).1)
  have h_card : (t ∩ B).card + (t ∩ C).card ≤ t.card := by
    rw [← Finset.card_union_of_disjoint h_disj]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  linarith [ht.1.card_eq, ht.2.1, ht.2.2]

-- Proven: Te = Se ∪ bridges
lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G M e ∪ (trianglesSharingEdge G e).filter
      (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2) := by
  ext t; simp only [Finset.mem_union, S_e, trianglesSharingEdge, Finset.mem_filter]
  constructor
  · intro ht; by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- Proven: X_ef empty when disjoint
lemma X_ef_empty_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (h_disj : Disjoint e f) : X_ef G e f = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]; intro t ht
  simp only [X_ef, Finset.mem_filter] at ht
  have h_card : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
    rw [← Finset.card_union_of_disjoint]; apply Finset.card_le_card
    exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    exact Finset.disjoint_of_subset_right Finset.inter_subset_right
      (Finset.disjoint_of_subset_left Finset.inter_subset_right h_disj)
  linarith [ht.1.card_eq, ht.2.1, ht.2.2]

-- Proven: triangle card is 3
lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 := ht.card_eq

-- Proven: packing element is triangle
lemma packing_mem_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (e : Finset V) (he : e ∈ M) :
    e ∈ G.cliqueFinset 3 := hM.1 he

-- Key structural lemma: S_B triangles contain v1 or v2 or use external
lemma S_B_vertex_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (B : Finset V) (hB : B ∈ M)
    (v1 v2 : V) (hv1 : v1 ∈ B) (hv2 : v2 ∈ B) (hne : v1 ≠ v2)
    (t : Finset V) (ht : t ∈ S_e G M B) (hv1_not : v1 ∉ t) (hv2_not : v2 ∉ t) :
    ∃ b x : V, b ∈ B ∧ b ≠ v1 ∧ b ≠ v2 ∧ x ∉ B ∧ {v1, v2, b} = B ∧
    (t ∩ B).card = 2 ∧ v1 ∉ t ∧ v2 ∉ t := by
  sorry

-- Proven: subadditivity
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- Full proof in slot262

-- Key: at most 2 externals per base edge (else 5-packing)
lemma base_externals_le_2_or_5packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M)
    (b1 b2 : V) (hb1 : b1 ∈ e) (hb2 : b2 ∈ e) (hne : b1 ≠ b2)
    (externals : Finset (Finset V))
    (h_ext : ∀ t ∈ externals, t ∈ S_e G M e ∧ {b1, b2} ⊆ t ∧ t \ e ≠ ∅)
    (h_card : externals.card ≥ 3) :
    ∃ M5 : Finset (Finset V), M5.card = 5 ∧ isTrianglePacking G M5 := by
  sorry

/--
MAIN LEMMA: Middle coverage from endpoint cover.

Given E' covering T_A ∪ T_D with |E'| ≤ 8, either:
- Some subset covers S_B ∪ X_BC ∪ S_C, OR
- A 5-packing exists (contradicting ν=4)
-/
lemma path4_middle_coverage (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (E' : Finset (Sym2 V)) (hE' : E' ⊆ G.edgeFinset) (hE'_card : E'.card ≤ 8)
    (hE'_cover : isTriangleCover G (trianglesSharingEdge G A ∪ trianglesSharingEdge G D) E') :
    (∃ E'' ⊆ E', isTriangleCover G (S_e G M B ∪ X_ef G B C ∪ S_e G M C) E'') ∨
    (∃ M5, M5.card = 5 ∧ isTrianglePacking G M5) := by
  /-
  PROOF SKETCH:
  1. Get spine vertices v1, v2, v3
  2. X_BC triangles contain v2 - need edges incident to v2
  3. S_B triangles either contain v1 (covered by X_AB ⊆ T_A) or v2 or use external
  4. S_C triangles either contain v3 (covered by X_CD ⊆ T_D) or v2 or use external
  5. Count externals: if ≥ 3 on any base, get 5-packing
  6. Otherwise, base edges (≤ 2 per triangle) plus v2-incident edges suffice
  -/
  obtain ⟨v1, v2, v3, hv1, hv2, hv3, h12, h23, h13⟩ := path4_spine_vertices M A B C D hpath
  by_cases h_middle_empty : S_e G M B ∪ X_ef G B C ∪ S_e G M C = ∅
  · left; exact ⟨∅, Finset.empty_subset E', ⟨Finset.empty_subset _, fun t ht => (h_middle_empty ▸ ht : t ∈ (∅ : Finset _)).elim⟩⟩
  · sorry

-- Final theorem: PATH_4 τ ≤ 8
theorem path4_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by sorry

end
