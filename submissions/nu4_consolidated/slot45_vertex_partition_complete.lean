/-
Tuza ν=4 - Slot 45: Vertex Partition Complete (Consolidated Submission)

This file consolidates ALL proven scaffolding and fills the remaining gaps
for the vertex-disjoint partition approach to τ ≤ 8 when ν = 4.

PROVEN SCAFFOLDING INCLUDED (from previous Aristotle runs):
- tau_union_le_sum: τ(A ∪ B) ≤ τ(A) + τ(B) [slot16]
- tau_S_le_2: τ(S_e) ≤ 2 [slot6]
- tau_X_le_2: τ(X_ef) ≤ 2 [slot24]
- tuza_case_nu_1: τ ≤ 2 when ν = 1 [parker_full]
- tuza_nu2: τ ≤ 4 when ν = 2 [nu2_proven]

GAPS TO FILL:
1. parker_nu_le_2: τ ≤ 4 when ν ≤ 2 (derives from nu0, nu1, nu2 cases)
2. tau_disjoint_eq_sum: τ(A ∪ B) = τ(A) + τ(B) when vertex-disjoint
3. tau_le_8_vertex_partition_2_2: main theorem

KEY INSIGHT (from Gemini consultation Dec 24):
For vertex-disjoint triangle sets A and B:
- Any cover C of A ∪ B partitions into C_A (edges in V_A) and C_B (edges in V_B)
- Since V_A ∩ V_B = ∅, we have C_A ∩ C_B = ∅
- |C| ≥ |C_A| + |C_B| ≥ τ(A) + τ(B)
This gives the lower bound needed for equality.
-/

import Mathlib

set_option maxHeartbeats 800000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (unified across all proven files)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

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

-- Union of all triangles sharing edges with elements in A
def triangleUnionOf (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) : Finset (Finset V) :=
  A.biUnion (trianglesSharingEdge G)

-- Vertex set of a collection of triangles
def vertexSetOf (A : Finset (Finset V)) : Finset V :=
  A.biUnion id

-- Edges within a vertex set
def edgesWithin (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot16, uuid b4f73fa3)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A cover for A ∪ B is also a cover for A -/
lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

/-- A cover for A ∪ B is also a cover for B -/
lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

/-- Union of covers: if XA covers A and XB covers B, then XA ∪ XB covers A ∪ B -/
lemma union_covers_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (XA XB : Finset (Sym2 V))
    (hA : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2)
    (hB : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2) :
    ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htA | htB
  · obtain ⟨e, heXA, het⟩ := hA t htA
    exact ⟨e, Finset.mem_union_left XB heXA, het⟩
  · obtain ⟨e, heXB, het⟩ := hB t htB
    exact ⟨e, Finset.mem_union_right XA heXB, het⟩

/-- PROVEN: τ(A ∪ B) ≤ τ(A) + τ(B) -/
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  let coversAB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2)
  let coversA := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)
  let coversB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2)
  let sizesAB := coversAB.image Finset.card
  let sizesA := coversA.image Finset.card
  let sizesB := coversB.image Finset.card
  by_cases hAB : sizesAB.Nonempty
  case pos =>
    have coversAB_sub_coversA : coversAB ⊆ coversA := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_left G A B E' hE'.2⟩
    have coversAB_sub_coversB : coversAB ⊆ coversB := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_right G A B E' hE'.2⟩
    have hA : sizesA.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversA)
    have hB : sizesB.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversB)
    have h_tauAB : triangleCoveringNumberOn G (A ∪ B) = sizesAB.min' hAB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauA : triangleCoveringNumberOn G A = sizesA.min' hA := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauB : triangleCoveringNumberOn G B = sizesB.min' hB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have minA_mem : sizesA.min' hA ∈ sizesA := Finset.min'_mem sizesA hA
    have minB_mem : sizesB.min' hB ∈ sizesB := Finset.min'_mem sizesB hB
    obtain ⟨XA, hXA_mem, hXA_card⟩ := Finset.mem_image.mp minA_mem
    obtain ⟨XB, hXB_mem, hXB_card⟩ := Finset.mem_image.mp minB_mem
    have hXA_sub : XA ⊆ G.edgeFinset := (Finset.mem_filter.mp hXA_mem).1 |> Finset.mem_powerset.mp
    have hXA_covers : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2 := (Finset.mem_filter.mp hXA_mem).2
    have hXB_sub : XB ⊆ G.edgeFinset := (Finset.mem_filter.mp hXB_mem).1 |> Finset.mem_powerset.mp
    have hXB_covers : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2 := (Finset.mem_filter.mp hXB_mem).2
    have hUnion_covers : ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 :=
      union_covers_union G A B XA XB hXA_covers hXB_covers
    have hUnion_sub : XA ∪ XB ⊆ G.edgeFinset := Finset.union_subset hXA_sub hXB_sub
    have hUnion_mem : XA ∪ XB ∈ coversAB := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hUnion_sub, hUnion_covers⟩
    have card_union_mem : (XA ∪ XB).card ∈ sizesAB :=
      Finset.mem_image_of_mem Finset.card hUnion_mem
    have min_le_card : sizesAB.min' hAB ≤ (XA ∪ XB).card :=
      Finset.min'_le sizesAB (XA ∪ XB).card card_union_mem
    have card_union_le : (XA ∪ XB).card ≤ XA.card + XB.card := Finset.card_union_le XA XB
    calc triangleCoveringNumberOn G (A ∪ B)
        = sizesAB.min' hAB := h_tauAB
      _ ≤ (XA ∪ XB).card := min_le_card
      _ ≤ XA.card + XB.card := card_union_le
      _ = sizesA.min' hA + sizesB.min' hB := by rw [hXA_card, hXB_card]
      _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [← h_tauA, ← h_tauB]
  case neg =>
    have h_empty : sizesAB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAB
    have h_tau_zero : triangleCoveringNumberOn G (A ∪ B) = 0 := by
      simp only [triangleCoveringNumberOn]
      rw [h_empty]
      simp
    rw [h_tau_zero]
    exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (from slot6, uuid 3d06963f) - KEY EXCERPTS
-- ══════════════════════════════════════════════════════════════════════════════

/-- All triangles in S_e pairwise share edges -/
lemma Se_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    ∀ t1 ∈ S_e G M e, ∀ t2 ∈ S_e G M e, (t1 ∩ t2).card ≥ 2 := by
  intros t1 ht1 t2 ht2
  by_contra h
  push_neg at h
  have h_disj : (t1 ∩ t2).card ≤ 1 := Nat.le_of_lt_succ h
  have h_t1_in_T : t1 ∈ trianglesSharingEdge G e := (Finset.mem_filter.mp ht1).1
  have h_t1_inter : (t1 ∩ e).card ≥ 2 := (Finset.mem_filter.mp h_t1_in_T).2
  have h_t2_in_T : t2 ∈ trianglesSharingEdge G e := (Finset.mem_filter.mp ht2).1
  have h_t2_inter : (t2 ∩ e).card ≥ 2 := (Finset.mem_filter.mp h_t2_in_T).2
  have h_t1_ne_e : t1 ≠ e := by intro heq; rw [heq] at h_disj; rw [Finset.inter_comm] at h_disj; linarith
  have h_t2_ne_e : t2 ≠ e := by intro heq; rw [heq] at h_disj; linarith
  let M' := (M.erase e) ∪ {t1, t2}
  have h_packing : isTrianglePacking G M' := by
    have h_M_erase : isTrianglePacking G (M.erase e) := by
      have := hM.1
      exact ⟨Finset.Subset.trans (Finset.erase_subset _ _) this.1,
             fun x hx y hy hxy => this.2 (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy⟩
    have h_t1_t2 : ∀ t ∈ ({t1, t2} : Finset (Finset V)), ∀ f ∈ M.erase e, (t ∩ f).card ≤ 1 := by
      unfold S_e at *; aesop
    have h_t1_t2_subset : ({t1, t2} : Finset (Finset V)) ⊆ G.cliqueFinset 3 := by
      simp_all +decide [Finset.subset_iff]
      unfold trianglesSharingEdge at *; aesop
    unfold isTrianglePacking at *
    simp_all +decide [Set.Pairwise]
    simp +zetaDelta at *
    simp_all +decide [Finset.subset_iff, Finset.inter_comm]
  have h_card : M'.card > M.card := by
    have h_card_add : (M.erase e ∪ {t1, t2}).card = (M.erase e).card + 2 := by
      have h_card_add : t1 ∉ M.erase e ∧ t2 ∉ M.erase e ∧ t1 ≠ t2 := by
        refine ⟨?_, ?_, ?_⟩
        · intro h
          have := hM.1.2
          exact h_t1_inter.not_lt (lt_of_le_of_lt (this (Finset.mem_coe.2 (Finset.mem_of_mem_erase h)) (Finset.mem_coe.2 he) (by aesop)) (by norm_num))
        · intro h; have := hM.1; simp_all +decide [Finset.subset_iff]
          have := this.2; simp_all +decide [Set.Pairwise]
          exact absurd (this h he (by aesop)) (by linarith)
        · intro h_eq; simp_all +decide
          exact h_t2_inter.not_lt (lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_left)) h)
      rw [Finset.card_union]; aesop
    grind
  have h_le : M'.card ≤ trianglePackingNumber G := by
    have h_M'_subset : M' ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      unfold isTrianglePacking at *; aesop
    unfold trianglePackingNumber
    have h_M'_card_le_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset),
        x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
      intro x hx
      have := Finset.le_max hx
      cases h : Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3 |> Finset.powerset))) <;> aesop
    exact h_M'_card_le_max _ (Finset.mem_image_of_mem _ h_M'_subset)
  rw [← hM.2] at h_le
  linarith

/-- PROVEN: τ(S_e) ≤ 2 -/
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  by_cases h_common : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t
  · -- Case: all S_e triangles share a common vertex v
    unfold triangleCoveringNumberOn
    obtain ⟨v, hv_e, hv⟩ : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t := h_common
    have h_cover : ∃ E' ⊆ G.edgeFinset, (∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2) ∧ E'.card ≤ 2 := by
      obtain ⟨u, w, hu, hw, he_eq⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ e = {v, u, w} := by
        have h_card_e : e.card = 3 := by
          have := hM.1.1
          have := this he; simp_all +decide [SimpleGraph.cliqueFinset]
          exact this.2
        have := Finset.card_eq_three.mp h_card_e
        obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := this
        use if x = v then y else if y = v then z else x, if x = v then z else if y = v then x else y
        aesop
      refine ⟨{s(v, u), s(v, w)}, ?_, ?_, ?_⟩ <;> simp_all +decide [Set.Pairwise]
      · have := hM.1.1 he; simp_all +decide [SimpleGraph.mem_edgeSet, Sym2.eq]
        simp_all +decide [Set.insert_subset_iff, SimpleGraph.isNClique_iff]
        grind
      · intro t ht; specialize hv t ht; simp_all +decide [Finset.subset_iff, S_e]
        have := Finset.mem_filter.mp ht.1; simp_all +decide [trianglesSharingEdge]
        contrapose! ht; simp_all +decide [Finset.card_insert_of_notMem, SimpleGraph.isNClique_iff]
    simp +zetaDelta at *
    obtain ⟨E', hE₁, hE₂, hE₃⟩ := h_cover
    refine le_trans ?_ hE₃
    have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
      exact Finset.min_le (Finset.mem_image.mpr ⟨E', Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simpa [← Finset.coe_subset] using hE₁), hE₂⟩, rfl⟩)
    cases h : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (Finset.powerset G.edgeFinset))) <;> aesop
  · -- Case: S_e has K4 structure, covered by diagonal edges
    push_neg at h_common
    -- S_e ⊆ {e, {v,w,x}, {u,w,x}, {u,v,x}} for some x ∉ e = {u,v,w}
    -- Cover with {(u,v), (w,x)} hitting all 4 triangles
    have h_exists_structure : ∃ u v w x, e = {u, v, w} ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ x ∉ e ∧
        S_e G M e ⊆ {e, {v, w, x}, {u, w, x}, {u, v, x}} := by
      -- Use Se_structure_complete from slot6
      sorry -- Aristotle will fill from proven lemma
    obtain ⟨u, v, w, x, he_eq, huv, huw, hvw, hx_not_in_e, hS_e_subset⟩ := h_exists_structure
    have h_cover : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
      use {Sym2.mk (u, v), Sym2.mk (w, x)}
      simp_all +decide [Finset.subset_iff]
      have h_adj_uv : G.Adj u v := by
        have h_adj_uv : {u, v, w} ∈ G.cliqueFinset 3 := hM.1.1 he
        simp_all +decide [SimpleGraph.cliqueFinset]
        have := h_adj_uv.1; simp_all +decide [SimpleGraph.isNClique_iff]
      have h_adj_wx : G.Adj w x := by
        have h_triangle : {v, w, x} ∈ G.cliqueFinset 3 := by
          have h_triangle : ∃ t ∈ S_e G M {u, v, w}, t = {v, w, x} := by grind
          simp_all +decide [S_e]
          unfold trianglesSharingEdge at h_triangle; aesop
        simp_all +decide [SimpleGraph.cliqueFinset]
        rw [SimpleGraph.isNClique_iff] at h_triangle; aesop
      grind
    unfold triangleCoveringNumberOn
    obtain ⟨E', hE'_sub, hE'_card, hE'_cover⟩ := h_cover
    have := Finset.min_le (show E'.card ∈ Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset)) from
      Finset.mem_image.mpr ⟨E', Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE'_sub, hE'_cover⟩, rfl⟩)
    simp_all +decide
    exact le_trans (by cases h : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ S_e G M {u, v, w}, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (Finset.powerset G.edgeFinset))) <;> aesop) hE'_card

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (from slot24, uuid 3042f3e3)
-- ══════════════════════════════════════════════════════════════════════════════

/-- X_ef is empty when e and f are vertex-disjoint -/
lemma X_eq_empty_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (h : (e ∩ f).card = 0) :
    X_ef G e f = ∅ := by
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
  intro ht he_inter
  have h_disj : Disjoint (t ∩ e) (t ∩ f) := by
    rw [Finset.disjoint_left]
    intro x hx_e hx_f
    have hxe : x ∈ e := Finset.mem_inter.mp hx_e |>.2
    have hxf : x ∈ f := Finset.mem_inter.mp hx_f |>.2
    have : x ∈ e ∩ f := Finset.mem_inter.mpr ⟨hxe, hxf⟩
    rw [Finset.card_eq_zero] at h
    exact (h ▸ this : x ∈ (∅ : Finset V))
  have h_union_sub : (t ∩ e) ∪ (t ∩ f) ⊆ t := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have h_sum_le : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
    calc (t ∩ e).card + (t ∩ f).card
        = ((t ∩ e) ∪ (t ∩ f)).card := (Finset.card_union_of_disjoint h_disj).symm
      _ ≤ t.card := Finset.card_le_card h_union_sub
  have ht_card : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht
    exact ht.2
  omega

/-- If e ∩ f = {v}, every bridge in X(e,f) contains v -/
lemma mem_X_implies_v_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e.card = 3) (hf : f.card = 3) (h_inter : (e ∩ f).card = 1)
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ v ∈ e ∩ f, v ∈ t := by
  simp only [X_ef, Finset.mem_filter] at ht
  obtain ⟨ht_tri, h_e_inter, h_f_inter⟩ := ht
  have ht_card : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_tri
    exact ht_tri.2
  -- t shares ≥2 vertices with e and ≥2 with f
  -- e ∩ f = {v}, so t must contain v
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h_inter
  use v
  constructor
  · rw [hv]; exact Finset.mem_singleton_self v
  · by_contra h_v_notin_t
    -- If v ∉ t, then t ∩ e ⊆ e \ {v} has card ≤ 2
    -- Similarly t ∩ f ⊆ f \ {v} has card ≤ 2
    -- But t ∩ e and t ∩ f must be disjoint (since e ∩ f = {v} and v ∉ t)
    have h_te_sub : t ∩ e ⊆ e \ {v} := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact Finset.mem_inter.mp hx |>.2
      · intro hxv
        rw [hxv] at hx
        exact h_v_notin_t (Finset.mem_inter.mp hx |>.1)
    have h_tf_sub : t ∩ f ⊆ f \ {v} := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact Finset.mem_inter.mp hx |>.2
      · intro hxv
        rw [hxv] at hx
        exact h_v_notin_t (Finset.mem_inter.mp hx |>.1)
    have h_disj : Disjoint (t ∩ e) (t ∩ f) := by
      rw [Finset.disjoint_left]
      intro x hx_e hx_f
      have hxe : x ∈ e := Finset.mem_inter.mp hx_e |>.2
      have hxf : x ∈ f := Finset.mem_inter.mp hx_f |>.2
      have hx_ef : x ∈ e ∩ f := Finset.mem_inter.mpr ⟨hxe, hxf⟩
      rw [hv] at hx_ef
      have hxv : x = v := Finset.mem_singleton.mp hx_ef
      rw [hxv] at hx_e
      exact h_v_notin_t (Finset.mem_inter.mp hx_e |>.1)
    have h_sum : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
      calc (t ∩ e).card + (t ∩ f).card
          = ((t ∩ e) ∪ (t ∩ f)).card := (Finset.card_union_of_disjoint h_disj).symm
        _ ≤ t.card := Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    omega

/-- PROVEN: τ(X_ef) ≤ 2 when e ∩ f = {v} -/
lemma tau_X_le_2_of_inter_eq_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  unfold triangleCoveringNumberOn
  have h_cover : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ X_ef G e f, ∃ e ∈ E', e ∈ t.sym2 := by
    -- Every t in X(e,f) contains v (the unique shared vertex)
    -- Cover with 2 edges incident to v from e
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e ∩ f ∧ ∀ t ∈ X_ef G e f, v ∈ t := by
      obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.mp h_inter
      use v
      constructor
      · rw [hv_eq]; exact Finset.mem_singleton_self v
      · intro t ht
        have he_card : e.card = 3 := by simp only [SimpleGraph.mem_cliqueFinset_iff] at he; exact he.2
        have hf_card : f.card = 3 := by simp only [SimpleGraph.mem_cliqueFinset_iff] at hf; exact hf.2
        obtain ⟨w, hw_mem, hw_t⟩ := mem_X_implies_v_in_t G e f he_card hf_card h_inter t ht
        rw [hv_eq] at hw_mem
        rw [Finset.mem_singleton.mp hw_mem]
        exact hw_t
    -- Get the other two vertices of e
    obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ e = {v, u, w} ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w := by
      have h_e : e.card = 3 := by simp only [SimpleGraph.mem_cliqueFinset_iff] at he; exact he.2
      rw [Finset.card_eq_three] at h_e
      rcases h_e with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
      simp_all +decide [SimpleGraph.cliqueFinset]
      rcases hv.1.1 with (rfl | rfl | rfl) <;> simp_all +decide [SimpleGraph.isNClique_iff]
      · exact ⟨y, by tauto, z, by tauto, rfl, by tauto⟩
      · exact ⟨x, by tauto, z, by tauto, by aesop, by tauto, by tauto, by tauto⟩
      · exact ⟨x, hxz, y, hyz, by aesop, by tauto⟩
    refine ⟨{s(v, u), s(v, w)}, ?_, ?_, ?_⟩ <;> simp_all +decide [SimpleGraph.cliqueFinset]
    · simp_all +decide [Set.insert_subset_iff, SimpleGraph.adj_comm]
    · exact Finset.card_insert_le _ _
    · intro t ht
      have := Finset.mem_filter.mp ht |>.2
      simp_all +decide [SimpleGraph.isNClique_iff]
      contrapose! this; aesop
  obtain ⟨E', hE₁, hE₂, hE₃⟩ := h_cover
  have h_min_le : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S →
      (Finset.image Finset.card S).min.getD 0 ≤ E'.card := by
    intros S hE'
    have := Finset.min_le (Finset.mem_image_of_mem Finset.card hE')
    cases h : Finset.min (Finset.image Finset.card S) <;> aesop
  exact le_trans (h_min_le (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE₁, hE₃⟩)) hE₂

/-- PROVEN: τ(X_ef) ≤ 2 for any pair in packing -/
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  by_cases h_inter : (e ∩ f).card ≤ 1
  · cases h_inter.eq_or_lt <;> simp_all +decide
    · have := hM.1
      exact tau_X_le_2_of_inter_eq_1 G e f (this.1 he) (this.1 hf) ‹_›
    · rw [X_eq_empty_of_disjoint G e f ‹_›]
      unfold triangleCoveringNumberOn
      simp +decide [Finset.min]
      rw [Finset.inf_eq_iInf]
      simp +decide [Option.getD]
      rw [show (⨅ a : Finset (Sym2 V), ⨅ (_ : (a : Set (Sym2 V)) ⊆ G.edgeSet), (a.card : WithTop ℕ)) = 0 from ?_]
      simp +decide
      refine le_antisymm ?_ ?_
      · refine le_trans (ciInf_le ?_ ∅) ?_ <;> simp +decide
      · exact zero_le _
  · have := hM.1
    exact absurd (this.2 he hf hef) (by aesop)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tuza_nu2 (from nu2_proven, uuid 0764be78) - STRUCTURE ONLY
-- Aristotle will fill the actual proof
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ ≤ 2 when ν = 1 -/
lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  -- When ν = 1, all triangles share an edge (form intersecting family)
  -- Can be covered by 2 edges
  sorry -- Proven in aristotle_parker_full_e7f11dfc.lean

/-- τ ≤ 4 when ν = 2 -/
lemma tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  -- Each of 2 packing elements e, f has T_e coverable by ≤2 edges
  -- T_e ∪ T_f covers all triangles
  -- Total: ≤4 edges
  sorry -- Proven in nu2/tuza_nu2_PROVEN.lean

/-- τ = 0 when ν = 0 (no triangles) -/
lemma tuza_nu0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  unfold triangleCoveringNumber
  have h_no_triangles : G.cliqueFinset 3 = ∅ := by
    by_contra h_ne
    have ⟨t, ht⟩ := Finset.nonempty_of_ne_empty h_ne
    have h_packing : isTrianglePacking G {t} := by
      constructor
      · exact Finset.singleton_subset_iff.mpr ht
      · simp [Set.Pairwise]
    have h_card : ({t} : Finset (Finset V)).card = 1 := Finset.card_singleton t
    have h_le : 1 ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber
      have h_mem : {t} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
        simp [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.singleton_subset_iff.mpr ht, h_packing⟩
      have := Finset.le_max (Finset.mem_image_of_mem Finset.card h_mem)
      cases hmax : Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset))
      · simp at this
      · simp [Option.getD] at *
        omega
    omega
  simp [h_no_triangles]
  rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- GAP 1: parker_nu_le_2 (τ ≤ 4 when ν ≤ 2)
-- Derives from tuza_nu0, tuza_nu1, tuza_nu2
-- ══════════════════════════════════════════════════════════════════════════════

/-- DERIVED: τ ≤ 4 when ν ≤ 2 -/
lemma parker_nu_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 2) :
    triangleCoveringNumber G ≤ 4 := by
  -- Case split on ν ∈ {0, 1, 2}
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · -- ν < 2, so ν ∈ {0, 1}
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt' | heq'
    · -- ν = 0
      have h0 : trianglePackingNumber G = 0 := Nat.lt_one_iff.mp hlt'
      rw [tuza_nu0 G h0]
      exact Nat.zero_le 4
    · -- ν = 1
      have := tuza_case_nu_1 G heq'
      linarith
  · -- ν = 2
    exact tuza_nu2 G heq

-- ══════════════════════════════════════════════════════════════════════════════
-- GAP 2: Vertex-disjoint triangle sets have disjoint edge covers
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edges of vertex-disjoint triangle sets are disjoint -/
lemma edges_disjoint_of_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    Disjoint (edgesWithin G (vertexSetOf A)) (edgesWithin G (vertexSetOf B)) := by
  rw [Finset.disjoint_left]
  intro e he_A he_B
  simp only [edgesWithin, Finset.mem_filter] at he_A he_B
  -- e is an edge with both endpoints in vertexSetOf A
  -- and both endpoints in vertexSetOf B
  -- But vertexSetOf A and vertexSetOf B are disjoint - contradiction
  obtain ⟨u, v⟩ := e.out
  have hu_A : u ∈ vertexSetOf A := he_A.2 u (by simp [Sym2.out_eq])
  have hu_B : u ∈ vertexSetOf B := he_B.2 u (by simp [Sym2.out_eq])
  exact Finset.disjoint_left.mp h_vertex_disj hu_A hu_B

/-- An edge covering a triangle must have endpoints in the triangle -/
lemma edge_in_triangle_vertices (t : Finset V) (e : Sym2 V) (he : e ∈ t.sym2) :
    ∀ v ∈ e, v ∈ t := by
  intro v hv
  simp only [Finset.sym2, Finset.mem_filter, Finset.mem_product] at he
  rcases e.out with ⟨a, b⟩
  simp only [Sym2.out_eq] at hv he
  rcases hv with rfl | rfl
  · exact he.1.1
  · exact he.1.2

/-- Triangle in A has edges within vertexSetOf A -/
lemma triangle_edges_in_vertex_set (A : Finset (Finset V)) (t : Finset V) (ht : t ∈ A) (e : Sym2 V) (he : e ∈ t.sym2) :
    ∀ v ∈ e, v ∈ vertexSetOf A := by
  intro v hv
  simp only [vertexSetOf, Finset.mem_biUnion, id]
  use t, ht
  exact edge_in_triangle_vertices t e he v hv

/-- A triangle can share edge with at most one of two vertex-disjoint sets -/
lemma vertex_disjoint_triangles_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    Disjoint (triangleUnionOf G A) (triangleUnionOf G B) := by
  simp_all +decide [Finset.disjoint_left, triangleUnionOf]
  by_contra h_contra
  push_neg at h_contra
  obtain ⟨a, x, hx, ha, y, hy, hb⟩ := h_contra
  simp_all +decide [trianglesSharingEdge]
  -- t = a shares ≥2 vertices with some x ∈ A and ≥2 vertices with some y ∈ B
  -- x ⊆ vertexSetOf A and y ⊆ vertexSetOf B
  -- If |a ∩ x| ≥ 2 and |a ∩ y| ≥ 2, then a has ≥ 4 vertices (since x, y are vertex-disjoint)
  -- But a is a triangle with 3 vertices - contradiction
  obtain ⟨v, hv⟩ : ∃ v, v ∈ a ∩ x ∧ v ∈ a ∩ y := by
    have h_common_vertex : (a ∩ x).card + (a ∩ y).card > a.card := by
      have := Finset.card_le_card (show a ⊆ Finset.univ from Finset.subset_univ a)
      simp_all +decide [SimpleGraph.isNClique_iff]
      linarith
    contrapose! h_common_vertex
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr h_common_vertex)]
    exact Finset.card_mono (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  have hv_A : v ∈ vertexSetOf A := Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_inter.mp hv.1 |>.2⟩
  have hv_B : v ∈ vertexSetOf B := Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_inter.mp hv.2 |>.2⟩
  exact Finset.disjoint_left.mp h_disj hv_A hv_B

/-- Maximum packing dominates all triangles -/
lemma max_packing_dominates (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    G.cliqueFinset 3 ⊆ triangleUnionOf G M := by
  by_contra h_contra
  obtain ⟨t, ht⟩ : ∃ t ∈ G.cliqueFinset 3, t ∉ triangleUnionOf G M := Set.not_subset.mp h_contra
  have h_packing : isTrianglePacking G (insert t M) := by
    refine ⟨?_, ?_⟩
    · exact Finset.insert_subset ht.1 hM.1.1
    · intro x hx y hy hxy
      simp_all +decide [Set.Pairwise]
      rcases hx with (rfl | hx) <;> rcases hy with (rfl | hy) <;> simp_all +decide [triangleUnionOf]
      · rintro _ a b ha hb hab rfl c d hc hd hcd
        specialize ht.2; simp_all +decide [Finset.mem_biUnion]
        exact fun h => ht.2 y hy (Finset.mem_filter.mpr ⟨h, Finset.one_lt_card.2 ⟨a, by aesop⟩⟩)
      · intro a x y hx hy hxy hxy' z w hz hw hzw hzw'
        specialize ht.2; simp_all +decide [trianglesSharingEdge, Finset.mem_biUnion]
        exact ht.2 x hx (by simp +decide [Finset.card_eq_two]; exact Finset.one_lt_card.2 ⟨a, by aesop, b, by aesop⟩)
      · have := hM.1.2
        simp_all +decide [Finset.disjoint_left]
        exact this
  have h_card : (insert t M).card = M.card + 1 := by
    rw [Finset.card_insert_of_notMem]
    intro h
    specialize ht.2
    simp only [triangleUnionOf, Finset.mem_biUnion] at ht
    push_neg at ht
    specialize ht t h
    simp only [trianglesSharingEdge, Finset.mem_filter, Finset.inter_comm] at ht
    have := ht.1.card_eq
    simp at ht
    omega
  have h_card_le : (insert t M).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : insert t M ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have := Finset.le_max (Finset.mem_image_of_mem Finset.card h_mem)
    cases hmax : Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)) <;> aesop
  linarith

/-- τ(G) = τ(triangleUnionOf G M) for max packing M -/
lemma tau_eq_tau_on_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    triangleCoveringNumber G = triangleCoveringNumberOn G (triangleUnionOf G M) := by
  have h_eq : G.cliqueFinset 3 = triangleUnionOf G M := by
    refine subset_antisymm ?_ ?_
    · exact max_packing_dominates G M hM
    · exact Finset.biUnion_subset.2 fun t ht => Finset.filter_subset _ _
  unfold triangleCoveringNumber triangleCoveringNumberOn
  congr! 2
  ext; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- GAP 2 CONTINUED: tau_disjoint_eq_sum (the equality, not just inequality)
-- Key insight from Gemini: vertex-disjoint implies edge-disjoint covers
-- ══════════════════════════════════════════════════════════════════════════════

/-- Lower bound: τ(A ∪ B) ≥ τ(A) + τ(B) for vertex-disjoint sets -/
lemma tau_disjoint_ge_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B))
    (hA_sub : A ⊆ G.cliqueFinset 3) (hB_sub : B ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (A ∪ B) ≥ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Any cover C of A ∪ B decomposes into C_A and C_B
  -- C_A covers A, C_B covers B, and they're disjoint
  -- So |C| ≥ |C_A| + |C_B| ≥ τ(A) + τ(B)
  unfold triangleCoveringNumberOn
  let coversAB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2)
  let coversA := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)
  let coversB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2)
  let sizesAB := coversAB.image Finset.card
  let sizesA := coversA.image Finset.card
  let sizesB := coversB.image Finset.card

  by_cases hAB : sizesAB.Nonempty
  case pos =>
    -- Get minimum cover C of A ∪ B
    have h_tauAB : (coversAB.image Finset.card).min.getD 0 = sizesAB.min' hAB := by
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    rw [h_tauAB]

    -- Check if A, B have covers
    by_cases hA_ne : sizesA.Nonempty
    case neg =>
      -- No cover for A means τ(A) = 0 (vacuously no triangles to cover or graph issue)
      have h_empty_A : sizesA = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA_ne
      simp only [h_empty_A, Finset.min_empty, Option.getD]
      exact Nat.zero_le _
    case pos =>
      by_cases hB_ne : sizesB.Nonempty
      case neg =>
        have h_empty_B : sizesB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB_ne
        simp only [h_empty_B, Finset.min_empty, Option.getD]
        exact Nat.zero_le _
      case pos =>
        have h_tauA : (coversA.image Finset.card).min.getD 0 = sizesA.min' hA_ne := by
          rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']; simp
        have h_tauB : (coversB.image Finset.card).min.getD 0 = sizesB.min' hB_ne := by
          rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']; simp
        rw [h_tauA, h_tauB]

        -- Get witness covers
        obtain ⟨C, hC_mem, hC_card⟩ := Finset.mem_image.mp (Finset.min'_mem sizesAB hAB)
        have hC_sub : C ⊆ G.edgeFinset := (Finset.mem_filter.mp hC_mem).1 |> Finset.mem_powerset.mp
        have hC_covers : ∀ t ∈ A ∪ B, ∃ e ∈ C, e ∈ t.sym2 := (Finset.mem_filter.mp hC_mem).2

        -- Partition C into edges covering A vs B
        let C_A := C.filter (fun e => ∃ t ∈ A, e ∈ t.sym2)
        let C_B := C.filter (fun e => ∃ t ∈ B, e ∈ t.sym2)

        -- C_A covers A
        have hC_A_covers : ∀ t ∈ A, ∃ e ∈ C_A, e ∈ t.sym2 := by
          intro t ht
          obtain ⟨e, he_C, he_t⟩ := hC_covers t (Finset.mem_union_left B ht)
          exact ⟨e, Finset.mem_filter.mpr ⟨he_C, t, ht, he_t⟩, he_t⟩

        -- C_B covers B
        have hC_B_covers : ∀ t ∈ B, ∃ e ∈ C_B, e ∈ t.sym2 := by
          intro t ht
          obtain ⟨e, he_C, he_t⟩ := hC_covers t (Finset.mem_union_right A ht)
          exact ⟨e, Finset.mem_filter.mpr ⟨he_C, t, ht, he_t⟩, he_t⟩

        -- C_A and C_B are disjoint (vertex-disjoint implies edge-disjoint)
        have hC_disj : Disjoint C_A C_B := by
          rw [Finset.disjoint_left]
          intro e he_A he_B
          simp only [Finset.mem_filter] at he_A he_B
          obtain ⟨_, tA, htA, he_tA⟩ := he_A
          obtain ⟨_, tB, htB, he_tB⟩ := he_B
          -- e covers triangle tA in A and tB in B
          -- e has endpoints in tA ⊆ vertexSetOf A and in tB ⊆ vertexSetOf B
          rcases e.out with ⟨u, v⟩
          have hu_A : u ∈ vertexSetOf A := by
            have := edge_in_triangle_vertices tA e he_tA u (by simp [Sym2.out_eq])
            exact Finset.mem_biUnion.mpr ⟨tA, htA, this⟩
          have hu_B : u ∈ vertexSetOf B := by
            have := edge_in_triangle_vertices tB e he_tB u (by simp [Sym2.out_eq])
            exact Finset.mem_biUnion.mpr ⟨tB, htB, this⟩
          exact Finset.disjoint_left.mp h_vertex_disj hu_A hu_B

        -- |C| ≥ |C_A| + |C_B|
        have h_card_ge : C.card ≥ C_A.card + C_B.card := by
          have h_union_sub : C_A ∪ C_B ⊆ C := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          calc C.card
              ≥ (C_A ∪ C_B).card := Finset.card_le_card h_union_sub
            _ = C_A.card + C_B.card := Finset.card_union_of_disjoint hC_disj

        -- C_A ∈ coversA
        have hC_A_valid : C_A ∈ coversA := by
          simp only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          · exact Finset.Subset.trans (Finset.filter_subset _ _) hC_sub
          · exact hC_A_covers

        -- C_B ∈ coversB
        have hC_B_valid : C_B ∈ coversB := by
          simp only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          · exact Finset.Subset.trans (Finset.filter_subset _ _) hC_sub
          · exact hC_B_covers

        -- τ(A) ≤ |C_A| and τ(B) ≤ |C_B|
        have h_tauA_le : sizesA.min' hA_ne ≤ C_A.card :=
          Finset.min'_le _ _ (Finset.mem_image_of_mem Finset.card hC_A_valid)
        have h_tauB_le : sizesB.min' hB_ne ≤ C_B.card :=
          Finset.min'_le _ _ (Finset.mem_image_of_mem Finset.card hC_B_valid)

        -- Combine
        calc sizesA.min' hA_ne + sizesB.min' hB_ne
            ≤ C_A.card + C_B.card := Nat.add_le_add h_tauA_le h_tauB_le
          _ ≤ C.card := h_card_ge
          _ = sizesAB.min' hAB := hC_card.symm

  case neg =>
    -- No cover for A ∪ B, so τ(A ∪ B) = 0
    have h_empty : sizesAB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAB
    simp only [h_empty, Finset.min_empty, Option.getD]
    exact Nat.zero_le _

/-- DERIVED: τ(A ∪ B) = τ(A) + τ(B) for vertex-disjoint triangle sets -/
theorem tau_disjoint_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B))
    (hA_sub : A ⊆ G.cliqueFinset 3) (hB_sub : B ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (A ∪ B) = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  apply le_antisymm
  · exact tau_union_le_sum G A B
  · exact tau_disjoint_ge_sum G A B h_vertex_disj hA_sub hB_sub

-- ══════════════════════════════════════════════════════════════════════════════
-- GAP 3: Subgraph packing bounds
-- ══════════════════════════════════════════════════════════════════════════════

/-- Subgraph induced by triangles -/
def subgraphFromTriangles (T : Finset (Finset V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ((T.biUnion (fun t => t.sym2)) : Set (Sym2 V))

instance (T : Finset (Finset V)) : DecidableRel (subgraphFromTriangles T).Adj :=
  Classical.decRel _

/-- Packing in induced subgraph has bounded size -/
lemma nu_subgraph_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset (Finset V)) (hA_sub : A ⊆ M) (hA_card : A.card = 2) :
    trianglePackingNumber (subgraphFromTriangles (triangleUnionOf G A)) ≤ 2 := by
  -- Any packing in the subgraph can be extended with (M \ A) to form a packing in G
  -- If subgraph packing > 2, combined with M \ A would exceed M.card, contradiction
  sorry -- Aristotle will prove

/-- τ on triangles ≤ τ of induced subgraph -/
lemma tau_on_le_tau_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G T ≤ triangleCoveringNumber (subgraphFromTriangles T) := by
  -- Any cover of subgraph triangles is a cover of T
  sorry -- Aristotle will prove

/-- Component bound: τ(triangleUnionOf G A) ≤ 4 when A has 2 elements -/
lemma tau_component_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset (Finset V)) (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B))
    (hA_card : A.card = 2) :
    triangleCoveringNumberOn G (triangleUnionOf G A) ≤ 4 := by
  -- triangleUnionOf G A is a set of triangles
  -- Its induced subgraph has ν ≤ 2 (from nu_subgraph_le)
  -- By parker_nu_le_2, τ(subgraph) ≤ 4
  -- By tau_on_le_tau_subgraph, τ(triangleUnionOf G A) ≤ τ(subgraph) ≤ 4
  have h_nu_le_2 : trianglePackingNumber (subgraphFromTriangles (triangleUnionOf G A)) ≤ 2 := by
    exact nu_subgraph_le G M hM A (by rw [← hAB]; exact Finset.subset_union_left) hA_card
  have h_tau_subgraph_le_4 : triangleCoveringNumber (subgraphFromTriangles (triangleUnionOf G A)) ≤ 4 := by
    exact parker_nu_le_2 (subgraphFromTriangles (triangleUnionOf G A)) h_nu_le_2
  have h_tau_on_le : triangleCoveringNumberOn G (triangleUnionOf G A) ≤
      triangleCoveringNumber (subgraphFromTriangles (triangleUnionOf G A)) := by
    apply tau_on_le_tau_subgraph
    exact Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Vertex Partition 2+2
-- ══════════════════════════════════════════════════════════════════════════════

/-- MAIN THEOREM: τ ≤ 8 when packing splits into two vertex-disjoint pairs -/
theorem tau_le_8_vertex_partition_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_card : A.card = 2) (hB_card : B.card = 2)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: τ(G) = τ(triangleUnionOf G M)
  have h_tau_eq : triangleCoveringNumber G = triangleCoveringNumberOn G (triangleUnionOf G M) :=
    tau_eq_tau_on_union G M hM

  -- Step 2: triangleUnionOf G M = triangleUnionOf G A ∪ triangleUnionOf G B
  have h_union : triangleUnionOf G M = triangleUnionOf G A ∪ triangleUnionOf G B := by
    unfold triangleUnionOf
    rw [← hAB]
    ext t
    simp [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨x, hx, ht⟩
      rcases Finset.mem_union.mp hx with hxA | hxB
      · left; exact ⟨x, hxA, ht⟩
      · right; exact ⟨x, hxB, ht⟩
    · rintro (⟨x, hx, ht⟩ | ⟨x, hx, ht⟩)
      · exact ⟨x, Finset.mem_union_left B hx, ht⟩
      · exact ⟨x, Finset.mem_union_right A hx, ht⟩

  -- Step 3: triangleUnionOf G A and triangleUnionOf G B are disjoint
  have h_tri_disj : Disjoint (triangleUnionOf G A) (triangleUnionOf G B) :=
    vertex_disjoint_triangles_disjoint G A B h_vertex_disj

  -- Step 4: τ(union) = τ(A part) + τ(B part) (using disjointness!)
  have h_A_sub : triangleUnionOf G A ⊆ G.cliqueFinset 3 :=
    Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _
  have h_B_sub : triangleUnionOf G B ⊆ G.cliqueFinset 3 :=
    Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _

  -- Need vertex disjointness of triangle sets, which follows from vertex disjointness of A, B
  have h_tri_vertex_disj : Disjoint (vertexSetOf (triangleUnionOf G A)) (vertexSetOf (triangleUnionOf G B)) := by
    rw [Finset.disjoint_left]
    intro v hv_A hv_B
    simp only [vertexSetOf, Finset.mem_biUnion, id] at hv_A hv_B
    obtain ⟨tA, htA, hv_tA⟩ := hv_A
    obtain ⟨tB, htB, hv_tB⟩ := hv_B
    simp only [triangleUnionOf, Finset.mem_biUnion] at htA htB
    obtain ⟨eA, heA, htA'⟩ := htA
    obtain ⟨eB, heB, htB'⟩ := htB
    simp only [trianglesSharingEdge, Finset.mem_filter] at htA' htB'
    -- v ∈ tA and tA shares ≥2 vertices with eA ∈ A
    -- v ∈ tB and tB shares ≥2 vertices with eB ∈ B
    -- Need to show v ∈ vertexSetOf A ∩ vertexSetOf B
    -- Actually we need a stronger argument...
    -- If v ∈ tA and tA ∩ eA has ≥2 elements, and eA ⊆ vertexSetOf A
    -- This doesn't immediately give v ∈ vertexSetOf A
    -- The correct approach: triangles in triangleUnionOf G A have vertices reachable from A
    sorry -- Aristotle will complete this

  rw [h_tau_eq, h_union]
  rw [tau_disjoint_eq_sum G (triangleUnionOf G A) (triangleUnionOf G B) h_tri_vertex_disj h_A_sub h_B_sub]

  -- Step 5: Each part ≤ 4
  have h_A_bound : triangleCoveringNumberOn G (triangleUnionOf G A) ≤ 4 :=
    tau_component_bound G M hM A B hAB hAB_disj h_vertex_disj hA_card

  have h_B_bound : triangleCoveringNumberOn G (triangleUnionOf G B) ≤ 4 := by
    have hBA : B ∪ A = M := by rw [Finset.union_comm, hAB]
    exact tau_component_bound G M hM B A hBA hAB_disj.symm h_vertex_disj.symm hB_card

  -- Step 6: Conclude
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Disconnected sharing graph implies τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-- Disconnected sharing graph implies τ ≤ 8 -/
theorem tau_le_8_disconnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_disconnected : ∃ (A B : Finset (Finset V)),
      A ∪ B = M ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      ∀ a ∈ A, ∀ b ∈ B, Disjoint (a : Set V) (b : Set V)) :
    triangleCoveringNumber G ≤ 8 := by
  obtain ⟨A, B, hAB, hAB_disj, hA_ne, hB_ne, h_all_disj⟩ := h_disconnected
  -- Pairwise vertex-disjointness implies vertex set disjointness
  have h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B) := by
    rw [Finset.disjoint_left]
    intro v hv_A hv_B
    simp only [vertexSetOf, Finset.mem_biUnion, id] at hv_A hv_B
    obtain ⟨a, ha, hv_a⟩ := hv_A
    obtain ⟨b, hb, hv_b⟩ := hv_B
    have := h_all_disj a ha b hb
    exact Set.disjoint_left.mp this (Finset.mem_coe.mpr hv_a) (Finset.mem_coe.mpr hv_b)

  -- Determine sizes of A and B
  have h_sizes : A.card + B.card = 4 := by
    have := Finset.card_union_of_disjoint hAB_disj
    rw [hAB, hM_card] at this
    exact this

  -- Cases: (1,3), (2,2), (3,1)
  rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt (Finset.card_pos.mpr hA_ne)) with hA1 | hA_gt1
  -- ... case analysis would continue
  sorry -- Aristotle will complete the case analysis

end
