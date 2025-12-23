/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b4f73fa3-9cbc-4877-9819-f5e077da1c54
-/

/-
Tuza ν=4: tau_pair_le_4 via V-decomposition
Slot 19 - FULL SCAFFOLDING from slot16 (no sorry for proven lemmas)

PROVEN CODE BELOW - copied exactly from Aristotle output.
NEW TARGET at bottom: tau_pair_le_4
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Helper lemmas from slot16 (FULL PROOFS - NO SORRY)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum from slot16 (FULL PROOF - NO SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/--
The key union bound lemma: τ(A ∪ B) ≤ τ(A) + τ(B)
PROVEN by Aristotle in slot16 (uuid: b4f73fa3-9cbc-4877-9819-f5e077da1c54)
-/
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Define abbreviations for the filtered powersets
  let coversAB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2)
  let coversA := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)
  let coversB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2)
  let sizesAB := coversAB.image Finset.card
  let sizesA := coversA.image Finset.card
  let sizesB := coversB.image Finset.card

  -- Case split: does a cover for A∪B exist?
  by_cases hAB : sizesAB.Nonempty
  case pos =>
    -- Covers for A∪B exist
    -- Therefore covers for A and B also exist (weaker predicate)
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

    -- Use Finset.min' for nonempty finsets
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

    -- Get witness covers achieving the minimum
    have minA_mem : sizesA.min' hA ∈ sizesA := Finset.min'_mem sizesA hA
    have minB_mem : sizesB.min' hB ∈ sizesB := Finset.min'_mem sizesB hB

    -- Extract actual covers XA and XB
    obtain ⟨XA, hXA_mem, hXA_card⟩ := Finset.mem_image.mp minA_mem
    obtain ⟨XB, hXB_mem, hXB_card⟩ := Finset.mem_image.mp minB_mem

    -- Get properties of XA and XB
    have hXA_sub : XA ⊆ G.edgeFinset := (Finset.mem_filter.mp hXA_mem).1 |> Finset.mem_powerset.mp
    have hXA_covers : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2 := (Finset.mem_filter.mp hXA_mem).2
    have hXB_sub : XB ⊆ G.edgeFinset := (Finset.mem_filter.mp hXB_mem).1 |> Finset.mem_powerset.mp
    have hXB_covers : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2 := (Finset.mem_filter.mp hXB_mem).2

    -- XA ∪ XB covers A ∪ B
    have hUnion_covers : ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 :=
      union_covers_union G A B XA XB hXA_covers hXB_covers

    -- XA ∪ XB is a valid cover (subset of edges)
    have hUnion_sub : XA ∪ XB ⊆ G.edgeFinset := Finset.union_subset hXA_sub hXB_sub

    -- Therefore XA ∪ XB ∈ coversAB
    have hUnion_mem : XA ∪ XB ∈ coversAB := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hUnion_sub, hUnion_covers⟩

    -- |XA ∪ XB| ∈ sizesAB
    have card_union_mem : (XA ∪ XB).card ∈ sizesAB :=
      Finset.mem_image_of_mem Finset.card hUnion_mem

    -- sizesAB.min' ≤ |XA ∪ XB|
    have min_le_card : sizesAB.min' hAB ≤ (XA ∪ XB).card :=
      Finset.min'_le sizesAB (XA ∪ XB).card card_union_mem

    -- |XA ∪ XB| ≤ |XA| + |XB|
    have card_union_le : (XA ∪ XB).card ≤ XA.card + XB.card := Finset.card_union_le XA XB

    -- Chain the inequalities
    calc triangleCoveringNumberOn G (A ∪ B)
        = sizesAB.min' hAB := h_tauAB
      _ ≤ (XA ∪ XB).card := min_le_card
      _ ≤ XA.card + XB.card := card_union_le
      _ = sizesA.min' hA + sizesB.min' hB := by rw [hXA_card, hXB_card]
      _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [← h_tauA, ← h_tauB]

  case neg =>
    -- No covers for A∪B exist, so τ(A∪B) = 0
    have h_empty : sizesAB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAB
    have h_tau_zero : triangleCoveringNumberOn G (A ∪ B) = 0 := by
      simp only [triangleCoveringNumberOn]
      rw [h_empty]
      simp
    rw [h_tau_zero]
    exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: V-decomposition corollaries from slot16 (FULL PROOFS)
-- ══════════════════════════════════════════════════════════════════════════════

lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

/-- Key corollary for V-decomposition approach to τ(T_e ∪ T_f) ≤ 4 -/
theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  rw [v_decomposition_union triangles v]
  exact tau_union_le_sum G _ _

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: Lemmas for tau_pair_le_4 (for Aristotle to prove)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles all containing vertex v can be covered by 2 edges incident to v -/
lemma tau_containing_vertex_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V)
    (htri : triangles ⊆ G.cliqueFinset 3)
    (hv : ∀ t ∈ triangles, v ∈ t) :
    triangleCoveringNumberOn G triangles ≤ 2 := by
  sorry

/-- Triangles on ≤4 vertices can be covered by 2 edges -/
lemma tau_on_four_vertices_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (W : Finset V) (hW : W.card ≤ 4)
    (htri_sub : ∀ t ∈ triangles, t ⊆ W) :
    triangleCoveringNumberOn G triangles ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: tau_pair_le_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- The pairwise bound: τ(T_e ∪ T_f) ≤ 4 when e,f share exactly vertex v -/
theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

end
