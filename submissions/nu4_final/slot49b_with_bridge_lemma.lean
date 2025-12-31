/-
Slot49b: Adjacent Pair Bound - With Bridge Lemma

CONTEXT:
- slot44 proved 14 helper lemmas but failed on tau_adjacent_pair_le_4
- This version adds an INTERMEDIATE LEMMA to bridge the gap

KEY INSIGHT:
The naive bound τ(S_e) + τ(S_f) + τ(X_ef) = 6 fails because it doesn't
account for overlap. The bridge lemma makes this overlap EXPLICIT.

NEW LEMMA: T_pair_decomposition
- Decomposes T_pair into S_e, S_f, X_ef, and {e,f}
- Makes the overlap structure visible to Aristotle

NEW LEMMA: cover_overlap_at_v
- Proves that covers from Se_structure share edges through v
- This is the key insight that reduces 6 → 4
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot49a)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

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

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum infrastructure (from slot44)
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangleCover (G : SimpleGraph V) (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

lemma isTriangleCover_union (G : SimpleGraph V) (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) :=
  ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_left _ he₁, he₂ ⟩ ; exact hB.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_right _ he₁, he₂ ⟩ ] ⟩

lemma triangleCoveringNumberOn_le_of_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  have h_min : triangleCoveringNumberOn G triangles ≤ Finset.min (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card) := by
    unfold triangleCoveringNumberOn;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 ) G.edgeFinset.powerset ) ) <;> aesop;
  contrapose! h_min;
  refine' lt_of_le_of_lt _ ( WithTop.coe_lt_coe.mpr h_min );
  simp +decide [ Finset.min ];
  exact ⟨ E', ⟨ fun e he => by have := h.1 he; aesop, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := h.2 t ht; aesop ⟩, le_rfl ⟩

lemma exists_min_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ∃ E', isTriangleCover G triangles E') :
    ∃ E', isTriangleCover G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G triangles E' ∧ ∀ E'' : Finset (Sym2 V), isTriangleCover G triangles E'' → E'.card ≤ E''.card := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ _, fun a ha => ha.1 ⟩;
  use E';
  unfold triangleCoveringNumberOn;
  rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 } ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from ?_ ];
  · rw [ show Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from rfl, Finset.min_eq_inf_withTop ];
    rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) ).inf WithTop.some = WithTop.some E'.card from ?_ ] ; aesop;
    refine' le_antisymm _ _ <;> simp_all +decide [ Finset.inf_le ];
    exact ⟨ E', ⟨ fun e he => by have := hE'.1.1 he; aesop, hE'.1 ⟩, le_rfl ⟩;
  · ext; simp [isTriangleCover]

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · obtain ⟨E_A, hE_A⟩ := exists_min_isTriangleCover G A hA
      obtain ⟨E_B, hE_B⟩ := exists_min_isTriangleCover G B hB;
      have h_union : isTriangleCover G (A ∪ B) (E_A ∪ E_B) := by
        exact isTriangleCover_union G A B E_A E_B hE_A.1 hE_B.1;
      exact le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover _ _ _ h_union ) ( by rw [ ← hE_A.2, ← hE_B.2 ] ; exact Finset.card_union_le _ _ );
    · sorry  -- edge case, proven in slot44
  · sorry  -- edge case, proven in slot44

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (from slot44)
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  simp_all +decide [ Finset.ext_iff, X_ef ];
  by_contra hv_not_in_t
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx hx' => hv_not_in_t <| by have := hv x; aesop;
  have h_card : (t ∩ e) ∪ (t ∩ f) ⊆ t := by
    aesop_cat;
  have := Finset.card_le_card h_card; simp_all +decide [ Finset.card_union_add_card_inter ] ;
  linarith [ ht.1.card_eq ]

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry  -- Full proof in slot44, ~40 lines

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 and Se_structure_lemma (from slot44)
-- ══════════════════════════════════════════════════════════════════════════════

lemma Se_structure_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ uv, uv ⊆ e ∧ uv.card = 2 ∧ ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) ∨
    (∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) := by
  sorry  -- Full proof in slot44, ~30 lines

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry  -- Full proof in slot44, uses Se_structure_lemma

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW BRIDGE LEMMAS (the key additions!)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles in T_pair either share edge with e only, f only, or both -/
lemma T_pair_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) :
    T_pair G e f = S_e G M e ∪ S_e G M f ∪ X_ef G e f ∪
      ((trianglesSharingEdge G e).filter (fun t => ∃ g ∈ M, g ≠ e ∧ g ≠ f ∧ (t ∩ g).card ≥ 2)) ∪
      ((trianglesSharingEdge G f).filter (fun t => ∃ g ∈ M, g ≠ e ∧ g ≠ f ∧ (t ∩ g).card ≥ 2)) := by
  sorry

/-- For adjacent e,f sharing v, all triangles in T_pair contain v OR share base edge -/
lemma T_pair_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    ∀ t ∈ T_pair G e f, v ∈ t ∨
      (∃ uv ⊆ e, uv.card = 2 ∧ v ∉ uv ∧ uv ⊆ t) ∨
      (∃ uv ⊆ f, uv.card = 2 ∧ v ∉ uv ∧ uv ⊆ t) := by
  sorry

/-- The key overlap lemma: Se_structure on adjacent pairs creates shared edges -/
lemma cover_overlap_at_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (a b : V) (hab : e = {v, a, b} ∨ (a ∈ e ∧ b ∈ e ∧ a ≠ b ∧ a ≠ v ∧ b ≠ v))
    (c d : V) (hcd : f = {v, c, d} ∨ (c ∈ f ∧ d ∈ f ∧ c ≠ d ∧ c ≠ v ∧ d ≠ v)) :
    ∃ E : Finset (Sym2 V), E.card ≤ 4 ∧ E ⊆ G.edgeFinset ∧
      ∀ t ∈ T_pair G e f, ∃ e' ∈ E, e' ∈ t.sym2 := by
  -- Key insight: Use Se_structure on both e and f
  -- Case 1: Both have common edge through v → 2 edges from each, but they share v
  -- Case 2: Both have common external vertex → edges {v,x_e} and {v,x_f} plus bases
  -- Case 3: Mixed → combine appropriately
  -- In all cases, edges through v provide overlap
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Adjacent Pair Bound (using bridge lemmas)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_adjacent_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- Get the vertices of e and f
  have he_clique := hM.1.1 he
  have hf_clique := hM.1.1 hf
  -- e = {v, a, b} for some a, b
  -- f = {v, c, d} for some c, d
  -- Use cover_overlap_at_v to get 4-edge cover
  -- Then apply triangleCoveringNumberOn_le_of_isTriangleCover
  sorry

end
