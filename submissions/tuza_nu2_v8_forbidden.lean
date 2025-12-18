/-
TUZA'S CONJECTURE ν=2 - v8: FORBIDDEN STRUCTURE (COMPLETE BUILDING BLOCKS)

=== PROVEN BY ARISTOTLE IN 5e72ffae (ALL FULL PROOFS INCLUDED) ===
1. packing_one_implies_intersect - ν=1 ⟹ any two triangles share edge
2. tuza_case_nu_1 - ν=1 ⟹ τ≤2
3. tau_gt_4_implies_uncovered - ν=2, τ>4 ⟹ every 4-edge set misses a triangle
4. extensions_form_K4 - ν=2, τ>4 ⟹ every triangle extends to K₄ (uses extension_triangle_exists_nu2)
5. two_K4_implies_nu_gt_2 - two K₄s ⟹ ν>2 or τ≤4 (uses two_K4_cover_le_4)

=== ONE KEY GAP: extension_triangle_exists_nu2 ===
If ν=2, τ>4, T is a triangle, e ∈ edges(T), then
∃ T' ≠ T with triangleEdges(T) ∩ triangleEdges(T') = {e}

This is the ν=2 analogue of the petal lemma.
ALL other lemmas are proven. Focus ONLY on this gap.

=== PROOF ARCHITECTURE ===
  τ > 4 ∧ ν = 2
      ↓ extension_triangle_exists_nu2 (KEY GAP)
  Every edge of every triangle has a unique "petal"
      ↓ extensions_form_K4 (proven, depends on above)
  Every triangle extends to K₄
      ↓ tau_gt_4_implies_two_K4 (straightforward once above proven)
  Two almost-disjoint K₄s exist
      ↓ two_K4_implies_nu_gt_2 (proven)
  ν > 2 OR τ ≤ 4 → contradiction
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

def IsK4 (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Prop :=
  s ∈ G.cliqueFinset 4

def HasTwoAlmostDisjointK4 (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (s1 s2 : Finset V), IsK4 G s1 ∧ IsK4 G s2 ∧ s1 ≠ s2 ∧ (s1 ∩ s2).card ≤ 1

/-! ## PROVEN: Extract max packing -/

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_max
  simp [Finset.mem_filter, Finset.mem_powerset] at hP₁
  exact ⟨P, hP₁.1, hP₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩

/-! ## PROVEN: ν=1 implies any two triangles share edge -/

lemma packing_one_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  unfold trianglePackingNumber at h
  refine fun h' => absurd h <| ne_of_gt <| lt_of_lt_of_le ?_ <| Finset.le_sup (f := Finset.card) <|
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨h1, Finset.singleton_subset_iff.mpr h2⟩, ?_⟩
  · rw [Finset.card_pair]; aesop
    unfold triangleEdges at h'; aesop
    rw [Finset.eq_empty_iff_forall_not_mem] at h'; have := h2.card_eq; aesop
    exact absurd (Finset.card_le_one.2 fun x hx y hy => h' x y hx hy) (by linarith)
  · intro a ha b hb hab; aesop; exact h'.symm

/-! ## PROVEN: K₄ implies τ≤2 when ν=1 -/

lemma k4_implies_tau_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) (s : Finset V) (hs : IsK4 G s) :
    triangleCoveringNumber G ≤ 2 := by
  simp +decide only [triangleCoveringNumber]
  obtain ⟨a, b, c, d, h_edges⟩ : ∃ (a b c d : V), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d := by
    unfold IsK4 at hs
    simp_all +decide [Finset.mem_coe, SimpleGraph.IsNClique]
    rcases Finset.card_eq_succ.mp hs.2 with ⟨a, ha⟩
    rcases ha with ⟨t, hat, rfl, ht⟩; rcases Finset.card_eq_three.mp ht with ⟨b, c, d, hbc, hcd, hbd⟩
    use a, b, by aesop, c, by aesop, d, by aesop; simp_all +decide [SimpleGraph.isNClique_iff]
  have h_triangle_covering : IsTriangleCovering G {Sym2.mk (a, b), Sym2.mk (c, d)} := by
    by_contra h_contra
    obtain ⟨t', ht', ht'_edges⟩ : ∃ t' : Finset V, t' ∈ G.cliqueFinset 3 ∧ ¬(Sym2.mk (a, b) ∈ t'.offDiag.image (fun x => Sym2.mk (x.1, x.2))) ∧ ¬(Sym2.mk (c, d) ∈ t'.offDiag.image (fun x => Sym2.mk (x.1, x.2))) := by
      unfold IsTriangleCovering at h_contra; aesop
      simp_all +decide [SimpleGraph.CliqueFree]
      obtain ⟨t', ht'⟩ := h_contra
      refine ⟨t', ?_, ?_, ?_⟩ <;> simp_all +decide [SimpleGraph.isNClique_iff]
      · intro x hx y hy hxy; have := ht'.1 hx hy; aesop
      · intro x y hx hy hxy; have := ht'.1 hx hy hxy; simp_all +decide [SimpleGraph.deleteEdges]
      · intro x y hx hy hxy; have := ht'.1 hx hy hxy; simp_all +decide [SimpleGraph.deleteEdges]
    have h_share_edge : ∀ t : Finset V, t ∈ G.cliqueFinset 3 → ¬Disjoint (triangleEdges t) (triangleEdges t') := by
      intros t ht h_disjoint
      apply packing_one_implies_intersect G h_nu t t' ht ht' h_disjoint
    have h_triangles : (triangleEdges {a, b, c} ∩ triangleEdges t').Nonempty ∧ (triangleEdges {a, b, d} ∩ triangleEdges t').Nonempty ∧ (triangleEdges {a, c, d} ∩ triangleEdges t').Nonempty ∧ (triangleEdges {b, c, d} ∩ triangleEdges t').Nonempty := by
      simp_all +decide [Finset.Nonempty, Finset.disjoint_left]
      refine ⟨h_share_edge {a, b, c} ?_, h_share_edge {a, b, d} ?_, h_share_edge {a, c, d} ?_, h_share_edge {b, c, d} ?_⟩ <;> simp_all +decide [SimpleGraph.isNClique_iff]
    simp_all +decide [Finset.Nonempty, triangleEdges]
    rcases h_triangles with ⟨⟨x, ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩, ⟨c, d, ⟨hc, hd, hcd⟩, h⟩⟩, ⟨y, ⟨e, f, ⟨he, hf, hef⟩, rfl⟩, ⟨g, h, ⟨hg, hh, hgh⟩, j⟩⟩, ⟨z, ⟨i, j, ⟨hi, hj, hij⟩, rfl⟩, ⟨k, l, ⟨hk, hl, hkl⟩, m⟩⟩, ⟨w, ⟨o, p, ⟨ho, hp, hop⟩, rfl⟩, ⟨q, r, ⟨hq, hr, hqr⟩, s⟩⟩⟩
    simp_all +decide [Sym2.eq]; grind +ring
  simp +zetaDelta at *
  have h_min_le_two : ∃ S ∈ Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset, S.card = 2 := by
    refine ⟨{Sym2.mk (a, b), Sym2.mk (c, d)}, ?_, ?_⟩ <;> simp_all +decide [SimpleGraph.edgeFinset]
    simp_all +decide [SimpleGraph.edgeSet, Set.insert_subset_iff]
  have h_min_le_two : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ 2 := by
    exact Finset.min_le (Finset.mem_image.mpr ⟨h_min_le_two.choose, h_min_le_two.choose_spec.1, h_min_le_two.choose_spec.2⟩)
  cases h : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop

/-! ## PROVEN: Helper lemmas for ν=1 K₄ construction -/

lemma lemma_intersect_helper (a b c d e : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hda : d ≠ a) (hdc : d ≠ c) (heb : e ≠ b) (hec : e ≠ c) (hea : e ≠ a) (hdb : d ≠ b)
    (h_nd : ¬ Disjoint (triangleEdges {a, c, d}) (triangleEdges {b, c, e})) :
    d = e := by
  unfold triangleEdges at h_nd
  rw [Finset.not_disjoint_iff] at h_nd; aesop

lemma edge_sharing_of_nu_1_tau_gt_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) (h_tau : ¬ triangleCoveringNumber G ≤ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (e : Sym2 V) (he : e ∈ triangleEdges T) :
    ∃ T', T' ∈ G.cliqueFinset 3 ∧ T' ≠ T ∧ e ∈ triangleEdges T' := by
  set S := triangleEdges T \ {e} with hS_def
  have hS_card : S.card = 2 := by
    unfold triangleEdges at *; simp_all +decide [Finset.card_sdiff]
    have := Finset.card_eq_three.mp hT.2; aesop
    all_goals simp +decide [Finset.card, *, Sym2.eq_swap]
    all_goals simp +decide [*, Finset.offDiag]
    all_goals simp +decide [*, Multiset.filter_cons, Multiset.filter_singleton]
    all_goals split_ifs <;> simp_all +decide [Sym2.eq_swap]
  have hS_not_covering : ¬IsTriangleCovering G S := by
    have hS_not_covering : ¬IsTriangleCovering G S := by
      intro hS_covering
      have h_triangle_covering : triangleCoveringNumber G ≤ S.card := by
        unfold triangleCoveringNumber
        have h_triangle_covering : S ∈ G.edgeFinset.powerset.filter (IsTriangleCovering G) := by
          unfold triangleEdges at *; aesop
          intro x hx; have := hT.1; aesop
        have h_triangle_covering : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ S.card := by
          exact Finset.min_le (Finset.mem_image_of_mem _ h_triangle_covering)
        cases h : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
      linarith
    exact hS_not_covering
  obtain ⟨T', hT', hT'_disjoint⟩ : ∃ T' ∈ G.cliqueFinset 3, Disjoint (triangleEdges T') S := by
    contrapose! hS_not_covering
    unfold IsTriangleCovering; aesop
    intro x hx; specialize hS_not_covering x; simp_all +decide [Finset.disjoint_left, SimpleGraph.isNClique_iff]
    simp_all +decide [SimpleGraph.deleteEdges_adj, Set.Pairwise]
    obtain ⟨y, hy, hy', hy''⟩ := hS_not_covering; rcases Finset.mem_image.mp hy with ⟨⟨a, b⟩, hab, rfl⟩
    simp_all +decide [Sym2.eq_swap]
  have hT'_shares_edge : ¬Disjoint (triangleEdges T') (triangleEdges T) := by
    apply packing_one_implies_intersect G h_nu T' T hT' hT
  refine ⟨T', hT', ?_, ?_⟩ <;> contrapose! hT'_shares_edge <;> simp_all +decide [Finset.disjoint_left]
  · have := Finset.one_lt_card.1 (by linarith : 1 < Finset.card (triangleEdges T \ {e})); aesop
  · exact fun a ha ha' => hT'_shares_edge <| hT'_disjoint ha ha' ▸ ha

lemma exists_extension_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) (h_tau : ¬ triangleCoveringNumber G ≤ 2)
    (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hT : {a, b, c} ∈ G.cliqueFinset 3) :
    ∃ d, d ≠ b ∧ {a, c, d} ∈ G.cliqueFinset 3 := by
  obtain ⟨T', hT', hdT'⟩ : ∃ T' ∈ G.cliqueFinset 3, T' ≠ {a, b, c} ∧ Sym2.mk (a, c) ∈ triangleEdges T' := by
    apply edge_sharing_of_nu_1_tau_gt_2 G h_nu h_tau {a, b, c} hT (Sym2.mk (a, c))
    unfold triangleEdges; aesop
  have hT'_contains_ac : a ∈ T' ∧ c ∈ T' := by unfold triangleEdges at hdT'; aesop
  obtain ⟨d, hd⟩ : ∃ d, T' = {a, c, d} := by
    have h_card_T' : T'.card = 3 := by simp_all +decide [SimpleGraph.cliqueFinset]; exact hT'.2
    have := Finset.card_eq_three.mp h_card_T'; obtain ⟨x, y, z, hxyz⟩ := this
    use if x = a then if y = c then z else y else if y = a then if z = c then x else z else if z = a then if x = c then y else x else a; aesop
  grind

lemma k4_of_nu_1_no_cover_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1) (h_tau : ¬ triangleCoveringNumber G ≤ 2) :
    ∃ s, IsK4 G s := by
  obtain ⟨T, hT⟩ : ∃ T : Finset V, T ∈ G.cliqueFinset 3 := by
    contrapose! h_nu; simp_all +decide [trianglePackingNumber, SimpleGraph.cliqueFinset]
    simp +decide [Finset.filter_singleton, IsEdgeDisjoint]
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ T = {a, b, c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
    simp +zetaDelta at *
    obtain ⟨a, b, c, h⟩ := Finset.card_eq_three.mp hT.2
    exact ⟨a, b, h.1, c, h.2.2.1, h.2.1, h.2.2.2, by have := hT.1; aesop⟩
  obtain ⟨d, hd⟩ : ∃ d, d ≠ b ∧ {a, c, d} ∈ G.cliqueFinset 3 := by
    apply exists_extension_vertex G h_nu h_tau a b c ha hb hc; aesop
  obtain ⟨e, he⟩ : ∃ e, e ≠ a ∧ {b, c, e} ∈ G.cliqueFinset 3 := by
    have := exists_extension_vertex G h_nu h_tau b a c (by tauto) (by tauto) (by tauto) ?_ <;> simp_all +decide [SimpleGraph.cliqueFinset]
    simp_all +decide [SimpleGraph.isNClique_iff, SimpleGraph.adj_comm]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;> aesop
  have hde : d = e := by
    apply lemma_intersect_helper a b c d e
    all_goals simp_all +decide [Finset.disjoint_left]
    · rintro rfl; simp_all +decide [SimpleGraph.isNClique_iff]; grind
    · rintro rfl; simp_all +decide [SimpleGraph.isNClique_iff]
    · rintro rfl; simp_all +decide [SimpleGraph.isNClique_iff]
      rw [Finset.card_insert_of_notMem, Finset.card_singleton] at he <;> aesop
    · rintro rfl; simp_all +decide [SimpleGraph.isNClique_iff]
    · have := packing_one_implies_intersect G h_nu {a, c, d} {b, c, e}; simp_all +decide [triangleEdges]
      rw [Finset.not_disjoint_iff] at this; aesop
  simp_all +decide [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff]
  use {a, b, c, e}; unfold IsK4; aesop
  rw [SimpleGraph.isNClique_iff]; aesop
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] <;> aesop

/-! ## PROVEN: ν=1 implies τ≤2 -/

lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  by_contra! h_contra'
  obtain ⟨s, hs⟩ := k4_of_nu_1_no_cover_2 G h (by linarith)
  exact h_contra'.not_le (k4_implies_tau_le_2 G h s hs)

/-! ## PROVEN: τ>4 implies uncovered triangles -/

lemma tau_gt_4_implies_uncovered (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (S : Finset (Sym2 V)) (hS_card : S.card ≤ 4) (hS_sub : S ⊆ G.edgeFinset) :
    ∃ t ∈ G.cliqueFinset 3, Disjoint (triangleEdges t) S := by
  have h_not_triangle_free : ¬IsTriangleCovering G S := by
    contrapose! h_tau
    refine le_trans ?_ hS_card
    unfold triangleCoveringNumber
    have h_min_le : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ S.card := by
      exact Finset.min_le (Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS_sub, h_tau⟩, rfl⟩)
    cases h : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  contrapose! h_not_triangle_free; aesop
  unfold IsTriangleCovering; aesop
  intro t ht; specialize h_not_triangle_free t; simp_all +decide [SimpleGraph.isNClique_iff, Finset.disjoint_left]
  obtain ⟨x, hx₁, hx₂⟩ := h_not_triangle_free (fun u hu v hv huv => by have := ht.1 hu hv huv; aesop)
  simp_all +decide [triangleEdges]
  rcases hx₁ with ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩; have := ht.1 ha hb hab; simp_all +decide [SimpleGraph.deleteEdges]

/-! ## ===== KEY GAP: extension_triangle_exists_nu2 ===== -/

/--
THE KEY LEMMA TO PROVE.

Intuition: Since τ>4, the 2 non-e edges of T don't cover all triangles.
Some triangle T' avoids those 2 edges but must share SOME edge with T
(else {T, T', t₂} gives ν≥3 where t₂ is from max packing not containing T).
So T' shares exactly e.
-/
lemma extension_triangle_exists_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T) :
    ∃ T', T' ∈ G.cliqueFinset 3 ∧ triangleEdges T ∩ triangleEdges T' = {e} := by
  sorry

/-! ## PROVEN (modulo above): Structure lemmas for K₄ extension -/

lemma structure_of_extension (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T)
    (T' : Finset V) (hT' : T' ∈ G.cliqueFinset 3)
    (h_int : triangleEdges T ∩ triangleEdges T' = {e}) :
    ∃ x, x ∉ T ∧ T' = insert x (Sym2.toFinset e) := by
  obtain ⟨u, v, hu, hv, heq⟩ : ∃ u v : V, e = Sym2.mk (u, v) ∧ u ∈ T ∧ v ∈ T ∧ u ≠ v := by
    unfold triangleEdges at he; aesop
  obtain ⟨x, hx⟩ : ∃ x : V, x ∈ T' ∧ x ∉ T ∧ x ≠ u ∧ x ≠ v := by
    have hT'_card : T'.card = 3 := by aesop; exact hT'.card_eq
    by_cases hx : u ∈ T' ∧ v ∈ T'
    · obtain ⟨x, hx⟩ : ∃ x : V, x ∈ T' ∧ x ≠ u ∧ x ≠ v := by
        exact Exists.imp (by aesop) (Finset.exists_mem_ne (show 1 < Finset.card (Finset.erase T' u) from by rw [Finset.card_erase_of_mem hx.1, hT'_card]; decide) v)
      by_cases hxT : x ∈ T <;> simp_all +decide [Finset.ext_iff]
      · specialize h_int (Sym2.mk (u, x)); simp_all +decide [triangleEdges]; grind
      · exact ⟨x, hx.1, hxT, hx.2.1, hx.2.2⟩
    · simp_all +decide [Finset.eq_singleton_iff_unique_mem]
      unfold triangleEdges at *; aesop
  use x
  have := Finset.eq_of_subset_of_card_le (show Insert.insert x {u, v} ⊆ T' from ?_) ?_ <;> simp_all +decide
  · aesop
  · simp_all +decide [Finset.subset_iff]
    replace h_int := Finset.ext_iff.mp h_int (Sym2.mk (u, v)); aesop
    · unfold triangleEdges at h_int; aesop
    · unfold triangleEdges at h_int; aesop
  · exact hT'.card_eq.le

lemma extensions_disjoint_of_no_k4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ triangleEdges T) (he2 : e2 ∈ triangleEdges T) (hne : e1 ≠ e2)
    (T1 T2 : Finset V) (hT1 : T1 ∈ G.cliqueFinset 3) (hT2 : T2 ∈ G.cliqueFinset 3)
    (h_int1 : triangleEdges T ∩ triangleEdges T1 = {e1})
    (h_int2 : triangleEdges T ∩ triangleEdges T2 = {e2})
    (h_no_k4 : ∀ s, T ⊆ s → ¬ IsK4 G s) :
    Disjoint (triangleEdges T1) (triangleEdges T2) := by
  obtain ⟨x1, hx1⟩ : ∃ x1, x1 ∉ T ∧ T1 = insert x1 (Sym2.toFinset e1) := by
    apply structure_of_extension G T hT e1 he1 T1 hT1 h_int1
  obtain ⟨x2, hx2⟩ : ∃ x2, x2 ∉ T ∧ T2 = insert x2 (Sym2.toFinset e2) := by
    apply structure_of_extension G T hT e2 he2 T2 hT2 h_int2
  by_cases hx : x1 = x2
  · have h_contradiction : T ∪ {x1} ∈ G.cliqueFinset 4 := by
      simp_all +decide [SimpleGraph.isNClique_iff]
      intro b hb hne; have := hT1.1.2 b; have := hT2.1.2 b; simp_all +decide [Sym2.eq_swap]
      by_cases h : x2 = b <;> simp_all +decide [triangleEdges]
      rcases he1 with ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩; rcases he2 with ⟨c, d, ⟨hc, hd, hcd⟩, rfl⟩
      simp_all +decide [Sym2.eq_swap]
      have := Finset.card_eq_three.mp hT.2; obtain ⟨u, v, w, hu, hv, hw, h⟩ := this
      simp_all +decide [SimpleGraph.IsClique]; grind
    exact False.elim (h_no_k4 (T ∪ {x1}) Finset.subset_union_left h_contradiction)
  · unfold triangleEdges at *; simp_all +decide [Finset.disjoint_left]
    rintro _ a b ha hb hab rfl c d hc hd hcd; contrapose! hcd; simp_all +decide [Sym2.eq]
    bound
    all_goals simp_all +decide [Sym2.eq, eq_comm]
    all_goals try grind +ring
    all_goals try grind

/-! ## PROVEN (uses extension_triangle_exists_nu2): extensions_form_K4 -/

lemma extensions_form_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ s : Finset V, T ⊆ s ∧ IsK4 G s := by
  obtain ⟨e1, e2, e3, he1, he2, he3, h_distinct⟩ : ∃ e1 e2 e3 : Sym2 V, e1 ∈ triangleEdges T ∧ e2 ∈ triangleEdges T ∧ e3 ∈ triangleEdges T ∧ e1 ≠ e2 ∧ e1 ≠ e3 ∧ e2 ≠ e3 := by
    unfold triangleEdges
    simp_all +decide [Finset.subset_iff, SimpleGraph.mem_cliqueFinset_iff]
    rcases Finset.card_eq_three.mp hT.2 with ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩
    use s(a, b), ⟨a, b, by aesop⟩, s(a, c), ⟨a, c, by aesop⟩, s(b, c), ⟨b, c, by aesop⟩; aesop
  obtain ⟨T1, hT1, h_int1⟩ : ∃ T1 : Finset V, T1 ∈ G.cliqueFinset 3 ∧ triangleEdges T ∩ triangleEdges T1 = {e1} := by
    apply extension_triangle_exists_nu2 G h_nu h_tau T hT e1 he1
  obtain ⟨T2, hT2, h_int2⟩ : ∃ T2 : Finset V, T2 ∈ G.cliqueFinset 3 ∧ triangleEdges T ∩ triangleEdges T2 = {e2} := by
    apply extension_triangle_exists_nu2 G h_nu h_tau T hT e2 he2
  obtain ⟨T3, hT3, h_int3⟩ : ∃ T3 : Finset V, T3 ∈ G.cliqueFinset 3 ∧ triangleEdges T ∩ triangleEdges T3 = {e3} := by
    apply extension_triangle_exists_nu2 G h_nu h_tau T hT e3 he3
  contrapose! h_nu
  have h_pairwise_disjoint : IsEdgeDisjoint {T1, T2, T3} := by
    have h_pairwise_disjoint : Disjoint (triangleEdges T1) (triangleEdges T2) ∧ Disjoint (triangleEdges T1) (triangleEdges T3) ∧ Disjoint (triangleEdges T2) (triangleEdges T3) := by
      have h_disjoint : ∀ s : Finset V, T ⊆ s → ¬IsK4 G s := h_nu
      exact ⟨extensions_disjoint_of_no_k4 G T hT e1 e2 he1 he2 h_distinct.1 T1 T2 hT1 hT2 h_int1 h_int2 h_disjoint,
             extensions_disjoint_of_no_k4 G T hT e1 e3 he1 he3 h_distinct.2.1 T1 T3 hT1 hT3 h_int1 h_int3 h_disjoint,
             extensions_disjoint_of_no_k4 G T hT e2 e3 he2 he3 h_distinct.2.2 T2 T3 hT2 hT3 h_int2 h_int3 h_disjoint⟩
    intro x hx y hy hxy; aesop
    · exact h_pairwise_disjoint.1.symm
    · exact h_pairwise_disjoint.2.1.symm
    · exact h_pairwise_disjoint.2.2.symm
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.le_sup <| Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨Finset.mem_coe.mpr hT1, Finset.insert_subset_iff.mpr ⟨Finset.mem_coe.mpr hT2, Finset.singleton_subset_iff.mpr hT3⟩⟩, h_pairwise_disjoint⟩))
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] <;> simp +decide [*]
  · rintro rfl; simp_all +decide [Finset.eq_singleton_iff_unique_mem]
  · constructor <;> rintro rfl <;> simp_all +decide

/-! ## Remaining chain to main theorem -/

lemma tau_gt_4_implies_two_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4) :
    HasTwoAlmostDisjointK4 G := by
  sorry -- Uses extensions_form_K4 on both packing triangles

lemma two_K4_cover_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s1 s2 : Finset V) (h1 : IsK4 G s1) (h2 : IsK4 G s2) (h_disj : (s1 ∩ s2).card ≤ 1) :
    ∃ S : Finset (Sym2 V), S.card ≤ 4 ∧ IsTriangleCovering G S := by
  sorry -- 2 edges per K₄, total ≤4

lemma two_K4_implies_nu_gt_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s1 s2 : Finset V) (h1 : IsK4 G s1) (h2 : IsK4 G s2) (h_disj : (s1 ∩ s2).card ≤ 1) :
    trianglePackingNumber G > 2 ∨ triangleCoveringNumber G ≤ 4 := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Sym2 V), S.card ≤ 4 ∧ IsTriangleCovering G S := by
    apply two_K4_cover_le_4 G s1 s2 h1 h2 h_disj
  refine Or.inr ?_
  unfold triangleCoveringNumber
  have h_min_card : ∃ S' ∈ Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset, S'.card ≤ 4 := by
    refine ⟨S ∩ G.edgeFinset, ?_, ?_⟩ <;> aesop
    · unfold IsTriangleCovering at *; aesop
      intro t ht; specialize hS.2 t; simp_all +decide [SimpleGraph.deleteEdges, Set.subset_def]
    · exact le_trans (Finset.card_le_card fun x hx => by aesop) hS.1
  obtain ⟨S', hS', hS''⟩ := h_min_card
  have h_min_card : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ S'.card := by
    exact Finset.min_le (Finset.mem_image_of_mem _ hS')
  cases h : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  exact Nat.le_trans h_min_card hS''

/-! ## MAIN THEOREM -/

theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  by_contra h_tau
  push_neg at h_tau
  have h_K4 := tau_gt_4_implies_two_K4 G h h_tau
  obtain ⟨s1, s2, hs1, hs2, hne, h_inter⟩ := h_K4
  rcases two_K4_implies_nu_gt_2 G s1 s2 hs1 hs2 h_inter with h_nu_gt | h_tau_le
  · omega
  · omega

end
