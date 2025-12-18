/-
TUZA'S CONJECTURE ν=2 - v9: ROBUSTIFIED (Grok + Gemini reviewed)

=== BREAKTHROUGH: extension_triangle_exists_nu2 PROVEN BY ARISTOTLE (7a29e24c) ===

PROVEN lemmas from 7a29e24c output:
1. nu_eq_two_of_unique_edge
2. packing_intersects_unique_triangle_edges
3. nu_le_one_of_disjoint_T
4. covering_le_delete_add_card
5. nu_le_one_of_delete_other_edges
6. unique_edge_implies_tau_le_4
7. triangle_share_edge_implies_eq_or_intersect_eq_singleton
8. extension_triangle_exists_nu2 (THE KEY GAP - NOW PROVEN!)

=== NEW HELPER LEMMAS (v9) ===
9. triangle_shares_edge_with_packing - any triangle shares edge with packing (ν≥3 otherwise)
10. tau_gt_4_implies_two_K4_with_packing - tracks which packing triangles extend to K₄s

=== REMAINING 2 GAPS (ROBUSTIFIED per Gemini) ===
1. tau_gt_4_implies_two_K4 - K₄s are almost-disjoint since base triangles edge-disjoint
2. two_K4_cover_le_4 - NOW TAKES h_nu, packing triangles as hypotheses
   Key: All triangles share edge with packing → contained in K₄s → τ(K₄)=2 each → total ≤4

=== PROOF ARCHITECTURE ===
  ν = 2 ∧ τ > 4
      ↓ exists_max_packing
  Get packing P = {T₁, T₂} with Disjoint(edges(T₁), edges(T₂))
      ↓ extensions_form_K4 (uses extension_triangle_exists_nu2 ✅)
  T₁ ⊆ K₄¹, T₂ ⊆ K₄²
      ↓ triangle_shares_edge_with_packing
  Every triangle T shares edge with T₁ or T₂
      ↓ two_K4_cover_le_4 (sorry - uses ν=2 constraint)
  Triangles sharing with Tᵢ are inside K₄ⁱ → τ ≤ 2+2 = 4
      → Contradiction with τ > 4
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

/-! ## PROVEN: v=1 implies any two triangles share edge -/

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

/-! ## PROVEN: K4 implies tau<=2 when v=1 -/

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

/-! ## PROVEN: Helper lemmas for v=1 K4 construction -/

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

/-! ## PROVEN: v=1 implies tau<=2 -/

lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  by_contra! h_contra'
  obtain ⟨s, hs⟩ := k4_of_nu_1_no_cover_2 G h (by linarith)
  exact h_contra'.not_le (k4_implies_tau_le_2 G h s hs)

/-! ## PROVEN: tau>4 implies uncovered triangles -/

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

/-! ## ===== PROVEN BY ARISTOTLE (7a29e24c): Helper lemmas for extension_triangle_exists_nu2 ===== -/

noncomputable section AristotleLemmas

lemma nu_eq_two_of_unique_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T)
    (h_unique : ∀ T', T' ∈ G.cliqueFinset 3 → e ∈ triangleEdges T' → T' = T) :
    trianglePackingNumber (G.deleteEdges {e}) = 2 := by
      have h_tau_gt_3 : triangleCoveringNumber (G.deleteEdges {e}) > 3 := by
        have h_tau_le : triangleCoveringNumber G ≤ triangleCoveringNumber (G.deleteEdges {e}) + 1 := by
          unfold triangleCoveringNumber at *; aesop;
          obtain ⟨S, hS⟩ : ∃ S : Finset (Sym2 V), S ⊆ (G.deleteEdges {e}).edgeFinset ∧ IsTriangleCovering (G.deleteEdges {e}) S ∧ S.card = Option.getD (Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset)).min (Finset.filter (Membership.mem (G.deleteEdges {e}).edgeSet) Finset.univ).card := by
            have h_exists_min : ∃ S ∈ Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset, S.card = Option.getD (Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset)).min (Finset.filter (Membership.mem (G.deleteEdges {e}).edgeSet) Finset.univ).card := by
              have h_exists_min : Finset.Nonempty (Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset) := by
                refine' ⟨ ( G.deleteEdges { e } ).edgeFinset, _ ⟩ ; simp +decide [ IsTriangleCovering ];
              have h_exists_min : ∃ S ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset), S = Option.getD (Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset)).min (Finset.filter (Membership.mem (G.deleteEdges {e}).edgeSet) Finset.univ).card := by
                have h_exists_min : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset)) = some (Option.getD (Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges {e})) (G.deleteEdges {e}).edgeFinset.powerset)).min (Finset.filter (Membership.mem (G.deleteEdges {e}).edgeSet) Finset.univ).card) := by
                  cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering ( G.deleteEdges { e } ) ) ( G.deleteEdges { e } ).edgeFinset.powerset ) ) <;> aesop;
                  contrapose! h;
                  obtain ⟨ x, hx ⟩ := h_exists_min; use x; aesop;
                exact ⟨ _, Finset.mem_of_min h_exists_min, rfl ⟩;
              aesop;
            exact ⟨ h_exists_min.choose, Finset.mem_powerset.mp ( Finset.mem_filter.mp h_exists_min.choose_spec.1 |>.1 ), Finset.mem_filter.mp h_exists_min.choose_spec.1 |>.2, h_exists_min.choose_spec.2 ⟩;
          have hS_plus_e : IsTriangleCovering G (S ∪ {e}) := by
            unfold IsTriangleCovering at *; aesop;
          have h_tau_le_card : triangleCoveringNumber G ≤ (S ∪ {e}).card := by
            unfold triangleCoveringNumber; aesop;
            have h_tau_le_card : (Insert.insert e S).card ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
              simp_all +decide [ Finset.subset_iff, Set.subset_def ];
              use Insert.insert e S; aesop;
              · unfold triangleEdges at he; aesop;
                have := hT.1; aesop;
              · specialize left a a_1; simp_all +decide [ SimpleGraph.deleteEdges ] ;
            have := Finset.min_le h_tau_le_card; aesop;
            cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
          convert h_tau_le_card.trans _ using 1;
          · unfold triangleCoveringNumber; aesop;
          · exact le_trans ( Finset.card_union_le _ _ ) ( by simp +decide [ hS.2.2 ] )
        linarith [h_tau];
      by_cases h_nu_le_1 : trianglePackingNumber (G.deleteEdges {e}) ≤ 1;
      · have h_contra : triangleCoveringNumber (G.deleteEdges {e}) ≤ 2 := by
          apply tuza_case_nu_1;
          interval_cases _ : trianglePackingNumber ( G.deleteEdges { e } ) <;> simp_all +decide;
          have h_no_triangles : ∀ t ∈ (G.deleteEdges {e}).cliqueFinset 3, False := by
            unfold trianglePackingNumber at *; aesop;
            specialize ‹∀ i ⊆ ( G.deleteEdges { e } ).cliqueFinset 3, IsEdgeDisjoint i → i = ∅› { t } ; simp_all +decide [ IsEdgeDisjoint ];
          unfold triangleCoveringNumber at h_tau_gt_3;
          unfold IsTriangleCovering at h_tau_gt_3;
          simp_all +decide [ Finset.min ];
          rw [ Finset.inf_eq_bot_iff.mpr ] at h_tau_gt_3 <;> simp_all +decide [ Option.getD ];
          exact fun t ht => h_no_triangles t ht;
        grind;
      · refine' le_antisymm _ _;
        · have h_subgraph : (G.deleteEdges {e}).cliqueFinset 3 ⊆ G.cliqueFinset 3 := by
            intro t ht; simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ] ;
            intro u hu v hv huv; have := ht.1 hu hv huv; aesop;
          refine' h_nu ▸ Finset.sup_mono _;
          simp_all +decide [ Finset.subset_iff ];
        · linarith

lemma packing_intersects_unique_triangle_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T)
    (h_unique : ∀ T', T' ∈ G.cliqueFinset 3 → e ∈ triangleEdges T' → T' = T)
    (P : Finset (Finset V)) (hP : P ⊆ (G.deleteEdges {e}).cliqueFinset 3)
    (hP_disjoint : IsEdgeDisjoint P) (hP_card : P.card = 2) :
    ¬ Disjoint (P.biUnion triangleEdges) (triangleEdges T) := by
      contrapose! h_unique;
      have h_union : P ∪ {T} ⊆ G.cliqueFinset 3 := by
        simp_all +decide [ Finset.subset_iff ];
        intro x hx; specialize hP hx; rw [ SimpleGraph.isNClique_iff ] at *; aesop;
        intro u hu v hv huv; specialize left_1 hu hv; aesop;
      have h_union_disjoint : IsEdgeDisjoint (P ∪ {T}) := by
        intro a ha b hb hab; cases Finset.mem_union.mp ha <;> cases Finset.mem_union.mp hb <;> aesop;
        · exact h_unique.mono_left ( Finset.subset_biUnion_of_mem _ h );
        · exact h_unique.mono_left ( Finset.subset_biUnion_of_mem triangleEdges h_1 ) |> Disjoint.symm
      have h_union_card : (P ∪ {T}).card = 3 := by
        simp_all +decide [ Finset.disjoint_left ];
        grind;
      have h_contradiction : trianglePackingNumber G ≥ 3 := by
        refine' le_trans _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_union, h_union_disjoint ⟩ ) ; aesop;
      linarith

lemma nu_le_one_of_disjoint_T (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    trianglePackingNumber (G.deleteEdges (triangleEdges T)) ≤ 1 := by
      by_contra h_contra
      obtain ⟨P, hP⟩ : ∃ P : Finset (Finset V), P ⊆ (G.deleteEdges (↑(triangleEdges T) : Set (Sym2 V))).cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = 2 := by
        obtain ⟨P, hP_sub, hP_disjoint, hP_card⟩ : ∃ P : Finset (Finset V), P ⊆ (G.deleteEdges (triangleEdges T)).cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber (G.deleteEdges (triangleEdges T)) := by
          apply exists_max_packing;
        obtain ⟨Q, hQ_sub, hQ_card⟩ : ∃ Q : Finset (Finset V), Q ⊆ P ∧ Q.card = 2 := by
          exact Finset.exists_subset_card_eq ( by linarith );
        exact ⟨ Q, Finset.Subset.trans hQ_sub hP_sub, fun s hs t ht hst => hP_disjoint ( hQ_sub hs ) ( hQ_sub ht ) hst, hQ_card ⟩;
      have hP_disjoint : ∀ T' ∈ P, Disjoint (triangleEdges T') (triangleEdges T) := by
        intro T' hT'
        have hT'_edges : ∀ e ∈ triangleEdges T', e ∈ (G.deleteEdges (↑(triangleEdges T) : Set (Sym2 V))).edgeFinset := by
          intro e he
          have hT'_edges : e ∈ (G.deleteEdges (↑(triangleEdges T) : Set (Sym2 V))).edgeFinset := by
            have hT'_clique : T' ∈ (G.deleteEdges (↑(triangleEdges T) : Set (Sym2 V))).cliqueFinset 3 := by
              exact hP.1 hT'
            unfold triangleEdges at he; aesop;
            · have := hT'_clique.1 left_2 left_3; aesop;
            · have := hT'_clique.1 left_2 left_3; simp_all +decide [ SimpleGraph.deleteEdges_adj ] ;
          exact hT'_edges;
        rw [ Finset.disjoint_left ] ; aesop;
        specialize hT'_edges a a_1 ; simp_all +decide [ SimpleGraph.deleteEdges ];
      have hP_union_T : IsEdgeDisjoint (insert T P) := by
        intro x hx y hy hxy; aesop;
        · exact Disjoint.symm ( hP_disjoint y h_2 );
        · exact left_1 h_1 h_2 hxy;
      have hP_union_T_card : (insert T P).card = 3 := by
        rw [ Finset.card_insert_of_notMem ] <;> aesop;
        specialize hP_disjoint T a ; simp_all +decide [ Finset.disjoint_left ];
        unfold triangleEdges at hP_disjoint; simp_all +decide [ Finset.ext_iff ] ;
        rcases Finset.card_eq_three.mp hT.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; specialize hP_disjoint ( Sym2.mk ( x, y ) ) x y ; aesop;
      have h_contra : trianglePackingNumber G ≥ (insert T P).card := by
        refine' Finset.le_sup ( f := Finset.card ) _;
        simp_all +decide [ Finset.subset_iff ];
        intro T' hT'; specialize hP; have := hP.1 hT'; simp_all +decide [ SimpleGraph.IsNClique ] ;
        have := hP.1 hT'; rw [ SimpleGraph.isNClique_iff ] at *; aesop;
        intro x hx y hy; specialize left_2 hx hy; aesop;
      linarith

lemma covering_le_delete_add_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset (Sym2 V)) :
    triangleCoveringNumber G ≤ triangleCoveringNumber (G.deleteEdges U) + U.card := by
      obtain ⟨C, hC⟩ : ∃ C : Finset (Sym2 V), C ⊆ (G.deleteEdges U).edgeFinset ∧ IsTriangleCovering (G.deleteEdges U) C ∧ C.card = triangleCoveringNumber (G.deleteEdges U) := by
        have h_exists_C : ∃ C : Finset (Sym2 V), C ⊆ (G.deleteEdges U).edgeFinset ∧ IsTriangleCovering (G.deleteEdges U) C ∧ C.card = triangleCoveringNumber (G.deleteEdges U) := by
          have h_min : ∃ C ∈ (G.deleteEdges U).edgeFinset.powerset.filter (IsTriangleCovering (G.deleteEdges U)), ∀ D ∈ (G.deleteEdges U).edgeFinset.powerset.filter (IsTriangleCovering (G.deleteEdges U)), C.card ≤ D.card := by
            apply_rules [ Finset.exists_min_image ];
            refine' ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_iff.mpr _ ), _ ⟩ ⟩;
            exact ( G.deleteEdges ( U : Set ( Sym2 V ) ) ).edgeFinset;
            · exact fun _ _ => by assumption;
            · unfold IsTriangleCovering; aesop;
          unfold triangleCoveringNumber; aesop;
          have h_min : (Finset.image Finset.card (Finset.filter (IsTriangleCovering (G.deleteEdges U)) (G.deleteEdges U).edgeFinset.powerset)).min = some w.card := by
            refine' le_antisymm _ _ <;> simp_all +decide [ Finset.min ];
            · refine' Finset.inf_le _ ; aesop;
            · exact fun D hD hD' => WithTop.coe_le_coe.mpr ( right D hD hD' );
          aesop;
        exact h_exists_C;
      set S := C ∪ U with hS;
      have hS_covering : IsTriangleCovering G S := by
        unfold IsTriangleCovering at *; aesop;
        simp_all +decide [ Set.union_comm ];
      have h_tau_le_S : triangleCoveringNumber G ≤ S.card := by
        have h_tau_le_S : triangleCoveringNumber G ≤ Finset.card (Finset.filter (fun e => e ∈ G.edgeFinset) S) := by
          have h_tau_le_S : ∀ S' : Finset (Sym2 V), S' ⊆ G.edgeFinset → IsTriangleCovering G S' → triangleCoveringNumber G ≤ S'.card := by
            unfold triangleCoveringNumber;
            intro S' hS'_sub hS'_covering
            have h_min : Finset.min (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) ≤ S'.card := by
              exact Finset.min_le ( Finset.mem_image.mpr ⟨ S', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS'_sub, hS'_covering ⟩, rfl ⟩ );
            cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
          apply h_tau_le_S;
          · exact fun x hx => Finset.mem_filter.mp hx |>.2;
          · unfold IsTriangleCovering at *; aesop;
            convert hS_covering using 1;
            ext; aesop;
        exact h_tau_le_S.trans ( Finset.card_filter_le _ _ );
      exact h_tau_le_S.trans ( Finset.card_union_le _ _ ) |> le_trans <| by rw [ hC.2.2 ] ;

lemma nu_le_one_of_delete_other_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T)
    (h_unique : ∀ T', T' ∈ G.cliqueFinset 3 → e ∈ triangleEdges T' → T' = T) :
    trianglePackingNumber (G.deleteEdges ((triangleEdges T).erase e)) ≤ 1 := by
      by_contra h_contra
      obtain ⟨P, hP⟩ : ∃ P : Finset (Finset V), P ⊆ (G.deleteEdges (↑((triangleEdges T).erase e) : Set (Sym2 V))).cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = 2 := by
        have h_exists_packing : ∃ P : Finset (Finset V), P ⊆ (G.deleteEdges ((triangleEdges T).erase e)).cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card > 1 := by
          contrapose! h_contra;
          exact Finset.sup_le fun x hx => h_contra x ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hx |>.1 ) ) ( Finset.mem_filter.mp hx |>.2 );
        obtain ⟨ P, hP₁, hP₂, hP₃ ⟩ := h_exists_packing;
        obtain ⟨ Q, hQ ⟩ := Finset.exists_subset_card_eq hP₃;
        exact ⟨ Q, Finset.Subset.trans hQ.1 hP₁, fun x hx y hy hxy => hP₂ ( hQ.1 hx ) ( hQ.1 hy ) hxy, hQ.2 ⟩;
      have hP_disjoint_U : ∀ T' ∈ P, Disjoint (triangleEdges T') ((triangleEdges T).erase e) := by
        intro T' hT'
        have hT'_in_G_minus_U : T' ∈ (G.deleteEdges ((triangleEdges T).erase e)).cliqueFinset 3 := by
          exact hP.1 hT';
        have hT'_in_G_minus_U : ∀ u ∈ T', ∀ v ∈ T', u ≠ v → ¬(Sym2.mk (u, v)) ∈ ((triangleEdges T).erase e) := by
          intro u hu v hv huv; intro h; have := hP.1 hT'; simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ] ;
          have := hT'_in_G_minus_U.1 hu hv; simp_all +decide [ SimpleGraph.deleteEdges ] ;
        exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by rcases Finset.mem_image.mp hx₁ with ⟨ ⟨ u, v ⟩, huv, rfl ⟩ ; exact hT'_in_G_minus_U u ( Finset.mem_offDiag.mp huv |>.1 ) v ( Finset.mem_offDiag.mp huv |>.2.1 ) ( Finset.mem_offDiag.mp huv |>.2.2 ) hx₂;
      have hP_disjoint_e : ∀ T' ∈ P, ¬(e ∈ triangleEdges T') := by
        intro T' hT' he'; specialize h_unique T' ?_ he'; simp_all +decide [ Finset.subset_iff ] ;
        · simp_all +decide [ SimpleGraph.isNClique_iff ];
          specialize hP ; have := hP.1 hT' ; aesop;
          exact left_1 hT' |>.1.mono ( by aesop_cat );
        · specialize hP_disjoint_U T' hT'; simp_all +decide [ Finset.disjoint_left ] ;
          have h_triangle_edges : (triangleEdges T).card = 3 := by
            unfold triangleEdges; aesop;
            have := Finset.card_eq_three.mp ( hT.card_eq ) ; aesop;
            simp +decide [ *, Finset.card ];
            simp +decide [ *, Finset.offDiag ];
            simp +decide [ *, Multiset.filter_cons, Multiset.filter_singleton ];
            split_ifs <;> simp_all +decide [ Sym2.eq_swap ];
          exact absurd ( Finset.card_le_one.mpr ( fun x hx y hy => by rw [ hP_disjoint_U hx, hP_disjoint_U hy ] ) ) ( by linarith );
      have hP_union_T : IsEdgeDisjoint (P ∪ {T}) := by
        simp_all +decide [ IsEdgeDisjoint ];
        intro x hx y hy hxy; aesop;
        · specialize hP_disjoint_U y h_2; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
        · specialize hP_disjoint_U x h_1; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
        · exact left_1 h_1 h_2 hxy;
      have hP_union_T_card : (P ∪ {T}).card = 3 := by
        grind;
      have h_contradiction : trianglePackingNumber G ≥ 3 := by
        refine' le_trans _ ( Finset.le_sup <| show P ∪ { T } ∈ ( G.cliqueFinset 3 |> Finset.powerset |> Finset.filter IsEdgeDisjoint ) from _ );
        · linarith;
        · simp_all +decide [ Finset.subset_iff ];
          intro T' hT'; specialize hP; have := hP.1 hT'; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact fun x hx y hy hxy => by have := hP.1 hT'; exact this.1 hx hy hxy |> fun h => by aesop;
      grind

lemma unique_edge_implies_tau_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T)
    (h_unique : ∀ T', T' ∈ G.cliqueFinset 3 → e ∈ triangleEdges T' → T' = T) :
    triangleCoveringNumber G ≤ 4 := by
      set U : Finset (Sym2 V) := (triangleEdges T).erase e
      have hU_card : U.card = 2 := by
        rw [ Finset.card_erase_of_mem he, show Finset.card ( triangleEdges T ) = 3 from ?_ ];
        unfold triangleEdges at *; aesop;
        have := Finset.card_eq_three.mp hT.2; aesop;
        all_goals simp +decide [ *, Finset.image_insert, Finset.offDiag_insert ] ;
      have h_tau_G_minus_U : triangleCoveringNumber (G.deleteEdges U) ≤ 2 := by
        have h_nu_G_minus_U : trianglePackingNumber (G.deleteEdges U) ≤ 1 := by
          convert nu_le_one_of_delete_other_edges G h_nu T hT e he h_unique using 1;
        cases h_nu_G_minus_U.eq_or_lt <;> simp_all +decide;
        · apply_rules [ tuza_case_nu_1 ];
        · have h_no_triangles : (G.deleteEdges U).cliqueFinset 3 = ∅ := by
            unfold trianglePackingNumber at *; aesop;
            exact fun x hx => by simpa using h { x } ( Finset.singleton_subset_iff.mpr <| by simpa using hx ) ( by simp +decide [ IsEdgeDisjoint ] ) ;
          unfold triangleCoveringNumber; aesop;
          unfold IsTriangleCovering; aesop;
          rw [ Finset.min_eq_inf_withTop ];
          rw [ Finset.inf_eq_iInf ];
          rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
          rotate_left;
          exact 0;
          · exact fun _ => zero_le _;
          · intro w hw;
            refine' ⟨ 0, _ ⟩ ; aesop;
          · exact Nat.zero_le _;
      exact le_trans ( covering_le_delete_add_card _ _ ) ( by linarith! )

lemma triangle_share_edge_implies_eq_or_intersect_eq_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (T T' : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT' : T' ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T) (he' : e ∈ triangleEdges T') :
    T = T' ∨ triangleEdges T ∩ triangleEdges T' = {e} := by
      by_contra h_neq
      push_neg at h_neq;
      have h_three_vertices : (Finset.card (T ∩ T')) ≥ 3 := by
        have h_three_vertices : (Finset.card (triangleEdges T ∩ triangleEdges T')) ≥ 2 := by
          exact Finset.one_lt_card.2 ⟨ e, Finset.mem_inter.2 ⟨ he, he' ⟩, by obtain ⟨ x, hx ⟩ := Finset.exists_of_ssubset ( lt_of_le_of_ne ( Finset.singleton_subset_iff.2 ( Finset.mem_inter.2 ⟨ he, he' ⟩ ) ) ( Ne.symm h_neq.2 ) ) ; aesop ⟩;
        have h_three_vertices : (triangleEdges T ∩ triangleEdges T') ⊆ Finset.image (fun p : V × V => Sym2.mk (p.1, p.2)) (Finset.offDiag (T ∩ T')) := by
          intro x hx; unfold triangleEdges at hx; aesop;
        have := Finset.card_le_card h_three_vertices; simp_all +decide [ Finset.card_image_of_injOn ] ;
        have h_three_vertices : (Finset.card (Finset.image (fun p : V × V => Sym2.mk p) (Finset.offDiag (T ∩ T')))) ≤ (Finset.card (T ∩ T')) * (Finset.card (T ∩ T') - 1) / 2 := by
          have h_three_vertices : (Finset.card (Finset.image (fun p : V × V => Sym2.mk p) (Finset.offDiag (T ∩ T')))) ≤ Finset.card (Finset.offDiag (T ∩ T')) / 2 := by
            have h_card_image : ∀ p ∈ Finset.offDiag (T ∩ T'), Finset.card (Finset.filter (fun q => Sym2.mk q = Sym2.mk p) (Finset.offDiag (T ∩ T'))) ≥ 2 := by
              intro p hp; have := Finset.card_pos.2 ⟨ p, Finset.mem_filter.2 ⟨ hp, rfl ⟩ ⟩ ; simp_all +decide [ Sym2.eq ] ;
              exact Finset.one_lt_card.2 ⟨ p, by aesop, p.swap, by aesop ⟩;
            have h_card_image : (Finset.offDiag (T ∩ T')).card = Finset.sum (Finset.image (fun p : V × V => Sym2.mk p) (Finset.offDiag (T ∩ T'))) (fun q => Finset.card (Finset.filter (fun p => Sym2.mk p = q) (Finset.offDiag (T ∩ T')))) := by
              rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; aesop;
            rw [ h_card_image, Nat.le_div_iff_mul_le zero_lt_two ];
            exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun x hx => show Finset.card ( Finset.filter ( fun p => Sym2.mk p = x ) ( Finset.offDiag ( T ∩ T' ) ) ) ≥ 2 from by rcases Finset.mem_image.mp hx with ⟨ p, hp, rfl ⟩ ; solve_by_elim );
          simp_all +decide [ Finset.offDiag_card ];
          rwa [ Nat.mul_sub_left_distrib, Nat.mul_one ];
        nlinarith [ Nat.div_mul_le_self ( ( T ∩ T' ).card * ( ( T ∩ T' ).card - 1 ) ) 2, Nat.sub_add_cancel ( show 1 ≤ ( T ∩ T' ).card from Nat.pos_of_ne_zero ( by aesop_cat ) ) ];
      have h_three_vertices : T ⊆ T' := by
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : T ∩ T' ⊆ T ) ; aesop;
        exact this ( by linarith [ hT.card_eq ] );
      have := Finset.eq_of_subset_of_card_le h_three_vertices ; simp_all +decide;
      exact this.ne ( by rw [ SimpleGraph.isNClique_iff ] at hT hT'; aesop )

end AristotleLemmas

/-! ## ===== PROVEN BY ARISTOTLE (7a29e24c): THE KEY GAP ===== -/

lemma extension_triangle_exists_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (e : Sym2 V) (he : e ∈ triangleEdges T) :
    ∃ T', T' ∈ G.cliqueFinset 3 ∧ triangleEdges T ∩ triangleEdges T' = {e} := by
  by_contra h_contra;
  have h_unique : ∀ T' ∈ G.cliqueFinset 3, e ∈ triangleEdges T' → T' = T := by
    intro T' hT' he';
    exact Classical.not_not.1 fun h => h_contra ⟨ T', hT', by have := triangle_share_edge_implies_eq_or_intersect_eq_singleton G T T' hT hT' e he he'; aesop ⟩;
  exact h_tau.not_le ( unique_edge_implies_tau_le_4 G h_nu T hT e he h_unique )

/-! ## PROVEN: Structure lemmas for K4 extension -/

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

/-! ## PROVEN: extensions_form_K4 -/

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

/-! ## Remaining gaps - ROBUSTIFIED per Gemini feedback -/

/-
KEY INSIGHT (Gemini): When ν=2, any triangle must share an edge with the packing.
If triangle T shares edge with packing triangle T₁ ⊆ K₄¹, then T is either:
  (a) inside K₄¹, or
  (b) would create ν≥3 (contradiction)
So all triangles are contained in K₄¹ ∪ K₄².
-/

/-- Any triangle in G must share an edge with some triangle in a maximal packing -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (P : Finset (Finset V)) (hP_sub : P ⊆ G.cliqueFinset 3)
    (hP_disj : IsEdgeDisjoint P) (hP_card : P.card = 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ T' ∈ P, ¬ Disjoint (triangleEdges T) (triangleEdges T') := by
  by_contra h_all_disjoint
  push_neg at h_all_disjoint
  -- If T is edge-disjoint from all packing triangles, then P ∪ {T} is a packing of size 3
  have h_new_packing : IsEdgeDisjoint (insert T P) := by
    intro x hx y hy hxy
    cases Finset.mem_insert.mp hx with
    | inl hxT =>
      cases Finset.mem_insert.mp hy with
      | inl hyT => simp_all
      | inr hyP => subst hxT; exact h_all_disjoint y hyP
    | inr hxP =>
      cases Finset.mem_insert.mp hy with
      | inl hyT => subst hyT; exact (h_all_disjoint x hxP).symm
      | inr hyP => exact hP_disj hxP hyP hxy
  have h_card_3 : (insert T P).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · omega
    · intro hTP
      have := h_all_disjoint T hTP
      simp_all +decide [Finset.disjoint_left]
      -- T shares all edges with itself
      unfold triangleEdges at this
      have hT_card := hT.card_eq
      rcases Finset.card_eq_three.mp hT_card with ⟨a, b, c, hab, hac, hbc, rfl⟩
      specialize this (Sym2.mk (a, b)) a b
      simp_all +decide
  have h_contra : trianglePackingNumber G ≥ 3 := by
    refine le_trans (by omega : 3 ≤ (insert T P).card) ?_
    refine Finset.le_sup (f := Finset.card) ?_
    refine Finset.mem_filter.mpr ⟨?_, h_new_packing⟩
    refine Finset.mem_powerset.mpr ?_
    intro x hx
    cases Finset.mem_insert.mp hx with
    | inl h => subst h; exact hT
    | inr h => exact hP_sub h
  omega

/-- Get two K₄s from the packing triangles. Tracks which packing triangles they extend. -/
lemma tau_gt_4_implies_two_K4_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4) :
    ∃ (T1 T2 : Finset V) (s1 s2 : Finset V),
      T1 ∈ G.cliqueFinset 3 ∧ T2 ∈ G.cliqueFinset 3 ∧
      Disjoint (triangleEdges T1) (triangleEdges T2) ∧
      T1 ⊆ s1 ∧ T2 ⊆ s2 ∧ IsK4 G s1 ∧ IsK4 G s2 := by
  -- Get the maximal packing
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  rw [h_nu] at hP_card
  -- Extract two triangles from the packing
  obtain ⟨T1, T2, hT1P, hT2P, hne, hP_eq⟩ : ∃ T1 T2 : Finset V,
      T1 ∈ P ∧ T2 ∈ P ∧ T1 ≠ T2 ∧ P = {T1, T2} := by
    have := Finset.card_eq_two.mp hP_card
    obtain ⟨a, b, hab, rfl⟩ := this
    exact ⟨a, b, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
           hab, rfl⟩
  have hT1 : T1 ∈ G.cliqueFinset 3 := hP_sub hT1P
  have hT2 : T2 ∈ G.cliqueFinset 3 := hP_sub hT2P
  have h_edge_disj : Disjoint (triangleEdges T1) (triangleEdges T2) := hP_disj hT1P hT2P hne
  -- Each packing triangle extends to a K₄
  obtain ⟨s1, hs1_sub, hs1_K4⟩ := extensions_form_K4 G h_nu h_tau T1 hT1
  obtain ⟨s2, hs2_sub, hs2_K4⟩ := extensions_form_K4 G h_nu h_tau T2 hT2
  exact ⟨T1, T2, s1, s2, hT1, hT2, h_edge_disj, hs1_sub, hs2_sub, hs1_K4, hs2_K4⟩

lemma tau_gt_4_implies_two_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2) (h_tau : triangleCoveringNumber G > 4) :
    HasTwoAlmostDisjointK4 G := by
  obtain ⟨T1, T2, s1, s2, _, _, h_edge_disj, hs1_sub, hs2_sub, hs1_K4, hs2_K4⟩ :=
    tau_gt_4_implies_two_K4_with_packing G h_nu h_tau
  -- The K₄s s1 and s2 are almost-disjoint because their base triangles are edge-disjoint
  -- If |s1 ∩ s2| ≥ 2, they share an edge, but T1 ⊆ s1 and T2 ⊆ s2 are edge-disjoint
  -- So s1 ≠ s2 and their intersection is at most 1 vertex
  sorry

/-- Helper (Gemini): If T shares edge with T_base ⊆ K₄ but T ⊈ K₄,
    there exists U ⊆ K₄ disjoint from T (the "outlier" argument). -/
lemma exists_disjoint_in_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : IsK4 G s)
    (T_base : Finset V) (hT_base_sub : T_base ⊆ s) (hT_base : T_base ∈ G.cliqueFinset 3)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (h_share : ¬Disjoint (triangleEdges T) (triangleEdges T_base))
    (h_not_in_s : ¬T ⊆ s) :
    ∃ U, U ⊆ s ∧ U ∈ G.cliqueFinset 3 ∧ Disjoint (triangleEdges T) (triangleEdges U) := by
  -- In K₄ = {a,b,c,d}, if T shares edge ab with T_base but has vertex outside,
  -- then the opposite triangle {c,d,x} (where x ∈ {a,b}) is disjoint from T's edges
  sorry

/-- Two K₄s covering triangles from disjoint packing give τ ≤ 4.
    ROBUSTIFIED: Now takes h_nu and packing triangles as hypotheses (per Gemini).
    Proof strategy (Gemini "outlier" argument):
    1. Every triangle T shares edge with T1 or T2 (by triangle_shares_edge_with_packing)
    2. If T shares edge with T1 but T ⊈ s1, get U ⊆ s1 disjoint from T
    3. Then {T, U, T2} would be packing of size 3, contradicting ν=2
    4. So all triangles ⊆ s1 ∪ s2, and τ(K₄)=2 each gives τ ≤ 4 -/
lemma two_K4_cover_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (T1 T2 : Finset V) (hT1 : T1 ∈ G.cliqueFinset 3) (hT2 : T2 ∈ G.cliqueFinset 3)
    (h_packing_disj : Disjoint (triangleEdges T1) (triangleEdges T2))
    (s1 s2 : Finset V) (h1 : IsK4 G s1) (h2 : IsK4 G s2)
    (hs1 : T1 ⊆ s1) (hs2 : T2 ⊆ s2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 4 ∧ IsTriangleCovering G S := by
  -- Get covers for each K₄ (τ(K₄) = 2)
  -- Show all triangles are in s1 ∪ s2 (outlier → ν≥3 contradiction)
  -- Union of covers has size ≤ 4
  sorry

/-- Conclusion from two K₄s: either ν > 2 or τ ≤ 4 -/
lemma two_K4_implies_tau_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 2)
    (T1 T2 : Finset V) (hT1 : T1 ∈ G.cliqueFinset 3) (hT2 : T2 ∈ G.cliqueFinset 3)
    (h_packing_disj : Disjoint (triangleEdges T1) (triangleEdges T2))
    (s1 s2 : Finset V) (h1 : IsK4 G s1) (h2 : IsK4 G s2)
    (hs1 : T1 ⊆ s1) (hs2 : T2 ⊆ s2) :
    triangleCoveringNumber G ≤ 4 := by
  obtain ⟨S, hS_card, hS_cover⟩ := two_K4_cover_le_4 G h_nu T1 T2 hT1 hT2 h_packing_disj s1 s2 h1 h2 hs1 hs2
  unfold triangleCoveringNumber
  have h_min_card : ∃ S' ∈ Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset, S'.card ≤ 4 := by
    refine ⟨S ∩ G.edgeFinset, ?_, ?_⟩ <;> aesop
    · unfold IsTriangleCovering at *; aesop
      intro t ht; specialize hS_cover t; simp_all +decide [SimpleGraph.deleteEdges, Set.subset_def]
    · exact le_trans (Finset.card_le_card fun x hx => by aesop) hS_card
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
  -- Get two K₄s with their packing triangles tracked
  obtain ⟨T1, T2, s1, s2, hT1, hT2, h_edge_disj, hs1_sub, hs2_sub, hs1_K4, hs2_K4⟩ :=
    tau_gt_4_implies_two_K4_with_packing G h h_tau
  -- Use the robust covering lemma
  have h_cover := two_K4_implies_tau_le_4 G h T1 T2 hT1 hT2 h_edge_disj s1 s2 hs1_K4 hs2_K4 hs1_sub hs2_sub
  omega

end
