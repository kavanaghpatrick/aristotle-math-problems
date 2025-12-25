/-
Tuza ν=4 Strategy - Slot 62: PATH_4 with FIXED Sym2 Syntax

FIXES FROM SLOT61:
1. Sym2.mk a b → s(a, b)  (correct Lean 4 Mathlib syntax)
2. Finset.card_self_inter → use Finset.inter_self and card

PROVEN IN SLOT61 (included here):
- tau_union_le_sum (FULL PROOF from Aristotle)
- triangle_shares_edge_with_packing (FULL PROOF)
- isCover lemmas (FULL PROOFS)

TARGETS:
- avoiding_contains_base_edge (now with correct syntax)
- two_edges_cover_sharing_triangles
- tau_le_8_path4 (main theorem)
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

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧
  (A ∩ D).card = 0 ∧
  (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot61 Aristotle output)
-- ══════════════════════════════════════════════════════════════════════════════

def isCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E, e ∈ t.sym2

lemma isCover_union {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset (Finset V)} {EA EB : Finset (Sym2 V)}
    (hA : isCover G A EA) (hB : isCover G B EB) :
    isCover G (A ∪ B) (EA ∪ EB) := by
      have := hA.2;
      have h_union_subset : EA ∪ EB ⊆ G.edgeFinset := by
        exact Finset.union_subset hA.1 hB.1;
      exact ⟨ h_union_subset, fun t ht => by rcases Finset.mem_union.mp ht with ( ht | ht ) <;> [ exact Exists.elim ( this t ht ) fun e he => ⟨ e, Finset.mem_union_left _ he.1, he.2 ⟩ ; exact Exists.elim ( hB.2 t ht ) fun e he => ⟨ e, Finset.mem_union_right _ he.1, he.2 ⟩ ] ⟩

lemma exists_min_cover_of_coverable {G : SimpleGraph V} [DecidableRel G.Adj] {triangles : Finset (Finset V)}
    (h : ∃ E, isCover G triangles E) :
    ∃ E, isCover G triangles E ∧ E.card = triangleCoveringNumberOn G triangles := by
      unfold triangleCoveringNumberOn;
      cases' h with E hE;
      have h_min_eq : ∃ E' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)), E'.card = (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)))).min.getD 0 := by
        have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ) from ?_ );
        · obtain ⟨ a, ha ⟩ := this;
          have := Finset.mem_image.mp ( Finset.mem_of_min ha ) ; aesop;
        · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE.1, hE.2 ⟩ ) ⟩;
      exact ⟨ h_min_eq.choose, ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp h_min_eq.choose_spec.1 |>.1 ), h_min_eq.choose_spec.1 |> fun h => by aesop ⟩, h_min_eq.choose_spec.2 ⟩

lemma card_le_of_isCover {G : SimpleGraph V} [DecidableRel G.Adj] {triangles : Finset (Finset V)}
    {E : Finset (Sym2 V)} (h : isCover G triangles E) :
    triangleCoveringNumberOn G triangles ≤ E.card := by
      unfold triangleCoveringNumberOn;
      have h_mem : E ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset) := by
        exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h.2 ⟩;
      norm_num +zetaDelta at *;
      have h_mem_image : E.card ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}) := by
        exact Finset.mem_image.mpr ⟨ E, by aesop ⟩;
      have h_min_le : ∀ x ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ x := by
        exact fun x hx => Finset.min_le hx;
      specialize h_min_le _ h_mem_image;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( G.edgeFinset.powerset ) ) ) <;> aesop

lemma not_coverable_implies_zero {G : SimpleGraph V} [DecidableRel G.Adj] {triangles : Finset (Finset V)}
    (h : ¬ ∃ E, isCover G triangles E) :
    triangleCoveringNumberOn G triangles = 0 := by
      simp_all +decide [ triangleCoveringNumberOn ];
      rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from _ ] ; aesop;
      ext E'; simp +decide [ isCover ];
      exact fun hE' => by have := h E'; unfold isCover at this; aesop;

lemma coverable_of_coverable_union_left {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset (Finset V)}
    (h : ∃ E, isCover G (A ∪ B) E) :
    ∃ E, isCover G A E := by
      exact ⟨ h.choose, ⟨ h.choose_spec.1, fun t ht => h.choose_spec.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩

lemma coverable_of_coverable_union_right {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset (Finset V)}
    (h : ∃ E, isCover G (A ∪ B) E) :
    ∃ E, isCover G B E := by
      rcases h with ⟨ E, hE ⟩ ; exact ⟨ E, ⟨ hE.1, fun t ht => hE.2 t ( Finset.mem_union_right _ ht ) ⟩ ⟩ ;

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases h : ∃ E, isCover G (A ∪ B) E;
  · obtain ⟨EA, hEA⟩ := exists_min_cover_of_coverable (coverable_of_coverable_union_left h)
    obtain ⟨EB, hEB⟩ := exists_min_cover_of_coverable (coverable_of_coverable_union_right h);
    have h_union : isCover G (A ∪ B) (EA ∪ EB) := by
      exact isCover_union hEA.1 hEB.1;
    exact le_trans ( card_le_of_isCover h_union ) ( by rw [ ← hEA.2, ← hEB.2 ] ; exact Finset.card_union_le _ _ );
  · rw [ not_coverable_implies_zero ];
    · exact Nat.zero_le _;
    · aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Every triangle shares edge with max packing (from slot61)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_in_M : t ∉ M) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_contra h
  push_neg at h
  have h_can_add : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with hxM | rfl
      · exact hM.1.1 hxM
      · exact ht
    · intro x hx y hy hxy
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx with hx_in_M | hx_eq_t
      · rcases hy with hy_in_M | hy_eq_t
        · exact hM.1.2 hx_in_M hy_in_M hxy
        · subst hy_eq_t
          have := h x hx_in_M
          omega
      · subst hx_eq_t
        rcases hy with hy_in_M | hy_eq_t
        · have : (t ∩ y).card ≤ 1 := h y hy_in_M
          rw [Finset.inter_comm]; omega
        · subst hy_eq_t; exact absurd rfl hxy
  have h_le : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : M ∪ {t} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_can_add.1, h_can_add⟩
    have h_in_image : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card :=
      Finset.mem_image_of_mem Finset.card h_mem
    have h_le_max := Finset.le_max h_in_image
    cases hmax : ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max with
    | bot =>
      exfalso
      have : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card := h_in_image
      rw [Finset.max_eq_bot] at hmax
      exact Finset.eq_empty_iff_forall_not_mem.mp hmax _ this
    | coe n =>
      simp only [Option.getD]
      rw [hmax] at h_le_max
      exact WithBot.coe_le_coe.mp h_le_max
  have h_card : (M ∪ {t}).card = M.card + 1 := by
    rw [Finset.card_union_eq_card_add_card, Finset.card_singleton]
    simp [Finset.disjoint_singleton_right, ht_not_in_M]
  rw [hM.2] at h_le
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Avoiding triangles contain base edge (FIXED SYNTAX)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If t avoids v but shares edge with e={v,a,b}, then t contains base edge {a,b}.
    This is because:
    - Edges of e are {va, vb, ab}
    - t can't contain va or vb (those contain v, but t avoids v)
    - So t must share the base edge ab -/
lemma avoiding_contains_base_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v a b : V) (hv_in_e : v ∈ e) (ha_in_e : a ∈ e) (hb_in_e : b ∈ e)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (h_avoids_v : v ∉ t)
    (h_shares_edge : (t ∩ e).card ≥ 2) :
    s(a, b) ∈ t.sym2 := by
  -- t shares ≥2 vertices with e = {v, a, b}
  -- But v ∉ t, so t ∩ e ⊆ {a, b}
  -- |t ∩ e| ≥ 2 and t ∩ e ⊆ {a, b} implies t ∩ e = {a, b}
  -- So both a, b ∈ t, hence {a,b} ∈ t.sym2
  have h_e_eq : e = {v, a, b} := by
    have h_card : e.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff] at he
      exact he.2
    rw [Finset.card_eq_three] at h_card
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h_card
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_in_e ha_in_e hb_in_e
    aesop
  have h_inter_sub : t ∩ e ⊆ {a, b} := by
    intro x hx
    simp only [Finset.mem_inter] at hx
    simp only [h_e_eq, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 h_avoids_v
    · simp
    · simp
  have h_inter_eq : t ∩ e = {a, b} := by
    apply Finset.eq_of_subset_of_card_le h_inter_sub
    simp only [Finset.card_insert_of_not_mem (Finset.not_mem_singleton.mpr hab), Finset.card_singleton]
    exact h_shares_edge
  have ha_in_t : a ∈ t := by
    have : a ∈ t ∩ e := by rw [h_inter_eq]; simp
    exact Finset.mem_of_mem_inter_left this
  have hb_in_t : b ∈ t := by
    have : b ∈ t ∩ e := by rw [h_inter_eq]; simp
    exact Finset.mem_of_mem_inter_left this
  simp only [Finset.mem_sym2_iff]
  exact ⟨ha_in_t, hb_in_t⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- DIRECT COVERING APPROACH: 2 edges per packing element (FIXED SYNTAX)
-- ══════════════════════════════════════════════════════════════════════════════

/-- For a triangle T = {x, y, z}, sharing an edge means sharing 2 vertices.
    So every triangle sharing edge with T contains one of xy, yz, or xz. -/
lemma two_edges_cover_sharing_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (x y z : V) (hT_eq : T = {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∀ t ∈ trianglesSharingEdge G T,
      (s(x, y) ∈ t.sym2) ∨ (s(y, z) ∈ t.sym2) ∨ (s(x, z) ∈ t.sym2) := by
  intro t ht
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ T).card ≥ 2 := ht.2
  rw [hT_eq] at h_share
  have h_two_in : ∃ a b, a ≠ b ∧ a ∈ t ∩ ({x, y, z} : Finset V) ∧ b ∈ t ∩ ({x, y, z} : Finset V) := by
    have h_pos : 2 ≤ (t ∩ {x, y, z}).card := h_share
    rcases Finset.one_lt_card.mp (by linarith : 1 < (t ∩ {x, y, z}).card) with ⟨a, ha, b, hb, hab⟩
    exact ⟨a, b, hab, ha, hb⟩
  obtain ⟨a, b, hab, ha, hb⟩ := h_two_in
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ha hb
  have h_ab_in_t : s(a, b) ∈ t.sym2 := by
    simp only [Finset.mem_sym2_iff]
    exact ⟨ha.1, hb.1⟩
  rcases ha.2 with rfl | rfl | rfl <;> rcases hb.2 with rfl | rfl | rfl
  all_goals (try exact absurd rfl hab)
  all_goals (simp only [Sym2.eq, Sym2.rel_iff'] at h_ab_in_t ⊢; try left; try right; assumption)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4 (FIXED SYNTAX)
-- ══════════════════════════════════════════════════════════════════════════════

/-- For PATH_4 with ν = 4, we have τ ≤ 8.

    Strategy: For each packing element, choose 2 edges incident to the shared vertex.
    This gives 8 edges total that cover all triangles.

    For A—B with shared v_ab: use edges from A incident to v_ab, and from B incident to v_ab.
    For C—D with shared v_cd: use edges from C incident to v_cd, and from D incident to v_cd. -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  obtain ⟨hM_eq, hAB, hBC, hCD, hAC, hAD, hBD,
          h_card_AB, h_card_BC, h_card_CD, h_card_AC, h_card_AD, h_card_BD⟩ := hpath
  have h_AB_one : ∃ v_ab, A ∩ B = {v_ab} := by
    rw [Finset.card_eq_one] at h_card_AB; exact h_card_AB
  have h_CD_one : ∃ v_cd, C ∩ D = {v_cd} := by
    rw [Finset.card_eq_one] at h_card_CD; exact h_card_CD
  obtain ⟨v_ab, hv_ab⟩ := h_AB_one
  obtain ⟨v_cd, hv_cd⟩ := h_CD_one
  have h_covered : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
    intro t ht
    by_cases h_in_M : t ∈ M
    · use t, h_in_M
      have : t.card = 3 := by
        simp only [SimpleGraph.mem_cliqueFinset_iff] at ht; exact ht.2
      -- t ∩ t = t, so card = 3 ≥ 2
      rw [Finset.inter_self]
      linarith
    · exact triangle_shares_edge_with_packing G M hM t ht h_in_M
  -- Aristotle to complete: construct 8-edge cover
  sorry

end
