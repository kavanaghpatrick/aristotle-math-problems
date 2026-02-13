/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dddd0278-cd90-4792-92ac-8313d4234f19

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma cover_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma base_edges_card_le_M_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (hM : ∀ e ∈ M, e.card = 3 ∧ v ∈ e) :
    (baseEdgesFromPacking G M v).card ≤ M.card

- theorem base_edges_cover_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (hv : ∀ e ∈ M, v ∈ e)
    (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (trianglesAvoiding G v) ≤ 4
-/

/-
Tuza nu=4: Base Cover Lemma - Slot 52

THEOREM: Base edges cover all triangles avoiding v.
  base_edges_cover_avoiding: triangleCoveringNumberOn G (trianglesAvoiding G v) <= 4

PROOF SKETCH:
1. By maximality, every triangle shares edge with some M-element e = {v,a,b}
2. If triangle avoids v, it cannot share spokes {v,a} or {v,b}
3. Therefore it must share base edge {a,b}
4. At most 4 base edges (one per M-element)

PROVEN HELPER LEMMAS (10+):
1. avoiding_contains_base_edge - Core lemma from slot61
2. triangle_card_eq_three - Triangles have exactly 3 vertices
3. triangle_inter_subset - Intersection properties
4. avoiding_not_in_triangle - v not in avoiding triangle
5. base_edge_in_sym2 - Base edge is in triangle's sym2
6. triangle_has_three_edges - Triangle has exactly 3 edges
7. vertex_in_clique_three - Membership in 3-clique
8. inter_card_ge_two_means_share_edge - Sharing condition
9. triangle_shares_edge_with_packing - Maximality
10. cover_union_mono - Monotonicity of covers
11. four_base_edges_bound - At most 4 base edges

RISK: Medium (Tier 2 - needs scaffolding)
TARGET: 1 sorry (main theorem)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ============================================================================
-- DEFINITIONS
-- ============================================================================

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

/-- Triangles containing vertex v -/
def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

/-- Triangles avoiding vertex v -/
def trianglesAvoiding (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∉ t)

/-- Triangles that share an edge (>=2 vertices) with a given set -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ s).card ≥ 2)

/-- Base edge of a triangle {v, a, b} with respect to apex v -/
def baseEdge (v a b : V) : Sym2 V := s(a, b)

-- ============================================================================
-- HELPER LEMMA 1: Triangle card equals 3
-- ============================================================================

lemma triangle_card_eq_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 := by
  simp only [SimpleGraph.mem_cliqueFinset_iff] at ht
  exact ht.2

-- ============================================================================
-- HELPER LEMMA 2: Triangle has three distinct vertices
-- ============================================================================

lemma triangle_has_three_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ t = {x, y, z} := by
  have h_card := triangle_card_eq_three G t ht
  rw [Finset.card_eq_three] at h_card
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h_card
  exact ⟨x, y, z, hxy, hyz.symm, hxz, rfl⟩

-- ============================================================================
-- HELPER LEMMA 3: Avoiding means not in triangle
-- ============================================================================

lemma avoiding_not_in_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (t : Finset V) (ht : t ∈ trianglesAvoiding G v) : v ∉ t := by
  simp only [trianglesAvoiding, Finset.mem_filter] at ht
  exact ht.2

-- ============================================================================
-- HELPER LEMMA 4: Triangles in avoiding are still cliques
-- ============================================================================

lemma avoiding_subset_cliques (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    trianglesAvoiding G v ⊆ G.cliqueFinset 3 := by
  intro t ht
  simp only [trianglesAvoiding, Finset.mem_filter] at ht
  exact ht.1

-- ============================================================================
-- HELPER LEMMA 5: Vertex in clique three
-- ============================================================================

lemma vertex_in_clique_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v a b : V) (hv : v ∈ e) (ha : a ∈ e) (hb : b ∈ e)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    e = {v, a, b} := by
  have h_card := triangle_card_eq_three G e he
  rw [Finset.card_eq_three] at h_card
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h_card
  ext w
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ha hb
    rcases hw with rfl | rfl | rfl
    · rcases hv with rfl | rfl | rfl <;>
      rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      simp_all
    · rcases hv with rfl | rfl | rfl <;>
      rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      simp_all
    · rcases hv with rfl | rfl | rfl <;>
      rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      simp_all
  · intro hw
    rcases hw with rfl | rfl | rfl
    · exact hv
    · exact ha
    · exact hb

-- ============================================================================
-- HELPER LEMMA 6: Intersection subset when avoiding
-- ============================================================================

lemma inter_subset_when_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (v a b : V) (he_eq : e = {v, a, b})
    (t : Finset V) (h_avoids : v ∉ t) :
    t ∩ e ⊆ {a, b} := by
  intro x hx
  simp only [Finset.mem_inter] at hx
  rw [he_eq] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx.2 with rfl | rfl | rfl
  · exact absurd hx.1 h_avoids
  · simp
  · simp

-- ============================================================================
-- HELPER LEMMA 7: Inter card ge 2 forces base edge (KEY LEMMA)
-- ============================================================================

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
  -- First establish e = {v, a, b}
  have h_e_eq : e = {v, a, b} := by
    have h_card : e.card = 3 := triangle_card_eq_three G e he
    rw [Finset.card_eq_three] at h_card
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h_card
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_in_e ha_in_e hb_in_e
    -- All of v, a, b are in {x, y, z} and they are distinct
    aesop

  -- Since v not in t, intersection is subset of {a, b}
  have h_inter_sub : t ∩ e ⊆ {a, b} := inter_subset_when_avoiding G e v a b h_e_eq t h_avoids_v

  -- But |t ∩ e| >= 2, so t ∩ e = {a, b}
  have h_inter_eq : t ∩ e = {a, b} := by
    apply Finset.eq_of_subset_of_card_le h_inter_sub
    simp only [Finset.card_insert_of_not_mem (Finset.not_mem_singleton.mpr hab), Finset.card_singleton]
    exact h_shares_edge

  -- Extract a, b in t
  have ha_in_t : a ∈ t := by
    have : a ∈ t ∩ e := by rw [h_inter_eq]; simp
    exact Finset.mem_of_mem_inter_left this

  have hb_in_t : b ∈ t := by
    have : b ∈ t ∩ e := by rw [h_inter_eq]; simp
    exact Finset.mem_of_mem_inter_left this

  -- Now {a, b} is in t.sym2
  simp only [Finset.mem_sym2_iff]
  exact ⟨ha_in_t, hb_in_t⟩

-- ============================================================================
-- HELPER LEMMA 8: Triangle shares edge with packing (Maximality)
-- ============================================================================

/-- In a maximum packing, every triangle shares an edge with some packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_in_M : t ∉ M) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_contra h
  push_neg at h
  -- If t doesn't share edge with any M-element, we can add t to M
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

  -- But then |M ∪ {t}| > |M| = ν, contradicting maximality
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

-- ============================================================================
-- HELPER LEMMA 9: Union cover bound
-- ============================================================================

noncomputable section AristotleLemmas

/-
If E is a valid triangle cover for A, then the triangle covering number of A is at most the cardinality of E.
-/
lemma triangleCoveringNumberOn_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E : Finset (Sym2 V))
    (hE_subset : E ⊆ G.edgeFinset)
    (hE_cover : ∀ t ∈ A, ∃ e ∈ E, e ∈ t.sym2) :
    triangleCoveringNumberOn G A ≤ E.card := by
      -- By definition of `triangleCoveringNumberOn`, since `E` is a valid triangle cover for `A`, we have that `E` is in the set of triangle covers of `A`.
      have hE_in_triangle_covers : E ∈ {E' : Finset (Sym2 V) | E' ⊆ G.edgeFinset ∧ ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2} := by
        exact ⟨ hE_subset, hE_cover ⟩;
      convert Set.mem_setOf_eq.mp hE_in_triangle_covers |> fun h => _;
      unfold triangleCoveringNumberOn;
      simp +zetaDelta at *;
      have hE_in_triangle_covers : E ∈ {E' : Finset (Sym2 V) | E' ⊆ G.edgeFinset ∧ ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t} := by
        exact ⟨ fun e he => by simpa using h.1 he, h.2 ⟩;
      have hE_in_triangle_covers : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ E.card := by
        exact Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE_in_triangle_covers.1, hE_in_triangle_covers.2 ⟩ ) );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

/-
If a triangle cover exists for A, then there exists a minimum size triangle cover for A whose size equals the triangle covering number.
-/
lemma exists_min_triangleCoverOn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V))
    (h : ∃ E, E ⊆ G.edgeFinset ∧ ∀ t ∈ A, ∃ e ∈ E, e ∈ t.sym2) :
    ∃ E, E ⊆ G.edgeFinset ∧ (∀ t ∈ A, ∃ e ∈ E, e ∈ t.sym2) ∧ E.card = triangleCoveringNumberOn G A := by
      obtain ⟨ E, hE ⟩ := h;
      have h_min_exists : ∃ C ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2), ∀ E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2), C.card ≤ E'.card := by
        apply_rules [ Finset.exists_min_image ];
        exact ⟨ E, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE.1, hE.2 ⟩ ⟩;
      obtain ⟨ C, hC₁, hC₂ ⟩ := h_min_exists;
      refine' ⟨ C, _, _, _ ⟩;
      · aesop;
      · aesop;
      · unfold triangleCoveringNumberOn;
        rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ).min = some ( C.card ) from ?_ ];
        · rfl;
        · refine' le_antisymm _ _;
          · exact Finset.min_le ( Finset.mem_image_of_mem _ hC₁ );
          · simp +zetaDelta at *;
            exact fun a x hx₁ hx₂ hx₃ => WithTop.coe_le_coe.mpr ( hx₃ ▸ hC₂ x hx₁ hx₂ )

end AristotleLemmas

lemma cover_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Standard subadditivity
  -- Consider two cases: either there is no triangle cover for A or B, or there is.
  by_cases hA : ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ (∀ t ∈ A, ∃ e ∈ E, e ∈ t.sym2)
  by_cases hB : ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ (∀ t ∈ B, ∃ e ∈ E, e ∈ t.sym2);
  · -- By `exists_min_triangleCoverOn`, there exist covers $E_A$ for $A$ and $E_B$ for $B$ such that $|E_A| = \text{triangleCoveringNumberOn } G A$ and $|E_B| = \text{triangleCoveringNumberOn } G B$.
    obtain ⟨E_A, hE_A_subset, hE_A_cover, hE_A_card⟩ : ∃ E_A : Finset (Sym2 V), E_A ⊆ G.edgeFinset ∧ (∀ t ∈ A, ∃ e ∈ E_A, e ∈ t.sym2) ∧ E_A.card = triangleCoveringNumberOn G A := by
      exact?
    obtain ⟨E_B, hE_B_subset, hE_B_cover, hE_B_card⟩ : ∃ E_B : Finset (Sym2 V), E_B ⊆ G.edgeFinset ∧ (∀ t ∈ B, ∃ e ∈ E_B, e ∈ t.sym2) ∧ E_B.card = triangleCoveringNumberOn G B := by
      exact exists_min_triangleCoverOn G B hB;
    refine' le_trans ( triangleCoveringNumberOn_le_card G ( A ∪ B ) ( E_A ∪ E_B ) _ _ ) _;
    · exact Finset.union_subset hE_A_subset hE_B_subset;
    · intro t ht; cases' Finset.mem_union.mp ht with ht ht <;> [ exact Exists.elim ( hE_A_cover t ht ) fun e he => ⟨ e, Finset.mem_union_left _ he.1, he.2 ⟩ ; exact Exists.elim ( hE_B_cover t ht ) fun e he => ⟨ e, Finset.mem_union_right _ he.1, he.2 ⟩ ] ;
    · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( hE_A_card.le ) ( hE_B_card.le ) );
  · norm_num +zetaDelta at *;
    unfold triangleCoveringNumberOn;
    rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => by obtain ⟨ t, ht₁, ht₂ ⟩ := hB E' ( by simpa using Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ) ) ; obtain ⟨ e, he₁, he₂ ⟩ := Finset.mem_filter.mp hE' |>.2 t ht₁; specialize ht₂ e he₁; aesop ] ; simp +decide;
    rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) = ∅ from _ ] ; simp +decide;
    simp +decide [ Finset.ext_iff ];
    grind;
  · rw [ triangleCoveringNumberOn ];
    rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2 } = ∅ from _ ];
    · exact Nat.zero_le _;
    · exact Finset.eq_empty_of_forall_notMem fun E' hE' => hA ⟨ E', Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => Finset.mem_filter.mp hE' |>.2 t ( Finset.mem_union_left _ ht ) ⟩

/- Aristotle took a wrong turn (reason code: 13). Please try again. -/
-- ============================================================================
-- HELPER LEMMA 10: Cover monotonicity
-- ============================================================================

lemma cover_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (h : A ⊆ B) :
    triangleCoveringNumberOn G A ≤ triangleCoveringNumberOn G B := by
  -- Fewer triangles need fewer edges to cover
  sorry

-- ============================================================================
-- HELPER LEMMA 11: Base edges from packing
-- ============================================================================

/-- Extract base edges from packing elements relative to shared vertex -/
def baseEdgesFromPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun e =>
    (e.filter (· ≠ v)).sym2.filter (fun edge => edge ∈ G.edgeFinset))

-- ============================================================================
-- HELPER LEMMA 12: Base edges card bound
-- ============================================================================

lemma base_edges_card_le_M_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (hM : ∀ e ∈ M, e.card = 3 ∧ v ∈ e) :
    (baseEdgesFromPacking G M v).card ≤ M.card := by
  -- Each triangle contributes at most 1 base edge (the edge not containing v)
  -- With 4 triangles, at most 4 base edges
  -- Since each element in M contributes at most one base edge, the cardinality of baseEdgesFromPacking G M v is less than or equal to the cardinality of M.
  have h_card : (baseEdgesFromPacking G M v).card ≤ Finset.sum M (fun e => 1) := by
    have h_card : (baseEdgesFromPacking G M v).card ≤ Finset.sum M (fun e => (e.filter (· ≠ v)).sym2.filter (fun edge => edge ∈ G.edgeFinset) |>.card) := by
      convert Finset.card_biUnion_le;
    refine' h_card.trans ( Finset.sum_le_sum fun e he => _ );
    -- Since $e$ is a triangle containing $v$, removing $v$ leaves exactly two elements, say $a$ and $b$.
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : V, a ≠ b ∧ a ∈ e ∧ b ∈ e ∧ a ≠ v ∧ b ≠ v ∧ e = {v, a, b} := by
      obtain ⟨ a, b, c, ha, hb, hc, hab ⟩ := Finset.card_eq_three.mp ( hM e he |>.1 );
      cases eq_or_ne a v <;> cases eq_or_ne b v <;> cases eq_or_ne c v <;> simp_all +decide;
      · exact ⟨ b, c, hc, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
      · exact ⟨ a, c, hb, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
      · exact ⟨ a, b, ha, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
      · grind;
    simp_all +decide [ Finset.filter_insert, Finset.filter_singleton ];
    simp +decide [ Finset.sym2, Finset.filter_insert, Finset.filter_singleton, ha ];
    simp +decide [ Multiset.sym2, Finset.filter ];
    erw [ Quotient.liftOn_mk ] ; simp +decide [ List.sym2 ] ;
    by_cases h : s(a, b) ∈ G.edgeSet <;> simp +decide [ h ];
  aesop

-- ============================================================================
-- HELPER LEMMA 13: Avoiding triangles share base with some packing element
-- ============================================================================

lemma avoiding_shares_base_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (hv : ∀ e ∈ M, v ∈ e)
    (t : Finset V) (ht : t ∈ trianglesAvoiding G v) :
    ∃ e ∈ M, ∃ a b : V, a ∈ e ∧ b ∈ e ∧ a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ s(a, b) ∈ t.sym2 := by
  -- t is a clique avoiding v
  have ht_clique : t ∈ G.cliqueFinset 3 := avoiding_subset_cliques G v ht
  have h_avoids : v ∉ t := avoiding_not_in_triangle G v t ht

  -- Case: t in M
  by_cases ht_in_M : t ∈ M
  · -- t contains v by hypothesis, but t avoids v - contradiction
    have hv_in_t := hv t ht_in_M
    exact absurd hv_in_t h_avoids

  -- Case: t not in M, so shares edge with some packing element
  obtain ⟨e, he_in_M, h_share⟩ := triangle_shares_edge_with_packing G M hM t ht_clique ht_in_M
  have he_clique : e ∈ G.cliqueFinset 3 := hM.1.1 he_in_M
  have hv_in_e := hv e he_in_M

  -- e = {v, a, b} for some a, b
  obtain ⟨x, y, z, hxy, hyz, hxz, he_eq⟩ := triangle_has_three_vertices G e he_clique
  simp only [he_eq, Finset.mem_insert, Finset.mem_singleton] at hv_in_e

  -- Identify which is v and which are a, b
  rcases hv_in_e with rfl | rfl | rfl
  · -- v = x, so a = y, b = z
    have ha_in_e : y ∈ e := by rw [he_eq]; simp
    have hb_in_e : z ∈ e := by rw [he_eq]; simp
    have hv_in_e' : x ∈ e := by rw [he_eq]; simp
    have h_base := avoiding_contains_base_edge G e he_clique x y z hv_in_e' ha_in_e hb_in_e
        hxy hxz.symm hyz.symm t ht_clique h_avoids h_share
    exact ⟨e, he_in_M, y, z, ha_in_e, hb_in_e, hxy.symm, hxz, hyz.symm, h_base⟩
  · -- v = y, so a = x, b = z
    have ha_in_e : x ∈ e := by rw [he_eq]; simp
    have hb_in_e : z ∈ e := by rw [he_eq]; simp
    have hv_in_e' : y ∈ e := by rw [he_eq]; simp
    have h_base := avoiding_contains_base_edge G e he_clique y x z hv_in_e' ha_in_e hb_in_e
        hxy hyz.symm hxz t ht_clique h_avoids h_share
    exact ⟨e, he_in_M, x, z, ha_in_e, hb_in_e, hxy, hyz, hxz, h_base⟩
  · -- v = z, so a = x, b = y
    have ha_in_e : x ∈ e := by rw [he_eq]; simp
    have hb_in_e : y ∈ e := by rw [he_eq]; simp
    have hv_in_e' : z ∈ e := by rw [he_eq]; simp
    have h_base := avoiding_contains_base_edge G e he_clique z x y hv_in_e' ha_in_e hb_in_e
        hxz hyz hxy t ht_clique h_avoids h_share
    exact ⟨e, he_in_M, x, y, ha_in_e, hb_in_e, hxz.symm, hyz.symm, hxy, h_base⟩

-- ============================================================================
-- MAIN THEOREM: Base edges cover avoiding triangles
-- ============================================================================

/-
PROOF SKETCH:
1. By maximality, every triangle shares edge with some M-element e = {v,a,b}
2. If triangle avoids v, it cannot share spokes {v,a} or {v,b}
3. Therefore it must share base edge {a,b}
4. At most 4 base edges (one per M-element with |M| = 4)

The base edges from M are the edges {a,b} where each e in M has form {v,a,b}.
Each avoiding triangle t:
- Shares edge with some e in M (maximality)
- Has v not in t (avoiding)
- Must share base {a,b} (avoiding_contains_base_edge)
So 4 base edges (one per packing element) cover all avoiding triangles.
-/
theorem base_edges_cover_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (hv : ∀ e ∈ M, v ∈ e)
    (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (trianglesAvoiding G v) ≤ 4 := by
  /-
  Strategy:
  1. Define the set of base edges B = {base(e) | e in M}
  2. Show |B| <= 4 (one base edge per packing element)
  3. Show B covers all avoiding triangles (by avoiding_shares_base_with_packing)
  4. Therefore tau(avoiding) <= |B| <= 4
  -/
  -- By Lemma 13, every avoiding triangle t shares an edge with some M-element e = {v,a,b}.
  have h_base_edges_cover : ∀ t ∈ trianglesAvoiding G v, ∃ e ∈ M, ∃ a b : V, a ∈ e ∧ b ∈ e ∧ a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ s(a, b) ∈ t.sym2 := by
    exact?;
  -- By Lemma 12, the set of base edges from M has cardinality at most 4.
  have h_base_edges_card : (baseEdgesFromPacking G M v).card ≤ 4 := by
    convert base_edges_card_le_M_card G M v _;
    · exact hM_card.symm;
    · exact fun e he => ⟨ triangle_card_eq_three G e ( hM.1.1 he ), hv e he ⟩;
  refine' le_trans _ h_base_edges_card;
  -- Since the base edges from M cover all avoiding triangles, the triangle covering number on the avoiding triangles is bounded by the size of these base edges.
  have h_cover : ∀ t ∈ trianglesAvoiding G v, ∃ e ∈ baseEdgesFromPacking G M v, e ∈ t.sym2 := by
    intro t ht; obtain ⟨ e, he, a, b, ha, hb, hav, hbv, hab, h ⟩ := h_base_edges_cover t ht; use s(a, b); simp_all +decide [ baseEdgesFromPacking ] ;
    have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact ⟨ e, he, ⟨ ha, hb ⟩, this.1 ( by aesop ) ( by aesop ) ( by aesop ) ⟩;
  unfold triangleCoveringNumberOn;
  by_cases h : ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding G v, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ).min = none <;> simp_all +decide;
  cases h' : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding G v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp_all +decide;
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card ( show baseEdgesFromPacking G M v ∈ Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding G v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) from ?_ ) ) ; aesop;
  simp_all +decide [ Finset.subset_iff ];
  unfold baseEdgesFromPacking; aesop;

end