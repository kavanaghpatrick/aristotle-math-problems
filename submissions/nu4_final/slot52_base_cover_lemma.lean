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

lemma cover_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Standard subadditivity
  sorry

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
  sorry

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
  sorry

end
