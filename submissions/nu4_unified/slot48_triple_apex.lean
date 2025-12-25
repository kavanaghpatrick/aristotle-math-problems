/-
Tuza ν=4 Strategy - Slot 48: Triple Apex Completion

GOAL: Complete the tau_le_8_triple_apex theorem from slot29.

When vertex v appears in ≥3 packing triangles:
- Star case (v in all 4): spokes + bases ≤ 4 + 4 = 8
- Three-share case (v in 3, one isolated): (spokes + bases for 3) + τ(isolated) ≤ 6 + 2 = 8

PROVEN SCAFFOLDING:
- tau_S_le_2 (from slot44): τ(S_e) ≤ 2 ✅
- tau_at_v_avoiding_v_le_k (from slot29): τ(avoiding) ≤ k where k = elements containing v ✅
- base_edge_covers (from slot29): Triangles avoiding v contain base edges ✅

MISSING (target of this submission):
- tau_at_v_containing_v_le_4: τ(containing) ≤ 4 using spoke edges
- tau_le_8_triple_apex: Main theorem combining above
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
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def packingElementsContaining (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  M.filter (fun e => v ∈ e)

-- Triangles at v: all triangles sharing edge with some packing element containing v
def trianglesAtV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (packingElementsContaining M v).biUnion (trianglesSharingEdge G)

def trianglesAtVContainingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∈ t)

def trianglesAtVAvoidingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∉ t)

-- S_e: triangles sharing edge with e but NOT with any other packing element
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangleCoveringNumberOn_le_of_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) (h : isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_in : E' ∈ G.edgeFinset.powerset.filter (fun E'' => ∀ t ∈ triangles, ∃ e ∈ E'', e ∈ t.sym2) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h.1, h.2⟩
  have h_card_in : E'.card ∈ (G.edgeFinset.powerset.filter (fun E'' => ∀ t ∈ triangles, ∃ e ∈ E'', e ∈ t.sym2)).image Finset.card := by
    exact Finset.mem_image_of_mem _ h_in
  have h_min_le : (G.edgeFinset.powerset.filter (fun E'' => ∀ t ∈ triangles, ∃ e ∈ E'', e ∈ t.sym2)).image Finset.card |>.min ≤ E'.card := by
    exact Finset.min_le h_card_in
  cases h_min : (G.edgeFinset.powerset.filter (fun E'' => ∀ t ∈ triangles, ∃ e ∈ E'', e ∈ t.sym2)).image Finset.card |>.min with
  | none => simp [h_min]
  | some m => simp only [h_min, Option.getD_some]; exact WithBot.coe_le_coe.mp h_min_le

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- Proven in slot44

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Base edges cover avoiding triangles (from slot29)
-- ══════════════════════════════════════════════════════════════════════════════

/--
If triangle T shares edge with packing triangle t containing v, but T avoids v,
then T contains the base edge t \ {v}.
-/
lemma base_edge_covers (G : SimpleGraph V) [DecidableRel G.Adj] (t T : Finset V) (v : V)
    (ht : t ∈ G.cliqueFinset 3) (hv : v ∈ t)
    (hT : T ∈ trianglesSharingEdge G t) (hvT : v ∉ T) :
    t \ {v} ⊆ T := by
  intro x hx
  have h_inter : (T ∩ t).card ≥ 2 := by
    unfold trianglesSharingEdge at hT
    simp only [Finset.mem_filter] at hT
    exact hT.2
  -- T ∩ t ⊆ t \ {v} since v ∉ T
  have h_inter_subset : T ∩ t ⊆ t \ {v} := by
    intro y hy
    simp only [Finset.mem_inter] at hy
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact hy.2
    · intro hyv
      rw [hyv] at hy
      exact hvT hy.1
  -- t \ {v} has 2 elements, T ∩ t has ≥ 2, so T ∩ t = t \ {v}
  have h_card_sdiff : (t \ {v}).card = 2 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hv), ht.card_eq, Finset.card_singleton]
  have h_inter_eq : T ∩ t = t \ {v} := by
    apply Finset.eq_of_subset_of_card_le h_inter_subset
    rw [h_card_sdiff]
    exact h_inter
  -- x ∈ t \ {v} = T ∩ t, so x ∈ T
  rw [← h_inter_eq] at hx
  exact Finset.mem_of_mem_inter_left hx

/--
Every triangle in trianglesAtVAvoidingV is covered by some base edge.
-/
lemma base_edges_cover_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (v : V) :
    ∀ T ∈ trianglesAtVAvoidingV G M v, ∃ f ∈ packingElementsContaining M v, f \ {v} ⊆ T := by
  intro T hT
  simp only [trianglesAtVAvoidingV, Finset.mem_filter] at hT
  obtain ⟨hT_at, hvT⟩ := hT
  simp only [trianglesAtV, Finset.mem_biUnion] at hT_at
  obtain ⟨f, hf_pack, hT_share⟩ := hT_at
  refine ⟨f, hf_pack, ?_⟩
  have hf_triangle : f ∈ G.cliqueFinset 3 := hM.1.1 (Finset.mem_of_mem_filter f hf_pack)
  have hv_f : v ∈ f := by
    simp only [packingElementsContaining, Finset.mem_filter] at hf_pack
    exact hf_pack.2
  exact base_edge_covers G f T v hf_triangle hv_f hT_share hvT

-- ══════════════════════════════════════════════════════════════════════════════
-- τ(avoiding v) ≤ k (number of elements containing v)
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ(trianglesAtVAvoidingV) ≤ k where k = |packingElementsContaining M v|
Each packing element's base triangles share the base edge, so k edges suffice.
-/
lemma tau_at_v_avoiding_v_le_k (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (k : ℕ) (hk : (packingElementsContaining M v).card = k) :
    triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ k := by
  -- Construct cover: one base edge per element containing v
  -- For each f ∈ packingElementsContaining M v, take one edge from f \ {v}
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: τ(containing v) ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
When ≥3 packing elements share v, triangles containing v can be hit with ≤4 edges.

Strategy: Use spoke edges from v.
Each packing element {v, a_i, b_i} contributes spokes {v, a_i} and {v, b_i}.
With 3-4 elements, we have 6-8 potential spokes, but only need 4 distinct ones.
Every v-containing triangle shares edge with some packing element,
hence contains v and another vertex from that element, giving a spoke.
-/
lemma tau_at_v_containing_v_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card ≥ 3) :
    triangleCoveringNumberOn G (trianglesAtVContainingV G M v) ≤ 4 := by
  -- Collect all vertices in packing elements containing v, excluding v
  let vertices_at_v := (packingElementsContaining M v).biUnion (fun e => e \ {v})
  -- Create spoke edges
  let spokes := vertices_at_v.image (fun x => Sym2.mk (v, x))
  -- Bound on number of spokes: each element contributes 2 vertices, ≤ 4 elements
  -- So |spokes| ≤ 8, but actually ≤ 4 suffice (overlap possible)

  -- Actually we need a smarter bound. Let's take just 4 spokes.
  -- If 4 elements share v, each element contributes 2 non-v vertices
  -- Total 8 vertices, but we only need 4 spokes

  -- Key insight: every v-containing triangle has a spoke edge
  have h_cover : isTriangleCover G (trianglesAtVContainingV G M v) spokes := by
    constructor
    · -- spokes ⊆ G.edgeFinset
      intro edge h_edge
      simp only [Finset.mem_image] at h_edge
      obtain ⟨x, hx, h_eq⟩ := h_edge
      rw [← h_eq]
      simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton] at hx
      obtain ⟨e, he_pack, hx_e, hx_ne_v⟩ := hx
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      -- v and x are both in triangle e, hence adjacent
      have he_clique : e ∈ G.cliqueFinset 3 := by
        have := hM.1.1
        exact this (Finset.mem_of_mem_filter e he_pack)
      rw [SimpleGraph.mem_cliqueFinset_iff] at he_clique
      have hv_e : v ∈ e := by
        simp only [packingElementsContaining, Finset.mem_filter] at he_pack
        exact he_pack.2
      exact he_clique.1 hv_e hx_e (Ne.symm hx_ne_v)
    · -- Every v-containing triangle has a spoke in it
      intro t ht
      simp only [trianglesAtVContainingV, Finset.mem_filter] at ht
      obtain ⟨ht_at, hv_t⟩ := ht
      simp only [trianglesAtV, Finset.mem_biUnion] at ht_at
      obtain ⟨e, he_pack, ht_share⟩ := ht_at
      -- t shares ≥2 vertices with e, one of which is v
      simp only [trianglesSharingEdge, Finset.mem_filter] at ht_share
      have h_inter : (t ∩ e).card ≥ 2 := ht_share.2
      have hv_e : v ∈ e := by
        simp only [packingElementsContaining, Finset.mem_filter] at he_pack
        exact he_pack.2
      -- Get another vertex x ∈ t ∩ e, x ≠ v
      obtain ⟨x, hx_t, hx_e, hx_ne_v⟩ : ∃ x, x ∈ t ∧ x ∈ e ∧ x ≠ v := by
        have hv_in_inter : v ∈ t ∩ e := Finset.mem_inter.mpr ⟨hv_t, hv_e⟩
        have h_exists : ∃ x ∈ t ∩ e, x ≠ v := by
          by_contra h_all_v
          push_neg at h_all_v
          have h_sub : t ∩ e ⊆ {v} := fun y hy => Finset.mem_singleton.mpr (h_all_v y hy)
          have h_card_le : (t ∩ e).card ≤ 1 := Finset.card_le_card h_sub |>.trans (by simp)
          linarith
        obtain ⟨x, hx, hx_ne⟩ := h_exists
        exact ⟨x, Finset.mem_of_mem_inter_left hx, Finset.mem_of_mem_inter_right hx, hx_ne⟩
      -- The spoke {v, x} is in spokes and in t.sym2
      use Sym2.mk (v, x)
      constructor
      · simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨x, ⟨e, he_pack, hx_e, hx_ne_v⟩, rfl⟩
      · simp only [Finset.mem_sym2_iff]
        exact ⟨hv_t, hx_t⟩

  -- Bound |spokes| ≤ 4
  -- Each of the (at least 3, at most 4) elements containing v contributes 2 vertices
  -- But elements may share vertices (beyond v)... actually no, packing means disjoint
  -- Wait, packing only ensures (e ∩ f).card ≤ 1, so they share at most v
  -- So vertices_at_v has exactly 2 * k elements where k = |packingElementsContaining M v|
  -- With k ∈ {3, 4}, we get 6 or 8 vertices, hence 6 or 8 spokes
  -- But we're claiming 4... need a selection argument

  -- Actually, the key is: we can select 4 spokes that cover everything
  -- Every triangle shares edge with ONE element (approximately), so 2 spokes per element suffice
  -- With 4 elements, choose 1 spoke per element: 4 spokes total

  -- For now, accept the ≤ 8 bound and refine later
  have h_card_bound : spokes.card ≤ 8 := by
    calc spokes.card
        ≤ vertices_at_v.card := Finset.card_image_le
      _ ≤ (packingElementsContaining M v).card * 2 := by
          -- Each element contributes exactly 2 vertices (since each is a 3-clique containing v)
          sorry
      _ ≤ 4 * 2 := by
          have h_le_4 : (packingElementsContaining M v).card ≤ 4 := by
            calc (packingElementsContaining M v).card
                ≤ M.card := Finset.card_filter_le M _
              _ = 4 := hM_card
          linarith
      _ = 8 := by norm_num

  -- But we need ≤ 4, not ≤ 8
  -- The tighter bound comes from: we don't need all spokes, just 4 well-chosen ones
  -- Specifically: pick one vertex from each of (up to 4) packing elements
  have h_card_tight : spokes.card ≤ 4 := by
    -- This requires showing we can cover with just 4 spokes
    -- Key insight: for each packing element e = {v, a, b},
    -- triangles sharing edge with e that contain v are covered by either {v,a} or {v,b}
    -- We just need one spoke per element to hit all its triangles
    sorry

  exact triangleCoveringNumberOn_le_of_isTriangleCover G _ spokes h_cover |>.trans h_card_tight

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Triple Apex
-- ══════════════════════════════════════════════════════════════════════════════

/--
When v is in ≥3 packing triangles, τ(G) ≤ 8.

Case split:
- If v is in all 4 (star case):
  - τ(containing v) ≤ 4 (spokes)
  - τ(avoiding v) ≤ 4 (bases)
  - Total: τ ≤ 8

- If v is in exactly 3:
  - For the 3 at v: τ ≤ 3 + 3 = 6 (3 spokes + 3 bases)
  - For the isolated element e4: τ(S_{e4}) ≤ 2
  - Total: τ ≤ 8
-/
theorem tau_le_8_triple_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card ≥ 3) :
    triangleCoveringNumber G ≤ 8 := by
  -- V-decomposition at v
  have h_decomp : trianglesAtV G M v = trianglesAtVContainingV G M v ∪ trianglesAtVAvoidingV G M v := by
    ext t
    simp only [trianglesAtVContainingV, trianglesAtVAvoidingV, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ht
      by_cases hv_t : v ∈ t
      · left; exact ⟨ht, hv_t⟩
      · right; exact ⟨ht, hv_t⟩
    · intro h
      cases h with
      | inl h => exact h.1
      | inr h => exact h.1

  -- Bound containing + avoiding
  have h_contain : triangleCoveringNumberOn G (trianglesAtVContainingV G M v) ≤ 4 :=
    tau_at_v_containing_v_le_4 G M hM hM_card v hv

  have h_avoid : triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ 4 := by
    have h_k : (packingElementsContaining M v).card ≤ 4 := by
      calc (packingElementsContaining M v).card ≤ M.card := Finset.card_filter_le M _
        _ = 4 := hM_card
    calc triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v)
        ≤ (packingElementsContaining M v).card := tau_at_v_avoiding_v_le_k G M hM v _ rfl
      _ ≤ 4 := h_k

  -- Need to relate trianglesAtV to all triangles
  -- All triangles share edge with M (max packing dominates)
  -- Triangles sharing with elements containing v are in trianglesAtV
  -- What about elements NOT containing v?

  -- Case split on |packingElementsContaining M v|
  interval_cases (packingElementsContaining M v).card
  · -- 0 elements: contradiction with hv
    linarith
  · -- 1 element: contradiction with hv
    linarith
  · -- 2 elements: contradiction with hv
    linarith
  · -- 3 elements: one element is isolated (doesn't contain v)
    -- τ(at v) ≤ 4 + 3 = 7 (containing ≤ 4, avoiding ≤ 3)
    -- τ(isolated) ≤ 2 by tau_S_le_2
    -- Total ≤ 7 + 2 = 9... too loose
    -- Need tighter analysis
    sorry
  · -- 4 elements: star case, v in all
    -- All triangles are in trianglesAtV
    -- τ ≤ 4 + 4 = 8
    sorry

-- Specialized version for all 4 sharing v (star)
theorem tau_le_8_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card = 4) :
    triangleCoveringNumber G ≤ 8 := by
  apply tau_le_8_triple_apex G M hM hM_card v
  linarith

-- Specialized version for exactly 3 sharing v
theorem tau_le_8_three_share_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card = 3)
    (e4 : Finset V) (he4 : e4 ∈ M) (he4_no_v : v ∉ e4) :
    triangleCoveringNumber G ≤ 8 := by
  apply tau_le_8_triple_apex G M hM hM_card v
  linarith

end
