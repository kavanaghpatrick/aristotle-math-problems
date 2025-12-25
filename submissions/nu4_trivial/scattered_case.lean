/-
Tuza ν=4 - Scattered Case (Empty Sharing Graph)

TARGET: If all 4 packing triangles are vertex-disjoint, prove τ ≤ 8.

KEY INSIGHT (confirmed by Gemini, Grok, Codex - Dec 24):
When packing elements are vertex-disjoint:
1. A bridge triangle would need ≥2 vertices from e AND ≥2 from f
2. But a triangle has only 3 vertices
3. So bridges(e) = ∅ for all e
4. Therefore T_e = S_e, and τ(T_e) ≤ 2 (proven)
5. Total: τ ≤ 4 × 2 = 8

This case is TRIVIAL once we prove the "no bridges" lemma.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven scaffolding)
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

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

-- X_ef: bridges between specific pair e, f
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- Packing is vertex-disjoint (scattered sharing graph)
def isVertexDisjointPacking (M : Finset (Finset V)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (e : Set V) (f : Set V)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slots 6, 16, 29)
-- ══════════════════════════════════════════════════════════════════════════════

-- T_e = S_e ∪ bridges
lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G M e ∪ bridges G M e := by
  ext t
  simp only [Finset.mem_union, S_e, bridges, trianglesSharingEdge, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- τ(A ∪ B) ≤ τ(A) + τ(B)
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot16/29, will be filled by Aristotle

-- τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- PROVEN in slot6/29, will be filled by Aristotle

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW LEMMAS FOR SCATTERED CASE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key insight: If e and f are vertex-disjoint, no triangle can share edges with both.
    A triangle sharing edge with e needs ≥2 vertices from e.
    A triangle sharing edge with f needs ≥2 vertices from f.
    But 2+2 = 4 > 3 = triangle size. Contradiction. -/
lemma X_ef_empty_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V)
    (h_disj : Disjoint (e : Set V) (f : Set V)) :
    X_ef G e f = ∅ := by
  -- A triangle can share ≥2 vertices with at most one of two disjoint sets
  -- Since e and f are disjoint and a triangle has 3 vertices,
  -- it can't have ≥2 from e AND ≥2 from f (would need 4 vertices)
  ext t
  constructor
  · intro ht
    simp only [X_ef, Finset.mem_filter] at ht
    obtain ⟨ht_tri, h_e_inter, h_f_inter⟩ := ht
    -- t is a 3-clique, so |t| = 3
    have h_t_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_tri
      exact ht_tri.2
    -- t ∩ e and t ∩ f are disjoint (since e and f are)
    have h_disj_finset : Disjoint (t ∩ e) (t ∩ f) := by
      simp only [Finset.disjoint_left]
      intro x hx_te hx_tf
      have hxe : x ∈ e := Finset.mem_inter.mp hx_te |>.2
      have hxf : x ∈ f := Finset.mem_inter.mp hx_tf |>.2
      exact h_disj.ne_of_mem (Finset.mem_coe.mpr hxe) (Finset.mem_coe.mpr hxf) rfl
    -- (t ∩ e) ∪ (t ∩ f) ⊆ t
    have h_union_sub : (t ∩ e) ∪ (t ∩ f) ⊆ t := Finset.union_subset
      (Finset.inter_subset_left) (Finset.inter_subset_left)
    -- |t ∩ e| + |t ∩ f| = |(t ∩ e) ∪ (t ∩ f)| ≤ |t| = 3
    have h_sum_le : (t ∩ e).card + (t ∩ f).card ≤ 3 := by
      calc (t ∩ e).card + (t ∩ f).card
          = ((t ∩ e) ∪ (t ∩ f)).card := (Finset.card_union_of_disjoint h_disj_finset).symm
        _ ≤ t.card := Finset.card_le_card h_union_sub
        _ = 3 := h_t_card
    -- But |t ∩ e| ≥ 2 and |t ∩ f| ≥ 2, so sum ≥ 4, contradiction
    omega
  · intro ht
    exact absurd ht (Finset.not_mem_empty t)

/-- For vertex-disjoint packing, all bridges are empty -/
lemma bridges_empty_of_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M)
    (h_disj : isVertexDisjointPacking M) :
    bridges G M e = ∅ := by
  ext t
  simp only [bridges, Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
  intro ht
  push_neg
  intro f hf hne
  -- e and f are vertex-disjoint
  have h_ef_disj : Disjoint (e : Set V) (f : Set V) := h_disj e he f hf hne.symm
  -- So X_ef is empty
  have h_X_empty := X_ef_empty_of_disjoint G e f h_ef_disj
  -- t cannot be in X_ef
  by_contra h_ge_2
  push_neg at h_ge_2
  have h_t_in_X : t ∈ X_ef G e f := by
    simp only [X_ef, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2, h_ge_2⟩
  rw [h_X_empty] at h_t_in_X
  exact Finset.not_mem_empty t h_t_in_X

/-- For vertex-disjoint packing, T_e = S_e -/
lemma Te_eq_Se_of_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M)
    (h_disj : isVertexDisjointPacking M) :
    trianglesSharingEdge G e = S_e G M e := by
  rw [Te_eq_Se_union_bridges G M e]
  rw [bridges_empty_of_vertex_disjoint G M e he h_disj]
  simp

/-- For vertex-disjoint packing, τ(T_e) ≤ 2 -/
lemma tau_Te_le_2_of_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_disj : isVertexDisjointPacking M) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  rw [Te_eq_Se_of_vertex_disjoint G M e he h_disj]
  exact tau_S_le_2 G M hM e he

-- ══════════════════════════════════════════════════════════════════════════════
-- CRITICAL LEMMA: No loose triangles in maximal vertex-disjoint packing
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key insight: A triangle that shares no edge with any packing element
    would be addable to the packing, contradicting maximality.

    In vertex-disjoint packing, "shares no edge with e" = "shares ≤1 vertex with e".
    If t shares ≤1 vertex with each e ∈ M, then t is edge-disjoint from all of M,
    so M ∪ {t} would be a valid packing of size 5, contradicting ν = 4. -/
lemma no_loose_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (h_disj : isVertexDisjointPacking M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_in_M : t ∉ M) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  -- If t shares ≤1 vertex with every e ∈ M, then t is edge-disjoint from M
  by_contra h
  push_neg at h
  -- Then M ∪ {t} is a valid packing
  have h_can_add : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · -- M ∪ {t} ⊆ triangles
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with hxM | rfl
      · exact hM.1.1 hxM
      · exact ht
    · -- Pairwise edge-disjoint
      intro x hx y hy hxy
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx with hx_in_M | hx_eq_t
      · rcases hy with hy_in_M | hy_eq_t
        · exact hM.1.2 hx_in_M hy_in_M hxy
        · subst hy_eq_t
          have h_lt := h x hx_in_M
          rw [Finset.inter_comm] at h_lt
          omega
      · subst hx_eq_t
        rcases hy with hy_in_M | hy_eq_t
        · have h_lt := h y hy_in_M
          omega
        · subst hy_eq_t; exact absurd rfl hxy
  -- But |M ∪ {t}| = 5 > ν(G) = 4
  have h_card : (M ∪ {t}).card = M.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · simp [ht_not_in_M]
  have h_exceeds : (M ∪ {t}).card > trianglePackingNumber G := by
    rw [h_card, hM.2]
    omega
  -- Contradiction: M ∪ {t} is a valid packing larger than M
  -- But M is maximal, so this is impossible
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
      -- If max is ⊥, that means the set is empty, but we have a member, contradiction
      exfalso
      have : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card := h_in_image
      rw [Finset.max_eq_bot] at hmax
      exact Finset.eq_empty_iff_forall_not_mem.mp hmax _ this
    | coe n =>
      simp only [Option.getD]
      rw [hmax] at h_le_max
      exact WithBot.coe_le_coe.mp h_le_max
  linarith

/-- All triangles in G are in the union of T_e for e ∈ M -/
lemma all_triangles_in_union_Te (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (h_disj : isVertexDisjointPacking M) :
    ∀ t ∈ G.cliqueFinset 3, t ∈ M.biUnion (trianglesSharingEdge G) := by
  intro t ht
  by_cases ht_M : t ∈ M
  · -- t ∈ M → t shares edge with itself → t ∈ T_t
    simp only [Finset.mem_biUnion]
    use t, ht_M
    simp only [trianglesSharingEdge, Finset.mem_filter]
    refine ⟨ht, ?_⟩
    -- Need to show (t ∩ t).card ≥ 2, but t ∩ t = t and t.card = 3
    simp only [Finset.inter_self]
    have h_t_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht
      exact ht.2
    omega
  · -- t ∉ M → by no_loose_triangles, ∃ e ∈ M with |t ∩ e| ≥ 2
    obtain ⟨e, he, h_inter⟩ := no_loose_triangles G M hM h_disj t ht ht_M
    simp only [Finset.mem_biUnion]
    use e, he
    simp only [trianglesSharingEdge, Finset.mem_filter]
    exact ⟨ht, h_inter⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Scattered Case
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: If ν = 4 with vertex-disjoint packing (scattered sharing graph), then τ ≤ 8 -/
theorem tau_le_8_scattered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_disj : isVertexDisjointPacking M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: All triangles in G are in ∪_{e ∈ M} T_e (no loose triangles)
  have h_all : ∀ t ∈ G.cliqueFinset 3, t ∈ M.biUnion (trianglesSharingEdge G) :=
    all_triangles_in_union_Te G M hM h_disj
  -- Step 2: Since M is vertex-disjoint, T_e = S_e for each e, so τ(T_e) ≤ 2
  have h_each : ∀ e ∈ M, triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
    intro e he
    exact tau_Te_le_2_of_vertex_disjoint G M hM e he h_disj
  -- Step 3: By union bound over 4 elements, τ(∪T_e) ≤ 4 × 2 = 8
  -- Step 4: Since all triangles are in ∪T_e, τ(G) ≤ τ(∪T_e) ≤ 8
  sorry -- Aristotle will complete the union bound calculation

end
