/-
Tuza ν=4: tau_containing_v_le_4

TARGET: Prove τ(triangles containing v in T_e ∪ T_f) ≤ 4

CONTEXT:
- e = {v, u, w} and f = {v, x, y} share exactly vertex v
- T_e = triangles sharing an EDGE with e
- T_f = triangles sharing an EDGE with f
- We want to cover all triangles in (T_e ∪ T_f) that contain v

KEY INSIGHT (verified by Grok/Codex):
A triangle t ∈ T_e containing v must share edge {v,u} or {v,w} with e.
(If it only shared {u,w}, it wouldn't contain v through that edge)

So triangles containing v in T_e are of form:
- {v, u, *} (share edge {v,u})
- {v, w, *} (share edge {v,w})

Similarly for T_f:
- {v, x, *} (share edge {v,x})
- {v, y, *} (share edge {v,y})

COVERING STRATEGY:
- Edge {v,u} covers all {v, u, *} triangles
- Edge {v,w} covers all {v, w, *} triangles
- Edge {v,x} covers all {v, x, *} triangles
- Edge {v,y} covers all {v, y, *} triangles
- Total: 4 edges suffice → τ ≤ 4
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL LEMMA: Triangles in T_e containing v share edge {v,u} or {v,w}
-- ══════════════════════════════════════════════════════════════════════════════

/-- If e = {v, u, w} and t ∈ T_e with v ∈ t, then t shares {v,u} or {v,w} with e -/
lemma triangle_containing_v_shares_v_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v u w : V) (he_eq : e = {v, u, w}) (huv : u ≠ v) (hwv : w ≠ v) (huw : u ≠ w)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G e) (hv : v ∈ t) :
    ({v, u} ⊆ t) ∨ ({v, w} ⊆ t) := by
  unfold trianglesSharingEdge at ht
  simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  obtain ⟨ht_clique, h_inter⟩ := ht
  -- t ∩ e has at least 2 elements
  -- Since v ∈ t ∩ e, there's another element in t ∩ e
  have hv_in_e : v ∈ e := by simp [he_eq]
  have hv_in_inter : v ∈ t ∩ e := Finset.mem_inter.mpr ⟨hv, hv_in_e⟩
  -- Get another element from the intersection
  have h_inter_ge_2 : (t ∩ e).card ≥ 2 := h_inter
  have h_exists_other : ∃ x ∈ t ∩ e, x ≠ v := by
    by_contra h_all_v
    push_neg at h_all_v
    have h_subset : t ∩ e ⊆ {v} := by
      intro x hx
      exact Finset.mem_singleton.mpr (h_all_v x hx)
    have h_card_le_1 : (t ∩ e).card ≤ 1 := Finset.card_le_card h_subset |>.trans (by simp)
    omega
  obtain ⟨x, hx_in_inter, hx_ne_v⟩ := h_exists_other
  have hx_in_t : x ∈ t := Finset.mem_inter.mp hx_in_inter |>.1
  have hx_in_e : x ∈ e := Finset.mem_inter.mp hx_in_inter |>.2
  -- x ∈ e = {v, u, w} and x ≠ v, so x = u or x = w
  simp only [he_eq, Finset.mem_insert, Finset.mem_singleton] at hx_in_e
  rcases hx_in_e with rfl | rfl | rfl
  · exact absurd rfl hx_ne_v
  · left; simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hv, hx_in_t⟩
  · right; simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hv, hx_in_t⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ(containing v in T_e ∪ T_f) ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ(containing v in T_e ∪ T_f) ≤ 4 when e ∩ f = {v} -/
theorem tau_containing_v_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v u w x y : V)
    (he_eq : e = {v, u, w}) (hf_eq : f = {v, x, y})
    (h_all_distinct : v ≠ u ∧ v ≠ w ∧ v ≠ x ∧ v ≠ y ∧ u ≠ w ∧ x ≠ y ∧ u ≠ x ∧ u ≠ y ∧ w ≠ x ∧ w ≠ y)
    (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G
      (trianglesContaining (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) v) ≤ 4 := by
  -- The 4 covering edges: {v,u}, {v,w}, {v,x}, {v,y}
  -- Every triangle t containing v in T_e ∪ T_f shares one of these edges
  let T := trianglesContaining (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) v
  -- Build the cover
  let C : Finset (Sym2 V) := {s(v,u), s(v,w), s(v,x), s(v,y)}

  -- Show C covers T
  have h_cover : ∀ t ∈ T, ∃ edge ∈ C, edge ∈ t.sym2 := by
    intro t ht
    unfold trianglesContaining at ht
    simp only [Finset.mem_filter, Finset.mem_union] at ht
    obtain ⟨ht_mem, hv_in_t⟩ := ht
    rcases ht_mem with h_in_Te | h_in_Tf
    · -- t ∈ T_e
      have h_shares := triangle_containing_v_shares_v_edge G e he v u w he_eq
        h_all_distinct.1.symm h_all_distinct.2.1.symm h_all_distinct.2.2.2.1 t h_in_Te hv_in_t
      rcases h_shares with h_vu | h_vw
      · use s(v,u)
        constructor
        · simp [C]
        · have hu_in_t : u ∈ t := Finset.mem_of_subset h_vu (by simp)
          simp [Finset.sym2, Sym2.mem_iff]
          exact ⟨hv_in_t, hu_in_t, h_all_distinct.1⟩
      · use s(v,w)
        constructor
        · simp [C]
        · have hw_in_t : w ∈ t := Finset.mem_of_subset h_vw (by simp)
          simp [Finset.sym2, Sym2.mem_iff]
          exact ⟨hv_in_t, hw_in_t, h_all_distinct.2.1⟩
    · -- t ∈ T_f
      have h_shares := triangle_containing_v_shares_v_edge G f hf v x y hf_eq
        h_all_distinct.2.2.1.symm h_all_distinct.2.2.2.2.1.symm h_all_distinct.2.2.2.2.2.1 t h_in_Tf hv_in_t
      rcases h_shares with h_vx | h_vy
      · use s(v,x)
        constructor
        · simp [C]
        · have hx_in_t : x ∈ t := Finset.mem_of_subset h_vx (by simp)
          simp [Finset.sym2, Sym2.mem_iff]
          exact ⟨hv_in_t, hx_in_t, h_all_distinct.2.2.1⟩
      · use s(v,y)
        constructor
        · simp [C]
        · have hy_in_t : y ∈ t := Finset.mem_of_subset h_vy (by simp)
          simp [Finset.sym2, Sym2.mem_iff]
          exact ⟨hv_in_t, hy_in_t, h_all_distinct.2.2.2.2.1⟩

  -- Show C has at most 4 elements and is subset of edgeFinset
  have h_card : C.card ≤ 4 := by simp [C]; decide
  have h_subset_edges : C ⊆ G.edgeFinset := by
    intro edge he_edge
    simp [C] at he_edge
    rcases he_edge with rfl | rfl | rfl | rfl <;>
    · apply SimpleGraph.mem_edgeFinset.mpr
      -- These edges exist because e and f are cliques containing v
      sorry

  -- Apply the bound
  unfold triangleCoveringNumberOn
  sorry

end
