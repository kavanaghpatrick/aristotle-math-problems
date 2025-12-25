/-
Tuza ν=4 - Two-Two VW Case (Two Disjoint Pairs)

TARGET: If M = {e1, e2, e3, e4} where (e1,e2) share vertex v and (e3,e4) share vertex w,
        with v ≠ w and no other shared vertices, prove τ ≤ 8.

KEY INSIGHT (confirmed by Gemini, Grok, Codex - Dec 24):
This is equivalent to two independent ν=2 subproblems:
1. Component C1 = {e1, e2} with shared vertex v → τ(C1) ≤ 4 (known for ν=2)
2. Component C2 = {e3, e4} with shared vertex w → τ(C2) ≤ 4 (known for ν=2)
3. No cross-bridges between C1 and C2 (same 4-vertex argument as scattered)
4. Total: τ ≤ 4 + 4 = 8

The same argument works for matching_2 (two disjoint edges in sharing graph).
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

-- X_ef: bridges between specific pair e, f
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- T_pair: all triangles sharing edge with either e or f
def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- Two components are vertex-disjoint
def componentsDisjoint (C1 C2 : Finset (Finset V)) : Prop :=
  ∀ e1 ∈ C1, ∀ e2 ∈ C2, Disjoint (e1 : Set V) (e2 : Set V)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

-- τ(A ∪ B) ≤ τ(A) + τ(B)
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot16/29

-- τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- PROVEN in slot6/29

-- τ(X_ef) ≤ 2
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- PROVEN in slot24

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: No cross-bridges between disjoint components
-- ══════════════════════════════════════════════════════════════════════════════

/-- If e and f are vertex-disjoint, no triangle can share edges with both -/
lemma X_ef_empty_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V)
    (h_disj : Disjoint (e : Set V) (f : Set V)) :
    X_ef G e f = ∅ := by
  -- A triangle can share ≥2 vertices with at most one of two disjoint sets
  ext t
  constructor
  · intro ht
    simp only [X_ef, Finset.mem_filter] at ht
    obtain ⟨ht_tri, h_e_inter, h_f_inter⟩ := ht
    have h_t_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_tri
      exact ht_tri.2
    have h_disj_finset : Disjoint (t ∩ e) (t ∩ f) := by
      simp only [Finset.disjoint_left]
      intro x hx_te hx_tf
      have hxe : x ∈ e := Finset.mem_inter.mp hx_te |>.2
      have hxf : x ∈ f := Finset.mem_inter.mp hx_tf |>.2
      exact h_disj.ne_of_mem (Finset.mem_coe.mpr hxe) (Finset.mem_coe.mpr hxf) rfl
    have h_union_sub : (t ∩ e) ∪ (t ∩ f) ⊆ t := Finset.union_subset
      (Finset.inter_subset_left) (Finset.inter_subset_left)
    have h_sum_le : (t ∩ e).card + (t ∩ f).card ≤ 3 := by
      calc (t ∩ e).card + (t ∩ f).card
          = ((t ∩ e) ∪ (t ∩ f)).card := (Finset.card_union_of_disjoint h_disj_finset).symm
        _ ≤ t.card := Finset.card_le_card h_union_sub
        _ = 3 := h_t_card
    omega
  · intro ht
    exact absurd ht (Finset.not_mem_empty t)

/-- No cross-bridges between vertex-disjoint components -/
lemma no_cross_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (C1 C2 : Finset (Finset V))
    (h_disj : componentsDisjoint C1 C2) :
    ∀ e1 ∈ C1, ∀ e2 ∈ C2, X_ef G e1 e2 = ∅ := by
  intro e1 he1 e2 he2
  exact X_ef_empty_of_disjoint G e1 e2 (h_disj e1 he1 e2 he2)

-- ══════════════════════════════════════════════════════════════════════════════
-- ν=2 BOUND (Parker's result)
-- ══════════════════════════════════════════════════════════════════════════════

/-- For a pair sharing a vertex, τ(T_e ∪ T_f) ≤ 4
    This follows from τ(S_e) ≤ 2, τ(S_f) ≤ 2, and bridges covered via shared vertex -/
lemma tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f)
    (v : V) (hv : v ∈ e ∧ v ∈ f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- T_pair = T_e ∪ T_f = (S_e ∪ X(e,f)) ∪ (S_f ∪ X(e,f)) = S_e ∪ S_f ∪ X(e,f)
  -- τ(S_e) ≤ 2, τ(S_f) ≤ 2, but X(e,f) goes through v and can be covered by v-incident edges
  -- Actually: τ ≤ τ(S_e) + τ(S_f) = 4 because X(e,f) ⊆ S_e ∪ S_f (bridges share edge with both)
  -- Wait, that's not quite right. Use union bound carefully.
  sorry -- Aristotle will prove this using the scaffolding

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Two-Two VW Case
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: If M has two disjoint vertex-sharing pairs, then τ ≤ 8 -/
theorem tau_le_8_two_two_vw (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (v w : V) (hvw : v ≠ w)
    (hv : v ∈ e1 ∧ v ∈ e2) (hw : w ∈ e3 ∧ w ∈ e4)
    (h_disj : componentsDisjoint {e1, e2} {e3, e4}) :
    triangleCoveringNumber G ≤ 8 := by
  -- C1 = {e1, e2} has τ(T_{e1} ∪ T_{e2}) ≤ 4 (pair sharing v)
  -- C2 = {e3, e4} has τ(T_{e3} ∪ T_{e4}) ≤ 4 (pair sharing w)
  -- No cross-bridges between C1 and C2 (vertex-disjoint components)
  -- So τ(G) ≤ 4 + 4 = 8
  sorry

/-- Alternative: matching_2 case (two disjoint edges in sharing graph) -/
theorem tau_le_8_matching_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    -- (e1, e2) share a vertex, (e3, e4) share a vertex
    (h12_share : (e1 ∩ e2).Nonempty)
    (h34_share : (e3 ∩ e4).Nonempty)
    -- Components are vertex-disjoint
    (h_disj : componentsDisjoint {e1, e2} {e3, e4}) :
    triangleCoveringNumber G ≤ 8 := by
  -- Same argument as two_two_vw
  sorry

end
