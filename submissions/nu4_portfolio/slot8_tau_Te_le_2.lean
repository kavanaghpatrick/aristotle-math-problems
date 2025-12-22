/-
Tuza ν=4 Portfolio - Slot 8: τ(T_e) ≤ 2

TARGET: Prove τ(T_e) ≤ 2 for any packing element e ∈ M

PROVEN FACTS (from tuza_tau_Se_COMPLETE.lean):
1. S_e triangles pairwise share edges (lemma_2_2)
2. Pairwise intersecting → common edge OR ≤4 vertices (intersecting_triangles_structure)
3. Common edge → τ ≤ 1 (common_edge_implies_tau_le_1)
4. ≤4 vertices → τ ≤ 2 (k4_cover)
5. τ(S_e) ≤ 2 (tau_S_e_le_2)

DECOMPOSITION:
T_e = S_e ∪ bridges(e), where bridges share edge with both e and some f ∈ M \ {e}

KEY INSIGHT:
- If S_e forms a STAR at edge {u,v}: τ(S_e) = 1, so 1 edge to spare for bridges
- If S_e forms a K4 in vertices U: bridges might fit in U (same 2 edges cover)

For bridges X(e,f) where e ∩ f = {v}: all bridge triangles contain v.
This geometric constraint may allow absorption into S_e cover.

STRATEGY: Boris Minimal - proven lemmas as scaffolding, let Aristotle find the path
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (consistent with tuza_tau_Se_COMPLETE.lean)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from tuza_tau_Se_COMPLETE.lean - ZERO SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

-- Parker's Lemma 2.2: S_e triangles pairwise share edges
lemma S_e_pairwise_shareEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    Set.Pairwise (S_e G e M : Set (Finset V)) shareEdge := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean (lemma_2_2)

-- Structure theorem: pairwise intersecting → common edge OR ≤4 vertices
lemma intersecting_triangles_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3)
    (h_pairwise : Set.Pairwise (T : Set (Finset V)) shareEdge) :
    (∃ u v : V, u ≠ v ∧ ∀ t ∈ T, {u, v} ⊆ t) ∨ (Finset.biUnion T id).card ≤ 4 := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean (intersecting_triangles_structure)

-- Common edge implies τ ≤ 1
lemma common_edge_implies_tau_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3)
    (u v : V) (huv : u ≠ v) (h_common : ∀ t ∈ T, {u, v} ⊆ t) :
    triangleCoveringNumberOn G T ≤ 1 := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean (common_edge_implies_tau_le_1)

-- K4 cover: ≤4 vertices implies τ ≤ 2
lemma k4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.card ≤ 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3 |>.filter (fun t => t ⊆ U)) ≤ 2 := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean (k4_cover)

-- THE KEY PROVEN RESULT: τ(S_e) ≤ 2
lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean (tau_S_e_le_2)

-- ══════════════════════════════════════════════════════════════════════════════
-- DECOMPOSITION LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- T_e = S_e ∪ bridges (partition)
lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G e M ∪ bridges G e M := by
  ext t
  simp only [Finset.mem_union, S_e, bridges, trianglesSharingEdge, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- S_e and bridges are disjoint
lemma Se_bridges_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    Disjoint (S_e G e M) (bridges G e M) := by
  rw [Finset.disjoint_iff_ne]
  intro t1 ht1 t2 ht2 heq
  simp only [S_e, bridges, Finset.mem_filter] at ht1 ht2
  subst heq
  obtain ⟨f, hfM, hfne, hcard⟩ := ht2.2
  have := ht1.2 f hfM hfne
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE STRUCTURE LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- Bridge triangles in X(e,f) contain the shared vertex when e ∩ f = {v}
lemma X_triangles_contain_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (h_inter : e ∩ f = {v})
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3) :
    ∀ t ∈ X_ef G e f, v ∈ t := by
  sorry  -- Bridge triangles share ≥2 vertices with both e and f; only v in common

-- Packing elements share ≤1 vertex
lemma packing_intersection_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (e ∩ f).card ≤ 1 := by
  exact hM.1.2 he hf hef

-- Packing elements either share exactly one vertex or are disjoint
lemma packing_pair_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (∃ v : V, e ∩ f = {v}) ∨ (e ∩ f = ∅) := by
  have h_card := packing_intersection_le_1 G M hM e f he hf hef
  interval_cases h : (e ∩ f).card
  · right; exact Finset.card_eq_zero.mp h
  · left; exact Finset.card_eq_one.mp h

-- ══════════════════════════════════════════════════════════════════════════════
-- CASE ANALYSIS: STAR vs K4
-- ══════════════════════════════════════════════════════════════════════════════

-- STAR CASE: If S_e forms a star, τ(S_e) = 1, leaving room for bridges
lemma tau_Te_star_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (u v : V) (huv : u ≠ v) (h_star : ∀ t ∈ S_e G e M, {u, v} ⊆ t) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry

-- K4 CASE: If S_e is contained in 4 vertices, bridges might fit there too
lemma tau_Te_k4_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (U : Finset V) (hU : U.card ≤ 4) (h_Se_in_U : ∀ t ∈ S_e G e M, t ⊆ U) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN TARGET
-- ══════════════════════════════════════════════════════════════════════════════

-- TARGET: τ(T_e) ≤ 2
theorem tau_Te_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry

end
