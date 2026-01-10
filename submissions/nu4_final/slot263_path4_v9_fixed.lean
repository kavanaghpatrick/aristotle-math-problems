/-
slot263 v9: PATH_4 τ ≤ 8 - Fixed to use proven packing lemma

KEY FIX: Line 496 changed from:
  path4_cover_card_le_8 G M cfg  -- NEGATED (false without packing)
To:
  path4_cover_card_le_8_of_packing G M hM.1 cfg  -- PROVEN

The main theorem has `hM : isMaxPacking G M`, and isMaxPacking = isTrianglePacking ∧ ...
So `hM.1 : isTrianglePacking G M` gives us what we need.

STILL NEEDS PROOF:
- cover_hits_sharing_B (line 323)
- cover_hits_sharing_C (line 332)
- Final step of tau_le_8_path4 (line 498)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (matches proven slot223a pattern)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0

-- PATH_4 structure (using ∩ notation like proven files)
structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  hM_card : M.card = 4
  -- Spine vertices (provided, not extracted)
  v1 : V
  v2 : V
  v3 : V
  -- Adjacency pattern: A-B-C-D path
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  -- Non-adjacent pairs
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅
  -- Membership witnesses
  h_v1_A : v1 ∈ A
  h_v1_B : v1 ∈ B
  h_v2_B : v2 ∈ B
  h_v2_C : v2 ∈ C
  h_v3_C : v3 ∈ C
  h_v3_D : v3 ∈ D

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each M-element has exactly 3 vertices -/
lemma M_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X : Finset V) (hX : X ∈ M) : X.card = 3 := by
  have := hM.1 hX
  exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2

-- ══════════════════════════════════════════════════════════════════════════════
-- EXPLICIT 8-EDGE COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- The explicit 8-edge cover for PATH_4 -/
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  -- All edges of endpoint A
  cfg.A.sym2.filter (fun e => e ∈ G.edgeFinset) ∪
  -- Spine edge {v1, v2}
  ({s(cfg.v1, cfg.v2)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  -- Spine edge {v2, v3}
  ({s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  -- All edges of endpoint D
  cfg.D.sym2.filter (fun e => e ∈ G.edgeFinset)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPER LEMMAS (from Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

/-- The number of edges within a set of 3 vertices is at most 3. -/
lemma card_edges_of_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hA : A.card = 3) :
    (A.sym2.filter (fun e => e ∈ G.edgeFinset)).card ≤ 3 := by
  all_goals rw [Finset.card_eq_three] at hA; obtain ⟨x, y, z, h⟩ := hA; simp_all +decide [Finset.filter]
  all_goals simp_all +decide [Finset.sym2, Multiset.sym2]
  all_goals erw [Quotient.liftOn_mk] at *; simp_all +decide [List.sym2]
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons, List.filter_singleton]; aesop

/-- The number of edges in a singleton set of potential edges is at most 1. -/
lemma card_spine_edge (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (({s(u, v)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset)).card ≤ 1 := by
  exact Finset.card_filter_le _ _

/-- PROVEN: If M is a triangle packing, then the path4 cover has at most 8 edges. -/
lemma path4_cover_card_le_8_of_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8 := by
  refine' le_trans (Finset.card_union_le _ _) _
  refine' le_trans (add_le_add_right (Finset.card_union_le _ _ |> le_trans <| add_le_add_right (Finset.card_union_le _ _) _) _) _
  refine' le_trans (add_le_add (add_le_add (add_le_add (card_edges_of_triangle G cfg.A _) (card_spine_edge G cfg.v1 cfg.v2)) (card_spine_edge G cfg.v2 cfg.v3)) (card_edges_of_triangle G cfg.D _)) _
  · exact M_element_card_3 G M hM _ cfg.hA
  · exact M_element_card_3 G M hM _ cfg.hD
  · norm_num

/-- The cover is a subset of G's edges -/
lemma path4_cover_subset_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    path4_cover G cfg ⊆ G.edgeFinset := by
  unfold path4_cover
  simp only [union_subset_iff, filter_subset_iff]
  exact ⟨⟨⟨fun _ h => h.2, fun _ h => h.2⟩, fun _ h => h.2⟩, fun _ h => h.2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERAGE LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN: Any triangle sharing an edge with A is covered -/
lemma cover_hits_sharing_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_shares : (t ∩ cfg.A).card ≥ 2) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, x ∈ t ∩ cfg.A ∧ y ∈ t ∩ cfg.A ∧ x ≠ y := by
    simpa using Finset.one_lt_card.1 ht_shares
  have h_adj : G.Adj x y := by
    simp_all +decide [SimpleGraph.isClique_iff, Finset.mem_inter]
    exact ht.1 (by aesop) (by aesop) hxy.2.2
  use s(x, y)
  unfold path4_cover; aesop

/-- PROVEN: Any triangle sharing an edge with D is covered -/
lemma cover_hits_sharing_D (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_shares : (t ∩ cfg.D).card ≥ 2) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : V, u ∈ cfg.D ∧ v ∈ cfg.D ∧ u ≠ v ∧ u ∈ t ∧ v ∈ t := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 ht_shares; use u, v; aesop
  use Sym2.mk (u, v)
  unfold path4_cover; simp_all +decide [Finset.mem_union, Finset.mem_filter]
  have := ht.1; aesop

/-- Any triangle sharing an edge with B (but not A) is covered via spine edge {v1, v2} -/
lemma cover_hits_sharing_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ cfg.B).card ≥ 2) (ht_not_A : (t ∩ cfg.A).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  -- t shares ≥2 vertices with B = {v1, v2, b}
  -- t shares ≤1 vertex with A
  -- Since A ∩ B = {v1}, if t shares v1 with A, it can share at most v1
  -- So t must share {v1, v2} or {v1, b} or {v2, b} with B
  -- Case {v1, v2}: covered by spine edge
  -- Case {v1, b} or {v2, b}: need to analyze further
  sorry

/-- Any triangle sharing an edge with C (but not D) is covered via spine edge {v2, v3} -/
lemma cover_hits_sharing_C (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_C : (t ∩ cfg.C).card ≥ 2) (ht_not_D : (t ∩ cfg.D).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: For PATH_4 configuration with ν(G) = 4, we have τ(G) ≤ 8 -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Path4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- The explicit cover
  let E := path4_cover G cfg
  -- Show E is a valid cover
  have hE_subset : E ⊆ G.edgeFinset := path4_cover_subset_edges G M cfg
  have hE_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
    intro t ht
    -- Every triangle either shares an edge with some M-element or is in M
    by_cases ht_in_M : t ∈ M
    · -- t ∈ M, so t ∈ {A, B, C, D}
      rw [cfg.hM_eq] at ht_in_M
      simp only [mem_insert, mem_singleton] at ht_in_M
      rcases ht_in_M with rfl | rfl | rfl | rfl
      · exact cover_hits_sharing_A G M cfg t ht (by simp)
      · exact cover_hits_sharing_B G M hM cfg t ht (by simp) (by
          have := cfg.hAB
          simp only [inter_comm] at this ⊢
          have h : cfg.B ∩ cfg.A = {cfg.v1} := by rw [inter_comm]; exact this
          simp [h])
      · exact cover_hits_sharing_C G M hM cfg t ht (by simp) (by
          have := cfg.hCD
          simp only [inter_comm] at this ⊢
          have h : cfg.C ∩ cfg.D = {cfg.v3} := by rw [inter_comm]; exact this
          simp [h])
      · exact cover_hits_sharing_D G M cfg t ht (by simp)
    · -- t ∉ M, so by maximality it shares an edge with some M-element
      have h_shares := hM.2 t ht ht_in_M
      obtain ⟨m, hm_M, hm_shares⟩ := h_shares
      rw [cfg.hM_eq] at hm_M
      simp only [mem_insert, mem_singleton] at hm_M
      rcases hm_M with rfl | rfl | rfl | rfl
      · exact cover_hits_sharing_A G M cfg t ht hm_shares
      · by_cases hA : (t ∩ cfg.A).card ≥ 2
        · exact cover_hits_sharing_A G M cfg t ht hA
        · push_neg at hA
          exact cover_hits_sharing_B G M hM cfg t ht hm_shares hA
      · by_cases hD : (t ∩ cfg.D).card ≥ 2
        · exact cover_hits_sharing_D G M cfg t ht hD
        · push_neg at hD
          exact cover_hits_sharing_C G M hM cfg t ht hm_shares hD
      · exact cover_hits_sharing_D G M cfg t ht hm_shares
  -- E is a cover of size ≤ 8
  have hE_cover : isTriangleCover G E := ⟨hE_subset, hE_covers⟩
  -- KEY FIX: Use the PROVEN packing lemma instead of the negated one
  -- hM : isMaxPacking G M, and isMaxPacking = isTrianglePacking ∧ ...
  -- So hM.1 : isTrianglePacking G M
  have hE_card : E.card ≤ 8 := path4_cover_card_le_8_of_packing G M hM.1 cfg
  -- Therefore τ(G) ≤ 8
  -- Need to show: minimum cover size ≤ 8, given we have a cover E with |E| ≤ 8
  sorry

end
