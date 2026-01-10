/-
slot263: PATH_4 τ ≤ 8 via EXPLICIT 8-edge construction

STRATEGY: Use structure pattern from proven slot223a files.
Vertices v1, v2, v3 are provided in the Path4 structure, avoiding extraction issues.

PATH_4 STRUCTURE:
  A = {v1, a, a'}     -- endpoint
  B = {v1, v2, b}     -- middle
  C = {v2, v3, c}     -- middle
  D = {v3, d, d'}     -- endpoint

8-EDGE COVER:
  From A: {v1,a}, {v1,a'}, {a,a'}     -- all 3 edges
  From B: {v1,v2}                      -- spine edge
  From C: {v2,v3}                      -- spine edge
  From D: {v3,d}, {v3,d'}, {d,d'}     -- all 3 edges
  Total: 8 edges
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

/-- The cover has at most 8 edges -/
lemma path4_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8 := by
  sorry

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

/-- Any triangle sharing an edge with A is covered -/
lemma cover_hits_sharing_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_shares : (t ∩ cfg.A).card ≥ 2) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry

/-- Any triangle sharing an edge with D is covered -/
lemma cover_hits_sharing_D (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_shares : (t ∩ cfg.D).card ≥ 2) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry

/-- Any triangle sharing an edge with B (but not A) is covered via spine edge {v1, v2} -/
lemma cover_hits_sharing_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ cfg.B).card ≥ 2) (ht_not_A : (t ∩ cfg.A).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
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
  have hE_card : E.card ≤ 8 := path4_cover_card_le_8 G M cfg
  -- Therefore τ(G) ≤ 8
  sorry

end
