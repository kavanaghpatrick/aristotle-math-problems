/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5875ee26-d7a7-4ec0-8ef9-d1e401ce8403

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot51_spoke_cover_lemma.lean

  GENERAL SPOKE COVER LEMMA for Phase 2

  THEOREM: If vertex v is in all packing elements M (|M| = 4), then spoke edges
  from v cover all triangles containing v with at most 4 edges.

  This is a GENERAL theorem (not Fin n specific) for lifting to SimpleGraph V.

  TIER: 2 (omega, card_union bounds, existence argument)

  INFORMAL PROOF SKETCH:
  1. Each triangle t containing v shares an edge with some M-element e (by maximality)
  2. Since v ∈ e and v ∈ t, and (t ∩ e).card ≥ 2, there exists w ∈ e \ {v} with w ∈ t
  3. The spoke s(v, w) covers t
  4. For each M-element e = {v, a, b}, we need at most 1 spoke to cover all triangles
     assigned to e (pick whichever of s(v,a) or s(v,b) covers more)
  5. With 4 M-elements and 1 spoke each, we have ≤ 4 spokes total
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaximalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 1: Packing element has card 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (e : Finset V) (he : e ∈ M) :
    e.card = 3 := by
  have : e ∈ G.cliqueFinset 3 := hM.1 he
  rw [SimpleGraph.mem_cliqueFinset_iff] at this
  exact this.2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 2: Triangle has card 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  exact ht.2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 3: Every triangle shares edge with maximal packing
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_maximal_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_cases ht_M : t ∈ M
  · exact ⟨t, ht_M, by simp [triangle_card_3 G t ht]⟩
  · exact hM.2 t ht ht_M

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 4: If (t ∩ e).card ≥ 2 and v ∈ both, there exists w ≠ v in both
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_edge_has_second_vertex (t e : Finset V) (v : V)
    (hv_t : v ∈ t) (hv_e : v ∈ e) (h_share : (t ∩ e).card ≥ 2) :
    ∃ w ∈ t ∩ e, w ≠ v := by
  have hv_inter : v ∈ t ∩ e := mem_inter.mpr ⟨hv_t, hv_e⟩
  by_contra h_all_v
  push_neg at h_all_v
  have h_sub : t ∩ e ⊆ {v} := by
    intro x hx
    simp only [mem_singleton]
    by_contra hxv
    exact hxv (h_all_v x hx)
  have h_card_le : (t ∩ e).card ≤ 1 := calc
    (t ∩ e).card ≤ ({v} : Finset V).card := card_le_card h_sub
    _ = 1 := card_singleton v
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 5: Spoke edge s(v,w) is in triangle's sym2 when v,w ∈ triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma spoke_in_triangle_sym2 (t : Finset V) (v w : V)
    (hv : v ∈ t) (hw : w ∈ t) (hvw : v ≠ w) :
    s(v, w) ∈ t.sym2 := by
  rw [mem_sym2_iff]
  exact ⟨hv, hw⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 6: Edges in clique are graph edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma clique_edge_in_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (v w : V) (hv : v ∈ t) (hw : w ∈ t) (hvw : v ≠ w) :
    s(v, w) ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  have h_clique := ht.1
  rw [SimpleGraph.isClique_iff] at h_clique
  have h_adj := h_clique hv hw hvw
  rw [SimpleGraph.mem_edgeFinset]
  exact h_adj

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 7: e \ {v} has card 2
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_other_vertices (e : Finset V) (v : V)
    (he : e.card = 3) (hv : v ∈ e) :
    (e.erase v).card = 2 := by
  rw [card_erase_of_mem hv, he]

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 8: Cover existence implies covering number bound
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover_card_implies_covering_number_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) (n : ℕ)
    (hE_sub : E' ⊆ G.edgeFinset)
    (hE_card : E'.card ≤ n)
    (hE_cover : ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) :
    triangleCoveringNumberOn G triangles ≤ n := by
  unfold triangleCoveringNumberOn
  have h_in_filter : E' ∈ G.edgeFinset.powerset.filter (fun E'' => ∀ t ∈ triangles, ∃ e ∈ E'', e ∈ t.sym2) := by
    simp only [mem_filter, mem_powerset]
    exact ⟨hE_sub, hE_cover⟩
  have h_min_le := Finset.min_le (mem_image_of_mem Finset.card h_in_filter)
  cases h : Finset.min ((G.edgeFinset.powerset.filter (fun E'' => ∀ t ∈ triangles, ∃ e ∈ E'', e ∈ t.sym2)).image Finset.card) with
  | none => simp [Option.getD]
  | some m =>
    simp only [Option.getD]
    rw [h] at h_min_le
    simp only [WithBot.coe_le_coe] at h_min_le
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 9: Triangle containing v covered by spoke from M-element
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_covered_by_packing_spoke (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t e : Finset V) (v : V)
    (hM : isTrianglePacking G M)
    (ht : t ∈ G.cliqueFinset 3) (he : e ∈ M)
    (hv_t : v ∈ t) (hv_e : v ∈ e)
    (h_share : (t ∩ e).card ≥ 2) :
    ∃ w : V, w ∈ e ∧ w ≠ v ∧ w ∈ t ∧ s(v, w) ∈ G.edgeFinset := by
  obtain ⟨w, hw_inter, hw_ne_v⟩ := shared_edge_has_second_vertex t e v hv_t hv_e h_share
  have hw_t := mem_inter.mp hw_inter |>.1
  have hw_e := mem_inter.mp hw_inter |>.2
  have hvw_edge := clique_edge_in_graph G t ht v w hv_t hw_t hw_ne_v.symm
  exact ⟨w, hw_e, hw_ne_v.symm, hw_t, hvw_edge⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 10: All spokes from M-elements definition
-- ══════════════════════════════════════════════════════════════════════════════

def allSpokesFromM (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun e => (e.erase v).image (fun w => s(v, w))) |>.filter (· ∈ G.edgeFinset)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 11: allSpokesFromM is subset of graph edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma allSpokesFromM_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) :
    allSpokesFromM G M v ⊆ G.edgeFinset := fun e he =>
  (mem_filter.mp he).2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMA 12: allSpokesFromM covers triangles containing v
-- ══════════════════════════════════════════════════════════════════════════════

lemma allSpokesFromM_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V)
    (hM : isMaximalPacking G M)
    (hv : ∀ e ∈ M, v ∈ e)
    (t : Finset V) (ht : t ∈ trianglesContaining G v) :
    ∃ e ∈ allSpokesFromM G M v, e ∈ t.sym2 := by
  simp only [trianglesContaining, mem_filter] at ht
  have ht_tri := ht.1
  have hv_t := ht.2
  obtain ⟨e_M, he_M, h_share⟩ := triangle_shares_edge_with_maximal_packing G M hM t ht_tri
  have hv_e := hv e_M he_M
  obtain ⟨w, hw_e, hw_ne_v, hw_t, hvw_edge⟩ :=
    triangle_covered_by_packing_spoke G M t e_M v hM.1 ht_tri he_M hv_t hv_e h_share
  use s(v, w)
  constructor
  · simp only [allSpokesFromM, mem_filter, mem_biUnion]
    constructor
    · use e_M, he_M
      simp only [mem_image, mem_erase]
      exact ⟨w, ⟨hw_ne_v, hw_e⟩, rfl⟩
    · exact hvw_edge
  · exact spoke_in_triangle_sym2 t v w hv_t hw_t hw_ne_v

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Spoke edges cover all triangles containing v
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Each triangle t containing v shares an edge with some M-element e (by maximality)
2. Since v ∈ e (hypothesis) and v ∈ t, the shared vertices include some w ≠ v
   (because (t ∩ e).card ≥ 2)
3. The spoke s(v, w) covers t and is in allSpokesFromM
4. For each M-element e = {v, a, b}, we pick ONE spoke (either s(v,a) or s(v,b))
   that covers all triangles sharing edge with e
5. KEY INSIGHT: Every triangle t sharing edge with e and containing v must contain
   at least one of a or b (since (t ∩ e).card ≥ 2 and v ∈ t ∩ e)
6. We pick for each e the spoke s(v, x) where x ∈ {a,b} maximizes coverage
7. Total: 4 spokes (one per M-element)

The existence of such a selection follows from: for each e, partition triangles
sharing edge with e into those containing a vs those containing b. At least one
group covers all (or use both spokes if needed, but one suffices per the argument).
-/
theorem spoke_edges_cover_containing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V)
    (hM : isMaximalPacking G M)
    (hM_card : M.card = 4)
    (hv : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumberOn G (trianglesContaining G v) ≤ 4 := by
  /-
  ARISTOTLE HINT: The proof should construct a 4-edge cover by selecting one spoke
  per M-element. Use the helpers:
  - allSpokesFromM_covers: shows all triangles are covered by SOME spoke
  - triangle_covered_by_packing_spoke: gives the covering spoke for each triangle
  - cover_card_implies_covering_number_le: converts existence to bound

  Key step: Define a function f : M → Sym2 V that picks one spoke per element
  such that f(e) covers all triangles assigned to e. Then show |image f| ≤ 4.
  -/
  sorry

end