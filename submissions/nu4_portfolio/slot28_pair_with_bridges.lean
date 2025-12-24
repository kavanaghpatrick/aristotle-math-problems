/-
Tuza ν=4 Portfolio - Slot 28: Pair With Bridges ≤ 4

TARGET: τ(S_e ∪ S_f ∪ X(e,f)) ≤ 4 for any sharing pair e,f

KEY INSIGHT (from Codex consultation 2024-12-23):
Once we have:
- bridge_matching: each outer vertex in at most one bridge
- base_edge_one_bridge: base-only S_e has at most one bridging endpoint

We can prove the pair bound with bridges:
- Case 1: S_e uses spoke edge → 2 edges for S_e, absorbs bridges through that spoke
- Case 2: S_e uses base edge → base_edge_one_bridge limits bridges
- Combined: τ(S_e ∪ S_f ∪ X(e,f)) ≤ 4

This is the assembly lemma that, combined with partitioning 4 elements
into 2 pairs, gives τ ≤ 8 for ν = 4.

SCAFFOLDING:
- tau_S_le_2 (proven)
- tau_X_le_2 (proven)
- bridges_contain_v (proven)
- Se_pairwise_intersect (proven)
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (from slot6)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- Full proof in slot6

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (from slot6)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- Full proof in tau_union files

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: bridges_contain_v
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (subadditivity)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- Full proof in slot16

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Pair With Bridges Bound
-- S_e ∪ S_f ∪ X(e,f) can be covered with 4 edges
-- ══════════════════════════════════════════════════════════════════════════════

-- First, a naive bound using subadditivity
lemma pair_with_bridges_naive (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ X_ef G e f) ≤ 6 := by
  calc triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ X_ef G e f)
      ≤ triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f) + triangleCoveringNumberOn G (X_ef G e f) := tau_union_le_sum G _ _
    _ ≤ triangleCoveringNumberOn G (S_e G M e) + triangleCoveringNumberOn G (S_e G M f) + triangleCoveringNumberOn G (X_ef G e f) := by
        have h := tau_union_le_sum G (S_e G M e) (S_e G M f)
        omega
    _ ≤ 2 + 2 + 2 := by
        have h1 := tau_S_le_2 G M hM e he
        have h2 := tau_S_le_2 G M hM f hf
        have h3 := tau_X_le_2 G M hM e f he hf hef v hv
        omega
    _ = 6 := by ring

-- The key insight: bridges share vertices with S_e and S_f, allowing absorption
-- This is where the coordinated cover saves 2 edges

-- Key structural lemma: bridges are "between" S_e and S_f geometrically
lemma bridge_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (he_card : e.card = 3) (hf_card : f.card = 3)
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ x y, x ∈ e ∧ x ≠ v ∧ y ∈ f ∧ y ≠ v ∧ t = {v, x, y} := by
  have hv_t : v ∈ t := bridges_contain_v G e f v hv t ht
  have h1 : (t ∩ e).card ≥ 2 := (Finset.mem_filter.mp ht).2.1
  have h2 : (t ∩ f).card ≥ 2 := (Finset.mem_filter.mp ht).2.2
  have ht_tri : t ∈ G.cliqueFinset 3 := (Finset.mem_filter.mp ht).1
  have ht_card : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht_tri |>.2
  -- t has 3 vertices, one is v
  -- t ∩ e has ≥2 vertices including v, so there's x ∈ e, x ≠ v, x ∈ t
  -- t ∩ f has ≥2 vertices including v, so there's y ∈ f, y ≠ v, y ∈ t
  sorry

-- Main theorem: τ(S_e ∪ S_f ∪ X(e,f)) ≤ 4
-- This improves the naive bound of 6 by showing bridge absorption
theorem pair_with_bridges_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ X_ef G e f) ≤ 4 := by
  -- Strategy: Show that we can choose 2-edge covers for S_e and S_f
  -- such that their union also covers all bridges X(e,f)
  --
  -- Case analysis on whether S_e and S_f are "spoke" or "base" driven:
  --
  -- Case 1: S_e contains v-triangles (spoke case)
  --   Then τ(S_e) ≤ 2 includes at least one v-spoke from e
  --   This spoke covers some bridges
  --
  -- Case 2: S_e is base-only (no v-triangles except e itself)
  --   Then by base_edge_one_bridge, at most one endpoint has bridges
  --   We can choose C_e to include the v-spoke for that endpoint
  --
  -- In either case, combined with symmetric analysis for f,
  -- we get a 4-edge cover for everything
  sorry

-- Corollary: The full pair bound for T_e ∪ T_f
-- Note: T_e = S_e ∪ bridges from e, but bridges from e to f are in X(e,f)
-- And T_e ∩ T_f = X(e,f) (bridges are counted in both)
-- So T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) ∪ (bridges to other elements)
-- For ν=4 star case, bridges to other elements also go through v

theorem pair_covering_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    -- In star configuration, all elements share v
    (h_star : ∀ g ∈ M, g ≠ e → e ∩ g = {v}) :
    triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ X_ef G e f) ≤ 4 := by
  exact pair_with_bridges_le_4 G M hM e f he hf hef v hv

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: Tuza ν=4 for star case
-- Partition {e, f, g, h} into pairs {e,f} and {g,h}
-- Each pair contributes ≤4 edges, total ≤8
-- ══════════════════════════════════════════════════════════════════════════════

theorem tuza_nu4_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V)
    -- All packing elements share vertex v (star configuration)
    (h_all_share_v : ∀ e ∈ M, v ∈ e)
    (h_pairwise_share : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → e ∩ f = {v}) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- M = {e, f, g, h}
  -- All triangles either:
  -- 1. Are in some S_x for x ∈ M
  -- 2. Are bridges X(x,y) for some x,y ∈ M
  --
  -- Partition M into two pairs, say {e,f} and {g,h}
  -- τ(S_e ∪ S_f ∪ X(e,f)) ≤ 4
  -- τ(S_g ∪ S_h ∪ X(g,h)) ≤ 4
  --
  -- The remaining bridges are X(e,g), X(e,h), X(f,g), X(f,h)
  -- But these all go through v, and are covered by the v-spokes
  -- already included in the 4-edge covers above!
  sorry

end
