/-
  slot519_bridge_aware_cover.lean

  BRIDGE-AWARE 2-EDGE COVER

  Key insight from slot518 negation:
  - S_e uses ≤2 edge-types (6-packing constraint) ✓
  - But S_e' includes bridges that may use the 3rd edge-type ✗

  NEW APPROACH:
  Bridges share edges with MULTIPLE M-elements. We can choose which
  element's edges cover each bridge. Use Hall's theorem / greedy assignment.

  STRATEGY:
  1. For S_e (exclusive externals): 2 edges suffice (proven in slot512)
  2. For bridges: each shares edge with ≥2 M-elements
  3. Assign each bridge to an M-element that can cover it with existing 2 edges
  4. If not possible, show at most 1 extra edge needed per element

  TIER: 2 (combinatorial assignment)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ∉ M ∧ 2 ≤ (sharesEdgeWith M T).card

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: Bridge shares edge with ≥2 M-elements
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_shares_with_multiple (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (hT : isBridge G M T) :
    2 ≤ (sharesEdgeWith M T).card := hT.2.2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: Each M-element has ≤3 edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_has_three_edges (e : Finset V) (he : e.card = 3) :
    e.sym2.card = 3 := by
  -- A 3-element set has exactly 3 pairs
  have : e.sym2 = e.sym2 := rfl
  simp only [card_sym2, he]
  norm_num

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: External uses exactly one edge of e
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_inter_is_edge (T e : Finset V) (hT : T.card = 3) (he : e.card = 3)
    (hTe : T ≠ e) (h_inter : 2 ≤ (T ∩ e).card) :
    (T ∩ e).card = 2 := by
  -- T ∩ e has ≥2 elements, but if it had 3, then T = e (contradiction)
  have h_le : (T ∩ e).card ≤ 3 := by
    calc (T ∩ e).card ≤ T.card := card_inter_le_left T e
      _ = 3 := hT
  interval_cases (T ∩ e).card
  · omega
  · omega
  · rfl
  · -- card = 3 means T ∩ e = T (since |T| = 3)
    have hTeq : T ∩ e = T := by
      apply eq_of_subset_of_card_le (inter_subset_left)
      simp [hT]
    -- Also T ∩ e ⊆ e, so T ⊆ e
    have hTsub : T ⊆ e := by
      rw [← hTeq]
      exact inter_subset_right
    -- |T| = |e| = 3 and T ⊆ e means T = e
    have : T = e := eq_of_subset_of_card_le hTsub (by simp [hT, he])
    exact (hTe this).elim

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 4: Shared edge covers the external
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_edge_covers (T e : Finset V) (hT : T.card = 3) (he : e.card = 3)
    (h_inter : 2 ≤ (T ∩ e).card) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  have h2 : (T ∩ e).card ≥ 2 := h_inter
  rw [Finset.two_le_card] at h2
  obtain ⟨a, ha, b, hb, hab⟩ := h2
  simp only [mem_inter] at ha hb
  use Sym2.mk a b
  constructor
  · exact mk_mem_sym2_iff.mpr ⟨ha.2, hb.2⟩
  · exact mk_mem_sym2_iff.mpr ⟨ha.1, hb.1⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 5: two_edges_cover_Se (from slot512, restated)
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- 6-packing constraint: at most 2 edge-types populated in S_e
  -- Select one edge per populated type
  sorry -- Proven in slot512

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 6: Bridges assigned to e are few
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridges assigned to e via min-index -/
def bridgesOf (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) 
    (e : Finset V) (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    isBridge G M T ∧ 
    e ∈ sharesEdgeWith M T ∧
    ∀ f ∈ sharesEdgeWith M T, idx e ≤ idx f)

/-- Each bridge shares an edge with e, so one of e's 3 edges covers it -/
lemma bridge_covered_by_some_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (he3 : e.card = 3)
    (hT_tri : T ∈ G.cliqueFinset 3) (hT_shares : e ∈ sharesEdgeWith M T) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  simp only [sharesEdgeWith, mem_filter] at hT_shares
  have hT3 : T.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
    exact hT_tri.1
  exact shared_edge_covers T e hT3 he3 hT_shares.2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 7: At most 2 bridges per M-element (6-packing constraint)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If e has ≥3 bridges assigned, each using a different edge-type of e,
then together with e and the other ends of these bridges, we get ≥6 
edge-disjoint triangles, contradicting ν = 4.
-/
lemma at_most_two_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3)
    (idx : Finset V → ℕ) :
    (bridgesOf G M e idx).card ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e ∪ bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-- S_e' = S_e ∪ bridgesOf e -/
def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

/-
PROOF SKETCH for two_edges_cover_Se_prime:
1. S_e uses ≤2 edge-types → covered by 2 edges E_Se
2. bridgesOf e has ≤2 elements (at_most_two_bridges)
3. Each bridge uses 1 edge-type of e
4. Case analysis:
   a) Bridges use edge-types already in E_Se → same 2 edges work
   b) Bridges use new edge-type → but then ≤1 bridge (since ≤2 total)
      and we can swap one edge in E_Se
5. Always achievable with 2 edges
-/
theorem two_edges_cover_Se_prime (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3)
    (idx : Finset V → ℕ) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- Get 2 edges covering S_e
  obtain ⟨E_Se, hE_card, hE_sub, hE_cov⟩ := two_edges_cover_Se G M hM hNu4 e he he3
  -- Bridges are ≤2 and each covered by some edge of e
  have h_bridges := at_most_two_bridges G M hM hNu4 e he he3 idx
  -- Need to show E_Se (or a modification) covers bridges too
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY (proven in slot518)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4)
    (hMax : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, 2 ≤ (T ∩ e).card)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (h_cards : ∀ e ∈ M, e.card = 3) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ edge ∈ Cover, edge ∈ T.sym2 := by
  -- Use tau_le_8_assembly with two_edges_cover_Se_prime
  sorry

end
