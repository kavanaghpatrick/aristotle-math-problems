/-
  slot518_Se_prime_from_Se.lean

  BUILD two_edges_cover_Se_prime FROM PROVEN two_edges_cover_Se

  Strategy:
  1. S_e ⊆ S_e' (externals exclusive to e are trivially min-index)
  2. Bridges in S_e' share an edge with e (by definition)
  3. The 2 edges covering S_e also cover bridges (they share edges with e)

  PROVEN BUILDING BLOCKS (from slot512):
  - two_edges_cover_Se: 2 edges from e cover all S_e
  - external_uses_one_edge_type: each external uses exactly one edge-type

  TIER: 2 (subset + bridge handling)
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

/-- S_e: triangles sharing edge with e, exclusive to e -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

/-- Which M-elements does T share an edge with? -/
def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

/-- S_e': triangles assigned to e by min-index rule -/
def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

/-- A bridge is a triangle sharing edges with multiple M-elements -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ∉ M ∧ 2 ≤ (sharesEdgeWith M T).card

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 1: S_e ⊆ S_e' (externals exclusive to e are trivially assigned to e)
-- ══════════════════════════════════════════════════════════════════════════════

lemma S_e_subset_S_e' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M) (idx : Finset V → ℕ) :
    S_e G M e ⊆ S_e' G M e idx := by
  intro T hT
  simp only [S_e, S_e', mem_filter, sharesEdgeWith] at hT ⊢
  refine ⟨hT.1, hT.2.1, hT.2.2.1, ?_⟩
  -- T only shares edge with e, so no f with idx f < idx e shares edge with T
  ext f
  simp only [mem_filter, mem_empty_iff_false, iff_false, not_and]
  intro hfM hf_inter _
  -- f shares edge with T, so f = e (by exclusivity in S_e)
  by_contra hfe
  have := hT.2.2.2 f hfM hfe
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 2: Bridges in S_e' share an edge with e
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_in_Se'_shares_edge_with_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (idx : Finset V → ℕ)
    (T : Finset V) (hT : T ∈ S_e' G M e idx) :
    2 ≤ (T ∩ e).card := by
  simp only [S_e', mem_filter] at hT
  exact hT.2.2.1

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 3: The shared edge covers the triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_edge_in_both_sym2 (T e : Finset V) (hT3 : T.card = 3) (he3 : e.card = 3)
    (h_inter : 2 ≤ (T ∩ e).card) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  -- T ∩ e has ≥2 elements, so there exist a, b ∈ T ∩ e with a ≠ b
  have hne : (T ∩ e).Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨a, ha⟩ := hne
  simp only [mem_inter] at ha
  have hcard2 : 2 ≤ (T ∩ e).card := h_inter
  have : 1 < (T ∩ e).card := by omega
  rw [one_lt_card] at this
  obtain ⟨x, hx, y, hy, hxy⟩ := this
  simp only [mem_inter] at hx hy
  use Sym2.mk x y
  constructor
  · exact Finset.mk_mem_sym2_iff.mpr ⟨hx.2, hy.2⟩
  · exact Finset.mk_mem_sym2_iff.mpr ⟨hx.1, hy.1⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 4: At most 3 edge-types, so at most 2 are populated (6-packing constraint)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edge-types used by S_e' -/
def usedEdgeTypes (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) 
    (e : Finset V) (idx : Finset V → ℕ) : Finset (Finset V) :=
  (S_e' G M e idx).image (fun T => T ∩ e)

/-- 6-packing constraint: if all 3 edge-types populated, we get a 6-packing -/
lemma at_most_two_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) (idx : Finset V → ℕ) :
    (usedEdgeTypes G M e idx).card ≤ 2 := by
  -- If 3 edge-types used, we get triangles T_ab, T_bc, T_ac all in S_e'
  -- Together with e and 3 other M-elements, this would give 6-packing
  -- Contradicts ν = 4
  by_contra h
  push_neg at h
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. S_e' = S_e ∪ (bridges assigned to e)
2. S_e is covered by 2 edges (proven in slot512)
3. Bridges share an edge with e, so covered by same 2 edges
4. At most 2 edge-types are populated (6-packing constraint)
5. Therefore 2 edges (one per populated type) cover all of S_e'
-/
theorem two_edges_cover_Se_prime (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3)
    (idx : Finset V → ℕ) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- Get the 2 edges covering S_e (from slot512 proof pattern)
  -- Every T in S_e' shares edge with e, and at most 2 edge-types are used
  -- So 2 edges suffice
  have h_types := at_most_two_edge_types G M hM hNu4 e he he3 idx
  -- Select one edge per used type
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: τ ≤ 8 from 2 edges per element
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_assembly (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    -- S_e' partitions non-M triangles
    (h_partition : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃! e, e ∈ M ∧ T ∈ S_e' G M e idx)
    -- Each element has card 3
    (h_cards : ∀ e ∈ M, e.card = 3)
    -- 2 edges cover each S_e'
    (h_cover : ∀ e ∈ M, ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ C ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ C, edge ∈ T.sym2) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ edge ∈ Cover, edge ∈ T.sym2 := by
  -- Collect 2 edges from each of 4 elements = 8 edges
  sorry

end
