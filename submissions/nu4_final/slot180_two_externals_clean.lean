/-
Tuza ν=4 Strategy - Slot 180: Two Externals Share Edge (Clean Version)

MULTI-AGENT REVIEW (Jan 2, 2026):
  Codex found that slot179's proof of two_externals_share_edge is BROKEN.
  This is a clean resubmission with proper proof structure.

KEY THEOREM: two_externals_share_edge
  If T₁, T₂ are distinct externals of M-element A, they must share an edge.

PROOF STRATEGY:
  1. Assume T₁, T₂ don't share an edge (edge-disjoint)
  2. Construct M' = {T₁, T₂} ∪ (M \ {A}) = {T₁, T₂, B, C, D}
  3. Show M' is a valid 5-packing:
     - T₁ ∩ T₂ ≤ 1 vertex (edge-disjoint → at most shared vertex)
     - T₁ ∩ B ≤ 1 vertex (external of A doesn't share edge with B)
     - T₂ ∩ B ≤ 1 vertex (same reason)
     - B ∩ C ≤ 1 vertex (M is packing)
     - etc. for all pairs
  4. |M'| = 5 contradicts ν = 4
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ e, e ∈ t.sym2 ∧ e ∈ S.sym2

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Edge-sharing implies 2-vertex intersection
-- ══════════════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨e, he_t, he_m⟩ := h_share
  rw [Finset.mem_sym2_iff] at he_t he_m
  obtain ⟨u, v, huv, hu_t, hv_t, rfl⟩ := he_t
  obtain ⟨u', v', _, hu'_m, hv'_m, heq⟩ := he_m
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu'_m⟩
    have : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv'_m⟩
    exact Finset.one_lt_card.mpr ⟨u, ‹u ∈ t ∩ m›, v, ‹v ∈ t ∩ m›, huv⟩
  · have : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hv'_m⟩
    have : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hu'_m⟩
    exact Finset.one_lt_card.mpr ⟨u, ‹u ∈ t ∩ m›, v, ‹v ∈ t ∩ m›, huv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Not sharing edge implies ≤1 vertex intersection
-- ══════════════════════════════════════════════════════════════════════════════

lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : (t ∩ m).card ≥ 2 := h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  have hu_t : u ∈ t := (Finset.mem_inter.mp hu).1
  have hu_m : u ∈ m := (Finset.mem_inter.mp hu).2
  have hv_t : v ∈ t := (Finset.mem_inter.mp hv).1
  have hv_m : v ∈ m := (Finset.mem_inter.mp hv).2
  apply h_not_share
  use ⟦(u, v)⟧
  constructor
  · rw [Finset.mem_sym2_iff]
    exact ⟨u, v, huv, hu_t, hv_t, rfl⟩
  · rw [Finset.mem_sym2_iff]
    exact ⟨u, v, huv, hu_m, hv_m, rfl⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: External of A intersects other M-elements in ≤1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  have ht_3 : t.card = 3 := by
    have : t ∈ G.cliqueFinset 3 := ht_ext.1
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.1
  have hB_3 : B.card = 3 := by
    have : B ∈ G.cliqueFinset 3 := hM.1.1 hB
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.1
  have h_not_share : ¬sharesEdgeWith t B := ht_ext.2.2.2 B hB hAB
  exact not_share_implies_one_vertex t B ht_3 hB_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY THEOREM: Two externals of same M-element share an edge
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁, T₂ are distinct externals of same M-element A, and they're edge-disjoint,
    then {T₁, T₂} ∪ (M \ {A}) is a 5-packing, contradicting ν = 4. -/
theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_edge_disj : ∀ e, e ∈ T₁.sym2 → e ∈ T₂.sym2 → False) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M' := by
  -- Construct M' = {T₁, T₂} ∪ (M \ {A})
  let M_minus_A := M.erase A
  let M' := {T₁, T₂} ∪ M_minus_A
  use M'
  constructor
  -- Part 1: |M'| = 5
  · -- T₁, T₂ are externals (not in M), M_minus_A has 3 elements
    -- Need to show: T₁ ∉ M_minus_A, T₂ ∉ M_minus_A, T₁ ≠ T₂
    -- Then |M'| = |{T₁, T₂}| + |M_minus_A| = 2 + 3 = 5
    sorry
  -- Part 2: M' is a triangle packing
  · constructor
    -- All elements are triangles
    · intro t ht
      sorry
    -- Pairwise intersection ≤ 1
    · intro t₁ ht₁ t₂ ht₂ h_ne
      -- Cases: both in {T₁, T₂}, both in M_minus_A, or mixed
      sorry

/-- KEY THEOREM: Two externals of the same M-element must share an edge.
    Otherwise we could form a 5-packing, contradicting ν = 4. -/
theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ e, e ∈ T₁.sym2 ∧ e ∈ T₂.sym2 := by
  by_contra h_no_common
  push_neg at h_no_common
  -- If no common edge, then T₁, T₂ are edge-disjoint
  have h_edge_disj : ∀ e, e ∈ T₁.sym2 → e ∈ T₂.sym2 → False := by
    intro e he₁ he₂
    exact h_no_common e he₁ he₂
  -- This allows 5-packing {T₁, T₂, B, C, D} where {B, C, D} = M \ {A}
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_edge_disj
  -- But ν(G) = 4 means no packing has size > 4
  -- We have a 5-packing M', contradiction
  -- The key insight: isMaxPacking means ν(G) ≤ 4
  -- But if M' is a valid 5-packing with M' ⊆ cliqueFinset 3, then ν(G) ≥ 5
  sorry

end
