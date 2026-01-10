/-
Tuza ν=4: Common Spoke Vertex Lemma (Slot 201)

KEY LEMMA: If externals of M-element A exist, they share a common A-vertex.

STRATEGY (Pigeonhole):
  - A has 3 vertices {a, b, c}
  - Each external T uses 2 vertices of A (shares an edge with A)
  - If T₁ uses {a,b} and T₂ uses {c,d} with {a,b} ∩ {c,d} = ∅, then T₁ ∩ T₂ ⊆ {external vertices}
  - But by slot182 (two_externals_share_edge), T₁ and T₂ share an edge
  - A 3-vertex set can't have two disjoint 2-subsets, so externals overlap on at least one A-vertex

PROVEN INFRASTRUCTURE:
  - slot139: triangle_shares_edge_with_packing (maximality)
  - slot182: two_externals_share_edge (5-packing contradiction)
  - slot200: fan_apex_cover setup

FROM FALSE_LEMMAS.md:
  - Pattern 6: External triangles at DIFFERENT M-elements don't necessarily share vertex
  - BUT: Externals of the SAME M-element DO share common vertex (fan apex)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven files)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- Two vertex sets share an edge: ∃ distinct u,v in both sets -/
def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

/-- External triangle: in G's cliques, not in M, shares edge with A only -/
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edges shared between two 3-sets have common vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- If two 3-sets each share an edge with a third 3-set, and the first two also share
    an edge with each other, then there is a vertex common to all three -/
lemma triangle_edges_share_vertex (A T₁ T₂ : Finset V)
    (hA : A.card = 3) (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3)
    (h_T1_A : sharesEdgeWith T₁ A)
    (h_T2_A : sharesEdgeWith T₂ A)
    (h_T1_T2 : sharesEdgeWith T₁ T₂) :
    ∃ v : V, v ∈ A ∧ v ∈ T₁ ∧ v ∈ T₂ := by
  -- T₁ ∩ A has ≥ 2 vertices (from h_T1_A)
  -- T₂ ∩ A has ≥ 2 vertices (from h_T2_A)
  -- A has 3 vertices
  -- By pigeonhole: (T₁ ∩ A) ∩ (T₂ ∩ A) ≠ ∅
  obtain ⟨u₁, v₁, huv₁, hu₁_T1, hv₁_T1, hu₁_A, hv₁_A⟩ := h_T1_A
  obtain ⟨u₂, v₂, huv₂, hu₂_T2, hv₂_T2, hu₂_A, hv₂_A⟩ := h_T2_A
  -- The edge in A from T₁ is {u₁, v₁}
  -- The edge in A from T₂ is {u₂, v₂}
  -- A has only 3 vertices, so these two 2-subsets of A must intersect
  have h_inter_nonempty : ({u₁, v₁} ∩ {u₂, v₂} : Finset V).Nonempty := by
    by_contra h_empty
    push_neg at h_empty
    simp only [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_not_mem,
               Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at h_empty
    -- All 4 of u₁, v₁, u₂, v₂ are distinct and in A (3 elements) - contradiction
    have h4 : ({u₁, v₁, u₂, v₂} : Finset V).card ≥ 4 := by
      have hu1_ne_u2 : u₁ ≠ u₂ := by
        intro heq; exact h_empty u₁ (Or.inl rfl) (by rw [heq]; left; rfl)
      have hu1_ne_v2 : u₁ ≠ v₂ := by
        intro heq; exact h_empty u₁ (Or.inl rfl) (by rw [heq]; right; rfl)
      have hv1_ne_u2 : v₁ ≠ u₂ := by
        intro heq; exact h_empty v₁ (Or.inr rfl) (by rw [heq]; left; rfl)
      have hv1_ne_v2 : v₁ ≠ v₂ := by
        intro heq; exact h_empty v₁ (Or.inr rfl) (by rw [heq]; right; rfl)
      simp only [Finset.card_insert_of_not_mem, Finset.card_singleton, Finset.mem_insert,
                 Finset.mem_singleton]
      sorry  -- Aristotle: use distinctness to show card = 4
    have h_sub : ({u₁, v₁, u₂, v₂} : Finset V) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have h_le := Finset.card_le_card h_sub
    omega
  obtain ⟨v, hv⟩ := h_inter_nonempty
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv
  use v
  constructor
  · -- v ∈ A: v is in {u₁, v₁} ⊆ A or {u₂, v₂} ⊆ A
    rcases hv.1 with rfl | rfl <;> assumption
  constructor
  · -- v ∈ T₁
    rcases hv.1 with rfl | rfl <;> assumption
  · -- v ∈ T₂
    rcases hv.2 with rfl | rfl <;> assumption

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMA: All externals of A share a common A-vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN (slot182): Two externals of same M-element share an edge -/
axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂

/-- Main lemma: All externals of A contain a common vertex from A -/
theorem common_spoke_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (h_nonempty : (externalsOf G M A).Nonempty) :
    ∃ v : V, v ∈ A ∧ ∀ T ∈ externalsOf G M A, v ∈ T := by
  -- Get an arbitrary external T₀
  obtain ⟨T₀, hT₀_mem⟩ := h_nonempty
  have hT₀ : isExternalOf G M A T₀ := by
    simp only [externalsOf, Finset.mem_filter] at hT₀_mem
    exact hT₀_mem.2
  -- Case: only one external
  by_cases h_single : (externalsOf G M A).card ≤ 1
  · -- T₀ is the only external; any vertex of T₀ ∩ A works
    obtain ⟨u, v, huv, hu_T0, hv_T0, hu_A, hv_A⟩ := hT₀.2.2.1
    use u
    constructor
    · exact hu_A
    · intro T hT
      have : T = T₀ := by
        have h1 : (externalsOf G M A) = {T₀} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          exact ⟨hT₀_mem, fun t ht => by
            have hcard := Finset.card_le_one.mp h_single
            exact hcard hT₀_mem ht⟩
        simp only [h1, Finset.mem_singleton] at hT
        exact hT
      rw [this]
      exact hu_T0
  · -- Multiple externals: use pigeonhole via edge-sharing
    push_neg at h_single
    -- A has card 3
    have hA_card : A.card = 3 := by
      have : A ∈ G.cliqueFinset 3 := hM.1.1 hA
      exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
    have hT₀_card : T₀.card = 3 := by
      have : T₀ ∈ G.cliqueFinset 3 := hT₀.1
      exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
    -- For any other external T, T and T₀ share an edge (slot182)
    -- By triangle_edges_share_vertex, there's a common A-vertex
    -- Key: T₀ ∩ A has ≥ 2 vertices, and for any T, T ∩ A has ≥ 2 vertices
    -- and T ∩ T₀ has ≥ 2 vertices (they share edge)
    -- By pigeonhole on A's 3 vertices: some vertex is in ALL externals

    -- Strategy: intersection of all (T ∩ A) over T ∈ externals is nonempty
    -- because each pair shares an edge and by pigeonhole on A's 3 vertices

    -- We'll show: ∃ v ∈ A, ∀ T ∈ externals, v ∈ T
    -- By inducting on the number of externals:

    -- Base: T₀ shares edge with A, so (T₀ ∩ A).card ≥ 2
    -- Inductive: Given v ∈ A ∩ T₀ ∩ ... ∩ Tₖ, show v ∈ T_{k+1}
    -- The key is: T_{k+1} shares edge with T₀ (slot182)
    -- and both share edge with A. By triangle_edges_share_vertex,
    -- there's a common vertex in A ∩ T₀ ∩ T_{k+1}

    -- Actually, simpler: For ANY T, we have A, T₀, T all share edges pairwise
    -- So there's v ∈ A ∩ T₀ ∩ T for each T
    -- The question is: is this v the SAME for all T?

    -- Use the following: (T₀ ∩ A) has ≥ 2 elements
    -- For each T ≠ T₀, the common vertex guaranteed by triangle_edges_share_vertex
    -- is in (T₀ ∩ A) because the pigeonhole forces it

    -- Let's find the common vertex directly:
    -- Take the intersection I = ⋂ {T ∩ A : T ∈ externals}
    -- Claim: I ≠ ∅

    -- Proof: By strong induction on |externals|.
    -- Each external T shares edge with A (so T ∩ A ≥ 2)
    -- Any two externals share edge (so T₁ ∩ T₂ ≥ 2)
    -- A has 3 vertices

    -- For 2 externals T₁, T₂:
    --   T₁ ∩ A ≥ 2, T₂ ∩ A ≥ 2, T₁ ∩ T₂ ≥ 2
    --   By triangle_edges_share_vertex, A ∩ T₁ ∩ T₂ ≠ ∅

    -- For n externals:
    --   Each pair shares an edge, all share edge with A
    --   The intersection of all (T ∩ A) is nonempty

    sorry  -- Aristotle: complete the intersection argument

/-- Corollary: The fan apex exists and all externals contain it -/
theorem fan_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ v : V, (v ∈ A ∧ ∀ T ∈ externalsOf G M A, v ∈ T) ∨ (externalsOf G M A = ∅) := by
  by_cases h : (externalsOf G M A).Nonempty
  · obtain ⟨v, hv_A, hv_all⟩ := common_spoke_vertex G M hM hM_card hν A hA h
    exact ⟨v, Or.inl ⟨hv_A, hv_all⟩⟩
  · push_neg at h
    simp only [Finset.not_nonempty_iff_eq_empty] at h
    -- Any vertex of A works
    have hA_card : A.card = 3 := by
      have : A ∈ G.cliqueFinset 3 := hM.1.1 hA
      exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : A.card > 0)
    exact ⟨a, Or.inr h⟩

end
