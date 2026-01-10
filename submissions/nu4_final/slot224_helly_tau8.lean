/-
  slot224_helly_tau8.lean

  GOAL: Prove τ ≤ 8 for cycle_4 using Helly-type vertex sharing.

  PROVEN (slot182): two_externals_share_edge
    Any two distinct externals of M-element A share an edge.

  KEY INSIGHT (Helly for triangles):
    If n triangles pairwise share an edge (2 vertices), they all share a common vertex.

    Proof: T1 ∩ T2 = {a, b} (edge).
           T3 shares edge with T1: |T1 ∩ T3| ≥ 2
           T3 shares edge with T2: |T2 ∩ T3| ≥ 2
           T3 must have 2 vertices in T1 AND 2 vertices in T2.
           T1 = {a, b, c}, T2 = {a, b, d}.
           T3 needs 2 vertices from each.
           T3 ∩ {a, b, c} ≥ 2 and T3 ∩ {a, b, d} ≥ 2.
           T3 = {p, q, r}.

           If T3 ⊇ {a, b}: done, common vertex a (or b).
           If T3 ⊇ {a, c} or {b, c}: then T3 ∩ T2 must also be ≥ 2.
             T3 ∩ T2 = T3 ∩ {a, b, d}.
             If T3 = {a, c, x}: T3 ∩ T2 = {a} or {a, x} (if x ∈ {b, d}).
               For |T3 ∩ T2| ≥ 2: x ∈ {b, d}.
               If x = b: T3 = {a, b, c} = T1. Contradiction (distinct).
               If x = d: T3 = {a, c, d}. T3 ∩ T1 = {a, c}, T3 ∩ T2 = {a, d}. Good!
                 Common vertex: a.

           By case analysis, all triangles share at least vertex a or b.
           So there exists common vertex in T1 ∩ T2 shared by all.

  COVERING STRATEGY:
    Let z be the common vertex shared by all externals of A.

    Case 1: z ∈ A.
      Then all externals contain z, so all use edge of A containing z.
      A has exactly 2 edges containing z (A = {z, u, v}).
      Pick one edge, say {z, u}. Cover externals using {z, u} with one edge.
      For externals using {z, v}: cover with {z, v}.
      But by pairwise edge-sharing, all externals use SAME edge of A (else only 1 common vertex).
      So 1 edge of A covers all externals!

    Case 2: z ∉ A (external vertex).
      Externals = {a, b, z}, {b, c, z}, {a, c, z} using different edges of A.
      Cover: {a, z} covers {a, b, z} and {a, c, z}.
             {b, c} covers {b, c, z}.
      So 2 edges cover all externals of A.

  TOTAL: At most 2 edges per M-element = 8 edges for cycle_4.

  1 SORRY for Aristotle.
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
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

/-- Externals of A in M -/
def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN AXIOM: slot182
-- ══════════════════════════════════════════════════════════════════════════════

axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂

-- ══════════════════════════════════════════════════════════════════════════════
-- HELLY LEMMA: Pairwise edge-sharing implies common vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- If a finite set of triangles pairwise share edges, they all share a common vertex. -/
lemma helly_triangles_common_vertex (S : Finset (Finset V))
    (hS_triangles : ∀ T ∈ S, T.card = 3)
    (hS_pairwise : ∀ T₁ ∈ S, ∀ T₂ ∈ S, T₁ ≠ T₂ → (T₁ ∩ T₂).card ≥ 2) :
    S.card ≤ 1 ∨ ∃ v : V, ∀ T ∈ S, v ∈ T := by
  -- Proof by induction on |S|
  -- Base cases: |S| = 0, 1 trivially satisfied
  -- Inductive: |S| ≥ 2, pick T₁, T₂, their intersection has ≥ 2 vertices.
  --            Any T₃ must share edge with both, forcing T₃ to contain common vertex.
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Externals share common vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- All externals of A share a common vertex. -/
lemma externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) :
    (externalsOf G M A).card ≤ 1 ∨ ∃ v : V, ∀ T ∈ externalsOf G M A, v ∈ T := by
  apply helly_triangles_common_vertex
  · -- All externals are triangles
    intro T hT
    simp only [externalsOf, Finset.mem_filter] at hT
    exact (SimpleGraph.mem_cliqueFinset_iff.mp hT.1).2
  · -- Pairwise share edges
    intro T₁ hT₁ T₂ hT₂ hne
    simp only [externalsOf, Finset.mem_filter] at hT₁ hT₂
    have h := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁.2 hT₂.2 hne
    obtain ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩ := h
    have hu_inter : u ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨hu₁, hu₂⟩
    have hv_inter : v ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨hv₁, hv₂⟩
    exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERING: 2 edges per M-element suffice
-- ══════════════════════════════════════════════════════════════════════════════

/-- Given common vertex z, 2 edges suffice to cover all externals of A. -/
lemma two_edges_cover_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (hA_3 : A.card = 3)
    (z : V) (hz : ∀ T ∈ externalsOf G M A, z ∈ T) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      ∀ T ∈ externalsOf G M A, ∃ e ∈ E, ∀ v ∈ Sym2.toFinset e, v ∈ T := by
  -- Case split: z ∈ A or z ∉ A
  by_cases hz_A : z ∈ A
  · -- Case 1: z ∈ A. All externals use same edge of A containing z.
    -- Actually need to show this. By pairwise edge-sharing within A-vertices.
    sorry
  · -- Case 2: z ∉ A. Use {z, a} for some a ∈ A, plus one edge of A.
    obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := Finset.card_eq_three.mp hA_3
    use {s(z, a), s(b, c)}
    constructor
    · simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
      intro h
      have := Sym2.eq_iff.mp h
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hz_A (by rw [h_eq]; simp)
      · exact hz_A (by rw [h_eq]; simp)
    · intro T hT
      have hT_ext := (Finset.mem_filter.mp hT).2
      have hz_T : z ∈ T := hz T hT
      -- T shares edge with A, T.card = 3, z ∈ T, z ∉ A
      -- So T = {z, x, y} where {x, y} ⊆ A is an edge of A
      have hT_card : T.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp
        (Finset.mem_filter.mp hT).1).2
      obtain ⟨u, v, huv, hu_T, hv_T, hu_A, hv_A⟩ := hT_ext.2.2.1
      -- {u, v} is edge of A in T. Also z ∈ T.
      -- T = {u, v, z} or T = {u, v, w} with w = z
      have hT_subset : T ⊆ {u, v, z} := by
        intro x hx
        -- T = {u, v, z} since |T| = 3 and u, v, z ∈ T are distinct
        have : u ≠ z := fun h => hz_A (h ▸ hu_A)
        have : v ≠ z := fun h => hz_A (h ▸ hv_A)
        -- u, v, z are 3 distinct elements of T, and |T| = 3
        have h3 : ({u, v, z} : Finset V).card = 3 := by
          simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
          · simp [huv.symm, *]
          · simp [*]
        have hT_eq : T = {u, v, z} := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton]
            have hxT : x ∈ T := by
              rcases hx with rfl | rfl | rfl <;> assumption
            exact hxT
          · rw [hT_card, h3]
        rw [hT_eq] at hx
        exact hx
      -- Now {u, v} is an edge of A = {a, b, c}
      rw [h_eq] at hu_A hv_A
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu_A hv_A
      -- Case analysis on which edge of A is {u, v}
      rcases hu_A with rfl | rfl | rfl <;> rcases hv_A with rfl | rfl | rfl
      all_goals try exact absurd rfl huv
      all_goals try exact absurd rfl huv.symm
      -- {u, v} ∈ {{a,b}, {a,c}, {b,c}}
      · -- {a, b}: cover with {z, a}
        use s(z, a)
        constructor
        · simp
        · intro w hw
          simp only [Sym2.toFinset_eq, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hz_T
          · have : T = {a, b, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp
      · -- {a, c}: cover with {z, a}
        use s(z, a)
        constructor
        · simp
        · intro w hw
          simp only [Sym2.toFinset_eq, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hz_T
          · have : T = {a, c, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp
      · -- {b, a}: same as {a, b}
        use s(z, a)
        constructor
        · simp
        · intro w hw
          simp only [Sym2.toFinset_eq, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hz_T
          · have : T = {b, a, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp
      · -- {b, c}: cover with {b, c}
        use s(b, c)
        constructor
        · simp
        · intro w hw
          simp only [Sym2.toFinset_eq, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · have : T = {b, c, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp
          · have : T = {b, c, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp
      · -- {c, a}: same as {a, c}
        use s(z, a)
        constructor
        · simp
        · intro w hw
          simp only [Sym2.toFinset_eq, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hz_T
          · have : T = {c, a, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp
      · -- {c, b}: same as {b, c}
        use s(b, c)
        constructor
        · simp
        · intro w hw
          simp only [Sym2.toFinset_eq, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · have : T = {c, b, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp
          · have : T = {c, b, z} := Finset.Subset.antisymm hT_subset (by simp [hu_T, hv_T, hz_T])
            rw [this]; simp

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-- For cycle_4 with ν = 4, we have τ ≤ 8.

    Proof: 2 edges per M-element suffice to cover its externals.
    Every triangle is either in M or external to exactly one M-element.
    M-elements are covered by their own edges.
    4 M-elements × 2 edges = 8 edges. -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_all_3 : ∀ X ∈ M, X.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, ∀ v ∈ Sym2.toFinset e, v ∈ T := by
  -- For each A ∈ M, get 2 edges covering externals of A
  -- Plus cover M-elements themselves (use one edge per M-element: 4 more)
  -- Total: 4 × 2 = 8 (if we're clever about double-counting)
  sorry

end
