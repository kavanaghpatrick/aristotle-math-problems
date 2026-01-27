/-
  slot489_local_cover_from_six_packing.lean

  DEBATE CONSENSUS: Connect slot412 (6-packing constraint) to τ ≤ 8

  KEY INSIGHT (from Grok-4 + Gemini):
  - slot412 proves: not_all_three_edge_types (if all 3 edges of m have externals → 6-packing)
  - Therefore: for each m ∈ M, at most 2 edge-types have external triangles
  - Therefore: 4 triangles × 2 edges = 8 edges suffice

  PROOF STRATEGY:
  1. For each m ∈ M, apply 6-packing constraint to get ≤2 active edge-types
  2. Select those 2 edges from each m
  3. Prove union covers all triangles via every_tri_shares_edge_with_packing

  TIER: 2 (assembly of proven components)
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

/-- Triangles sharing an edge with m (intersection ≥ 2 vertices) -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (m : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ m).card ≥ 2)

/-- External triangles for m: share edge with m but not with other M-elements -/
def externalsFor (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (m : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G m).filter (fun t => t ∉ M ∧ ∀ m' ∈ M, m' ≠ m → (t ∩ m').card ≤ 1)

/-- The 3 edges of a triangle m = {a, b, c} -/
def triangleEdges (m : Finset V) (hm : m.card = 3) : Finset (Sym2 V) :=
  m.sym2.filter (fun e => ∃ x y, x ∈ m ∧ y ∈ m ∧ x ≠ y ∧ e = s(x, y))

/-- External triangles for a specific edge e of m -/
def externalsForEdge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (m : Finset V) (e : Sym2 V) : Finset (Finset V) :=
  (externalsFor G M m).filter (fun t => e ∈ t.sym2)

/-- An edge-type of m "has externals" if some external triangle contains it -/
def edgeHasExternals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (m : Finset V) (e : Sym2 V) : Prop :=
  (externalsForEdge G M m e).Nonempty

-- ══════════════════════════════════════════════════════════════════════════════
-- 6-PACKING CONSTRAINT (from slot412)
-- ══════════════════════════════════════════════════════════════════════════════

/--
AXIOM from slot412: If all 3 edges of m have external triangles,
we can construct a 6-packing, contradicting ν = 4.

Therefore, at most 2 of the 3 edges have externals.
-/
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (m : Finset V) (hm : m ∈ M) (hm_tri : m ∈ G.cliqueFinset 3)
    (e1 e2 e3 : Sym2 V) (he_distinct : e1 ≠ e2 ∧ e1 ≠ e3 ∧ e2 ≠ e3)
    (he_edges : e1 ∈ m.sym2 ∧ e2 ∈ m.sym2 ∧ e3 ∈ m.sym2) :
    ¬(edgeHasExternals G M m e1 ∧ edgeHasExternals G M m e2 ∧ edgeHasExternals G M m e3)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: At most 2 edges per m have externals
-- ══════════════════════════════════════════════════════════════════════════════

/--
From 6-packing constraint: at most 2 edges of m have external triangles.
-/
lemma at_most_two_edges_have_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (m : Finset V) (hm : m ∈ M) :
    ∃ E : Finset (Sym2 V), E ⊆ m.sym2 ∧ E.card ≤ 2 ∧
      ∀ t ∈ externalsFor G M m, ∃ e ∈ E, e ∈ t.sym2 := by
  -- By 6-packing, not all 3 edges have externals
  -- So we can pick the ≤2 edges that DO have externals
  -- Those 2 edges cover all external triangles for m
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE HANDLING (from slot483, slot485)
-- ══════════════════════════════════════════════════════════════════════════════

/--
AXIOM from slot488: Every triangle shares edge with some packing element (by ν=4 maximality)
-/
axiom every_tri_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2

/--
A triangle is either:
1. In M (packing element) → covered by its own edges
2. External to exactly one m → covered by at_most_two_edges
3. Bridge (shares with 2+ elements) → covered by spoke edges (slot483)
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/--
MAIN: τ ≤ 8 for ν = 4.

For each m ∈ M, select ≤2 edges covering its externals (by 6-packing constraint).
Total: 4 × 2 = 8 edges.
These 8 edges cover all triangles.
-/
theorem tau_le_8_from_six_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4) :
    ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ E.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  -- For each m ∈ M, get the ≤2 edge cover
  have h_local : ∀ m ∈ M, ∃ E : Finset (Sym2 V), E ⊆ m.sym2 ∧ E.card ≤ 2 ∧
      ∀ t ∈ externalsFor G M m, ∃ e ∈ E, e ∈ t.sym2 :=
    fun m hm => at_most_two_edges_have_externals G M hM hM_card hNu4 m hm
  -- Choose the local covers
  choose f hf using h_local
  -- Union of local covers
  let E := M.biUnion f
  use E
  refine ⟨?_, ?_, ?_⟩
  · -- E ⊆ G.edgeFinset
    intro e he
    simp only [mem_biUnion] at he
    obtain ⟨m, hm, he'⟩ := he
    -- e ∈ m.sym2 and m is a triangle in G
    have hm_sub := (hf m hm).1 he'
    have hm_tri : m ∈ G.cliqueFinset 3 := hM.1 hm
    -- Need: e ∈ G.edgeFinset
    -- This follows from: e ∈ m.sym2 and m is a clique
    sorry
  · -- |E| ≤ 8
    calc E.card ≤ ∑ m ∈ M, (f m).card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, 2 := Finset.sum_le_sum (fun m hm => (hf m hm).2.1)
      _ = M.card * 2 := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 8 := by rw [hM_card]; norm_num
  · -- E covers all triangles
    intro t ht
    -- t shares edge with some m ∈ M
    obtain ⟨m, hm, hshare⟩ := every_tri_shares_edge G M hM hM_card hNu4 t ht
    -- Case: t ∈ M (packing element)
    by_cases ht_in_M : t ∈ M
    · -- t is in M, so t = m for some m
      -- Any edge of t covers t
      -- Use any edge from f(t)
      sorry
    · -- t ∉ M, so t is external or bridge
      -- Check if t is external to m (disjoint from other M-elements)
      by_cases h_ext : t ∈ externalsFor G M m
      · -- t is external to m → covered by f(m)
        obtain ⟨e, he, hcover⟩ := (hf m hm).2.2 t h_ext
        exact ⟨e, mem_biUnion.mpr ⟨m, hm, he⟩, hcover⟩
      · -- t is a bridge (shares with another m')
        -- By slot483: bridge has spoke edge in some m's cover
        -- The spoke edge covers t
        sorry

end
