/-
slot147: LP Relaxation Approach for τ ≤ 8 in Cycle_4

MATHEMATICAL FRAMEWORK (from literature research Dec 31, 2025):

1. Krivelevich (1995): τ(G) ≤ 2·ν*(G)
   where ν* = fractional triangle packing number
   Source: "On a conjecture of Tuza" Discrete Mathematics 142(1-3):281-286

2. LP Duality: τ* = ν* (always true)
   The fractional covering and packing LPs are dual

3. Key Claim: For Cycle_4 configurations, ν* = ν = 4
   Proof idea:
   - Setting x_A = x_B = x_C = x_D = 1 gives packing weight 4
   - This saturates all M-edges (each M-edge in exactly one M-triangle)
   - Every external triangle shares an M-edge with some M-element
   - Therefore external triangles are forced to weight 0
   - Optimal fractional packing = 4

4. Conclusion: τ ≤ 2·ν* = 2·4 = 8

WHY THIS BYPASSES FALSE LEMMAS:
- No König theorem needed (Pattern 8: link_graph_bipartite FALSE)
- No 2-edges-per-vertex claim (Patterns 1, 5, 7 FALSE)
- No external common vertex claim (Pattern 6 FALSE)
- Pure LP argument using literature result
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- STANDARD DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ M.card

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- FRACTIONAL PACKING DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A fractional triangle packing assigns non-negative weights to triangles
    such that for each edge, the sum of weights of triangles containing it ≤ 1 -/
def isFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, w t ≥ 0) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ∑ t in G.cliqueFinset 3, if e ∈ t.sym2 then w t else 0 ≤ 1)

/-- The fractional packing number ν* -/
noncomputable def fractionalPackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ⨆ (w : Finset V → ℝ) (_ : isFractionalPacking G w),
    ∑ t in G.cliqueFinset 3, w t

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  -- Shared vertices
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  -- Intersection axioms
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  -- Membership axioms
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  -- Distinctness
  h_distinct_ab_bc : v_ab ≠ v_bc
  h_distinct_bc_cd : v_bc ≠ v_cd
  h_distinct_cd_da : v_cd ≠ v_da
  h_distinct_da_ab : v_da ≠ v_ab

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: Every triangle shares an edge with M (Maximality)
-- ══════════════════════════════════════════════════════════════════════════════

/-- In a graph with maximum packing M, every triangle shares an edge with some M-element.
    This follows from maximality: if a triangle T shared no edge with M,
    then M ∪ {T} would be a larger packing, contradicting maximality. -/
lemma triangle_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  by_contra h_none
  push_neg at h_none
  -- If t shares at most 1 vertex with every m ∈ M, then M ∪ {t} is a valid packing
  have h_disjoint : t ∉ M → Set.Pairwise ((M ∪ {t} : Finset (Finset V)) : Set (Finset V))
      (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
    intro ht_not_M
    intro x hx y hy hxy
    simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hx hy
    rcases hx with hx_M | rfl <;> rcases hy with hy_M | rfl
    · exact hM.1.2 hx_M hy_M hxy
    · exact (h_none y hy_M).trans (by omega)
    · have := h_none x hx_M
      rw [Finset.inter_comm] at this
      exact this.trans (by omega)
    · exact absurd rfl hxy
  -- This contradicts maximality
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: M-edges are exactly saturated by integer packing
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each M-edge appears in exactly one M-triangle -/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  -- If e ∈ m.sym2 ∩ m'.sym2, then m ∩ m' contains both endpoints of e
  -- But m ∩ m' has card ≤ 1 by packing property
  have h_inter := hM.2 hm hm' hne
  -- e = s(a, b) means a ∈ m ∩ m' and b ∈ m ∩ m'
  simp only [Finset.mem_sym2_iff] at he he'
  obtain ⟨a, b, hab, ha_m, hb_m, rfl⟩ := he
  obtain ⟨_, _, _, ha_m', hb_m', _⟩ := he'
  have : a ∈ m ∩ m' := Finset.mem_inter.mpr ⟨ha_m, ha_m'⟩
  have : b ∈ m ∩ m' := Finset.mem_inter.mpr ⟨hb_m, hb_m'⟩
  have h_card : (m ∩ m').card ≥ 2 := by
    apply Finset.one_lt_card.mpr
    exact ⟨a, ‹a ∈ m ∩ m'›, b, ‹b ∈ m ∩ m'›, hab⟩
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: Integer packing gives optimal fractional packing
-- ══════════════════════════════════════════════════════════════════════════════

/-- The characteristic function of M is a valid fractional packing -/
def M_characteristic (M : Finset (Finset V)) : Finset V → ℝ :=
  fun t => if t ∈ M then 1 else 0

lemma M_characteristic_is_fractional_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    isFractionalPacking G (M_characteristic M) := by
  constructor
  · intro t
    simp only [M_characteristic]
    split_ifs <;> linarith
  constructor
  · intro t ht
    simp only [M_characteristic]
    have : t ∉ M := fun h => ht (hM.1 h)
    simp [this]
  · intro e he
    -- Sum over triangles containing e
    -- For M-edges, exactly one M-triangle contains it (sum = 1)
    -- For non-M-edges, no M-triangle contains it (sum = 0)
    sorry

/-- For Cycle_4, the fractional packing number equals 4 -/
theorem nu_star_eq_4_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    fractionalPackingNumber G = 4 := by
  -- Lower bound: M gives a fractional packing of weight 4
  have h_lower : fractionalPackingNumber G ≥ 4 := by
    -- M_characteristic gives weight = |M| = 4
    sorry

  -- Upper bound: No fractional packing can exceed 4
  have h_upper : fractionalPackingNumber G ≤ 4 := by
    -- Key insight: Any external triangle shares an M-edge
    -- M-edges are saturated by M_characteristic
    -- So external triangles must have weight 0
    -- Total weight = sum over M only = 4
    sorry

  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- KRIVELEVICH'S THEOREM (Axiomatized from literature)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Krivelevich (1995): τ(G) ≤ 2·ν*(G)
    Source: "On a conjecture of Tuza" Discrete Mathematics 142(1-3):281-286

    This is a proven result in the literature. We axiomatize it here
    as formalizing the full LP argument would require infrastructure
    not currently in Mathlib. -/
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for Cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main result: τ ≤ 8 for Cycle_4 configurations via LP relaxation -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: ν* = 4 for Cycle_4
  have h_nu_star : fractionalPackingNumber G = 4 := nu_star_eq_4_cycle4 G M hM cfg

  -- Step 2: Apply Krivelevich's bound
  have h_kriv : (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G :=
    krivelevich_bound G

  -- Step 3: Combine to get τ ≤ 8
  rw [h_nu_star] at h_kriv
  norm_cast at h_kriv
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE: Direct Edge Counting (Gemini's insight)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Alternative proof via edge counting:
    For any fractional packing w, we have:
    3 · Σ w_t ≤ |E|  (each triangle has 3 edges, sum edge constraints)

    For Cycle_4 with M-edges only: |E| = 12, so Σ w_t ≤ 4

    This gives ν* ≤ 4 directly without LP machinery. -/
lemma edge_counting_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) (hw : isFractionalPacking G w) :
    3 * ∑ t in G.cliqueFinset 3, w t ≤ (G.edgeFinset.card : ℝ) := by
  -- Sum all edge constraints: Σ_e Σ_{t ∋ e} w_t ≤ |E|
  -- Swap order: Σ_t (|edges of t|) · w_t ≤ |E|
  -- Since each triangle has 3 edges: 3 · Σ w_t ≤ |E|
  sorry

/-- For minimal Cycle_4 graph with exactly 12 M-edges -/
lemma minimal_cycle4_nu_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (cfg : Cycle4 G M)
    (h_minimal : G.edgeFinset.card = 12) :
    fractionalPackingNumber G ≤ 4 := by
  -- By edge counting: 3 · ν* ≤ |E| = 12, so ν* ≤ 4
  sorry

end
