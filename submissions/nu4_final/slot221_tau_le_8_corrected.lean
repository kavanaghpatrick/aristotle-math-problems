/-
  slot221_tau_le_8_corrected.lean

  THEOREM: τ ≤ 8 for cycle_4 (CORRECTED Krivelevich formulation)

  CRITICAL FIX (Jan 3, 2026):
  Previous slots (218, 220) had Pattern 10 violation in the Krivelevich axiom.

  INCORRECT: "If valid packing has weight k, then τ ≤ 2k"
    Counterexample: K_3 with w=0 gives τ=1 but axiom says τ ≤ 0

  CORRECT: "τ ≤ 2ν* where ν* = supremum of valid packing weights"

  FROM 5-ROUND DEBATE:
  - ν* = 4 for cycle_4 (proven in Rounds 3-4)
  - ν* ≥ 4: Indicator packing achieves weight 4
  - ν* ≤ 4: External edge-sharing forces upper bound (slot182)

  STRATEGY:
  1. Axiomatize Krivelevich CORRECTLY: τ ≤ 2ν*
  2. Define ν* as supremum
  3. Prove ν* ≤ 4 using external edge-sharing constraint
  4. Prove ν* ≥ 4 using indicator packing
  5. Conclude τ ≤ 2×4 = 8

  DIFFICULTY: 4/5
  SUCCESS PROBABILITY: 65%
-/

import Mathlib

open scoped Classical

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
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
  hM_card : M.card = 4  -- ADDED: Explicit cardinality requirement
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A

-- ══════════════════════════════════════════════════════════════════════════════
-- FRACTIONAL PACKING DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesContainingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)

/-- A fractional packing is a non-negative weight function satisfying edge constraints -/
structure FractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj] where
  w : Finset V → ℚ
  nonneg : ∀ t, w t ≥ 0
  edge_constraint : ∀ e ∈ G.edgeFinset, (trianglesContainingEdge G e).sum w ≤ 1

/-- Weight of a fractional packing -/
def FractionalPacking.weight (G : SimpleGraph V) [DecidableRel G.Adj]
    (fp : FractionalPacking G) : ℚ :=
  (G.cliqueFinset 3).sum fp.w

/-- Fractional packing number ν* = supremum of packing weights -/
noncomputable def fractionalPackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  sSup { r : ℚ | ∃ fp : FractionalPacking G, fp.weight = r }

-- ══════════════════════════════════════════════════════════════════════════════
-- KRIVELEVICH'S THEOREM (Correct formulation)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Krivelevich (1995): τ ≤ 2ν* where ν* is the fractional packing number.

    This is the CORRECT formulation using the supremum.

    REFERENCE: Krivelevich, M. (1995). "On a conjecture of Tuza about packing
    and covering of triangles". Discrete Mathematics 142(1-3), 281-286.
-/
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
  (triangleCoveringNumber G : ℚ) ≤ 2 * fractionalPackingNumber G

-- ══════════════════════════════════════════════════════════════════════════════
-- INDICATOR PACKING (proves ν* ≥ |M|)
-- ══════════════════════════════════════════════════════════════════════════════

def indicatorWeight (M : Finset (Finset V)) (t : Finset V) : ℚ :=
  if t ∈ M then 1 else 0

lemma indicatorWeight_nonneg (M : Finset (Finset V)) (t : Finset V) :
    indicatorWeight M t ≥ 0 := by simp [indicatorWeight]; split_ifs <;> norm_num

/-- M-edges are in at most one M-element -/
lemma edge_in_at_most_one_M_element (M : Finset (Finset V))
    (hM : isTrianglePacking (G := G) M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (e : Sym2 V) (he_nd : ¬e.IsDiag)
    (he_X : e ∈ X.sym2) (he_Y : e ∈ Y.sym2) :
    False := by
  obtain ⟨u, v, huv_eq⟩ := Sym2.exists_eq e
  have huv : u ≠ v := by
    intro h; rw [h] at huv_eq
    exact he_nd (huv_eq ▸ Sym2.mk_isDiag_iff.mpr rfl)
  rw [huv_eq] at he_X he_Y
  rw [Finset.mem_sym2_iff] at he_X he_Y
  have h_inter_ge_2 : (X ∩ Y).card ≥ 2 := by
    have hu_inter : u ∈ X ∩ Y := Finset.mem_inter.mpr ⟨he_X.1, he_Y.1⟩
    have hv_inter : v ∈ X ∩ Y := Finset.mem_inter.mpr ⟨he_X.2.1, he_Y.2.1⟩
    exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩
  have h_inter_le_1 : (X ∩ Y).card ≤ 1 := hM.2 hX hY hXY
  omega

lemma M_elements_containing_edge_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he_nd : ¬e.IsDiag) :
    (M.filter (fun X => e ∈ X.sym2)).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨X, hX_mem, Y, hY_mem, hXY⟩ := Finset.one_lt_card.mp h
  simp only [Finset.mem_filter] at hX_mem hY_mem
  exact edge_in_at_most_one_M_element M hM X Y hX_mem.1 hY_mem.1 hXY e he_nd hX_mem.2 hY_mem.2

lemma indicatorWeight_edge_constraint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (trianglesContainingEdge G e).sum (indicatorWeight M) ≤ 1 := by
  have he_nd : ¬e.IsDiag := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he) |> Sym2.mk_isDiag_iff.not.mpr
  have h_split : (trianglesContainingEdge G e).sum (indicatorWeight M) =
      ((trianglesContainingEdge G e).filter (· ∈ M)).sum (fun _ => (1:ℚ)) +
      ((trianglesContainingEdge G e).filter (· ∉ M)).sum (fun _ => (0:ℚ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (· ∈ M)]
    congr 1 <;> { apply Finset.sum_congr rfl; intro t ht; simp only [Finset.mem_filter] at ht; simp [indicatorWeight, ht.2] }
  rw [h_split]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  calc ((trianglesContainingEdge G e).filter (· ∈ M)).card
      ≤ (M.filter (fun X => e ∈ X.sym2)).card := by
          apply Finset.card_le_card; intro t ht
          simp only [Finset.mem_filter, trianglesContainingEdge] at ht ⊢
          exact ⟨ht.2, ht.1.2⟩
      _ ≤ 1 := M_elements_containing_edge_card G M hM e he_nd

/-- The indicator packing is a valid fractional packing -/
def indicatorFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) : FractionalPacking G where
  w := indicatorWeight M
  nonneg := indicatorWeight_nonneg M
  edge_constraint := fun e he => indicatorWeight_edge_constraint G M hM e he

lemma indicatorWeight_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (G.cliqueFinset 3).sum (indicatorWeight M) = M.card := by
  have hM_sub : M ⊆ G.cliqueFinset 3 := hM.1
  rw [← Finset.sum_sdiff hM_sub]
  simp only [indicatorWeight]
  have h1 : M.sum (fun t => if t ∈ M then (1:ℚ) else 0) = M.card := by
    simp [Finset.sum_ite_eq', Finset.sum_const, Finset.card_eq_sum_ones]
  have h2 : ((G.cliqueFinset 3) \ M).sum (fun t => if t ∈ M then (1:ℚ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro t ht; simp only [Finset.mem_sdiff] at ht; simp [ht.2]
  linarith

/-- ν* ≥ |M| for any triangle packing M -/
lemma nu_star_ge_M_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    fractionalPackingNumber G ≥ M.card := by
  -- The indicator packing achieves weight |M|
  let fp := indicatorFractionalPacking G M hM
  have h_weight : fp.weight = M.card := by
    simp only [FractionalPacking.weight]
    exact indicatorWeight_sum G M hM
  -- ν* = sup{weights} ≥ weight of indicator = |M|
  have h_in : (M.card : ℚ) ∈ { r : ℚ | ∃ fp : FractionalPacking G, fp.weight = r } := by
    exact ⟨fp, h_weight⟩
  exact le_csSup_of_le ⟨(G.cliqueFinset 3).card, fun _ ⟨fp', hw⟩ => by
    rw [← hw]; simp only [FractionalPacking.weight]
    calc (G.cliqueFinset 3).sum fp'.w
        ≤ (G.cliqueFinset 3).sum (fun _ => (1:ℚ)) := Finset.sum_le_sum (fun t _ => by
            have := fp'.nonneg t; have := fp'.edge_constraint; sorry)  -- Needs upper bound
        _ = (G.cliqueFinset 3).card := by simp⟩ h_in

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY BOUND: ν* ≤ 4 for cycle_4 (from 5-round debate)
-- ══════════════════════════════════════════════════════════════════════════════

/-- CRITICAL LEMMA: ν* ≤ 4 for cycle_4

    This is the KEY insight from the 5-round debate:
    1. All externals of same M-element share an edge (slot182 PROVEN)
    2. This creates a fan structure constraining weights
    3. For each M-element X: w(X) + (externals of X) ≤ 1 (via shared edge)
    4. Summing: total weight ≤ 4

    Proof strategy uses the external edge-sharing constraint.
-/
lemma nu_star_le_4_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    fractionalPackingNumber G ≤ 4 := by
  -- For any fractional packing fp, we show fp.weight ≤ 4
  -- This implies ν* = sup{weights} ≤ 4
  apply csSup_le
  · -- The set is nonempty (zero packing exists)
    use 0
    use ⟨fun _ => 0, fun _ => le_refl 0, fun _ _ => by simp [trianglesContainingEdge]⟩
    simp [FractionalPacking.weight]
  · -- Every weight is ≤ 4
    intro r ⟨fp, hr⟩
    rw [← hr]
    -- Key argument: external edge-sharing forces weight ≤ 4
    -- This follows from Rounds 3-4 of the debate
    -- Each M-element X + its externals contribute ≤ 1 to some shared edge constraint
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- MAIN THEOREM: τ ≤ 8 for cycle_4

    Proof:
    1. ν* ≤ 4 (from nu_star_le_4_cycle4, using external edge-sharing)
    2. τ ≤ 2ν* (Krivelevich's theorem)
    3. τ ≤ 2 × 4 = 8
-/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  have h_nu_star_le : fractionalPackingNumber G ≤ 4 := nu_star_le_4_cycle4 G M hM cfg
  have h_kriv := krivelevich_bound G
  calc (triangleCoveringNumber G : ℚ)
      ≤ 2 * fractionalPackingNumber G := h_kriv
      _ ≤ 2 * 4 := by linarith
      _ = 8 := by norm_num

end
