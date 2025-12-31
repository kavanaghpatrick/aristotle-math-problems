/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: adc20172-5974-4d09-8b5f-9d92fd739a14
-/

/-
Tuza ν=4 Cycle_4: τ ≤ 12 via All M-Edges Cover (FALLBACK)

Strategy: Cover ALL 12 edges of the packing M = {A, B, C, D}.
Since every triangle shares an edge with M (proven), this covers all triangles.

This is a safe fallback with near-guaranteed success.
4 triangles × 3 edges = 12 edges total.

From AI debate synthesis (Dec 30, 2025):
- Grok, Gemini, Codex all recommend this as Priority 1 baseline
- 95% expected success rate
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '≤'; expected command-/
open scoped Classical

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven Aristotle files)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

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
-- PROVEN LEMMA: Every triangle shares ≥2 vertices with some packing element
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  by_contra h_no_share
  push_neg at h_no_share
  -- If t shares ≤1 vertex with each X ∈ M, then M ∪ {t} is a larger packing
  have h_packing : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · -- M ∪ {t} ⊆ cliqueFinset 3
      intro s hs
      simp only [Finset.mem_union, Finset.mem_singleton] at hs
      cases hs with
      | inl h => exact hM.1.1 h
      | inr h => rw [h]; exact ht
    · -- Pairwise intersection ≤ 1
      intro s1 hs1 s2 hs2 hne
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hs1 hs2
      cases hs1 with
      | inl h1 =>
        cases hs2 with
        | inl h2 => exact hM.1.2 h1 h2 hne
        | inr h2 => subst h2; exact Nat.lt_succ_iff.mp (h_no_share s1 h1)
      | inr h1 =>
        cases hs2 with
        | inl h2 => subst h1; rw [Finset.inter_comm]; exact Nat.lt_succ_iff.mp (h_no_share s2 h2)
        | inr h2 => subst h1 h2; exact absurd rfl hne
  have h_not_mem : t ∉ M := by
    intro h_mem
    have := h_no_share t h_mem
    simp only [Finset.inter_self] at this
    have h_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at ht
      exact ht.2
    omega
  have h_card_increase : (M ∪ {t}).card = M.card + 1 := by
    rw [Finset.card_union_eq_card_add_card.mpr]
    · simp
    · simp [h_not_mem]
  have h_le : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : M ∪ {t} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_in_image : (M ∪ {t}).card ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card := by
      exact Finset.mem_image_of_mem _ h_mem
    exact Finset.le_max' _ _ h_in_image
  rw [h_card_increase, hM.2] at h_le
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Two triangles sharing ≥2 vertices share an edge
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_vertices_implies_shared_edge (t X : Finset V)
    (ht : t.card = 3) (hX : X.card = 3) (h_share : (t ∩ X).card ≥ 2) :
    ∃ e : Sym2 V, e ∈ t.sym2 ∧ e ∈ X.sym2 := by
  -- Extract two distinct vertices from the intersection
  have h_two : ∃ a b : V, a ∈ t ∩ X ∧ b ∈ t ∩ X ∧ a ≠ b := by
    have h_card := h_share
    interval_cases n : (t ∩ X).card
    · -- n = 2: intersection has exactly 2 elements
      obtain ⟨a, b, hab, h_eq⟩ := Finset.card_eq_two.mp rfl
      exact ⟨a, b, by simp [h_eq], by simp [h_eq], hab⟩
    · -- n = 3: intersection has 3 elements (t = X)
      obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := Finset.card_eq_three.mp rfl
      exact ⟨a, b, by simp [h_eq], by simp [h_eq], hab⟩
  obtain ⟨a, b, ha, hb, hab⟩ := h_two
  use s(a, b)
  constructor
  · -- s(a,b) ∈ t.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨Finset.mem_of_mem_inter_left ha, Finset.mem_of_mem_inter_left hb, hab⟩
  · -- s(a,b) ∈ X.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨Finset.mem_of_mem_inter_right ha, Finset.mem_of_mem_inter_right hb, hab⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING EDGES COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-- Union of all edges from packing elements -/
def packingEdges (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset (Finset V)}
    (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2 ∪ cfg.B.sym2 ∪ cfg.C.sym2 ∪ cfg.D.sym2

/-- Packing edges are graph edges -/
lemma packingEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    packingEdges G cfg ⊆ G.edgeFinset := by
  intro e he
  simp only [packingEdges, Finset.mem_union] at he
  -- e is in sym2 of some triangle in M
  rcases he with he | he | he | he <;> {
    rw [Finset.mem_sym2_iff] at he
    obtain ⟨ha, hb, hab⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    -- The triangle is a clique, so its vertices are pairwise adjacent
    have h_clique := hM.1.1
    simp only [Finset.subset_iff] at h_clique
    first
    | have := h_clique cfg.A cfg.hA
    | have := h_clique cfg.B cfg.hB
    | have := h_clique cfg.C cfg.hC
    | have := h_clique cfg.D cfg.hD
    simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
    exact this.1.2 ha hb hab
  }

/-- Packing edges have cardinality ≤ 12 -/
lemma packingEdges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    (packingEdges G cfg).card ≤ 12 := by
  simp only [packingEdges]
  -- Union bound: |A ∪ B ∪ C ∪ D| ≤ |A| + |B| + |C| + |D|
  calc (cfg.A.sym2 ∪ cfg.B.sym2 ∪ cfg.C.sym2 ∪ cfg.D.sym2).card
      ≤ cfg.A.sym2.card + cfg.B.sym2.card + cfg.C.sym2.card + cfg.D.sym2.card := by
        have h1 := Finset.card_union_le cfg.A.sym2 cfg.B.sym2
        have h2 := Finset.card_union_le (cfg.A.sym2 ∪ cfg.B.sym2) cfg.C.sym2
        have h3 := Finset.card_union_le (cfg.A.sym2 ∪ cfg.B.sym2 ∪ cfg.C.sym2) cfg.D.sym2
        omega
    _ ≤ 3 + 3 + 3 + 3 := by
        -- Each triangle has card 3, so sym2 has card 3
        have hA : cfg.A.card = 3 := by
          have := hM.1.1 cfg.A cfg.hA
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        have hB : cfg.B.card = 3 := by
          have := hM.1.1 cfg.B cfg.hB
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        have hC : cfg.C.card = 3 := by
          have := hM.1.1 cfg.C cfg.hC
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        have hD : cfg.D.card = 3 := by
          have := hM.1.1 cfg.D cfg.hD
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        -- sym2 of 3-set has 3 elements
        rw [Finset.card_sym2, Finset.card_sym2, Finset.card_sym2, Finset.card_sym2]
        simp only [hA, hB, hC, hD]
        native_decide
    _ = 12 := by norm_num

/-- Packing edges cover all triangles -/
lemma packingEdges_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ packingEdges G cfg, e ∈ t.sym2 := by
  intro t ht
  -- t shares ≥2 vertices with some X ∈ M
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- Get cardinalities
  have ht_card : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at ht
    exact ht.2
  have hX_card : X.card = 3 := by
    have := hM.1.1 X hX_mem
    simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
    exact this.2
  -- Therefore t shares an edge with X
  obtain ⟨e, he_in_t, he_in_X⟩ := shared_vertices_implies_shared_edge t X ht_card hX_card hX_share
  use e
  constructor
  · -- e ∈ packingEdges
    simp only [packingEdges, Finset.mem_union]
    rw [cfg.hM_eq] at hX_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
    rcases hX_mem with rfl | rfl | rfl | rfl
    · left; left; left; exact he_in_X
    · left; left; right; exact he_in_X
    · left; right; exact he_in_X
    · right; exact he_in_X
  · exact he_in_t

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 12
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_12_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 12 := by
  -- packingEdges is a valid cover of size ≤ 12
  let E := packingEdges G cfg
  have h_subset : E ⊆ G.edgeFinset := packingEdges_subset G M hM cfg
  have h_card : E.card ≤ 12 := packingEdges_card G M hM cfg
  have h_cover : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := packingEdges_cover G M hM cfg
  have h_valid : isTriangleCover G E := ⟨h_subset, h_cover⟩
  -- E is in the set of valid covers
  have h_in : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_subset, h_valid⟩
  -- τ ≤ |E| ≤ 12
  unfold triangleCoveringNumber
  have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨E, h_in⟩
  have h_in_image : E.card ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card :=
    Finset.mem_image_of_mem _ h_in
  have h_min_le := Finset.min'_le _ E.card h_in_image
  calc (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0

≤ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min' (Finset.Nonempty.image h_nonempty _) := by
        simp only [Finset.min_eq_min']
        rfl
    _ ≤ E.card := h_min_le
    _ ≤ 12 := h_card

end