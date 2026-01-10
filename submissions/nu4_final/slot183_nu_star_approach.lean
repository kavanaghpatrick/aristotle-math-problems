/-
Tuza's Conjecture: LP/Fractional Packing Approach Template

GOAL: Prove τ ≤ 2ν for ν=4 using LP relaxation.

MATHEMATICAL BACKGROUND:
- ν* (fractional packing number): Maximize Σ w(T) over triangles T
  subject to: w(T) ∈ [0,1] for all T
              Σ{w(T) : e ∈ T} ≤ 1 for each edge e
- τ* (fractional covering number): Minimize Σ y(e) over edges e
  subject to: y(e) ∈ [0,1] for all e
              Σ{y(e) : e ∈ T} ≥ 1 for each triangle T
- LP Duality: ν* = τ* (strong duality)
- Key inequalities: ν ≤ ν* = τ* ≤ τ
- Krivelevich (1995): τ ≤ 2ν*

STRATEGY:
1. Define fractionalTrianglePacking (weight function)
2. Define isFractionalPacking (validity predicate)
3. Define fractionalPackingNumber (supremum of weights)
4. Prove nu_star_le_nu: An integral packing gives a fractional packing
5. Use Krivelevich's theorem: τ ≤ 2ν*
6. For ν=4: If ν* = 4, then τ ≤ 8

REFERENCES:
- Krivelevich, M. "On a conjecture of Tuza about packing and covering of
  triangles." Discrete Mathematics 142(1-3):281-286, 1995.
- Haxell, P.E. "Packing and covering triangles in graphs." Discrete Math. 195:251-254, 1999.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: BASIC DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle in graph G is a 3-clique. -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3

/-- The set of all triangles in G. -/
def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  G.cliqueFinset 3

/-- A triangle packing: pairwise edge-disjoint triangles. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ triangles G ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- A maximal triangle packing: every triangle shares an edge with some packing element. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ triangles G, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

/-- Triangle packing number: maximum size of a packing. -/
noncomputable def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup { n : ℕ | ∃ M : Finset (Finset V), isTrianglePacking G M ∧ M.card = n }

/-- Triangle covering number: minimum size of an edge set hitting all triangles. -/
noncomputable def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
    (∀ t ∈ triangles G, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n }

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: FRACTIONAL PACKING DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A fractional triangle packing assigns a weight w : Triangles → ℝ to each triangle.
    This is the weight function type. -/
abbrev FractionalWeight (V : Type*) := Finset V → ℝ

/-- Predicate: w is a valid fractional packing for G.
    - Nonnegativity: w(t) ≥ 0 for all t
    - Support: w(t) = 0 if t is not a triangle
    - Edge constraints: For each edge e, Σ{w(t) : e ∈ t} ≤ 1 -/
def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : FractionalWeight V) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ triangles G → w t = 0) ∧
  (∀ e ∈ G.edgeFinset,
    ((triangles G).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

/-- Total weight of a fractional packing. -/
def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : FractionalWeight V) : ℝ :=
  (triangles G).sum w

/-- The fractional packing number ν*(G): supremum of weights over all valid fractional packings. -/
noncomputable def fractionalPackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { r : ℝ | ∃ w : FractionalWeight V, IsFractionalPacking G w ∧ packingWeight G w = r }

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: FRACTIONAL COVERING DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A fractional edge cover assigns a weight y : Edges → ℝ to each edge. -/
abbrev FractionalCoverWeight (V : Type*) := Sym2 V → ℝ

/-- Predicate: y is a valid fractional edge cover for G.
    - Nonnegativity: y(e) ≥ 0 for all e
    - Support: y(e) = 0 if e is not an edge
    - Triangle constraints: For each triangle t, Σ{y(e) : e ∈ t} ≥ 1 -/
def IsFractionalCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : FractionalCoverWeight V) : Prop :=
  (∀ e, 0 ≤ y e) ∧
  (∀ e, e ∉ G.edgeFinset → y e = 0) ∧
  (∀ t ∈ triangles G,
    (t.sym2.filter (fun e => e ∈ G.edgeFinset)).sum y ≥ 1)

/-- Total weight of a fractional cover. -/
def coverWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : FractionalCoverWeight V) : ℝ :=
  G.edgeFinset.sum y

/-- The fractional covering number τ*(G): infimum of weights over all valid fractional covers. -/
noncomputable def fractionalCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf { r : ℝ | ∃ y : FractionalCoverWeight V, IsFractionalCover G y ∧ coverWeight G y = r }

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: INDICATOR FUNCTION (INTEGRAL PACKING AS FRACTIONAL)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Indicator function: assigns 1 to packing elements, 0 to others.
    This embeds an integral packing into the space of fractional packings. -/
def indicatorPacking (M : Finset (Finset V)) (t : Finset V) : ℝ :=
  if t ∈ M then 1 else 0

lemma indicatorPacking_nonneg (M : Finset (Finset V)) (t : Finset V) :
    0 ≤ indicatorPacking M t := by
  unfold indicatorPacking
  split_ifs <;> linarith

lemma indicatorPacking_zero_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∉ triangles G) :
    indicatorPacking M t = 0 := by
  unfold indicatorPacking
  split_ifs with h
  · exfalso
    exact ht (hM.1 h)
  · rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: KEY LEMMA - M-EDGE UNIQUENESS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each edge in a triangle packing appears in exactly one packing element.
    This is the key structural lemma for proving indicator packings are valid. -/
lemma M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he_edge : e ∈ G.edgeFinset)
    (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2 := by
  by_contra hne
  -- If e is in both m1 and m2, then both endpoints of e are in m1 ∩ m2
  -- This gives |m1 ∩ m2| ≥ 2, contradicting the packing property
  rw [SimpleGraph.mem_edgeFinset] at he_edge
  obtain ⟨u, v⟩ := e
  have hne_uv : u ≠ v := G.ne_of_adj he_edge
  simp only [Finset.mem_sym2_iff, Sym2.mem_iff] at he1 he2
  have hu1 : u ∈ m1 := he1 u (Or.inl rfl)
  have hv1 : v ∈ m1 := he1 v (Or.inr rfl)
  have hu2 : u ∈ m2 := he2 u (Or.inl rfl)
  have hv2 : v ∈ m2 := he2 v (Or.inr rfl)
  have hu_inter : u ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨hu1, hu2⟩
  have hv_inter : v ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨hv1, hv2⟩
  have h_card : (m1 ∩ m2).card ≥ 2 := Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, hne_uv⟩
  have h_pairwise := hM.2 hm1 hm2 hne
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: INDICATOR IS A VALID FRACTIONAL PACKING
-- ══════════════════════════════════════════════════════════════════════════════

/-- At most one packing element contains any given edge. -/
lemma filter_M_card_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ((triangles G).filter (fun t => e ∈ t.sym2) ∩ M).card ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  obtain ⟨m1, hm1, m2, hm2, hne⟩ := Finset.one_lt_card.mp h_gt
  simp only [Finset.mem_inter, Finset.mem_filter] at hm1 hm2
  exact hne (M_edge_unique_owner G M hM e he m1 m2 hm1.2 hm2.2 hm1.1.2 hm2.1.2)

/-- The indicator function of an integral packing is a valid fractional packing.
    This is the key theorem connecting ν to ν*. -/
theorem indicator_is_fractional_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    IsFractionalPacking G (indicatorPacking M) := by
  refine ⟨indicatorPacking_nonneg M,
         indicatorPacking_zero_outside G M hM, ?_⟩
  -- Edge constraint: sum over triangles containing e is ≤ 1
  intro e he
  -- Split sum into M-part and non-M part
  let S := (triangles G).filter (fun t => e ∈ t.sym2)
  have h_sum : S.sum (indicatorPacking M) = (S ∩ M).card := by
    rw [← Finset.sum_inter_add_sum_diff S M (indicatorPacking M)]
    have h1 : (S ∩ M).sum (indicatorPacking M) = (S ∩ M).card := by
      simp only [indicatorPacking]
      rw [Finset.sum_ite_mem, Finset.inter_comm M (S ∩ M)]
      simp [Finset.inter_assoc]
    have h2 : (S \ M).sum (indicatorPacking M) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp only [Finset.mem_sdiff] at ht
      simp only [indicatorPacking, if_neg ht.2]
    linarith
  calc S.sum (indicatorPacking M) = (S ∩ M).card := h_sum
    _ ≤ 1 := filter_M_card_le_one G M hM e he

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 7: ν ≤ ν* (INTEGRAL ≤ FRACTIONAL)
-- ══════════════════════════════════════════════════════════════════════════════

/-- The indicator packing achieves weight equal to the packing size. -/
lemma indicator_weight_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    packingWeight G (indicatorPacking M) = M.card := by
  unfold packingWeight
  -- Split sum: triangles = M ∪ (triangles \ M)
  have h_part : triangles G = M ∪ (triangles G \ M) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro ht
      by_cases h : t ∈ M <;> [left; right] <;> [exact h; exact ⟨ht, h⟩]
    · intro h
      rcases h with h | ⟨h, _⟩ <;> [exact hM.1 h; exact h]
  have h_disj : Disjoint M (triangles G \ M) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    exact (Finset.mem_sdiff.mp ht').2 ht
  rw [h_part, Finset.sum_union h_disj]
  -- M.sum = |M|
  have hM_sum : M.sum (indicatorPacking M) = M.card := by
    simp only [indicatorPacking]
    calc M.sum (fun t => if t ∈ M then (1 : ℝ) else 0)
        = M.sum (fun _ => (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro t ht
          simp only [if_pos ht]
      _ = M.card := by simp
  -- (triangles \ M).sum = 0
  have hext_sum : (triangles G \ M).sum (indicatorPacking M) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_sdiff] at ht
    simp only [indicatorPacking, if_neg ht.2]
  rw [hM_sum, hext_sum]
  ring

/-- The fractional packing number is at least the integral packing number.
    This follows because any integral packing can be viewed as a fractional packing. -/
theorem nu_le_nu_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M.card : ℝ) ≤ fractionalPackingNumber G := by
  -- The indicator packing achieves weight M.card
  have hw : IsFractionalPacking G (indicatorPacking M) := indicator_is_fractional_packing G M hM
  have hweight : packingWeight G (indicatorPacking M) = M.card := indicator_weight_eq_card G M hM
  -- This shows M.card is in the set whose supremum is ν*
  rw [← hweight]
  apply le_csSup
  -- BddAbove: The set is bounded above (by number of triangles, or by finite graph considerations)
  · sorry -- Aristotle: prove BddAbove using finite graph
  -- Membership: packingWeight is in the set
  · exact ⟨indicatorPacking M, hw, rfl⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 8: ν* ≤ 4 FOR ν = 4 (UPPER BOUND)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each triangle element has weight at most 1 (from any edge constraint). -/
lemma weight_le_one_of_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : FractionalWeight V) (hw : IsFractionalPacking G w)
    (t : Finset V) (ht : t ∈ triangles G) :
    w t ≤ 1 := by
  -- t is a 3-clique, so it has at least one edge e
  -- The edge constraint for e gives w(t) ≤ Σ{w(s) : e ∈ s} ≤ 1
  have h_is_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have h_card : t.card = 3 := h_is_clique.card_eq
  -- Get two distinct vertices from the 3-clique
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.card_le_two.not.mp (by omega : ¬t.card ≤ 2)
  have h_adj : G.Adj a b := h_is_clique.2 ha hb hab
  let e := Sym2.mk (a, b)
  have h_e_edge : e ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr h_adj
  have h_e_in_t : e ∈ t.sym2 := by
    rw [Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  have h_t_in : t ∈ (triangles G).filter (fun s => e ∈ s.sym2) :=
    Finset.mem_filter.mpr ⟨ht, h_e_in_t⟩
  calc w t ≤ ((triangles G).filter (fun s => e ∈ s.sym2)).sum w :=
       Finset.single_le_sum (fun s _ => hw.1 s) h_t_in
    _ ≤ 1 := hw.2.2 e h_e_edge

/-- For a maximal packing M with |M| = 4, the sum of weights over M is at most 4. -/
lemma M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : FractionalWeight V) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card := by
  -- Each M-element has w(m) ≤ 1 (by weight_le_one_of_triangle)
  have h_each_le_1 : ∀ m ∈ M, w m ≤ 1 := fun m hm =>
    weight_le_one_of_triangle G w hw m (hM.1 hm)
  calc M.sum w ≤ M.sum (fun _ => (1 : ℝ)) := Finset.sum_le_sum (fun m hm => h_each_le_1 m hm)
    _ = M.card := by simp

/-- The fractional packing number is at most 4 for graphs with a maximal 4-packing.
    This is the hard direction requiring an exchange/optimality argument. -/
theorem nu_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    fractionalPackingNumber G ≤ 4 := by
  -- Strategy: Show that for ANY fractional packing w, packingWeight G w ≤ 4
  -- Then use csSup_le
  apply csSup_le
  -- Nonemptiness: zero packing exists
  · use 0
    use fun _ => 0
    constructor
    · refine ⟨fun _ => le_refl 0, fun _ _ => rfl, ?_⟩
      intro e _
      simp only [Finset.sum_const_zero]
    · simp only [packingWeight, Finset.sum_const_zero]
  -- Upper bound: each packing has weight ≤ 4
  · intro r ⟨w, hw, rfl⟩
    -- This is the main content: prove packingWeight G w ≤ 4
    -- The full proof requires showing externals are bounded by edge capacity
    sorry -- Aristotle: prove via edge-counting or exchange argument

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 9: ν* = 4 FOR ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/-- The fractional packing number equals 4 for graphs with a maximal 4-packing. -/
theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    fractionalPackingNumber G = 4 := by
  apply le_antisymm
  · exact nu_star_le_4 G M hM hM4
  · -- ν* ≥ 4: from the indicator packing
    have h := nu_le_nu_star G M hM.1
    rw [hM4] at h
    exact h

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 10: LP DUALITY (τ* = ν*)
-- ══════════════════════════════════════════════════════════════════════════════

/-- LP strong duality: τ* = ν*.
    This is a standard result in LP theory - we axiomatize it here. -/
axiom lp_duality (G : SimpleGraph V) [DecidableRel G.Adj] :
    fractionalCoveringNumber G = fractionalPackingNumber G

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 11: KRIVELEVICH'S THEOREM (τ ≤ 2ν*)
-- ══════════════════════════════════════════════════════════════════════════════

/-
CITATION: M. Krivelevich, "On a conjecture of Tuza about packing and covering
          of triangles," Discrete Mathematics 142(1-3):281-286, 1995.

THEOREM: For any graph G, τ(G) ≤ 2ν*(G).

This is a published theorem that we axiomatize. The key insight is that
while τ* = ν*, the integral covering number τ can be at most 2 times
the fractional packing number ν*.
-/

/-- Krivelevich's bound: τ ≤ 2ν* (published theorem). -/
axiom krivelevich_tau_le_2_nu_star (G : SimpleGraph V) [DecidableRel G.Adj] :
    (coveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 12: MAIN THEOREM - TUZA'S CONJECTURE FOR ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/-- TUZA'S CONJECTURE for ν = 4: τ(G) ≤ 8.

    This follows from:
    1. ν* = 4 (nu_star_eq_4)
    2. τ ≤ 2ν* (Krivelevich)
    3. τ ≤ 2 × 4 = 8 -/
theorem tuza_nu_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    coveringNumber G ≤ 8 := by
  have h1 : (coveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G :=
    krivelevich_tau_le_2_nu_star G
  have h2 : fractionalPackingNumber G = 4 := nu_star_eq_4 G M hM hM4
  rw [h2] at h1
  -- h1 : (coveringNumber G : ℝ) ≤ 2 * 4 = 8
  have h3 : (2 : ℝ) * 4 = 8 := by norm_num
  rw [h3] at h1
  -- Convert from ℝ inequality to ℕ inequality
  exact_mod_cast h1

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 13: AUXILIARY LEMMAS (FOR ARISTOTLE TO COMPLETE)
-- ══════════════════════════════════════════════════════════════════════════════

/-- External triangles share an edge with some packing element (by maximality). -/
lemma external_shares_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht_tri : t ∈ triangles G) (ht_ext : t ∉ M) :
    ∃ e, e ∈ G.edgeFinset ∧ e ∈ t.sym2 ∧ ∃ m ∈ M, e ∈ m.sym2 := by
  -- By maximality, t shares ≥ 2 vertices with some m ∈ M
  -- Two vertices of a triangle determine an edge
  obtain ⟨m, hm, h_inter⟩ := hM.2 t ht_tri ht_ext
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.card_le_two.not.mp (by omega : ¬(t ∩ m).card ≤ 2)
  rw [Finset.mem_inter] at ha hb
  let e := Sym2.mk (a, b)
  use e
  constructor
  · -- e is an edge of G (both a,b are in the triangle t, which is a clique)
    have h_is_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht_tri
    exact SimpleGraph.mem_edgeFinset.mpr (h_is_clique.2 ha.1 hb.1 hab)
  constructor
  · -- e ∈ t.sym2
    rw [Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> [exact ha.1; exact hb.1]
  · -- e ∈ m.sym2 for some m ∈ M
    use m, hm
    rw [Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> [exact ha.2; exact hb.2]

/-- When all M-elements have weight 1, external triangles have weight 0.
    This is the "saturation" lemma. -/
theorem externals_zero_when_M_saturated (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (w : FractionalWeight V) (hw : IsFractionalPacking G w)
    (h_sat : ∀ m ∈ M, w m = 1) :
    ∀ t ∈ triangles G, t ∉ M → w t = 0 := by
  intro t ht_tri ht_ext
  -- t shares an edge e with some M-element m
  obtain ⟨e, he_edge, he_t, m, hm, he_m⟩ := external_shares_M_edge G M hM t ht_tri ht_ext
  -- The edge constraint for e gives: w(m) + w(t) + ... ≤ 1
  have h_constr := hw.2.2 e he_edge
  -- Since w(m) = 1, we need w(t) ≤ 0
  have h_m_in : m ∈ (triangles G).filter (fun s => e ∈ s.sym2) :=
    Finset.mem_filter.mpr ⟨hM.1.1 hm, he_m⟩
  have h_t_in : t ∈ (triangles G).filter (fun s => e ∈ s.sym2) :=
    Finset.mem_filter.mpr ⟨ht_tri, he_t⟩
  have h_t_ne_m : t ≠ m := fun h => ht_ext (h ▸ hm)
  -- Sum over filter ≥ w(m) + w(t) = 1 + w(t)
  have h_sum_ge : w m + w t ≤ ((triangles G).filter (fun s => e ∈ s.sym2)).sum w := by
    have h_sub : ({m, t} : Finset (Finset V)) ⊆ (triangles G).filter (fun s => e ∈ s.sym2) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> assumption
    calc w m + w t = ({m, t} : Finset (Finset V)).sum w := (Finset.sum_pair h_t_ne_m.symm).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset (fun s hs => h_sub hs) (fun s _ _ => hw.1 s)
  -- Combine: 1 + w(t) ≤ sum ≤ 1, so w(t) ≤ 0
  rw [h_sat m hm] at h_sum_ge
  -- From h_sum_ge : 1 + w t ≤ sum w and h_constr : sum w ≤ 1
  -- We get 1 + w t ≤ 1, so w t ≤ 0
  -- Combined with w t ≥ 0 (nonnegativity), we get w t = 0
  linarith [hw.1 t]

end
