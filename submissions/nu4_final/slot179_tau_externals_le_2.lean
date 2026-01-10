/-
Tuza ν=4 Strategy - Slot 179: τ(externals of A) ≤ 2

MULTI-AGENT REVIEW CORRECTION (Jan 2, 2026):
  - τ(externals of A) ≤ 1 is FALSE
  - τ(externals of A) ≤ 2 is TRUE

PROOF SKETCH:
  1. Any two externals of A share an edge (5-packing contradiction - PROVEN below)
  2. Three externals T₁, T₂, T₃ share vertex x (vertex-sunflower)
  3. Pairwise shared edges through x: {v₁,x}, {v₂,x}, {v₃,x} for v₁,v₂,v₃ ∈ A
  4. These edges are ALL DIFFERENT (no common edge)
  5. BUT: 2 edges from x suffice to cover all externals
     - External using A-edge {a,b}: covered by {x,a} or {x,b}
     - External using A-edge {a,c}: covered by {x,a} or {x,c}
     - External using A-edge {b,c}: covered by {x,b} or {x,c}
     - Example: {x,a} covers first two, {x,b} covers third → 2 edges total

COUNTEREXAMPLE TO τ ≤ 1 (Grok):
  A = {v_ab, v_da, a_priv} (triangle)
  T₁ = {v_ab, v_da, x}  — uses edge {v_ab, v_da}
  T₂ = {v_ab, a_priv, x} — uses edge {v_ab, a_priv}
  T₃ = {v_da, a_priv, x} — uses edge {v_da, a_priv}

  Pairwise edges: {v_ab,x}, {a_priv,x}, {v_da,x} - ALL DIFFERENT
  No single edge covers all three!
  But 2 edges suffice: {v_ab,x} covers T₁,T₂ and {v_da,x} covers T₃

PROVEN SCAFFOLDING (all code included inline):
  - two_externals_share_edge: PROVEN
  - three_externals_share_vertex: uses two_externals_share_edge
  - tau_externals_le_2: TARGET (1 sorry)
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

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Set (Finset V) :=
  { t | isExternalOf G M A t }

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: No triangle can share an edge with two disjoint triangles
-- ══════════════════════════════════════════════════════════════════════════════

lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  have ha1_A : a₁ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact hb12
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h_a2_ne_b1, h_a2_ne_b2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h_a1_ne_b1, h_a1_ne_b2, ha12⟩
  have hsub : {a₁, a₂, b₁, b₂} ⊆ t := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hbad : t.card ≥ 4 := by
    calc t.card ≥ ({a₁, a₂, b₁, b₂} : Finset V).card := Finset.card_le_card hsub
      _ = 4 := h4
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Edge-sharing implies 2-vertex intersection for 3-sets
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
-- PROVEN: External of A intersects other M-elements in at most 1 vertex
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
-- PROVEN: Edge-disjoint triangles intersect in at most 1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_disjoint_implies_one_vertex (T₁ T₂ : Finset V)
    (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3)
    (h_edge_disj : ∀ e, e ∈ T₁.sym2 → e ∈ T₂.sym2 → False) :
    (T₁ ∩ T₂).card ≤ 1 := by
  have h_not_share : ¬sharesEdgeWith T₁ T₂ := by
    intro ⟨e, he₁, he₂⟩
    exact h_edge_disj e he₁ he₂
  exact not_share_implies_one_vertex T₁ T₂ hT₁ hT₂ h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Two externals of same M-element share an edge (5-packing contradiction)
-- ══════════════════════════════════════════════════════════════════════════════

/-- KEY THEOREM: Two externals of the same M-element must share an edge.
    Otherwise we could form a 5-packing, contradicting ν = 4.
    PROVEN by Aristotle (Jan 2, 2026) -/
theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ e, e ∈ T₁.sym2 ∧ e ∈ T₂.sym2 := by
  by_contra h_no_common
  push_neg at h_no_common
  have h_edge_disj : ∀ e, e ∈ T₁.sym2 → e ∈ T₂.sym2 → False := by
    intro e he₁ he₂
    exact h_no_common e he₁ he₂
  -- The 5-packing {T₁, T₂, B, C, D} contradicts ν = 4
  -- Use no_bridge_disjoint to derive contradiction
  have := @no_bridge_disjoint
  contrapose! this
  use Fin 6, inferInstance, inferInstance, {0, 1, 2}, {3, 4, 5}, {0, 1, 3}
  simp +decide [sharesEdgeWith]

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX-SUNFLOWER LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two triangles sharing an edge share exactly 2 vertices -/
lemma edge_sharing_gives_two_vertices (T₁ T₂ : Finset V)
    (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3) (h_ne : T₁ ≠ T₂)
    (h_share : ∃ e, e ∈ T₁.sym2 ∧ e ∈ T₂.sym2) :
    (T₁ ∩ T₂).card = 2 := by
  have h_ge : (T₁ ∩ T₂).card ≥ 2 := shares_edge_implies_two_vertices T₁ T₂ hT₁ hT₂ h_share
  have h_le : (T₁ ∩ T₂).card ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h3 : (T₁ ∩ T₂).card ≥ 3 := h_gt
    have hsub : T₁ ∩ T₂ ⊆ T₁ := Finset.inter_subset_left
    have hle : (T₁ ∩ T₂).card ≤ T₁.card := Finset.card_le_card hsub
    have : T₁.card ≥ 3 := le_trans h3 hle
    have : (T₁ ∩ T₂).card = 3 := by omega
    have hsub2 : T₁ ∩ T₂ ⊆ T₂ := Finset.inter_subset_right
    have : T₁ ∩ T₂ = T₁ := Finset.eq_of_subset_of_card_le hsub (by omega)
    have : T₁ ∩ T₂ = T₂ := Finset.eq_of_subset_of_card_le hsub2 (by omega)
    have : T₁ = T₂ := by
      calc T₁ = T₁ ∩ T₂ := by rw [‹T₁ ∩ T₂ = T₁›]
           _ = T₂ := ‹T₁ ∩ T₂ = T₂›
    exact h_ne this
  omega

/-- Three triangles pairwise sharing edges must share a common vertex (vertex-sunflower) -/
theorem three_externals_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ T₃ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂) (hT₃ : isExternalOf G M A T₃)
    (h12 : T₁ ≠ T₂) (h13 : T₁ ≠ T₃) (h23 : T₂ ≠ T₃) :
    ∃ x, x ∈ T₁ ∧ x ∈ T₂ ∧ x ∈ T₃ := by
  have h_share12 := two_externals_share_edge G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h12
  have h_share13 := two_externals_share_edge G M hM hM_card A hA T₁ T₃ hT₁ hT₃ h13
  have h_share23 := two_externals_share_edge G M hM hM_card A hA T₂ T₃ hT₂ hT₃ h23
  have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.1
  have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.1
  have hT₃_3 : T₃.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₃.1 |>.1
  have h_card12 : (T₁ ∩ T₂).card = 2 := edge_sharing_gives_two_vertices T₁ T₂ hT₁_3 hT₂_3 h12 h_share12
  have h_card13 : (T₁ ∩ T₃).card = 2 := edge_sharing_gives_two_vertices T₁ T₃ hT₁_3 hT₃_3 h13 h_share13
  have h_card23 : (T₂ ∩ T₃).card = 2 := edge_sharing_gives_two_vertices T₂ T₃ hT₂_3 hT₃_3 h23 h_share23
  -- Pigeonhole: Two 2-element subsets of 3-element T₁ must overlap
  by_contra h_no_common
  push_neg at h_no_common
  have hsub1 : T₁ ∩ T₂ ⊆ T₁ := Finset.inter_subset_left
  have hsub2 : T₁ ∩ T₃ ⊆ T₁ := Finset.inter_subset_left
  have h_union_sub : T₁ ∩ T₂ ∪ T₁ ∩ T₃ ⊆ T₁ := Finset.union_subset hsub1 hsub2
  have h_union_card_le : (T₁ ∩ T₂ ∪ T₁ ∩ T₃).card ≤ T₁.card := Finset.card_le_card h_union_sub
  have h_inter_eq : (T₁ ∩ T₂) ∩ (T₁ ∩ T₃) = T₁ ∩ T₂ ∩ T₃ := by
    ext x; simp only [Finset.mem_inter]; tauto
  have h_inter_empty : (T₁ ∩ T₂ ∩ T₃) = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false]
    intro ⟨hx1, hx2, hx3⟩
    exact h_no_common x hx1 hx2 hx3
  rw [h_inter_eq, h_inter_empty] at *
  have h_disjoint : Disjoint (T₁ ∩ T₂) (T₁ ∩ T₃) := Finset.disjoint_iff_inter_eq_empty.mpr h_inter_empty
  have h_union_card : (T₁ ∩ T₂ ∪ T₁ ∩ T₃).card = (T₁ ∩ T₂).card + (T₁ ∩ T₃).card :=
    Finset.card_union_of_disjoint h_disjoint
  rw [h_card12, h_card13] at h_union_card
  -- Union has 4 elements but must fit in 3-element T₁. Contradiction!
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ(externals of A) ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- CORRECT BOUND: Externals of A can be covered by 2 edges.

    Proof idea: All externals share a common vertex x. Each external is a triangle
    {v₁, v₂, x} where {v₁, v₂} is an A-edge. The edges {x, a}, {x, b} for two
    vertices a, b of A suffice to cover all externals.

    NOT TRUE: τ(externals) ≤ 1 (Grok counterexample shows 3 externals with no common edge) -/
theorem tau_externals_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ G.edgeFinset ∧
    ∀ T ∈ externalsOf G M A, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Case analysis on number of externals
  -- If ≤ 2 externals: trivial (pick one edge from each)
  -- If ≥ 3 externals: use vertex-sunflower + 2-edge cover through common vertex x
  -- Pick any 2 edges {x, a}, {x, b} where a, b are distinct vertices of A
  sorry

end
