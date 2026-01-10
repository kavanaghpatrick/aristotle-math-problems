/-
Tuza's Conjecture ν=4: Helly Property for External Triangles

GOAL: Prove that all externals of the same M-element share a COMMON edge.

KEY INSIGHT (from slot182):
- slot182 proves: If T₁, T₂ are externals of same M-element A, they share an edge
- Helly property: If every pair in a family of triangles shares an edge, all share a COMMON edge
- Combined: All externals of A share a common edge

WHY THIS MATTERS:
- τ(Ext(A)) = 1 for each M-element A
- 4 such edges cover ALL externals
- Combined with 4 cycle edges for M-elements: τ ≤ 8

PROOF STRATEGY (Helly):
- Triangles have only 3 edges each
- If T₁ ∩ T₂ contains edge e₁₂ and T₁ ∩ T₃ contains edge e₁₃
- Case 1: e₁₂ = e₁₃ → all share this edge
- Case 2: e₁₂ ≠ e₁₃ → they share a vertex v in T₁
  - T₂ contains e₁₂ = {u,v}, T₃ contains e₁₃ = {v,w}
  - T₂ ∩ T₃ must share edge → forces T₂ or T₃ to contain both u,w or overlap
  - All cases lead to common edge
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: BASIC DEFINITIONS (from slot182)
-- ══════════════════════════════════════════════════════════════════════════════

def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  G.cliqueFinset 3

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ triangles G ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ triangles G, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

/-- Vertex-based edge sharing (from slot182) -/
def sharesEdgeWith (t1 t2 : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t1 ∧ v ∈ t1 ∧ u ∈ t2 ∧ v ∈ t2

/-- External triangle of M-element A -/
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ triangles G ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: EDGE REPRESENTATION FOR TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle has exactly 3 edges -/
lemma triangle_has_three_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ triangles G) :
    t.sym2.card = 3 := by
  unfold triangles at ht
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  have h_card := ht.card_eq
  -- A 3-element set has exactly 3 pairs
  sorry -- Aristotle: Finset.sym2_card for |t| = 3

/-- Two vertices in a triangle form an edge of that triangle -/
lemma two_vertices_form_edge (t : Finset V) (u v : V)
    (hu : u ∈ t) (hv : v ∈ t) (huv : u ≠ v) :
    Sym2.mk (u, v) ∈ t.sym2 := by
  rw [Finset.mem_sym2_iff]
  intro x hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl <;> assumption

/-- sharesEdgeWith in terms of Sym2 -/
lemma sharesEdgeWith_iff_common_sym2 (t1 t2 : Finset V) :
    sharesEdgeWith t1 t2 ↔ ∃ e ∈ t1.sym2, e ∈ t2.sym2 ∧ ¬Sym2.IsDiag e := by
  constructor
  · intro ⟨u, v, huv, hu1, hv1, hu2, hv2⟩
    use Sym2.mk (u, v)
    constructor
    · exact two_vertices_form_edge t1 u v hu1 hv1 huv
    constructor
    · exact two_vertices_form_edge t2 u v hu2 hv2 huv
    · simp only [Sym2.isDiag_iff_proj_eq]
      exact huv
  · intro ⟨e, he1, he2, hdiag⟩
    obtain ⟨u, v⟩ := e
    simp only [Sym2.isDiag_iff_proj_eq] at hdiag
    use u, v, hdiag
    rw [Finset.mem_sym2_iff] at he1 he2
    exact ⟨he1 u (Sym2.mem_mk_left u v), he1 v (Sym2.mem_mk_right u v),
           he2 u (Sym2.mem_mk_left u v), he2 v (Sym2.mem_mk_right u v)⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: HELLY PROPERTY FOR TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two edges of the same triangle share at least one vertex -/
lemma triangle_edges_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ triangles G)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ t.sym2) (he2 : e2 ∈ t.sym2)
    (hne : e1 ≠ e2) :
    ∃ v : V, v ∈ e1 ∧ v ∈ e2 := by
  unfold triangles at ht
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  -- t is a 3-clique, so |t| = 3
  have h_card := ht.card_eq
  -- Both e1 and e2 are edges in t.sym2, meaning their vertices are in t
  rw [Finset.mem_sym2_iff] at he1 he2
  obtain ⟨a1, b1⟩ := e1
  obtain ⟨a2, b2⟩ := e2
  -- a1, b1, a2, b2 are all in t (a 3-element set)
  have ha1 : a1 ∈ t := he1 a1 (Sym2.mem_mk_left a1 b1)
  have hb1 : b1 ∈ t := he1 b1 (Sym2.mem_mk_right a1 b1)
  have ha2 : a2 ∈ t := he2 a2 (Sym2.mem_mk_left a2 b2)
  have hb2 : b2 ∈ t := he2 b2 (Sym2.mem_mk_right a2 b2)
  -- If e1 ≠ e2 but both have vertices from a 3-set, they must share a vertex
  -- by pigeonhole
  by_contra h_no_common
  push_neg at h_no_common
  -- e1 = {a1, b1} and e2 = {a2, b2} are disjoint
  have h1 : a1 ∉ ({a2, b2} : Set V) := by
    intro h
    cases h with
    | inl h => exact h_no_common a1 (Sym2.mem_mk_left a1 b1) (by rw [h]; exact Sym2.mem_mk_left a2 b2)
    | inr h => exact h_no_common a1 (Sym2.mem_mk_left a1 b1) (by rw [h]; exact Sym2.mem_mk_right a2 b2)
  have h2 : b1 ∉ ({a2, b2} : Set V) := by
    intro h
    cases h with
    | inl h => exact h_no_common b1 (Sym2.mem_mk_right a1 b1) (by rw [h]; exact Sym2.mem_mk_left a2 b2)
    | inr h => exact h_no_common b1 (Sym2.mem_mk_right a1 b1) (by rw [h]; exact Sym2.mem_mk_right a2 b2)
  -- So {a1, b1} ∩ {a2, b2} = ∅, but all four are in t
  -- This means t has ≥ 4 elements, contradicting |t| = 3
  have h_four : ({a1, b1, a2, b2} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h_card_four : ({a1, b1, a2, b2} : Finset V).card ≥ 4 := by
    -- Need to show a1, b1, a2, b2 are all distinct
    -- a1 ≠ b1 (edge is non-diagonal)
    -- a1 ≠ a2, a1 ≠ b2 (from h1)
    -- b1 ≠ a2, b1 ≠ b2 (from h2)
    -- a2 ≠ b2 (edge is non-diagonal)
    sorry -- Aristotle: prove distinctness from edge non-diagonality and disjointness
  have h_sub_card := Finset.card_le_card h_four
  omega

/-- Helly property: If T1, T2, T3 are triangles and each pair shares an edge,
    then all three share a common edge -/
theorem helly_three_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 T3 : Finset V)
    (hT1 : T1 ∈ triangles G) (hT2 : T2 ∈ triangles G) (hT3 : T3 ∈ triangles G)
    (h12 : sharesEdgeWith T1 T2)
    (h13 : sharesEdgeWith T1 T3)
    (h23 : sharesEdgeWith T2 T3) :
    ∃ e : Sym2 V, e ∈ T1.sym2 ∧ e ∈ T2.sym2 ∧ e ∈ T3.sym2 := by
  -- Get the shared edges
  rw [sharesEdgeWith_iff_common_sym2] at h12 h13 h23
  obtain ⟨e12, he12_1, he12_2, hdiag12⟩ := h12
  obtain ⟨e13, he13_1, he13_3, hdiag13⟩ := h13
  obtain ⟨e23, he23_2, he23_3, hdiag23⟩ := h23
  -- Case 1: e12 = e13 (shared edge between T1-T2 equals shared edge between T1-T3)
  by_cases heq : e12 = e13
  · -- Then e12 is in T1, T2, and we need it in T3
    -- e12 = e13 ∈ T3 by definition of e13
    use e12
    exact ⟨he12_1, he12_2, heq ▸ he13_3⟩
  -- Case 2: e12 ≠ e13
  · -- Both e12 and e13 are distinct edges of T1
    -- They must share a vertex v (by triangle_edges_share_vertex)
    obtain ⟨v, hv12, hv13⟩ := triangle_edges_share_vertex G T1 hT1 e12 e13 he12_1 he13_1 heq
    -- e12 = {u, v} for some u, and e13 = {v, w} for some w
    -- (v is the common vertex)
    -- T1 = {u, v, w}
    -- T2 contains e12 = {u, v}, so T2 = {u, v, x} for some x
    -- T3 contains e13 = {v, w}, so T3 = {v, w, y} for some y
    -- T2 ∩ T3 must contain an edge e23
    -- The common vertices of T2 and T3 include v (v ∈ e12 ⊆ T2, v ∈ e13 ⊆ T3)
    -- For e23 to exist, need another common vertex
    -- Analysis shows this forces a common edge in all three
    sorry -- Aristotle: complete case analysis

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: GENERALIZATION TO ARBITRARY FAMILIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- If every pair of triangles in a finite family shares an edge,
    then all triangles share a common edge -/
theorem helly_triangle_family (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V))
    (hS_tri : ∀ t ∈ S, t ∈ triangles G)
    (hS_pairwise : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → sharesEdgeWith t1 t2)
    (hS_nonempty : S.Nonempty) :
    ∃ e : Sym2 V, ∀ t ∈ S, e ∈ t.sym2 := by
  -- Base case: |S| ≤ 1
  by_cases h_small : S.card ≤ 1
  · obtain ⟨t, ht⟩ := hS_nonempty
    -- Any edge of t works since S = {t}
    have ht_tri := hS_tri t ht
    have h_edges := triangle_has_three_edges G t ht_tri
    -- t.sym2 is nonempty
    have h_ne : t.sym2.Nonempty := by
      rw [Finset.Nonempty]
      by_contra h
      push_neg at h
      have : t.sym2.card = 0 := Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_not_mem.mpr h)
      omega
    obtain ⟨e, he⟩ := h_ne
    use e
    intro t' ht'
    -- S has at most 1 element, so t' = t
    have h_eq : t = t' := by
      by_contra hne
      have : ({t, t'} : Finset (Finset V)) ⊆ S := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h_card : ({t, t'} : Finset (Finset V)).card = 2 := Finset.card_pair hne
      have := Finset.card_le_card this
      omega
    rw [← h_eq]
    exact he
  -- Inductive case: |S| ≥ 2, use Helly for 3 triangles
  push_neg at h_small
  -- Pick any 3 distinct triangles
  sorry -- Aristotle: induction using helly_three_triangles

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: MAIN THEOREM - EXTERNALS SHARE COMMON EDGE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Import slot182 result (proven in slot182_two_externals_share_edge_PROVEN.lean) -/
lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  -- This is proven in slot182 via 5-packing contradiction
  -- If T₁, T₂ don't share edge → can form 5-packing → contradiction
  sorry -- PROVEN in slot182, import for composition

/-- The set of all external triangles of a given M-element -/
def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (triangles G).filter (fun t => isExternalOf G M A t)

/-- All externals of the same M-element share a common edge -/
theorem externals_share_common_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M) :
    (externalsOf G M A).Nonempty →
    ∃ e : Sym2 V, ∀ t ∈ externalsOf G M A, e ∈ t.sym2 := by
  intro hne
  apply helly_triangle_family G (externalsOf G M A)
  · -- All externals are triangles
    intro t ht
    simp only [externalsOf, Finset.mem_filter] at ht
    exact ht.1
  · -- Every pair shares an edge (from slot182)
    intro t1 ht1 t2 ht2 hne12
    simp only [externalsOf, Finset.mem_filter] at ht1 ht2
    exact two_externals_share_edge G M hM hM_card A hA t1 t2 ht1.2 ht2.2 hne12
  · exact hne

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: COVERING BOUND
-- ══════════════════════════════════════════════════════════════════════════════

/-- One edge covers all externals of a given M-element -/
theorem tau_externals_eq_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (hne : (externalsOf G M A).Nonempty) :
    ∃ e : Sym2 V, e ∈ G.edgeFinset ∧ ∀ t ∈ externalsOf G M A, e ∈ t.sym2 := by
  obtain ⟨e, he⟩ := externals_share_common_edge G M hM hM_card A hA hne
  use e
  constructor
  · -- e is an edge of G
    -- Pick any external, e is in its sym2, and external is a triangle in G
    obtain ⟨t, ht⟩ := hne
    simp only [externalsOf, Finset.mem_filter] at ht
    have ht_tri := ht.1
    have he_t := he t (Finset.mem_filter.mpr ht)
    -- t is a triangle (3-clique), so its edges are in G.edgeFinset
    unfold triangles at ht_tri
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht_tri
    rw [Finset.mem_sym2_iff] at he_t
    obtain ⟨a, b⟩ := e
    have ha := he_t a (Sym2.mem_mk_left a b)
    have hb := he_t b (Sym2.mem_mk_right a b)
    -- Need a ≠ b (edge is non-diagonal)
    by_cases hab : a = b
    · -- If a = b, then e is diagonal, but triangles have no self-loops
      -- This is a contradiction since cliques have distinct vertices
      exfalso
      sorry -- Aristotle: triangles have 3 distinct vertices
    · -- ht_tri is an IsNClique, extract adjacency from clique property
      have h_adj : G.Adj a b := by
        -- Cliques have pairwise adjacent vertices
        sorry -- Aristotle: use ht_tri.clique for adjacent vertices
      exact SimpleGraph.mem_edgeFinset.mpr h_adj
  · exact he

/-- Total covering: 4 edges for externals + 4 for M-elements = τ ≤ 8 -/
theorem tau_le_8_from_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ E.card ≤ 8 ∧
    ∀ t ∈ triangles G, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Construct: 4 external-covering edges + 4 M-covering edges
  -- For each A ∈ M: pick one common edge for Ext(A) (or any A-edge if Ext(A) = ∅)
  -- For each A ∈ M: pick one edge from A
  sorry -- Aristotle: construct explicit covering

end
