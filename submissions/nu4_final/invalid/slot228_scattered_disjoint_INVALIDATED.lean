/-
  slot228_scattered_disjoint.lean

  TAU ≤ 8 FOR SCATTERED CASE (No Shared Vertices)

  This is the EASIEST case for ν=4. When M = {A, B, C, D} are pairwise
  vertex-disjoint, there are NO bridges and each M-element's triangles
  are independent.

  Strategy:
  - Each M-element A needs ≤ 2 edges to cover A and all its externals
  - 4 M-elements × 2 edges = 8 total
  - This avoids ALL false patterns (6, 9, 17, 20, 22) since there are no shared vertices!

  Confidence: 85%
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot139 PROVEN)
-- ═══════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ═══════════════════════════════════════════════════════════════════════════
-- SCATTERED CONFIGURATION
-- ═══════════════════════════════════════════════════════════════════════════

/-- Scattered: All M-elements are pairwise vertex-disjoint -/
def isScattered (M : Finset (Finset V)) : Prop :=
  ∀ A B : Finset V, A ∈ M → B ∈ M → A ≠ B → A ∩ B = ∅

-- ═══════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot139)
-- ═══════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  by_contra h_no_share
  push_neg at h_no_share
  have h_packing : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · intro s hs
      simp only [Finset.mem_union, Finset.mem_singleton] at hs
      cases hs with
      | inl h => exact hM.1.1 h
      | inr h => rw [h]; exact ht
    · intro s1 hs1 s2 hs2 hne
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
  exact hM.2 t ht h_not_mem

-- ═══════════════════════════════════════════════════════════════════════════
-- KEY INSIGHT: In scattered case, each external belongs to exactly ONE M-element
-- ═══════════════════════════════════════════════════════════════════════════

lemma scattered_unique_M_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (h_scattered : isScattered M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M) :
    ∃! A : Finset V, A ∈ M ∧ (t ∩ A).card ≥ 2 := by
  obtain ⟨A, hA_mem, hA_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  use A
  constructor
  · exact ⟨hA_mem, hA_share⟩
  · intro B ⟨hB_mem, hB_share⟩
    by_contra hAB
    -- If A ≠ B, then A ∩ B = ∅ by scattered
    have h_disjoint := h_scattered A B hA_mem hB_mem hAB
    -- t shares ≥2 vertices with A and ≥2 with B
    -- But A ∩ B = ∅, so t must have ≥4 vertices. Contradiction!
    have hA_two : ∃ a1 a2 : V, a1 ∈ t ∩ A ∧ a2 ∈ t ∩ A ∧ a1 ≠ a2 := by
      obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.mp hA_share
      exact ⟨a1, a2, ha1, ha2, hne⟩
    have hB_two : ∃ b1 b2 : V, b1 ∈ t ∩ B ∧ b2 ∈ t ∩ B ∧ b1 ≠ b2 := by
      obtain ⟨b1, hb1, b2, hb2, hne⟩ := Finset.one_lt_card.mp hB_share
      exact ⟨b1, b2, hb1, hb2, hne⟩
    obtain ⟨a1, a2, ha1, ha2, hne_a⟩ := hA_two
    obtain ⟨b1, b2, hb1, hb2, hne_b⟩ := hB_two
    -- a1, a2 ∈ A, b1, b2 ∈ B, and A ∩ B = ∅
    -- So {a1, a2} ∩ {b1, b2} = ∅
    have ha1_not_B : a1 ∉ B := by
      intro ha1_B
      have : a1 ∈ A ∩ B := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha1).2, ha1_B⟩
      rw [h_disjoint] at this
      exact Finset.not_mem_empty a1 this
    have ha2_not_B : a2 ∉ B := by
      intro ha2_B
      have : a2 ∈ A ∩ B := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha2).2, ha2_B⟩
      rw [h_disjoint] at this
      exact Finset.not_mem_empty a2 this
    -- So a1 ≠ b1, a1 ≠ b2, a2 ≠ b1, a2 ≠ b2
    have h_all_in_t : a1 ∈ t ∧ a2 ∈ t ∧ b1 ∈ t ∧ b2 ∈ t := by
      exact ⟨(Finset.mem_inter.mp ha1).1, (Finset.mem_inter.mp ha2).1,
             (Finset.mem_inter.mp hb1).1, (Finset.mem_inter.mp hb2).1⟩
    -- t has card 3, but we claim 4 distinct elements
    have h_card_t : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at ht
      exact ht.2
    -- We have a1 ≠ a2 and b1, b2 ∉ {a1, a2} ∩ B = ∅ means b1, b2 ≠ a1, a2
    -- But we only need 3 distinct elements... actually one of b1, b2 could equal a1 or a2
    -- Wait, a1 ∈ A means a1 ∉ B (since A ∩ B = ∅). And b1 ∈ B.
    -- So a1 ≠ b1. Similarly a1 ≠ b2, a2 ≠ b1, a2 ≠ b2.
    have h_a1_ne_b1 : a1 ≠ b1 := by
      intro heq; subst heq
      exact ha1_not_B (Finset.mem_inter.mp hb1).2
    have h_a1_ne_b2 : a1 ≠ b2 := by
      intro heq; subst heq
      exact ha1_not_B (Finset.mem_inter.mp hb2).2
    have h_a2_ne_b1 : a2 ≠ b1 := by
      intro heq; subst heq
      exact ha2_not_B (Finset.mem_inter.mp hb1).2
    have h_a2_ne_b2 : a2 ≠ b2 := by
      intro heq; subst heq
      exact ha2_not_B (Finset.mem_inter.mp hb2).2
    -- Now: a1 ≠ a2, a1 ≠ b1, a1 ≠ b2, a2 ≠ b1, a2 ≠ b2, b1 ≠ b2
    -- So {a1, a2, b1, b2} has 4 distinct elements, all in t
    -- But t.card = 3, contradiction
    have h_four : ({a1, a2, b1, b2} : Finset V).card ≥ 4 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
          Finset.card_insert_of_not_mem, Finset.card_singleton]
      · simp
      · simp [hne_b]
      · simp [h_a2_ne_b1, h_a2_ne_b2]
      · simp [hne_a, h_a1_ne_b1, h_a1_ne_b2]
    have h_subset : {a1, a2, b1, b2} ⊆ t := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h_all_in_t.1
      · exact h_all_in_t.2.1
      · exact h_all_in_t.2.2.1
      · exact h_all_in_t.2.2.2
    have := Finset.card_le_card h_subset
    omega

-- ═══════════════════════════════════════════════════════════════════════════
-- THE KEY LEMMA (1 SORRY)
-- ═══════════════════════════════════════════════════════════════════════════

/--
  In the scattered case, 2 edges from each M-element suffice to cover
  that M-element and all its externals.

  Proof sketch:
  - A = {a, b, c} is a triangle
  - Any external T of A shares edge with A, so T contains two of {a, b, c}
  - Pick edges {a, b} and {b, c}
  - Case 1: T contains a and b → covered by {a, b}
  - Case 2: T contains b and c → covered by {b, c}
  - Case 3: T contains a and c → T = {a, c, x} for some x
    - By maximality, T shares edge with some M-element
    - By scattered uniqueness, T shares edge only with A
    - So T uses edge {a, c} from A
    - Wait, {a, b} and {b, c} don't cover {a, c}...

  Actually need to be smarter: use {a, b} and {a, c}.
  Then any T with ≥2 vertices from {a, b, c} contains a.
  - If T contains a, b: covered by {a, b}
  - If T contains a, c: covered by {a, c}
  - If T contains b, c only: T = {b, c, x}
    - But wait, T is a triangle, A = {a, b, c} is a triangle
    - If T shares exactly {b, c} with A, that's still ≥2 vertices...

  The 2-edge claim is CORRECT: pick any vertex v ∈ A and take the two edges
  incident to v in A. Any triangle sharing ≥2 vertices with A must contain v
  or both other vertices. But if it contains both other vertices without v,
  that's exactly the edge opposite to v in A, which needs to be covered...

  Hmm, actually we might need all 3 edges of A. Let me reconsider.

  Wait, for externals T ∉ M: T shares edge with A means (T ∩ A).card ≥ 2.
  So T contains at least 2 of {a, b, c}.
  The 3 possible pairs are {a,b}, {b,c}, {a,c}.
  We need to cover all triangles containing any of these pairs.
  That's exactly "pick 2 edges of A" as long as the 2 edges cover all 3 pairs.
  But 2 edges only span 2 pairs directly...

  Actually: if we pick {a,b} and {b,c}, we cover:
  - All triangles containing edge {a,b}
  - All triangles containing edge {b,c}
  - But triangles containing only {a,c} are NOT covered!

  So we need 3 edges per M-element? That gives 12 total, not 8.

  BUT: the question is whether triangles T with (T ∩ A).card ≥ 2 that use
  edge {a, c} exist. For T to use {a, c}:
  - T = {a, c, x} for some x ∉ A
  - T must be a triangle in G (edges {a,c}, {a,x}, {c,x} all in G)

  The key insight: by the fan structure (slot182, slot224f), all externals
  of A share a common apex x. So all externals using different edges of A
  pass through x. Therefore, edge {b, x} covers all externals using edge {a,c}!

  Wait, but {b, x} is not in A... This might still give 8 edges total though:
  4 M-edges (one per M-element) + 4 fan-apex edges.

  Actually, in scattered case, we CAN use fan apex edges freely since
  there are no cross-M-element complications (Pattern 22 doesn't apply).

  Let me reconsider: for scattered case, we pick per M-element A:
  - 1 M-edge from A
  - 1 fan-apex edge {b, x_A} where x_A is the fan apex of A

  These 2 edges cover A (via the M-edge) and all externals (via fan structure).
  Total: 4 × 2 = 8.

  This is the correct argument!
-/
lemma two_edges_per_M_element_scattered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_scattered : isScattered M)
    (A : Finset V) (hA : A ∈ M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    ∃ E_A : Finset (Sym2 V), E_A.card ≤ 2 ∧ E_A ⊆ G.edgeFinset ∧
      ∀ t ∈ G.cliqueFinset 3, (t ∩ A).card ≥ 2 → ∃ e ∈ E_A, e ∈ t.sym2 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 FOR SCATTERED
-- ═══════════════════════════════════════════════════════════════════════════

theorem tau_le_8_scattered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_scattered : isScattered M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    triangleCoveringNumber G ≤ 8 := by
  -- For each M-element, get a 2-edge cover of its triangles
  have h_covers : ∀ A ∈ M, ∃ E_A : Finset (Sym2 V), E_A.card ≤ 2 ∧ E_A ⊆ G.edgeFinset ∧
      ∀ t ∈ G.cliqueFinset 3, (t ∩ A).card ≥ 2 → ∃ e ∈ E_A, e ∈ t.sym2 := by
    intro A hA
    exact two_edges_per_M_element_scattered G M hM hM_card h_scattered A hA hν
  -- Construct the union of all E_A
  choose E_A h_E_A using h_covers
  let E := M.biUnion E_A
  -- Show E.card ≤ 8
  have h_card : E.card ≤ 8 := by
    calc E.card = (M.biUnion E_A).card := rfl
      _ ≤ ∑ A in M, (E_A A (by exact Finset.mem_of_mem_filter A (Finset.filter_subset _ M))).card := by
        apply Finset.card_biUnion_le
      _ ≤ ∑ _ in M, 2 := by
        apply Finset.sum_le_sum
        intro A hA
        exact (h_E_A A hA).1
      _ = 2 * M.card := by ring
      _ = 2 * 4 := by rw [hM_card]
      _ = 8 := by norm_num
  -- Show E covers all triangles
  have h_cover : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
    intro t ht
    obtain ⟨A, hA_mem, hA_share⟩ := triangle_shares_edge_with_packing G M hM t ht
    obtain ⟨e, he_in_EA, he_in_t⟩ := (h_E_A A hA_mem).2.2 t ht hA_share
    exact ⟨e, Finset.mem_biUnion.mpr ⟨A, hA_mem, he_in_EA⟩, he_in_t⟩
  -- Show E ⊆ G.edgeFinset
  have h_subset : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨A, hA_mem, he_in_EA⟩ := Finset.mem_biUnion.mp he
    exact (h_E_A A hA_mem).2.1 he_in_EA
  -- Conclude τ ≤ 8
  have h_valid : isTriangleCover G E := ⟨h_subset, h_cover⟩
  have h_in : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_subset, h_valid⟩
  unfold triangleCoveringNumber
  have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨E, h_in⟩
  have h_in_image : E.card ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card :=
    Finset.mem_image_of_mem _ h_in
  have h_min_le := Finset.min'_le _ E.card h_in_image
  calc (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0
      ≤ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min'
          (Finset.Nonempty.image h_nonempty _) := by
        simp only [Finset.min_eq_min']
        rfl
    _ ≤ E.card := h_min_le
    _ ≤ 8 := h_card

end
