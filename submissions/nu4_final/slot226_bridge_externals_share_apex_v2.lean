/-
  slot226_bridge_externals_share_apex_v2.lean

  THE MAKE-OR-BREAK LEMMA FOR τ ≤ 8

  Question: Do externals of A and externals of B at shared vertex v share a common apex?

  ═══════════════════════════════════════════════════════════════════════════════
  MATHEMATICAL ANALYSIS (Gemini, Jan 4, 2026)
  ═══════════════════════════════════════════════════════════════════════════════

  Setup:
  - M = {A, B, C, D} is a maximal 4-packing in cycle_4 configuration
  - A ∩ B = {v} (shared vertex)
  - A = {v, a₁, a₂}, B = {v, b₁, b₂}
  - T₁ = {v, a, x₁} is external of A (a ∈ {a₁, a₂}, x₁ ∉ A ∪ B ∪ C ∪ D)
  - T₂ = {v, b, x₂} is external of B (b ∈ {b₁, b₂}, x₂ ∉ A ∪ B ∪ C ∪ D)

  Question: Must x₁ = x₂?

  Pattern 6 Counterexample (Dec 29):
  - A = {0,1,2}, B = {0,3,4}, v = 0
  - T₁ = {0,1,5}, T₂ = {0,3,6}
  - x₁ = 5, x₂ = 6, so x₁ ≠ x₂

  BUT: Pattern 6 may not have ν = 4! We need to verify the entire graph.

  ═══════════════════════════════════════════════════════════════════════════════
  KEY PROOF STRATEGY: CROSS-M-ELEMENT 5-PACKING
  ═══════════════════════════════════════════════════════════════════════════════

  The slot182 argument builds {T₁, T₂, B, C, D} (replacing A with two externals).
  This gives 5 elements, contradicting ν = 4.

  BUT: That requires T₁ and T₂ to be externals of the SAME M-element A.

  For cross-M-element externals, we need a different approach:

  APPROACH 1: Use THIRD external
  - If T₁ is external of A with apex x₁
  - And T₂ is external of B with apex x₂
  - And x₁ ≠ x₂
  - Consider T₃ = {v, b, x₁} (if this triangle exists!)
    - T₃ would be external of B with apex x₁
    - Then T₂ and T₃ are both externals of B with different apexes
    - By slot224f, T₂ and T₃ must share an external vertex
    - But their external vertices are x₂ and x₁, which are different!
    - Contradiction ONLY IF T₃ exists in G

  APPROACH 2: Use graph structure
  - T₁ = {v, a, x₁}, T₂ = {v, b, x₂}
  - T₁ ∩ T₂ = {v} if x₁ ≠ x₂ and a ≠ b (likely since a ∈ A, b ∈ B, A ∩ B = {v})
  - Also a ≠ x₂ (since a ∈ A and x₂ ∉ A by definition of external)
  - Also b ≠ x₁ (since b ∈ B and x₁ ∉ B)
  - So T₁ ∩ T₂ = {v} (only vertex v in common)
  - T₁ and T₂ are edge-disjoint!

  APPROACH 3: Consider {T₁, T₂, C, D} as potential extension
  - T₁ ∩ T₂ ⊆ {v} (if x₁ ≠ x₂)
  - T₁ ∩ C: T₁ doesn't share edge with C (external of A only)
  - T₁ ∩ D: T₁ doesn't share edge with D (external of A only)
  - Similarly for T₂
  - So {T₁, T₂, C, D} is a valid 4-packing
  - This doesn't contradict ν = 4... unless we can add a 5th!

  CRITICAL INSIGHT:
  - The question is: can we find a 5th triangle to add?
  - Since M was MAXIMAL, every triangle outside M shares an edge with some M-element
  - A is replaced by T₁ (which shares edge with A)
  - B is replaced by T₂ (which shares edge with B)
  - So any triangle that would extend M might now extend {T₁, T₂, C, D}

  Actually: If x₁ ≠ x₂, consider triangle A itself!
  - A = {v, a₁, a₂}
  - A ∩ T₁: shares edge {v, a} where a ∈ {a₁, a₂}
  - A ∩ T₂ = {v} (only v, since T₂ uses B-vertices)
  - A ∩ C: ≤ 1 (since M is a packing)
  - A ∩ D: = {v_DA} ≠ v (in cycle_4)

  Wait, v = v_AB, but v_DA ∈ A too. So A might share edge with D if v_DA ∈ T₂...
  This is getting complicated. Let me just set up the scaffolding for Aristotle.

  ═══════════════════════════════════════════════════════════════════════════════
  ACTUAL PROOF APPROACH FOR ARISTOTLE
  ═══════════════════════════════════════════════════════════════════════════════

  Assume x₁ ≠ x₂. Then:
  1. T₁ ∩ T₂ = {v} (edge-disjoint)
  2. Since T₁ is in G, the triangle {v, b, x₁} might exist in G (if edges {v,b}, {b,x₁}, {v,x₁} exist)
  3. If {v, b, x₁} exists and is in G, it's an external of B (shares {v,b} with B, doesn't share edge with A,C,D)
  4. Then T₂ = {v, b, x₂} and T₃ = {v, b, x₁} are both externals of B with same edge {v,b}
  5. By slot182, T₂ and T₃ share an edge
  6. But T₂ = {v, b, x₂} and T₃ = {v, b, x₁} share edge {v,b}! ✓

  Hmm, that doesn't give us a contradiction directly.

  Let me try: T₂ uses edge {v, b} from B. T₃ = {v, b, x₁} uses SAME edge {v,b}.
  So T₂ and T₃ use the SAME edge of B, meaning slot224f's "different edges" case doesn't apply.

  What if T₁ uses edge {v, a} and some OTHER external T₁' uses edge {a₁, a₂}?
  Then T₁ and T₁' use different A-edges, so by slot224f they share an external vertex.

  OK, the cleanest approach: The lemma may be FALSE. Let Aristotle verify or find counterexample.

  The key gap: Externals of DIFFERENT M-elements don't obviously share apexes.
  We've only proven that externals of the SAME M-element share an edge (slot182),
  and externals using DIFFERENT edges of same M-element share an external vertex (slot224f).

  ═══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot224f PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

/-- T is an external of A if it shares an edge with A and with NO other M-element. -/
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot182, slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  have hu_inter : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu_m⟩
  have hv_inter : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv_m⟩
  exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact h_not_share ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  have ht_3 : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht_ext.1 |>.2
  have hB_3 : B.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hB) |>.2
  exact not_share_implies_one_vertex t B ht_3 hB_3 (ht_ext.2.2.2 B hB hAB.symm)

lemma edge_disjoint_implies_one_vertex (T₁ T₂ : Finset V)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    (T₁ ∩ T₂).card ≤ 1 := by
  have h_not_share : ¬sharesEdgeWith T₁ T₂ := fun ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩ =>
    h_edge_disj u v huv hu₁ hv₁ hu₂ hv₂
  exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- 5-PACKING CONSTRUCTION (from slot182)
-- ══════════════════════════════════════════════════════════════════════════════

theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M' := by
  let M_minus_A := M.erase A
  let M' := {T₁, T₂} ∪ M_minus_A
  use M'
  have hT₁_not_M : T₁ ∉ M := hT₁.2.1
  have hT₂_not_M : T₂ ∉ M := hT₂.2.1
  have hM_minus_A_card : M_minus_A.card = 3 := by rw [Finset.card_erase_of_mem hA]; omega
  have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
  have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
  constructor
  · have hT₁_not_MA : T₁ ∉ M_minus_A := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MA : T₂ ∉ M_minus_A := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem]; simp [hT₁_ne_T₂]; simp [hT₁_ne_T₂]
    have h_disj : Disjoint {T₁, T₂} M_minus_A := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact fun h => hT₁_not_MA (h ▸ hy);
                                    exact fun h => hT₂_not_MA (h ▸ hy)]
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_A_card]
  · constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht_pair | ht_MA
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MA).2
    · intro t₁ ht₁ t₂ ht₂ h_ne
      rcases Finset.mem_union.mp ht₁ with ht₁_pair | ht₁_MA <;>
      rcases Finset.mem_union.mp ht₂ with ht₂_pair | ht₂_MA
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne
          · rw [Finset.mem_singleton] at ht₂_sing; rw [heq₁, ht₂_sing]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂, Finset.inter_comm]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne
      · have hB_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        have hB_ne_A : t₂ ≠ A := (Finset.mem_erase.mp ht₂_MA).1
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]; exact external_intersects_other_le_1 G M hM A t₂ hB_M hB_ne_A.symm T₁ hT₁
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          exact external_intersects_other_le_1 G M hM A t₂ hB_M hB_ne_A.symm T₂ hT₂
      · have hB_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have hB_ne_A : t₁ ≠ A := (Finset.mem_erase.mp ht₁_MA).1
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂, Finset.inter_comm]
          exact external_intersects_other_le_1 G M hM A t₁ hB_M hB_ne_A.symm T₁ hT₁
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing, Finset.inter_comm]
          exact external_intersects_other_le_1 G M hM A t₁ hB_M hB_ne_A.symm T₂ hT₂
      · exact hM.1.2 (Finset.mem_erase.mp ht₁_MA).2 (Finset.mem_erase.mp ht₂_MA).2 h_ne

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Two externals of SAME M-element share an edge (from slot182)
-- ══════════════════════════════════════════════════════════════════════════════

theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  have h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False :=
    fun u v huv hu₁ hv₁ hu₂ hv₂ => h_no_edge ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_edge_disj
  have h_bound := hν M' hM'_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Unique outside vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_has_unique_outside_vertex (T A : Finset V)
    (hT_3 : T.card = 3) (hTA : (T ∩ A).card = 2) :
    ∃! x, x ∈ T ∧ x ∉ A := by
  have h_diff : (T \ A).card = 1 := by
    have := Finset.card_sdiff_add_card_inter T A
    omega
  rw [Finset.card_eq_one] at h_diff
  obtain ⟨x, hx_eq⟩ := h_diff
  use x
  constructor
  · have hx_mem : x ∈ T \ A := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    exact ⟨Finset.mem_sdiff.mp hx_mem |>.1, Finset.mem_sdiff.mp hx_mem |>.2⟩
  · intro y ⟨hy_T, hy_not_A⟩
    have : y ∈ T \ A := Finset.mem_sdiff.mpr ⟨hy_T, hy_not_A⟩
    rw [hx_eq] at this
    exact Finset.mem_singleton.mp this

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External intersection with its M-element is exactly 2
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_inter_M_card_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_3 : T.card = 3) :
    (T ∩ A).card = 2 := by
  have h_ge : (T ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T A hT.2.2.1
  have h_le : (T ∩ A).card ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h_sub : T ⊆ A := by
      have h_inter_sub : T ∩ A ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ A).card = T.card := by
        have h1 : (T ∩ A).card ≤ T.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.2
    have h_sub' : A ⊆ T := by
      have h_inter_sub : T ∩ A ⊆ A := Finset.inter_subset_right
      have h_card_eq : (T ∩ A).card = A.card := by
        have h1 : (T ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.1
    have h_eq : T = A := Finset.Subset.antisymm h_sub h_sub'
    exact hT.2.1 (h_eq ▸ hA)
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: If T is external of A at vertex v, T = {v, a, x} for some a ∈ A, x ∉ A
-- ══════════════════════════════════════════════════════════════════════════════

/-- Extract the "apex" (external vertex) of an external triangle -/
lemma external_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_3 : T.card = 3) :
    ∃ x : V, x ∈ T ∧ x ∉ A ∧ ∀ y ∈ T, y ∉ A → y = x := by
  have h_inter := external_inter_M_card_eq_2 G M hM A hA hA_3 T hT hT_3
  obtain ⟨x, ⟨hx_T, hx_not_A⟩, hx_unique⟩ := external_has_unique_outside_vertex T A hT_3 h_inter
  exact ⟨x, hx_T, hx_not_A, fun y hy_T hy_not_A => hx_unique y ⟨hy_T, hy_not_A⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External of A containing v shares edge {v, a} with A for some a ∈ A
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_at_v_uses_edge_with_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T : Finset V) (hT : isExternalOf G M A T) (hT_3 : T.card = 3)
    (v : V) (hv_T : v ∈ T) (hv_A : v ∈ A) :
    ∃ a ∈ A, a ≠ v ∧ a ∈ T := by
  -- T ∩ A has 2 elements, one of which is v
  have h_inter := external_inter_M_card_eq_2 G M hM A hA hA_3 T hT hT_3
  have hv_inter : v ∈ T ∩ A := Finset.mem_inter.mpr ⟨hv_T, hv_A⟩
  -- Since |T ∩ A| = 2 and v ∈ T ∩ A, there's another element a ∈ T ∩ A
  have h_two := Finset.card_eq_two.mp h_inter
  obtain ⟨a, b, hab, h_eq⟩ := h_two
  rw [h_eq] at hv_inter
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv_inter
  cases hv_inter with
  | inl hv_a =>
    use b
    constructor
    · have : b ∈ {a, b} := Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
      rw [← h_eq] at this
      exact Finset.mem_inter.mp this |>.2
    constructor
    · exact fun h => hab (hv_a.trans h.symm)
    · have : b ∈ {a, b} := Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
      rw [← h_eq] at this
      exact Finset.mem_inter.mp this |>.1
  | inr hv_b =>
    use a
    constructor
    · have : a ∈ {a, b} := Finset.mem_insert.mpr (Or.inl rfl)
      rw [← h_eq] at this
      exact Finset.mem_inter.mp this |>.2
    constructor
    · exact fun h => hab (h.trans hv_b.symm)
    · have : a ∈ {a, b} := Finset.mem_insert.mpr (Or.inl rfl)
      rw [← h_eq] at this
      exact Finset.mem_inter.mp this |>.1

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: T₁ external of A at v, T₂ external of B at v, A ∩ B = {v}
-- Then T₁ ∩ A and T₂ ∩ B intersect only at v
-- ══════════════════════════════════════════════════════════════════════════════

lemma cross_external_M_edges_disjoint_except_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (hA_3 : A.card = 3) (hB_3 : B.card = 3)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (h_inter_AB : A ∩ B = {v}) :
    ∀ a b, a ∈ A → a ≠ v → b ∈ B → b ≠ v → a ≠ b := by
  intro a b ha ha_ne_v hb hb_ne_v h_eq
  -- If a = b, then a ∈ A ∩ B, but A ∩ B = {v} and a ≠ v
  have ha_inter : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, h_eq ▸ hb⟩
  rw [h_inter_AB] at ha_inter
  simp only [Finset.mem_singleton] at ha_inter
  exact ha_ne_v ha_inter

-- ══════════════════════════════════════════════════════════════════════════════
-- CROSS-M-ELEMENT 5-PACKING CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/--
  If T₁ is external of A, T₂ is external of B, and T₁ ∩ T₂ has ≤ 1 vertex,
  then {T₁, T₂, A, C, D} is a 5-packing (replacing B with T₂).

  Wait, that's not quite right. Let's think carefully:
  - T₁ shares edge with A (by definition of external)
  - T₂ doesn't share edge with A (by definition of external of B)

  So {T₁, T₂, A, C, D} has T₁ ∩ A ≥ 2, not a valid packing!

  The correct construction: {T₁, T₂, C, D, ???}
  But that's only 4 elements...

  KEY INSIGHT: We need to leverage that T₁ and T₂ are edge-disjoint (if x₁ ≠ x₂).
  Consider building {A, T₂, C, D} (dropping B, adding T₂):
  - A ∩ T₂: T₂ is external of B, so T₂ ∩ A ≤ 1 (since T₂ doesn't share edge with A)
  - T₂ ∩ C: T₂ is external of B, so T₂ ∩ C ≤ 1 (since T₂ doesn't share edge with C)
  - T₂ ∩ D: T₂ is external of B, so T₂ ∩ D ≤ 1 (since T₂ doesn't share edge with D)
  - A ∩ C ≤ 1, A ∩ D ≤ 1, C ∩ D ≤ 1 (from M being a packing)

  So {A, T₂, C, D} is a 4-packing. This doesn't contradict ν = 4!

  What we need: Find a FIFTH triangle to add to {A, T₂, C, D}.
  If such a fifth exists, we get ν ≥ 5, contradicting ν = 4.

  Candidate: Since M was maximal, and we dropped B to get {A, T₂, C, D},
  maybe B itself can be added? But B shares edge with A and C...

  Actually: Consider T₁. Can we add T₁ to {A, T₂, C, D}?
  - T₁ ∩ A: T₁ shares edge with A, so T₁ ∩ A ≥ 2. NOT VALID!

  So T₁ cannot be added to {A, T₂, C, D}. The replacement doesn't give 5-packing.

  ALTERNATIVE: What if we replace BOTH A and B?
  {T₁, T₂, C, D} is a 4-packing:
  - T₁ ∩ T₂: Need to show this is ≤ 1 (this is our goal - if x₁ ≠ x₂, then ≤ 1)
  - T₁ ∩ C: T₁ is external of A, so T₁ doesn't share edge with C → ≤ 1
  - T₁ ∩ D: T₁ is external of A, so T₁ doesn't share edge with D → ≤ 1
  - T₂ ∩ C: T₂ is external of B, so T₂ doesn't share edge with C → ≤ 1
  - T₂ ∩ D: T₂ is external of B, so T₂ doesn't share edge with D → ≤ 1
  - C ∩ D ≤ 1 (from M being a packing)

  So if T₁ ∩ T₂ ≤ 1, then {T₁, T₂, C, D} is a 4-packing.
  This still doesn't contradict ν = 4.

  FINAL APPROACH: Can we add A or B back to {T₁, T₂, C, D}?
  - A ∩ T₁ ≥ 2 (shares edge) → Cannot add A
  - B ∩ T₂ ≥ 2 (shares edge) → Cannot add B

  What about adding a DIFFERENT M-element?
  - A ∩ C ≤ 1 (from M packing) → Could add A to {T₂, C, D}... wait, that's {A, T₂, C, D}

  I think the issue is: replacing two adjacent M-elements with their externals
  doesn't increase the packing size.

  NEW APPROACH: Maybe we need to consider THREE externals.
-/

-- This intermediate lemma shows that {T₁, T₂, C, D} is a valid 4-packing
-- when T₁, T₂ are externals of different adjacent M-elements and are edge-disjoint
theorem four_packing_from_cross_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V)
    (hA : A ∈ M) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hM_eq : M = {A, B, C, D})
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_edge_disj : (T₁ ∩ T₂).card ≤ 1) :
    isTrianglePacking G {T₁, T₂, C, D} := by
  constructor
  · -- All elements are triangles
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hT₁.1
    · exact hT₂.1
    · exact hM.1.1 hC
    · exact hM.1.1 hD
  · -- Pairwise intersection ≤ 1
    intro t₁ ht₁ t₂ ht₂ h_ne
    simp only [Finset.coe_insert, Finset.coe_singleton,
               Set.mem_insert_iff, Set.mem_singleton_iff] at ht₁ ht₂
    rcases ht₁ with rfl | rfl | rfl | rfl <;> rcases ht₂ with rfl | rfl | rfl | rfl
    -- 16 cases, but only 6 are distinct pairs
    · exact absurd rfl h_ne
    · exact h_edge_disj  -- T₁ ∩ T₂ ≤ 1 (hypothesis)
    · exact external_intersects_other_le_1 G M hM A C hC hAC T₁ hT₁  -- T₁ ∩ C ≤ 1
    · exact external_intersects_other_le_1 G M hM A D hD hAD T₁ hT₁  -- T₁ ∩ D ≤ 1
    · rw [Finset.inter_comm]; exact h_edge_disj  -- T₂ ∩ T₁ ≤ 1
    · exact absurd rfl h_ne
    · exact external_intersects_other_le_1 G M hM B C hC hBC T₂ hT₂  -- T₂ ∩ C ≤ 1
    · exact external_intersects_other_le_1 G M hM B D hD hBD T₂ hT₂  -- T₂ ∩ D ≤ 1
    · rw [Finset.inter_comm]; exact external_intersects_other_le_1 G M hM A C hC hAC T₁ hT₁
    · rw [Finset.inter_comm]; exact external_intersects_other_le_1 G M hM B C hC hBC T₂ hT₂
    · exact absurd rfl h_ne
    · exact hM.1.2 hC hD hCD  -- C ∩ D ≤ 1
    · rw [Finset.inter_comm]; exact external_intersects_other_le_1 G M hM A D hD hAD T₁ hT₁
    · rw [Finset.inter_comm]; exact external_intersects_other_le_1 G M hM B D hD hBD T₂ hT₂
    · rw [Finset.inter_comm]; exact hM.1.2 hC hD hCD
    · exact absurd rfl h_ne

-- ══════════════════════════════════════════════════════════════════════════════
-- APPROACH: If x₁ ≠ x₂, T₁ and T₂ share only vertex v (not an edge)
-- This means {T₁, T₂, C, D} is a 4-packing, but we need a 5th to contradict ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
  KEY LEMMA: If T₁ = {v, a, x₁} (external of A) and T₂ = {v, b, x₂} (external of B)
  where a ∈ A \ {v}, b ∈ B \ {v}, and x₁ ≠ x₂, then T₁ ∩ T₂ = {v}.

  This follows from:
  - v ∈ T₁ ∩ T₂ (given)
  - a ∈ A, a ≠ v, and a ∉ B (since A ∩ B = {v})
  - b ∈ B, b ≠ v, and b ∉ A (since A ∩ B = {v})
  - x₁ ∉ A (external vertex), x₂ ∉ B (external vertex)
  - x₁ ≠ x₂ (assumption)

  Case analysis for any vertex w ∈ T₁ ∩ T₂:
  - If w = v: OK
  - If w = a: Then a ∈ T₂ = {v, b, x₂}. Since a ≠ v and a ∉ B (so a ≠ b), must have a = x₂.
              But x₂ ∉ B and a ∈ A. If a = x₂, need a ∉ B. Since A ∩ B = {v} and a ≠ v, a ∉ B. OK.
              So a = x₂ is possible. This means x₂ ∈ A.
  - If w = x₁: Then x₁ ∈ T₂ = {v, b, x₂}. Since x₁ ∉ A and v ∈ A, x₁ ≠ v.
               If x₁ = b, then x₁ ∈ B, but we need to check x₁ ∉ A ∪ B...
               Actually, the definition only says x₁ ∉ A. It's possible x₁ ∈ B.
               If x₁ = x₂, that contradicts our assumption.
               So x₁ = b is possible. This means the external vertex of T₁ is in B.

  Wait, this analysis shows that T₁ ∩ T₂ could have more than just {v}!
  The key question is whether the "external apex" must be outside both A AND B,
  or just outside its own M-element.

  By definition: isExternalOf G M A T means T shares edge with A and NOT with B, C, D.
  The "apex" is the vertex of T not in A. This apex could be in B, C, or D!

  So T₁ = {v, a, x₁} with x₁ ∉ A, but possibly x₁ ∈ B.
  And T₂ = {v, b, x₂} with x₂ ∉ B, but possibly x₂ ∈ A.

  If x₁ ∈ B: T₁ = {v, a, x₁} with v ∈ A ∩ B, a ∈ A, x₁ ∈ B.
             Does T₁ share edge with B? Check: {v, x₁} with v, x₁ ∈ B. YES!
             But T₁ is external of A, so it doesn't share edge with B. Contradiction!

  So if T₁ is external of A, its apex x₁ is NOT in B (at the shared vertex v).

  Actually, let me re-examine. T₁ doesn't share edge with B means:
  ¬∃ u v, u ≠ v ∧ u ∈ T₁ ∧ v ∈ T₁ ∧ u ∈ B ∧ v ∈ B

  If x₁ ∈ B and v ∈ B, then {v, x₁} would be a shared edge with B.
  So x₁ ∉ B (given v ∈ B).

  Similarly, since v ∈ B and a ∈ T₁, if a ∈ B then {v, a} shares edge with B.
  But a ∈ A and a ≠ v, so a ∉ B (since A ∩ B = {v}).

  So for T₁ = {v, a, x₁}:
  - v ∈ A ∩ B
  - a ∈ A, a ∉ B
  - x₁ ∉ A, x₁ ∉ B (since both {v, x₁} and {a, x₁} would create B-edge if x₁ ∈ B)

  Wait, if x₁ ∈ B, then {v, x₁} ⊆ T₁ ∩ B, giving a shared edge with B.
  This contradicts T₁ being external of A (which requires no edge shared with B).

  So x₁ ∉ B.

  Similarly, x₂ ∉ A.

  Now: T₁ ∩ T₂ for T₁ = {v, a, x₁} and T₂ = {v, b, x₂}:
  - v is in both (given)
  - a ∈ T₂? a ∈ {v, b, x₂}. Since a ≠ v and a ∉ B (so a ≠ b) and a ∈ A (so a ≠ x₂ since x₂ ∉ A).
    So a ∉ T₂.
  - x₁ ∈ T₂? x₁ ∈ {v, b, x₂}. x₁ ≠ v (since x₁ ∉ A and v ∈ A). x₁ ≠ b (since x₁ ∉ B and b ∈ B).
    x₁ = x₂ only if x₁ = x₂, which contradicts our assumption.
    So x₁ ∉ T₂.

  Therefore T₁ ∩ T₂ = {v} when x₁ ≠ x₂ and A ∩ B = {v}.
-/
lemma cross_externals_share_only_v
    (A B T₁ T₂ : Finset V)
    (hA_3 : A.card = 3) (hB_3 : B.card = 3)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (h_AB_inter : A ∩ B = {v})
    (hv_T₁ : v ∈ T₁) (hv_T₂ : v ∈ T₂)
    (hT₁_A_inter : (T₁ ∩ A).card = 2) (hT₂_B_inter : (T₂ ∩ B).card = 2)
    (hT₁_not_share_B : ¬sharesEdgeWith T₁ B)
    (hT₂_not_share_A : ¬sharesEdgeWith T₂ A)
    (x₁ : V) (hx₁_T₁ : x₁ ∈ T₁) (hx₁_not_A : x₁ ∉ A)
    (x₂ : V) (hx₂_T₂ : x₂ ∈ T₂) (hx₂_not_B : x₂ ∉ B)
    (hx₁_ne_x₂ : x₁ ≠ x₂) :
    T₁ ∩ T₂ = {v} := by
  -- First show x₁ ∉ B (otherwise {v, x₁} shares edge with B)
  have hx₁_not_B : x₁ ∉ B := by
    intro hx₁_B
    have h_share : sharesEdgeWith T₁ B := by
      use v, x₁
      exact ⟨fun h => hx₁_not_A (h ▸ hv_A), hv_T₁, hx₁_T₁, hv_B, hx₁_B⟩
    exact hT₁_not_share_B h_share

  -- Similarly, x₂ ∉ A (otherwise {v, x₂} shares edge with A)
  have hx₂_not_A : x₂ ∉ A := by
    intro hx₂_A
    have h_share : sharesEdgeWith T₂ A := by
      use v, x₂
      exact ⟨fun h => hx₂_not_B (h ▸ hv_B), hv_T₂, hx₂_T₂, hv_A, hx₂_A⟩
    exact hT₂_not_share_A h_share

  -- Get the other vertex a ∈ T₁ ∩ A (besides v)
  have h_T₁_A : ∃ a, a ∈ T₁ ∩ A ∧ a ≠ v := by
    have h_v_inter : v ∈ T₁ ∩ A := Finset.mem_inter.mpr ⟨hv_T₁, hv_A⟩
    rw [Finset.card_eq_two] at hT₁_A_inter
    obtain ⟨a, b, hab, h_eq⟩ := hT₁_A_inter
    rw [h_eq] at h_v_inter
    simp at h_v_inter
    cases h_v_inter with
    | inl hv_a => use b; rw [h_eq]; simp; exact ⟨Or.inr rfl, fun h => hab (hv_a.trans h.symm)⟩
    | inr hv_b => use a; rw [h_eq]; simp; exact ⟨Or.inl rfl, fun h => hab (h.trans hv_b.symm)⟩
  obtain ⟨a, ha_inter, ha_ne_v⟩ := h_T₁_A
  have ha_T₁ : a ∈ T₁ := Finset.mem_inter.mp ha_inter |>.1
  have ha_A : a ∈ A := Finset.mem_inter.mp ha_inter |>.2

  -- a ∉ B (since A ∩ B = {v} and a ≠ v)
  have ha_not_B : a ∉ B := by
    intro ha_B
    have ha_AB : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha_A, ha_B⟩
    rw [h_AB_inter] at ha_AB
    simp at ha_AB
    exact ha_ne_v ha_AB

  -- Similarly for b ∈ T₂ ∩ B
  have h_T₂_B : ∃ b, b ∈ T₂ ∩ B ∧ b ≠ v := by
    have h_v_inter : v ∈ T₂ ∩ B := Finset.mem_inter.mpr ⟨hv_T₂, hv_B⟩
    rw [Finset.card_eq_two] at hT₂_B_inter
    obtain ⟨a', b', hab, h_eq⟩ := hT₂_B_inter
    rw [h_eq] at h_v_inter
    simp at h_v_inter
    cases h_v_inter with
    | inl hv_a => use b'; rw [h_eq]; simp; exact ⟨Or.inr rfl, fun h => hab (hv_a.trans h.symm)⟩
    | inr hv_b => use a'; rw [h_eq]; simp; exact ⟨Or.inl rfl, fun h => hab (h.trans hv_b.symm)⟩
  obtain ⟨b, hb_inter, hb_ne_v⟩ := h_T₂_B
  have hb_T₂ : b ∈ T₂ := Finset.mem_inter.mp hb_inter |>.1
  have hb_B : b ∈ B := Finset.mem_inter.mp hb_inter |>.2

  -- b ∉ A (since A ∩ B = {v} and b ≠ v)
  have hb_not_A : b ∉ A := by
    intro hb_A
    have hb_AB : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb_A, hb_B⟩
    rw [h_AB_inter] at hb_AB
    simp at hb_AB
    exact hb_ne_v hb_AB

  -- Now T₁ = {v, a, x₁} and T₂ = {v, b, x₂} with all vertices distinct
  -- Show T₁ ∩ T₂ = {v}
  ext w
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · intro ⟨hw_T₁, hw_T₂⟩
    -- w ∈ T₁ = {v, a, x₁}
    have h_T₁_eq : T₁ = {v, a, x₁} := by
      have h_sub : {v, a, x₁} ⊆ T₁ := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hv_T₁, ha_T₁, hx₁_T₁⟩
      have h_card : ({v, a, x₁} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
        · simp only [Finset.mem_singleton, ne_eq]
          intro h; exact hx₁_not_A (h ▸ ha_A)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          constructor
          · exact ha_ne_v.symm
          · intro h; exact hx₁_not_A (h ▸ hv_A)
      exact Finset.eq_of_subset_of_card_le h_sub (h_card ▸ le_of_eq hT₁_3.symm) |>.symm
    rw [h_T₁_eq] at hw_T₁
    simp at hw_T₁

    -- w ∈ T₂ = {v, b, x₂}
    have h_T₂_eq : T₂ = {v, b, x₂} := by
      have h_sub : {v, b, x₂} ⊆ T₂ := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hv_T₂, hb_T₂, hx₂_T₂⟩
      have h_card : ({v, b, x₂} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
        · simp only [Finset.mem_singleton, ne_eq]
          intro h; exact hx₂_not_B (h ▸ hb_B)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          constructor
          · exact hb_ne_v.symm
          · intro h; exact hx₂_not_B (h ▸ hv_B)
      exact Finset.eq_of_subset_of_card_le h_sub (h_card ▸ le_of_eq hT₂_3.symm) |>.symm
    rw [h_T₂_eq] at hw_T₂
    simp at hw_T₂

    rcases hw_T₁ with rfl | rfl | rfl
    · rfl  -- w = v
    · -- w = a, but a ∈ {v, b, x₂}
      rcases hw_T₂ with h_eq | h_eq | h_eq
      · exact h_eq  -- a = v
      · exact absurd (h_eq ▸ hb_B) ha_not_B  -- a = b contradicts a ∉ B
      · exact absurd (h_eq ▸ ha_A) hx₂_not_A  -- a = x₂ contradicts x₂ ∉ A
    · -- w = x₁, but x₁ ∈ {v, b, x₂}
      rcases hw_T₂ with h_eq | h_eq | h_eq
      · exact absurd (h_eq.symm ▸ hv_A) hx₁_not_A  -- x₁ = v contradicts x₁ ∉ A
      · exact absurd (h_eq.symm ▸ hb_B) hx₁_not_B  -- x₁ = b contradicts x₁ ∉ B
      · exact absurd h_eq.symm hx₁_ne_x₂  -- x₁ = x₂ contradicts x₁ ≠ x₂

  · intro hw_v
    rw [hw_v]
    exact ⟨hv_T₁, hv_T₂⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- THE MAKE-OR-BREAK LEMMA (1 SORRY FOR ARISTOTLE)
-- ══════════════════════════════════════════════════════════════════════════════

/--
  Bridge Externals Share Apex Lemma

  Given:
  - M = {A, B, C, D} a maximal 4-packing in cycle_4 configuration
  - A ∩ B = {v} (v is the shared vertex between A and B)
  - T₁ is an external of A containing v (T₁ = {v, a, x₁} for some a ∈ A, x₁ ∉ A ∪ B)
  - T₂ is an external of B containing v (T₂ = {v, b, x₂} for some b ∈ B, x₂ ∉ A ∪ B)

  Question: Must x₁ = x₂?

  ANALYSIS:
  If x₁ ≠ x₂, then by cross_externals_share_only_v, T₁ ∩ T₂ = {v} (single vertex, not edge).
  This means {T₁, T₂, C, D} is a valid 4-packing (by four_packing_from_cross_externals).

  To contradict ν = 4, we need to find a FIFTH triangle that can extend {T₁, T₂, C, D}.
  Candidates:
  - A: Shares edge with T₁ (both share edge {v, a}). Cannot add.
  - B: Shares edge with T₂ (both share edge {v, b}). Cannot add.

  So the direct 5-packing argument doesn't work for cross-M-element externals.

  ALTERNATIVE APPROACH:
  Consider what happens when we look at ALL externals at v.
  - All externals of A at v form a "fan" with common apex (slot224f).
  - All externals of B at v form a "fan" with common apex (slot224f).
  - But do the A-fan and B-fan share the same apex?

  If they share the same apex x:
  - All externals at v share {v, x}
  - Cover: {v, x} covers all externals at v with 1 edge!
  - This gives τ ≤ 8 (4 M-elements covered by 4 edges, externals by 4 apex-edges)

  If they DON'T share the same apex:
  - At v, externals of A have apex x_A, externals of B have apex x_B, with x_A ≠ x_B
  - Need 2 edges at v: {v, x_A} and {v, x_B}
  - This gives 8 apex-edges + 4 M-edges = 12 edges (back to τ ≤ 12)

  CONJECTURE (for Aristotle to prove or disprove):
  In a cycle_4 configuration with ν = 4, externals of adjacent M-elements at their
  shared vertex must share a common apex.

  PROOF ATTEMPT:
  Suppose x₁ ≠ x₂. We've shown T₁ ∩ T₂ = {v}.
  Consider the triangle T₃ = {v, a, x₂} if it exists in G.
  - If T₃ exists, is it external of A or B?
  - T₃ shares edge {v, a} with A (since a ∈ A).
  - Does T₃ share edge with B?
    - T₃ ∩ B contains v (since v ∈ B).
    - Does x₂ ∈ B? We showed x₂ ∉ B.
    - Does a ∈ B? We showed a ∉ B.
    - So T₃ ∩ B = {v}, and T₃ doesn't share edge with B.
  - Does T₃ share edge with C or D? Need to check...
    - If A ∩ C = {v_DA} (in cycle_4), and a ∉ C, and x₂ ∉ C, then T₃ ∩ C ⊆ {v}... wait, v might not be in C.
    - This depends on the specific cycle_4 structure.

  This is getting complicated. Let Aristotle try to find a proof or counterexample.
-/
theorem bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (hA_3 : A.card = 3) (hB_3 : B.card = 3)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (h_AB_inter : A ∩ B = {v})  -- v is the ONLY shared vertex
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- Get the external apexes x₁ and x₂
  have hT₁_A_inter := external_inter_M_card_eq_2 G M hM A hA hA_3 T₁ hT₁ hT₁_3
  have hT₂_B_inter := external_inter_M_card_eq_2 G M hM B hB hB_3 T₂ hT₂ hT₂_3
  obtain ⟨x₁, hx₁_T₁, hx₁_not_A, hx₁_unique⟩ := external_apex_exists G M hM A hA hA_3 T₁ hT₁ hT₁_3
  obtain ⟨x₂, hx₂_T₂, hx₂_not_B, hx₂_unique⟩ := external_apex_exists G M hM B hB hB_3 T₂ hT₂ hT₂_3

  -- x₁ ∉ B (since T₁ doesn't share edge with B, and v ∈ B)
  have hx₁_not_B : x₁ ∉ B := by
    intro hx₁_B
    have h_share : sharesEdgeWith T₁ B := by
      have hne : v ≠ x₁ := fun h => hx₁_not_A (h ▸ hv_A)
      use v, x₁
      exact ⟨hne, hT₁_v, hx₁_T₁, hv_B, hx₁_B⟩
    exact hT₁.2.2.2 B hB hAB h_share

  -- x₂ ∉ A (since T₂ doesn't share edge with A, and v ∈ A)
  have hx₂_not_A : x₂ ∉ A := by
    intro hx₂_A
    have h_share : sharesEdgeWith T₂ A := by
      have hne : v ≠ x₂ := fun h => hx₂_not_B (h ▸ hv_B)
      use v, x₂
      exact ⟨hne, hT₂_v, hx₂_T₂, hv_A, hx₂_A⟩
    exact hT₂.2.2.2 A hA hAB.symm h_share

  -- If x₁ = x₂, we're done
  by_cases hx_eq : x₁ = x₂
  · use x₁
    exact ⟨hx₁_not_A, hx₁_not_B, hx₁_T₁, hx_eq ▸ hx₂_T₂⟩

  -- If x₁ ≠ x₂, we need to derive a contradiction using ν = 4
  -- This is where the lemma might be FALSE and Aristotle should find a counterexample
  exfalso

  -- We've shown that if x₁ ≠ x₂, then T₁ ∩ T₂ = {v}
  have h_T₁_not_share_B : ¬sharesEdgeWith T₁ B := hT₁.2.2.2 B hB hAB
  have h_T₂_not_share_A : ¬sharesEdgeWith T₂ A := hT₂.2.2.2 A hA hAB.symm

  have h_inter_v : T₁ ∩ T₂ = {v} := cross_externals_share_only_v
    A B T₁ T₂ hA_3 hB_3 hT₁_3 hT₂_3 v hv_A hv_B h_AB_inter hT₁_v hT₂_v
    hT₁_A_inter hT₂_B_inter h_T₁_not_share_B h_T₂_not_share_A
    x₁ hx₁_T₁ hx₁_not_A x₂ hx₂_T₂ hx₂_not_B hx_eq

  -- Now we have T₁ ∩ T₂ = {v}, so they share only one vertex (not an edge)
  -- This means {T₁, T₂, C, D} forms a valid 4-packing for appropriate C, D

  -- To get a 5-packing contradiction, we need to find a fifth triangle
  -- This is the key gap - Aristotle should try to prove or find counterexample

  sorry

end
