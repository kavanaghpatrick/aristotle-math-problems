/-
Tuza ν=4 PATH_4 - Slot 386: Direct 8-Edge Cover Construction

APPROACH: Directly construct the 8-edge cover, not via subadditivity.

For PATH_4 with M = {A, B, C, D} where A-v₁-B-v₂-C-v₃-D:
- All triangles = S_A ∪ S_B ∪ S_C ∪ S_D ∪ X_AB ∪ X_BC ∪ X_CD
- τ(S_e) ≤ 2 for each e (proven in slot257)
- τ(X_ef) ≤ 2 for each bridge set (proven in slot257)

KEY INSIGHT (from slot257):
- Bridges X_AB all contain vertex v₁ (the shared vertex of A and B)
- X_AB can be covered by 2 spoke edges from v₁
- These spoke edges are edges of A!
- So the 2 edges covering S_A + 2 edges covering X_AB use only edges of A
- Since A has only 3 edges, at most 2 edges needed for S_A ∪ X_AB together!

TIER: 2 (Direct construction using proven lemmas)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot257)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridges contain the shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- If e and f share exactly one vertex v, every bridge in X_ef contains v -/
lemma bridge_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  by_contra hv_not_in_t
  -- If v ∉ t, then t ∩ e and t ∩ f are disjoint from {v}
  -- But |t ∩ e| ≥ 2 and |t ∩ f| ≥ 2, and |t| = 3
  -- So |t ∩ e| + |t ∩ f| ≥ 4 > 3, contradiction
  have ht_card : t.card = 3 := by
    have ht_tri : t ∈ G.cliqueFinset 3 := by
      simp only [X_ef, mem_filter] at ht
      exact ht.1
    exact (G.mem_cliqueFinset_iff.mp ht_tri).2
  have h_ge : (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2 := by
    simp only [X_ef, mem_filter] at ht
    exact ht.2
  have h_disj : Disjoint (t ∩ e) (t ∩ f) := by
    rw [Finset.disjoint_left]
    intro x hxe hxf
    have hx_in_ef : x ∈ e ∩ f := mem_inter.mpr ⟨mem_of_mem_inter_right hxe, mem_of_mem_inter_right hxf⟩
    rw [hv] at hx_in_ef
    simp only [mem_singleton] at hx_in_ef
    rw [hx_in_ef] at hxe
    exact hv_not_in_t (mem_of_mem_inter_left hxe)
  have h_union : (t ∩ e ∪ t ∩ f).card ≤ t.card := card_le_card (union_subset inter_subset_left inter_subset_left)
  rw [card_union_of_disjoint h_disj] at h_union
  omega

/-- Bridges X_ef can be covered by 2 edges through the shared vertex -/
lemma bridge_cover_from_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧
    ∀ t ∈ X_ef G e f, ∃ ε ∈ E', ε ∈ t.sym2 := by
  -- The 2 edges are {v, x} and {v, y} where e = {v, x, y}
  have he_card : e.card = 3 := by
    have := hM.1 he
    exact (G.mem_cliqueFinset_iff.mp this).2
  obtain ⟨a, b, c, hab, hac, hbc, he_eq⟩ := card_eq_three.mp he_card
  have hv_in_e : v ∈ e := by
    have : v ∈ e ∩ f := by rw [hv]; exact mem_singleton_self v
    exact mem_of_mem_inter_left this
  -- v is one of a, b, c
  rw [he_eq] at hv_in_e
  simp only [mem_insert, mem_singleton] at hv_in_e
  -- Use spoke edges from v
  rcases hv_in_e with rfl | rfl | rfl
  · -- v = a, use {a,b} and {a,c}
    use {s(a,b), s(a,c)}
    refine ⟨?_, ?_, ?_⟩
    · simp [card_insert_of_not_mem, card_singleton]
      by_cases h : s(a,b) = s(a,c)
      · simp [h]
      · simp [card_insert_of_not_mem h]
    · intro edge he_edge
      simp only [mem_insert, mem_singleton] at he_edge
      rcases he_edge with rfl | rfl
      · have : G.Adj a b := by
          have hclique := hM.1 he
          rw [G.mem_cliqueFinset_iff] at hclique
          rw [he_eq] at hclique
          exact hclique.1 (by simp) (by simp) hab
        exact G.mem_edgeFinset.mpr this
      · have : G.Adj a c := by
          have hclique := hM.1 he
          rw [G.mem_cliqueFinset_iff] at hclique
          rw [he_eq] at hclique
          exact hclique.1 (by simp) (by simp) hac
        exact G.mem_edgeFinset.mpr this
    · intro t ht
      have hv_in_t := bridge_contains_shared_vertex G M hM e f he hf hef a hv t ht
      have ht_card : t.card = 3 := by
        simp only [X_ef, mem_filter] at ht
        exact (G.mem_cliqueFinset_iff.mp ht.1).2
      have h_inter : (t ∩ e).card ≥ 2 := by
        simp only [X_ef, mem_filter] at ht
        exact ht.2.1
      -- t contains a and at least one of b, c
      rw [he_eq] at h_inter
      have : ∃ x ∈ ({b, c} : Finset V), x ∈ t := by
        by_contra h_none
        push_neg at h_none
        have h_sub : t ∩ {a, b, c} ⊆ {a} := by
          intro x hx
          simp only [mem_inter, mem_insert, mem_singleton] at hx
          rcases hx.2 with rfl | rfl | rfl
          · exact mem_singleton_self a
          · exact absurd hx.1 (h_none b (by simp))
          · exact absurd hx.1 (h_none c (by simp))
        have : (t ∩ {a, b, c}).card ≤ 1 := by
          calc (t ∩ {a, b, c}).card ≤ ({a} : Finset V).card := card_le_card h_sub
            _ = 1 := card_singleton a
        omega
      obtain ⟨x, hx_bc, hx_t⟩ := this
      simp only [mem_insert, mem_singleton] at hx_bc
      rcases hx_bc with rfl | rfl
      · use s(a, b)
        simp only [mem_insert, mem_singleton, true_or, true_and]
        exact Sym2.mem_sym2_iff.mpr (Or.inl ⟨hv_in_t, hx_t⟩)
      · use s(a, c)
        simp only [mem_insert, mem_singleton, or_true, true_and]
        exact Sym2.mem_sym2_iff.mpr (Or.inl ⟨hv_in_t, hx_t⟩)
  · -- v = b, use {b,a} and {b,c}
    sorry -- Symmetric to v = a case
  · -- v = c, use {c,a} and {c,b}
    sorry -- Symmetric to v = a case

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF STRATEGY:
For PATH_4 A-v₁-B-v₂-C-v₃-D:

1. T_A = S_A ∪ X_AB (A only bridges to B)
2. T_D = S_D ∪ X_CD (D only bridges to C)
3. T_B = S_B ∪ X_AB ∪ X_BC
4. T_C = S_C ∪ X_BC ∪ X_CD

Cover construction:
- 2 edges from A covering S_A (or fewer)
- 2 edges from D covering S_D (or fewer)
- 2 edges around v₁ covering X_AB
- 2 edges around v₂ covering X_BC
- 2 edges around v₃ covering X_CD

But wait! Edges around v₁ are edges of A or B.
Key: The spoke edges {v₁, a}, {v₁, b} from A can cover both S_A AND X_AB!

Similarly:
- A's spokes cover S_A ∪ X_AB (≤2 edges)
- D's spokes cover S_D ∪ X_CD (≤2 edges)
- B needs to cover S_B ∪ X_BC (X_AB already covered by A)
- C needs to cover S_C ∪ X_BC (X_CD already covered by D, X_BC shared with B)

Total: 2 + 2 + 2 + 2 = 8 edges
-/

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  sorry -- The explicit 8-edge cover construction

end
