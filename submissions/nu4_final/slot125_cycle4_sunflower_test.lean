/-
SLOT 125: Test Sunflower Structure at Shared Vertices in Cycle_4
UUID: slot125_cycle4_sunflower

CONTEXT:
- General tau_at_shared_vertex_le_2 is FALSE (counterexamples exist)
- Grok constructed cycle_4 counterexample with 3 disjoint triangles at v_ab
- Codex claimed sunflower clustering makes it TRUE
- Need to determine actual bound

GOAL: Investigate the actual structure of triangles at shared vertices in cycle_4

APPROACH:
1. Every triangle at v must share edge with some packing element (maximality)
2. At v_ab, triangles share edges with A, B, C, or D
3. Key question: How many "independent" triangles can exist at v_ab?

DEPENDENCIES:
- PROVEN: tau_le_12_cycle4_conservative (UUID 5d2756b0)
- PROVEN: cycle4_disjoint_partition (UUID ec96692a)
- PROVEN: triangle_shares_edge_with_packing
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
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

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Subadditivity (from slot113)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) (h₁ : S₁ ⊆ G.cliqueFinset 3) (h₂ : S₂ ⊆ G.cliqueFinset 3)
    (bound₁ bound₂ : ℕ)
    (hS₁ : ∃ E₁ ⊆ G.edgeFinset, E₁.card ≤ bound₁ ∧ ∀ t ∈ S₁, ∃ e ∈ E₁, e ∈ t.sym2)
    (hS₂ : ∃ E₂ ⊆ G.edgeFinset, E₂.card ≤ bound₂ ∧ ∀ t ∈ S₂, ∃ e ∈ E₂, e ∈ t.sym2) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ bound₁ + bound₂ ∧ ∀ t ∈ S₁ ∪ S₂, ∃ e ∈ E, e ∈ t.sym2 := by
  obtain ⟨E₁, hE₁_sub, hE₁_card, hE₁_cover⟩ := hS₁
  obtain ⟨E₂, hE₂_sub, hE₂_card, hE₂_cover⟩ := hS₂
  use E₁ ∪ E₂
  refine ⟨Finset.union_subset hE₁_sub hE₂_sub, ?_, ?_⟩
  · calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := Finset.card_union_le E₁ E₂
         _ ≤ bound₁ + bound₂ := Nat.add_le_add hE₁_card hE₂_card
  · intro t ht
    simp only [Finset.mem_union] at ht
    cases ht with
    | inl h₁ => obtain ⟨e, he, he'⟩ := hE₁_cover t h₁; exact ⟨e, Finset.mem_union_left _ he, he'⟩
    | inr h₂ => obtain ⟨e, he, he'⟩ := hE₂_cover t h₂; exact ⟨e, Finset.mem_union_right _ he, he'⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Maximality (from slot113)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  by_contra h_contra
  push_neg at h_contra
  have h_larger : isTrianglePacking G (M ∪ {t}) := by
    refine ⟨?_, ?_⟩
    · exact Finset.union_subset hM.1.1 (Finset.singleton_subset_iff.mpr ht)
    · intro x hx y hy hxy
      simp only [Finset.mem_union, Finset.mem_singleton] at hx hy
      rcases hx with hx | rfl <;> rcases hy with hy | rfl
      · exact hM.1.2 hx hy hxy
      · exact Nat.le_of_lt_succ (h_contra x hx)
      · rw [Finset.inter_comm]; exact Nat.le_of_lt_succ (h_contra y hy)
      · exact absurd rfl hxy
  have h_card : (M ∪ {t}).card > M.card := by
    have : t ∉ M := by
      intro ht'
      have := h_contra t ht'
      rw [Finset.inter_self] at this
      have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
      omega
    simp [Finset.card_union_eq (Finset.disjoint_singleton_right.mpr this)]
  have := hM.2
  have h_bound : trianglePackingNumber G ≥ (M ∪ {t}).card := by
    unfold trianglePackingNumber
    have h_mem : (M ∪ {t}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_larger.1, h_larger⟩
    have := Finset.le_max (Finset.mem_image_of_mem Finset.card h_mem)
    cases h : ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max
    · simp at this
    · simp only [Option.getD_some]; exact this
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY STRUCTURE: Triangles at shared vertex share edge with adjacent packing elements
-- ══════════════════════════════════════════════════════════════════════════════

/-- In cycle_4, triangles containing v_ab share edge with A, B, or opposite elements C, D -/
lemma triangles_at_vab_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab : V) (hv_ab : v_ab ∈ A ∩ B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (hv : v_ab ∈ t) :
    (t ∩ A).card ≥ 2 ∨ (t ∩ B).card ≥ 2 ∨ (t ∩ C).card ≥ 2 ∨ (t ∩ D).card ≥ 2 := by
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  have hM_eq := hcycle.1
  rw [hM_eq] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
  rcases hX_mem with rfl | rfl | rfl | rfl <;> tauto

/-- Triangles at v_ab that share edge with A are covered by 2 spokes from A -/
lemma triangles_sharing_A_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hA : A ∈ G.cliqueFinset 3)
    (v_ab : V) (hv : v_ab ∈ A) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧
      ∀ t ∈ (G.cliqueFinset 3).filter (fun t => v_ab ∈ t ∧ (t ∩ A).card ≥ 2),
        ∃ e ∈ E, e ∈ t.sym2 := by
  -- A = {v_ab, a1, a2}. Spokes {v_ab, a1} and {v_ab, a2} cover triangles sharing edge with A.
  obtain ⟨a, b, c, hab, hac, hbc, hA_eq⟩ := Finset.card_eq_three.mp (SimpleGraph.mem_cliqueFinset_iff.mp hA).2
  -- Identify which of a, b, c is v_ab
  by_cases hav : a = v_ab
  · -- v_ab = a, so A = {v_ab, b, c}
    use ({s(v_ab, b), s(v_ab, c)} : Finset (Sym2 V))
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · have := (SimpleGraph.mem_cliqueFinset_iff.mp hA).1
        rw [SimpleGraph.isClique_iff, hA_eq] at this
        have := this (by simp : v_ab ∈ ({a, b, c} : Finset V)) (by simp : b ∈ ({a, b, c} : Finset V)) (by rw [hav]; exact hab.symm)
        exact this.symm.mem_edgeFinset
      · have := (SimpleGraph.mem_cliqueFinset_iff.mp hA).1
        rw [SimpleGraph.isClique_iff, hA_eq] at this
        have := this (by simp : v_ab ∈ ({a, b, c} : Finset V)) (by simp : c ∈ ({a, b, c} : Finset V)) (by rw [hav]; exact hac.symm)
        exact this.symm.mem_edgeFinset
    · exact Finset.card_insert_le _ _
    · intro t ht
      simp only [Finset.mem_filter] at ht
      obtain ⟨ht_tri, hv_in, hshare⟩ := ht
      -- t shares edge with A = {v_ab, b, c}, so t ∩ A has ≥2 elements
      -- Since v_ab ∈ t, t must contain v_ab and at least one of b, c
      have : b ∈ t ∨ c ∈ t := by
        by_contra h
        push_neg at h
        have h1 : t ∩ A ⊆ {v_ab} := by
          intro x hx
          simp only [Finset.mem_inter] at hx
          rw [hA_eq] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx.2 with rfl | rfl | rfl
          · rw [← hav]; exact Finset.mem_singleton_self _
          · exact absurd hx.1 h.1
          · exact absurd hx.1 h.2
        have := Finset.card_le_card h1
        simp at this
        omega
      rcases this with hb | hc
      · use s(v_ab, b), Finset.mem_insert_self _ _
        have := (SimpleGraph.mem_cliqueFinset_iff.mp ht_tri).1
        rw [SimpleGraph.isClique_iff] at this
        have hadj := this hv_in hb (by intro heq; rw [heq, hav] at hab; exact hab rfl)
        exact hadj.mem_sym2
      · use s(v_ab, c), Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have := (SimpleGraph.mem_cliqueFinset_iff.mp ht_tri).1
        rw [SimpleGraph.isClique_iff] at this
        have hadj := this hv_in hc (by intro heq; rw [heq, hav] at hac; exact hac rfl)
        exact hadj.mem_sym2
  · by_cases hbv : b = v_ab
    · -- Similar case for b = v_ab
      sorry
    · -- c = v_ab
      sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN APPROACH: Bound by 4 spokes (known to work) then try to improve
-- ══════════════════════════════════════════════════════════════════════════════

/-- At a shared vertex v in cycle_4, 4 spokes cover all triangles containing v -/
lemma tau_at_shared_vertex_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B) (h_inter : A ∩ B = {v}) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 4 ∧
      ∀ t ∈ trianglesContaining G v, ∃ e ∈ E, e ∈ t.sym2 := by
  -- A = {v, a1, a2}, B = {v, b1, b2}
  -- 4 spokes: {v, a1}, {v, a2}, {v, b1}, {v, b2}
  have hA_tri := hM.1.1 hA
  have hB_tri := hM.1.1 hB
  have hA_card := (SimpleGraph.mem_cliqueFinset_iff.mp hA_tri).2
  have hB_card := (SimpleGraph.mem_cliqueFinset_iff.mp hB_tri).2

  -- Get the other vertices of A and B
  obtain ⟨a, b, c, _, _, _, hA_eq⟩ := Finset.card_eq_three.mp hA_card
  obtain ⟨d, e, f, _, _, _, hB_eq⟩ := Finset.card_eq_three.mp hB_card

  -- The 4 non-v vertices give 4 spokes
  -- Any triangle containing v shares edge with some packing element
  -- Hence shares at least one of the 4 spokes
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- EXPLORE: Can we do better than 4? Test the sunflower hypothesis
-- ══════════════════════════════════════════════════════════════════════════════

/--
SUNFLOWER HYPOTHESIS (from Codex):
Triangles at v cluster around shared external vertices.
If true: 2 edges suffice.
If false: Need up to 4 edges.

This lemma tests whether triangles at v form a "sunflower" structure
where all petals share a common external vertex.
-/
lemma sunflower_at_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab : V) (hv_ab : v_ab ∈ A ∩ B) :
    -- Either all triangles at v_ab share a common external vertex (sunflower)
    (∃ x : V, x ≠ v_ab ∧ ∀ t ∈ trianglesContaining G v_ab, x ∈ t) ∨
    -- Or there exists a 2-edge cover anyway
    (∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ trianglesContaining G v_ab, ∃ e ∈ E, e ∈ t.sym2) ∨
    -- Or the bound is actually higher (Grok's counterexample)
    (∃ t1 t2 t3 : Finset V, t1 ∈ trianglesContaining G v_ab ∧ t2 ∈ trianglesContaining G v_ab ∧
      t3 ∈ trianglesContaining G v_ab ∧
      Disjoint (t1.sym2 : Set (Sym2 V)) t2.sym2 ∧
      Disjoint (t1.sym2 : Set (Sym2 V)) t3.sym2 ∧
      Disjoint (t2.sym2 : Set (Sym2 V)) t3.sym2) := by
  sorry

end
