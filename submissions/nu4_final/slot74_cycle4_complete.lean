/-
TUZA ν=4: CYCLE_4 COMPLETION
Goal: Prove τ ≤ 8 for graphs with cycle_4 packing structure

This file resumes from slot73 (eb28d806) which PROVED:
- cycle4_all_triangles_contain_shared: Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da

Remaining to prove:
- local_cover_le_2: At each shared vertex, 2 edges suffice to cover triangles containing it
- Final theorem: τ ≤ 4 × 2 = 8

Strategy:
1. Use cycle4_all_triangles_contain_shared to partition triangles by which shared vertex they contain
2. For each shared vertex v, prove τ(containing(v)) ≤ 2 using the disjoint triples contradiction
3. Apply tau_union_le_sum to combine: τ ≤ 2 + 2 + 2 + 2 = 8
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

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

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

def isCovering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun X => X.sym2.filter (fun e => v ∈ e))

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN INFRASTRUCTURE (from slot69-72)
-- ══════════════════════════════════════════════════════════════════════════════

lemma isCovering_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isCovering G A EA) (hB : isCovering G B EB) :
    isCovering G (A ∪ B) (EA ∪ EB) := by
  apply And.intro
  · exact Finset.union_subset hA.1 hB.1
  · intro t ht
    cases' Finset.mem_union.mp ht with htA htB
    · obtain ⟨e, heEA, heT⟩ := hA.right t htA
      exact ⟨e, Finset.mem_union_left _ heEA, heT⟩
    · obtain ⟨e, heEB, heT⟩ := hB.right t htB
      exact ⟨e, Finset.mem_union_right _ heEB, heT⟩

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Proof by case analysis on whether covering exists
  by_cases h_empty_A : A = ∅
  · simp [h_empty_A, triangleCoveringNumberOn]
  by_cases h_empty_B : B = ∅
  · simp [h_empty_B, triangleCoveringNumberOn]
  -- Standard subadditivity argument: EA covers A, EB covers B, EA ∪ EB covers A ∪ B
  -- |EA ∪ EB| ≤ |EA| + |EB|
  sorry -- PROVEN in slot69, slot71, slot72 - copy full proof

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_contra h_contra
  push_neg at h_contra
  -- If t doesn't share edge with any packing element, M ∪ {t} is a larger packing
  have h_union : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · exact Finset.union_subset hM.1.1 (Finset.singleton_subset_iff.mpr ht)
    · intro x hx y hy hxy
      cases' Finset.mem_union.mp hx with hxM hxt
      · cases' Finset.mem_union.mp hy with hyM hyt
        · exact hM.1.2 hxM hyM hxy
        · simp at hyt; subst hyt
          exact Nat.le_of_lt_succ (h_contra x hxM)
      · simp at hxt; subst hxt
        cases' Finset.mem_union.mp hy with hyM hyt
        · rw [Finset.inter_comm]
          exact Nat.le_of_lt_succ (h_contra y hyM)
        · simp at hyt; exact absurd hyt hxy
  -- This contradicts maximality of M
  have h_card : (M ∪ {t}).card > M.card := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_singleton_right]
      intro ht_in_M
      specialize h_contra t ht_in_M
      have : (t ∩ t).card = t.card := by simp
      rw [ht.card_eq] at this
      omega
  have h_max : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card := by
      apply Finset.mem_image.mpr
      use M ∪ {t}
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powerset.mpr
          exact Finset.union_subset hM.1.1 (Finset.singleton_subset_iff.mpr ht)
        · exact h_union
      · rfl
    have := Finset.le_max h_mem
    cases h : Finset.max _ <;> simp_all
  rw [hM.2] at h_max
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- FROM SLOT73: THE KEY THEOREM (ALREADY PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

lemma cycle4_element_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (v_left v_right x1 : V)
    (hX_eq : X = {v_left, v_right, x1})
    (h_ne : v_left ≠ v_right ∧ v_left ≠ x1 ∧ v_right ≠ x1)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G X) :
    v_left ∈ t ∨ v_right ∈ t := by
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ X).card ≥ 2 := ht.2
  rw [hX_eq] at h_share
  by_contra h_neither
  push_neg at h_neither
  have hsub : t ∩ {v_left, v_right, x1} ⊆ {x1} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 h_neither.1
    · exact absurd hx.1 h_neither.2
    · rfl
  have hcard : (t ∩ {v_left, v_right, x1}).card ≤ 1 := by
    calc (t ∩ {v_left, v_right, x1}).card ≤ ({x1} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton x1
  omega

lemma cycle4_no_loose_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t ∈ trianglesSharingEdge G A ∨ t ∈ trianglesSharingEdge G B ∨
    t ∈ trianglesSharingEdge G C ∨ t ∈ trianglesSharingEdge G D := by
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  rw [hcycle.1] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
  unfold trianglesSharingEdge
  rcases hX_mem with rfl | rfl | rfl | rfl <;> simp [hX_share]

theorem cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t := by
  obtain h_case := cycle4_no_loose_triangles G M hM A B C D hcycle t ht
  rcases h_case with hA | hB | hC | hD
  · -- t shares edge with A, so contains v_ab or v_da
    have h_inter_A : (t ∩ A).card ≥ 2 := by
      unfold trianglesSharingEdge at hA; simp at hA; exact hA.2
    have h_v_in_A : v_ab ∈ A ∧ v_da ∈ A := by
      constructor
      · have := Finset.mem_singleton.mp (Finset.ext_iff.mp hAB v_ab).mpr rfl
        exact Finset.mem_inter.mp (by rw [hAB]; exact Finset.mem_singleton_self v_ab) |>.1
      · have := Finset.mem_singleton.mp (Finset.ext_iff.mp hDA v_da).mpr rfl
        exact Finset.mem_inter.mp (by rw [hDA]; exact Finset.mem_singleton_self v_da) |>.2
    -- By pigeonhole: t shares ≥2 vertices with A = {v_ab, v_da, a1}
    -- If t avoids both v_ab and v_da, then t ∩ A ⊆ {a1}, so |t ∩ A| ≤ 1 < 2
    by_contra h_neither
    push_neg at h_neither
    have h_sub : t ∩ A ⊆ A \ {v_ab, v_da} := by
      intro x hx
      simp at hx ⊢
      exact ⟨hx.2, fun h => h_neither.1 (h ▸ hx.1), fun h => h_neither.2.2.2 (h ▸ hx.1)⟩
    have h_A_card : A.card = 3 := by
      have := hM.1.1 (hcycle.1.symm ▸ Finset.mem_insert_self A _)
      exact (Finset.mem_filter.mp this).2.2
    have h_small : (A \ {v_ab, v_da}).card ≤ 1 := by
      have h_distinct : v_ab ≠ v_da := by
        intro h_eq
        rw [h_eq] at hAB
        have := hcycle.2.2.2.2.2.2.2.2.2.2.1
        rw [hAB, hDA] at this
        simp at this
      rw [Finset.card_sdiff (by simp [h_v_in_A.1, h_v_in_A.2])]
      have h_pair : ({v_ab, v_da} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        simp [h_distinct]
      omega
    have := Finset.card_le_card h_sub
    omega
  · -- t shares edge with B
    left; right; left
    have h_inter_B : (t ∩ B).card ≥ 2 := by
      unfold trianglesSharingEdge at hB; simp at hB; exact hB.2
    have h_v_in_B : v_ab ∈ B ∧ v_bc ∈ B := by
      constructor
      · exact Finset.mem_inter.mp (by rw [hAB]; exact Finset.mem_singleton_self v_ab) |>.2
      · exact Finset.mem_inter.mp (by rw [hBC]; exact Finset.mem_singleton_self v_bc) |>.1
    by_contra h_not_bc
    -- If t doesn't contain v_bc, check if it contains v_ab
    by_cases h_ab : v_ab ∈ t
    · left; exact h_ab
    · -- t avoids both v_ab and v_bc
      have h_sub : t ∩ B ⊆ B \ {v_ab, v_bc} := by
        intro x hx; simp at hx ⊢
        exact ⟨hx.2, fun h => h_ab (h ▸ hx.1), fun h => h_not_bc (h ▸ hx.1)⟩
      have h_B_card : B.card = 3 := by
        have := hM.1.1 (hcycle.1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self B _))
        exact (Finset.mem_filter.mp this).2.2
      have h_distinct : v_ab ≠ v_bc := by
        intro h_eq
        have := hcycle.2.2.2.2.2.2.2.2.2.2.1
        rw [← h_eq, hAB] at hBC
        simp at *
      have h_small : (B \ {v_ab, v_bc}).card ≤ 1 := by
        rw [Finset.card_sdiff (by simp [h_v_in_B.1, h_v_in_B.2])]
        have h_pair : ({v_ab, v_bc} : Finset V).card = 2 := by
          rw [Finset.card_insert_of_notMem, Finset.card_singleton]; simp [h_distinct]
        omega
      have := Finset.card_le_card h_sub
      omega
  · -- t shares edge with C: contains v_bc or v_cd
    have h_inter_C : (t ∩ C).card ≥ 2 := by
      unfold trianglesSharingEdge at hC; simp at hC; exact hC.2
    have h_v_in_C : v_bc ∈ C ∧ v_cd ∈ C := by
      constructor
      · exact Finset.mem_inter.mp (by rw [hBC]; exact Finset.mem_singleton_self v_bc) |>.2
      · exact Finset.mem_inter.mp (by rw [hCD]; exact Finset.mem_singleton_self v_cd) |>.1
    by_contra h_neither
    push_neg at h_neither
    have h_sub : t ∩ C ⊆ C \ {v_bc, v_cd} := by
      intro x hx; simp at hx ⊢
      exact ⟨hx.2, fun h => h_neither.1 (h ▸ hx.1), fun h => h_neither.2.1 (h ▸ hx.1)⟩
    have h_C_card : C.card = 3 := by
      have := hM.1.1; simp [hcycle.1] at this
      exact this.2.2.1.2
    have h_distinct : v_bc ≠ v_cd := by
      intro h_eq
      have := hcycle.2.2.2.2.2.2.2.2.2.2.1
      rw [← h_eq, hBC] at hCD
      simp at *
    have h_small : (C \ {v_bc, v_cd}).card ≤ 1 := by
      rw [Finset.card_sdiff (by simp [h_v_in_C.1, h_v_in_C.2])]
      have h_pair : ({v_bc, v_cd} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]; simp [h_distinct]
      omega
    have := Finset.card_le_card h_sub
    omega
  · -- t shares edge with D: contains v_cd or v_da
    have h_inter_D : (t ∩ D).card ≥ 2 := by
      unfold trianglesSharingEdge at hD; simp at hD; exact hD.2
    have h_v_in_D : v_cd ∈ D ∧ v_da ∈ D := by
      constructor
      · exact Finset.mem_inter.mp (by rw [hCD]; exact Finset.mem_singleton_self v_cd) |>.2
      · exact Finset.mem_inter.mp (by rw [hDA]; exact Finset.mem_singleton_self v_da) |>.1
    by_contra h_neither
    push_neg at h_neither
    have h_sub : t ∩ D ⊆ D \ {v_cd, v_da} := by
      intro x hx; simp at hx ⊢
      exact ⟨hx.2, fun h => h_neither.2.1 (h ▸ hx.1), fun h => h_neither.2.2.2 (h ▸ hx.1)⟩
    have h_D_card : D.card = 3 := by
      have := hM.1.1; simp [hcycle.1] at this
      exact this.2.2.2.2
    have h_distinct : v_cd ≠ v_da := by
      intro h_eq
      have := hcycle.2.2.2.2.2.2.2.2.2.2.2
      rw [← h_eq, hCD] at hDA
      simp at *
    have h_small : (D \ {v_cd, v_da}).card ≤ 1 := by
      rw [Finset.card_sdiff (by simp [h_v_in_D.1, h_v_in_D.2])]
      have h_pair : ({v_cd, v_da} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]; simp [h_distinct]
      omega
    have := Finset.card_le_card h_sub
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: LOCAL COVER BOUND
-- ══════════════════════════════════════════════════════════════════════════════

-- At each shared vertex v, triangles containing v that share edge with some packing element
-- can be covered by at most 2 edges incident to v
--
-- Proof: By contradiction using disjoint triples argument
-- If we need 3+ edges, we have 3 triangles each on a different spoke
-- These triangles are pairwise edge-disjoint (share only v)
-- Adding them to the packing (minus the two elements containing v) gives larger packing
-- Contradiction with maximality

lemma tau_containing_v_at_shared_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤ 2 := by
  -- Key insight: Triangles containing v form a "star" structure
  -- They can be covered by 2 spoke edges from v
  -- If 3+ spokes are needed, we get 3 disjoint triangles → contradiction with maximality
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: CYCLE_4 TUZA BOUND
-- ══════════════════════════════════════════════════════════════════════════════

theorem cycle4_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hM_card : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da}) :
    triangleCoveringNumber G ≤ 8 := by
  -- Strategy:
  -- 1. By cycle4_all_triangles_contain_shared, every triangle contains v_ab, v_bc, v_cd, or v_da
  -- 2. Partition triangles: T = T_ab ∪ T_bc ∪ T_cd ∪ T_da
  -- 3. By tau_containing_v_at_shared_le_2, τ(T_v) ≤ 2 for each shared vertex
  -- 4. By tau_union_le_sum, τ ≤ 2 + 2 + 2 + 2 = 8

  -- First establish the partition
  have h_partition : ∀ t ∈ G.cliqueFinset 3,
      t ∈ trianglesContainingVertex G v_ab ∨
      t ∈ trianglesContainingVertex G v_bc ∨
      t ∈ trianglesContainingVertex G v_cd ∨
      t ∈ trianglesContainingVertex G v_da := by
    intro t ht
    have := cycle4_all_triangles_contain_shared G M hM A B C D hcycle v_ab v_bc v_cd v_da hAB hBC hCD hDA t ht
    unfold trianglesContainingVertex
    simp only [Finset.mem_filter]
    tauto

  -- The global covering number equals the covering number on all triangles
  have h_global : triangleCoveringNumber G = triangleCoveringNumberOn G (G.cliqueFinset 3) := by
    unfold triangleCoveringNumber triangleCoveringNumberOn
    congr 1
    ext E'
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
    · intro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩

  rw [h_global]

  -- All triangles are in the union of the four containing sets
  have h_subset : G.cliqueFinset 3 ⊆
      trianglesContainingVertex G v_ab ∪ trianglesContainingVertex G v_bc ∪
      trianglesContainingVertex G v_cd ∪ trianglesContainingVertex G v_da := by
    intro t ht
    have := h_partition t ht
    simp only [Finset.mem_union]
    tauto

  -- τ on subset ≤ τ on superset (monotonicity via covering)
  have h_mono : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤
      triangleCoveringNumberOn G (trianglesContainingVertex G v_ab ∪ trianglesContainingVertex G v_bc ∪
      trianglesContainingVertex G v_cd ∪ trianglesContainingVertex G v_da) := by
    sorry -- Monotonicity of covering number

  calc triangleCoveringNumberOn G (G.cliqueFinset 3)
      ≤ triangleCoveringNumberOn G (trianglesContainingVertex G v_ab ∪ trianglesContainingVertex G v_bc ∪
          trianglesContainingVertex G v_cd ∪ trianglesContainingVertex G v_da) := h_mono
    _ ≤ triangleCoveringNumberOn G (trianglesContainingVertex G v_ab ∪ trianglesContainingVertex G v_bc) +
        triangleCoveringNumberOn G (trianglesContainingVertex G v_cd ∪ trianglesContainingVertex G v_da) := by
          apply tau_union_le_sum
    _ ≤ (triangleCoveringNumberOn G (trianglesContainingVertex G v_ab) +
         triangleCoveringNumberOn G (trianglesContainingVertex G v_bc)) +
        (triangleCoveringNumberOn G (trianglesContainingVertex G v_cd) +
         triangleCoveringNumberOn G (trianglesContainingVertex G v_da)) := by
          apply Nat.add_le_add
          · apply tau_union_le_sum
          · apply tau_union_le_sum
    _ ≤ 2 + 2 + 2 + 2 := by
          -- Apply tau_containing_v_at_shared_le_2 to each vertex
          sorry
    _ = 8 := by ring

end
