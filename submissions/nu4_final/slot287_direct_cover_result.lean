/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6465a625-6b81-4601-8d71-a9e84d119fe8
-/

/-
  slot287: PATH_4 τ ≤ 8 - Direct Cover Construction

  DATE: Jan 7, 2026

  KEY INSIGHT: Use triangle_structure (PROVEN in slot285) directly.

  Simpler approach: Prove existence of 8-edge cover without explicit construction.
  The cover is: A.sym2 ∩ edges ∪ D.sym2 ∩ edges (6 edges max, covers endpoints)
               + 2 middle edges (covers spine triangles)
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 400000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Core Definitions -/

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-! ### PATH_4 Predicate -/

def isPath4Config (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (A B C D : Finset V) (v1 v2 v3 : V) : Prop :=
  M = {A, B, C, D} ∧
  A ∈ G.cliqueFinset 3 ∧ B ∈ G.cliqueFinset 3 ∧ C ∈ G.cliqueFinset 3 ∧ D ∈ G.cliqueFinset 3 ∧
  A ∩ B = {v1} ∧ B ∩ C = {v2} ∧ C ∩ D = {v3} ∧
  A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ D = ∅ ∧
  v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### PROVEN Lemmas -/

lemma triangle_card_3 (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 := by
  simp only [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff, Finset.mem_filter] at ht
  exact ht.2

lemma edge_in_triangle_sym2 (t : Finset V) (u w : V) (hu : u ∈ t) (hw : w ∈ t) :
    s(u, w) ∈ t.sym2 := by
  simp only [Finset.mem_sym2_iff]
  exact ⟨hu, hw⟩

lemma max_packing_shares_edge (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not : t ∉ M) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  by_contra h
  push_neg at h
  have h_packing : isTrianglePacking G (insert t M) := by
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM.1.1 hx
    · intro x hx y hy hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact Nat.lt_succ_iff.mp (h y hy)
      · rw [Finset.inter_comm]; exact Nat.lt_succ_iff.mp (h x hx)
      · exact hM.1.2 hx hy hxy
  have h_card : (insert t M).card = M.card + 1 := Finset.card_insert_of_not_mem ht_not
  have h_le : (insert t M).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : insert t M ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_img := Finset.mem_image_of_mem Finset.card h_mem
    exact Finset.le_max h_img |> WithTop.coe_le_coe.mp
  omega

/-! ### PROVEN: Triangle Structure -/

theorem triangle_structure (M : Finset (Finset V)) (A B C D : Finset V) (v1 v2 v3 : V)
    (hM : isMaxPacking G M)
    (hPath : isPath4Config G M A B C D v1 v2 v3)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v1 ∈ t ∨ v2 ∈ t ∨ v3 ∈ t ∨
    ((t ∩ A).card ≥ 2 ∧ v1 ∉ t) ∨
    ((t ∩ D).card ≥ 2 ∧ v3 ∉ t) := by
  by_contra h_contra
  push_neg at h_contra
  obtain ⟨hv1, hv2, hv3, hA_not, hD_not⟩ := h_contra
  by_cases ht_in : t ∈ M
  · rw [hPath.1] at ht_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
    rcases ht_in with rfl | rfl | rfl | rfl
    · have hv1_in_A : v1 ∈ A := by
        have := hPath.2.2.2.2.1
        rw [Finset.ext_iff] at this
        exact (this v1).mpr (by simp) |>.1
      exact hv1 hv1_in_A
    · have hv1_in_B : v1 ∈ B := by
        have := hPath.2.2.2.2.1
        rw [Finset.ext_iff] at this
        exact (this v1).mpr (by simp) |>.2
      exact hv1 hv1_in_B
    · have hv2_in_C : v2 ∈ C := by
        have := hPath.2.2.2.2.2.1
        rw [Finset.ext_iff] at this
        exact (this v2).mpr (by simp) |>.2
      exact hv2 hv2_in_C
    · have hv3_in_D : v3 ∈ D := by
        have := hPath.2.2.2.2.2.2.1
        rw [Finset.ext_iff] at this
        exact (this v3).mpr (by simp) |>.2
      exact hv3 hv3_in_D
  · obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_in
    rw [hPath.1] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact hA_not ⟨h_share, hv1⟩
    · have hB3 : B.card = 3 := triangle_card_3 G B hPath.2.1.2.1
      have h_sub : t ∩ B ⊆ B \ {v1, v2} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        exact ⟨hx.2, fun h => by cases h <;> simp_all⟩
      have h_card_rest : (B \ {v1, v2}).card ≤ 1 := by
        have hv1_in : v1 ∈ B := by
          have := hPath.2.2.2.2.1; rw [Finset.ext_iff] at this
          exact (this v1).mpr (by simp) |>.2
        have hv2_in : v2 ∈ B := by
          have := hPath.2.2.2.2.2.1; rw [Finset.ext_iff] at this
          exact (this v2).mpr (by simp) |>.1
        calc (B \ {v1, v2}).card = B.card - ({v1, v2} ∩ B).card := by
               rw [Finset.card_sdiff_add_card_inter]; ring
             _ ≤ 3 - 2 := by simp [hB3, hv1_in, hv2_in, hPath.2.2.2.2.2.2.2.2.1]
             _ = 1 := by norm_num
      have := Finset.card_le_card h_sub
      omega
    · have hC3 : C.card = 3 := triangle_card_3 G C hPath.2.1.2.2.1
      have h_sub : t ∩ C ⊆ C \ {v2, v3} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        exact ⟨hx.2, fun h => by cases h <;> simp_all⟩
      have h_card_rest : (C \ {v2, v3}).card ≤ 1 := by
        have hv2_in : v2 ∈ C := by
          have := hPath.2.2.2.2.2.1; rw [Finset.ext_iff] at this
          exact (this v2).mpr (by simp) |>.2
        have hv3_in : v3 ∈ C := by
          have := hPath.2.2.2.2.2.2.1; rw [Finset.ext_iff] at this
          exact (this v3).mpr (by simp) |>.1
        calc (C \ {v2, v3}).card = C.card - ({v2, v3} ∩ C).card := by
               rw [Finset.card_sdiff_add_card_inter]; ring
             _ ≤ 3 - 2 := by simp [hC3, hv2_in, hv3_in, hPath.2.2.2.2.2.2.2.2.2.1]
             _ = 1 := by norm_num
      have := Finset.card_le_card h_sub
      omega
    · exact hD_not ⟨h_share, hv3⟩

/-! ### Main Theorem: Existential Form -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid projection: Expected a value whose type is a structure
  hPath.right.left
has type
  Quot.lift (fun (l : List (Finset V)) => A ∈ l) ⋯ (G.cliqueFinset 3).val
Invalid projection: Expected a value whose type is a structure
  hPath.right.left
has type
  Quot.lift (fun (l : List (Finset V)) => A ∈ l) ⋯ (G.cliqueFinset 3).val
Invalid projection: Expected a value whose type is a structure
  hPath.right.left
has type
  Quot.lift (fun (l : List (Finset V)) => A ∈ l) ⋯ (G.cliqueFinset 3).val
Invalid projection: Expected a value whose type is a structure
  hPath.right.left
has type
  Quot.lift (fun (l : List (Finset V)) => A ∈ l) ⋯ (G.cliqueFinset 3).val
Tactic `rcases` failed: `h✝ : Quot.lift (fun (l : List (Sym2 V)) => e ∈ l) ⋯ coverA.val` is not an inductive datatype
Tactic `constructor` failed: target is not an inductive datatype

case h.left.h.h
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A B C D : Finset V
v1 v2 v3 : V
hM : isMaxPacking G M
hPath : isPath4Config G M A B C D v1 v2 v3
hA3 : A.card = 3
hB3 : B.card = 3
hC3 : C.card = 3
hD3 : D.card = 3
coverA : Finset (Sym2 V) := ⋯
coverD : Finset (Sym2 V) := ⋯
coverMiddle : Finset (Sym2 V) := ⋯
t : Finset V
ht : t ∈ G.cliqueFinset 3
hA_share : (t ∩ A).card ≥ 2
hv1_not : v1 ∉ t
x y : V
hxy : x ≠ y
hx : x ∈ t ∧ x ∈ A
hy : y ∈ t ∧ y ∈ A
⊢ s(x, y) ∈ coverA
Tactic `constructor` failed: target is not an inductive datatype

case h.left.h.h
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A B C D : Finset V
v1 v2 v3 : V
hM : isMaxPacking G M
hPath : isPath4Config G M A B C D v1 v2 v3
hA3 : A.card = 3
hB3 : B.card = 3
hC3 : C.card = 3
hD3 : D.card = 3
coverA : Finset (Sym2 V) := ⋯
coverD : Finset (Sym2 V) := ⋯
coverMiddle : Finset (Sym2 V) := ⋯
t : Finset V
ht : t ∈ G.cliqueFinset 3
hD_share : (t ∩ D).card ≥ 2
hv3_not : v3 ∉ t
x y : V
hxy : x ≠ y
hx : x ∈ t ∧ x ∈ D
hy : y ∈ t ∧ y ∈ D
⊢ s(x, y) ∈ coverD-/
/--
PROOF STRATEGY (existential - let Aristotle find the cover):

By triangle_structure, every triangle t contains a spine vertex OR is endpoint-private.
We claim there exist 8 edges covering all triangles.

The proof proceeds by:
1. For each triangle t, identify which case it falls into
2. Show an edge from our claimed cover hits t
3. Bound the cover size by 8 via cardinality arguments

INFORMAL PROOF SKETCH:
- Use A's 3 edges: covers A and all A-related triangles (spine v1 or A-private)
- Use D's 3 edges: covers D and all D-related triangles (spine v3 or D-private)
- Use 2 edges from B ∪ C touching v2: covers v2 triangles
- Total: at most 3 + 3 + 2 = 8 edges
-/
theorem tau_le_8_path4 (M : Finset (Finset V)) (A B C D : Finset V) (v1 v2 v3 : V)
    (hM : isMaxPacking G M)
    (hPath : isPath4Config G M A B C D v1 v2 v3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Helper facts about triangle cardinalities
  have hA3 : A.card = 3 := triangle_card_3 G A hPath.2.1.1
  have hB3 : B.card = 3 := triangle_card_3 G B hPath.2.1.2.1
  have hC3 : C.card = 3 := triangle_card_3 G C hPath.2.1.2.2.1
  have hD3 : D.card = 3 := triangle_card_3 G D hPath.2.1.2.2.2
  -- Use A.sym2 ∪ D.sym2 filtered to edges, plus middle edges
  let coverA := A.sym2.filter (fun e => e ∈ G.edgeFinset)
  let coverD := D.sym2.filter (fun e => e ∈ G.edgeFinset)
  -- For middle: pick edges from B and C that touch v2
  let coverMiddle := B.sym2.filter (fun e => e ∈ G.edgeFinset ∧ s(v2, v2) ≠ e ∧
                     (∃ x ∈ B, e = s(v2, x))) ∪
                     C.sym2.filter (fun e => e ∈ G.edgeFinset ∧ s(v2, v2) ≠ e ∧
                     (∃ x ∈ C, e = s(v2, x)))
  use coverA ∪ coverD ∪ coverMiddle
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 8
    -- A.sym2 has ≤ 3 edges, D.sym2 has ≤ 3 edges, middle has ≤ 4 edges but overlaps
    sorry
  · -- Subset of G.edgeFinset
    intro e he
    simp only [Finset.mem_union, Finset.mem_filter] at he
    rcases he with ⟨_, h⟩ | ⟨_, h⟩ | h
    · exact h
    · exact h
    · simp only [Finset.mem_union, Finset.mem_filter] at h
      rcases h with ⟨_, h', _⟩ | ⟨_, h', _⟩ <;> exact h'
  · -- Covers all triangles
    intro t ht
    have h_struct := triangle_structure G M A B C D v1 v2 v3 hM hPath t ht
    rcases h_struct with hv1 | hv2 | hv3 | ⟨hA_share, hv1_not⟩ | ⟨hD_share, hv3_not⟩
    · -- Case 1: v1 ∈ t
      -- v1 ∈ A, so if t shares edge with A, we're done via coverA
      -- Need to show t shares some edge with A (since v1 ∈ t ∩ A)
      sorry
    · -- Case 2: v2 ∈ t
      -- v2 ∈ B ∩ C, covered by middle edges
      sorry
    · -- Case 3: v3 ∈ t
      -- v3 ∈ D, so similar to case 1 via coverD
      sorry
    · -- Case 4: A-base-private
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hA_share
      simp only [Finset.mem_inter] at hx hy
      use s(x, y)
      constructor
      · simp only [Finset.mem_union, Finset.mem_filter]
        left; left
        constructor
        · simp only [Finset.mem_sym2_iff]; exact ⟨hx.2, hy.2⟩
        · have hclique := SimpleGraph.mem_cliqueFinset_iff.mp ht
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hx.1 hy.1 hxy)
      · exact edge_in_triangle_sym2 t x y hx.1 hy.1
    · -- Case 5: D-base-private
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hD_share
      simp only [Finset.mem_inter] at hx hy
      use s(x, y)
      constructor
      · simp only [Finset.mem_union, Finset.mem_filter]
        left; right
        constructor
        · simp only [Finset.mem_sym2_iff]; exact ⟨hx.2, hy.2⟩
        · have hclique := SimpleGraph.mem_cliqueFinset_iff.mp ht
          exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hx.1 hy.1 hxy)
      · exact edge_in_triangle_sym2 t x y hx.1 hy.1

end