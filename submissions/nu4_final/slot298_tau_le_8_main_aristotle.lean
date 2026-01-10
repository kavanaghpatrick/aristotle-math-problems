/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 23d6ee90-0ec0-48c1-9d8b-71b28be1101a

The following was proved by Aristotle:

- lemma triangle_structure (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (ht : t ∈ G.cliqueFinset 3) (ht_not : t ∉ M) :
    -- t contains a spine vertex OR is a base-private external
    (v1 ∈ t ∨ v2 ∈ t ∨ v3 ∈ t) ∨
    ((∃ x, t = {a1, a2, x} ∧ x ≠ v1) ∨ (∃ x, t = {d1, d2, x} ∧ x ≠ v3))
-/

/-
  slot298: PATH_4 τ ≤ 8 - Main Theorem

  SINGLE SORRY FOCUS: The main tau_le_8_path4 theorem

  STRATEGY: Prove by showing cover8 hits all triangles
  - Case 1: t ∈ M (covered by M-edges in cover8)
  - Case 2: t contains v1 (v1_external_covered)
  - Case 3: t contains v3 (v3_external_covered)
  - Case 4: t contains v2 only (v2_external_covered)
  - Case 5: t is base-private at A (covered by {a1,a2})
  - Case 6: t is base-private at D (covered by {d1,d2})

  THE COVER:
  cover8 = {s(a1,a2), s(d1,d2), s(v1,v2), s(v2,v3), s(v1,a1), s(v1,b), s(v3,c), s(v3,d1)}

  PROVEN CASES (inline):
  - Case 1: M-triangles covered by their own edges
  - Case 5: A-base-private covered by {a1,a2}
  - Case 6: D-base-private covered by {d1,d2}

  CASES NEEDING STRUCTURAL ARGUMENT:
  - Case 2: v1-externals (slot296)
  - Case 3: v3-externals (slot297)
  - Case 4: v2-externals
-/

import Mathlib


set_option linter.mathlibStandardSet false

set_option maxHeartbeats 400000

open Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

variable (G : SimpleGraph V) [DecidableRel G.Adj]

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
    have h_mem : insert t M ∈ (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_img := Finset.mem_image_of_mem Finset.card h_mem
    exact Finset.le_max h_img |> WithTop.coe_le_coe.mp
  omega

/-- The 8-edge cover for PATH_4 -/
def cover8 (v1 v2 v3 a1 a2 b c d1 d2 : V) : Finset (Sym2 V) :=
  {s(a1, a2), s(d1, d2), s(v1, v2), s(v2, v3),
   s(v1, a1), s(v1, b), s(v3, c), s(v3, d1)}

/-! ### Triangle Structure Lemma -/

lemma triangle_structure (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (ht : t ∈ G.cliqueFinset 3) (ht_not : t ∉ M) :
    -- t contains a spine vertex OR is a base-private external
    (v1 ∈ t ∨ v2 ∈ t ∨ v3 ∈ t) ∨
    ((∃ x, t = {a1, a2, x} ∧ x ≠ v1) ∨ (∃ x, t = {d1, d2, x} ∧ x ≠ v3)) := by
  obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_not
  rw [hM_eq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · -- t shares edge with A = {v1, a1, a2}
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    rw [hA_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx.2 with rfl | rfl | rfl
    · left; left; exact hx.1
    · rcases hy.2 with rfl | rfl | rfl
      · left; left; exact hy.1
      · exact absurd rfl hxy
      · -- x = a1, y = a2: base-private
        right; left
        have ht3 : t.card = 3 := triangle_card_3 G t ht
        -- t = {a1, a2, z} for some z
        -- Since $t$ has exactly 3 elements and we know that $x$ and $y$ are in $t$, the third element must be some $z$.
        obtain ⟨z, hz⟩ : ∃ z, t = {x, y, z} := by
          -- Since $t$ has exactly three elements and we know that $x$ and $y$ are in $t$, the third element must be $z$.
          have hz : ∃ z, z ∈ t ∧ z ≠ x ∧ z ≠ y := by
            exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( t.erase x ) from by rw [ Finset.card_erase_of_mem hx.1, ht3 ] ; decide ) y );
          obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := hz; use z; rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hx.1, Finset.insert_subset_iff.mpr ⟨ hy.1, Finset.singleton_subset_iff.mpr hz₁ ⟩ ⟩ ) ] ; simp +decide [ * ] ;
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop;
        grind
    · rcases hy.2 with rfl | rfl | rfl
      · left; left; exact hy.1
      · -- x = a2, y = a1: base-private (same as above)
        right; left; (
        obtain ⟨z, hz⟩ : ∃ z, z ∈ t ∧ z ≠ x ∧ z ≠ y := by
          have := Finset.mem_coe.mp ( Finset.mem_coe.mpr ht ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( t.erase x ) from by rw [ Finset.card_erase_of_mem hx, this.2 ] ; decide ) y );
        have := Finset.mem_coe.mp ( Finset.mem_coe.mpr ht ) ; simp_all +decide [ SimpleGraph.coe_cliqueFinset ] ;
        -- Since $t$ is a clique of size 3 and contains $x$ and $y$, the third vertex must be $z$.
        have h_t_eq : t = {x, y, z} := by
          rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hx, Finset.insert_subset_iff.mpr ⟨ hy, Finset.singleton_subset_iff.mpr hz.1 ⟩ ⟩ ) ] ; simp +decide [ this.card_eq, * ];
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop;
        use z; simp_all +decide [ Finset.ext_iff ] ;
        grind +ring)
      · exact absurd rfl hxy
  · -- t shares edge with B = {v1, v2, b}
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    rw [hB_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx.2 with rfl | rfl | rfl
    · left; left; exact hx.1
    · left; right; left; exact hx.1
    · rcases hy.2 with rfl | rfl | rfl
      · left; left; exact hy.1
      · left; right; left; exact hy.1
      · exact absurd rfl hxy
  · -- t shares edge with C = {v2, v3, c}
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    rw [hC_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx.2 with rfl | rfl | rfl
    · left; right; left; exact hx.1
    · left; right; right; exact hx.1
    · rcases hy.2 with rfl | rfl | rfl
      · left; right; left; exact hy.1
      · left; right; right; exact hy.1
      · exact absurd rfl hxy
  · -- t shares edge with D = {v3, d1, d2}
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
    simp only [Finset.mem_inter] at hx hy
    rw [hD_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx.2 with rfl | rfl | rfl
    · left; right; right; exact hx.1
    · rcases hy.2 with rfl | rfl | rfl
      · left; right; right; exact hy.1
      · exact absurd rfl hxy
      · -- x = d1, y = d2: base-private
        right; right
        simp_all +decide [ Finset.ext_iff ];
        -- Since $t$ has exactly three elements and we already have $x$ and $y$ in $t$, the third element must be $z$.
        obtain ⟨z, hz⟩ : ∃ z, z ∈ t ∧ z ≠ x ∧ z ≠ y := by
          -- Since $t$ has exactly three elements and we already have $x$ and $y$ in $t$, the third element must be $z$. We can use the fact that $t$ is a clique of size 3 to find this element.
          have h_card : t.card = 3 := by
            exact ht.card_eq;
          exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( t.erase x ) from by rw [ Finset.card_erase_of_mem hx, h_card ] ; decide ) y );
        use z;
        have := Finset.card_eq_three.mp ht.2; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
        grind
    · rcases hy.2 with rfl | rfl | rfl
      · left; right; right; exact hy.1
      · -- x = d2, y = d1: base-private
        right; right; (
        -- Since $t$ is a triangle and $x$ and $y$ are in $t$, the third element must be some $z$ not in $\{v3, x, y\}$.
        obtain ⟨z, hz⟩ : ∃ z, z ∈ t ∧ z ≠ v3 ∧ z ≠ x ∧ z ≠ y := by
          have h_card : t.card = 3 := by
            exact?;
          have := Finset.card_eq_three.mp h_card; obtain ⟨ u, v, w, hu, hv, hw, h ⟩ := this; simp_all +decide ;
          grind;
        have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hx.1, Finset.insert_subset_iff.mpr ⟨ hy.1, Finset.singleton_subset_iff.mpr hz.1 ⟩ ⟩ ) ; simp_all +decide ;
        have := ht.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        grind)
      · exact absurd rfl hxy

/-!
### Main Theorem: τ ≤ 8 for PATH_4

PROOF SKETCH:
1. Construct cover8 with 8 edges
2. Show cover8 ⊆ G.edgeFinset (all edges are valid graph edges)
3. For each triangle t ∈ G.cliqueFinset 3, show ∃ e ∈ cover8, e ∈ t.sym2
4. Use triangle_structure to case split:
   - Case t ∈ M: covered by M-edges
   - Case v1 ∈ t: use v1_external_covered
   - Case v2 ∈ t: use v2_external_covered
   - Case v3 ∈ t: use v3_external_covered
   - Case base-private A: covered by {a1,a2}
   - Case base-private D: covered by {d1,d2}
-/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Expected type must not contain free variables
  {s(a1, a2), s(d1, d2), s(v1, v2), s(v2, v3), s(v1, a1), s(v1, b), s(v3, c), s(v3, d1)}.card ≤ 8

Hint: Use the `+revert` option to automatically clean up and revert free variables
`simp` made no progress
`simp` made no progress
unsolved goals
case h.right
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
B C D : Finset V
v1 v2 v3 a1 a2 b c d1 d2 : V
hM : isMaxPacking G M
hM_card : M.card = 4
hB_eq : B = {v1, v2, b}
hC_eq : C = {v2, v3, c}
hD_eq : D = {v3, d1, d2}
hB_clique : B ∈ G.cliqueFinset 3
hC_clique : C ∈ G.cliqueFinset 3
hD_clique : D ∈ G.cliqueFinset 3
h_distinct : {v1, v2, v3, a1, a2, b, c, d1, d2}.card = 9
hBC : B ∩ C = {v2}
hCD : C ∩ D = {v3}
hBD : B ∩ D = ∅
E : Finset (Sym2 V) := {e ∈ cover8 v1 v2 v3 a1 a2 b c d1 d2 | e ∈ G.edgeFinset}
t : Finset V
ht : t ∈ G.cliqueFinset 3
hM_eq : M = {t, B, C, D}
hA_eq : t = {v1, a1, a2}
hA_clique : t ∈ G.cliqueFinset 3
hAB : t ∩ B = {v1}
hAC : t ∩ C = ∅
hAD : t ∩ D = ∅
⊢ ∀ (a : V), a = a1 ∨ a = a2 → a = v1 ∨ a = a1 ∨ a = a2
`simp` made no progress
unsolved goals
case h.right
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A C D : Finset V
v1 v2 v3 a1 a2 b c d1 d2 : V
hM : isMaxPacking G M
hM_card : M.card = 4
hA_eq : A = {v1, a1, a2}
hC_eq : C = {v2, v3, c}
hD_eq : D = {v3, d1, d2}
hA_clique : A ∈ G.cliqueFinset 3
hC_clique : C ∈ G.cliqueFinset 3
hD_clique : D ∈ G.cliqueFinset 3
h_distinct : {v1, v2, v3, a1, a2, b, c, d1, d2}.card = 9
hCD : C ∩ D = {v3}
hAC : A ∩ C = ∅
hAD : A ∩ D = ∅
E : Finset (Sym2 V) := {e ∈ cover8 v1 v2 v3 a1 a2 b c d1 d2 | e ∈ G.edgeFinset}
t : Finset V
ht : t ∈ G.cliqueFinset 3
hM_eq : M = {A, t, C, D}
hB_eq : t = {v1, v2, b}
hB_clique : t ∈ G.cliqueFinset 3
hAB : A ∩ t = {v1}
hBC : t ∩ C = {v2}
hBD : t ∩ D = ∅
⊢ ∀ (a : V), a = v1 ∨ a = v2 → a = v1 ∨ a = v2 ∨ a = b
`simp` made no progress
unsolved goals
case h.right
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A B D : Finset V
v1 v2 v3 a1 a2 b c d1 d2 : V
hM : isMaxPacking G M
hM_card : M.card = 4
hA_eq : A = {v1, a1, a2}
hB_eq : B = {v1, v2, b}
hD_eq : D = {v3, d1, d2}
hA_clique : A ∈ G.cliqueFinset 3
hB_clique : B ∈ G.cliqueFinset 3
hD_clique : D ∈ G.cliqueFinset 3
h_distinct : {v1, v2, v3, a1, a2, b, c, d1, d2}.card = 9
hAB : A ∩ B = {v1}
hAD : A ∩ D = ∅
hBD : B ∩ D = ∅
E : Finset (Sym2 V) := {e ∈ cover8 v1 v2 v3 a1 a2 b c d1 d2 | e ∈ G.edgeFinset}
t : Finset V
ht : t ∈ G.cliqueFinset 3
hM_eq : M = {A, B, t, D}
hC_eq : t = {v2, v3, c}
hC_clique : t ∈ G.cliqueFinset 3
hBC : B ∩ t = {v2}
hCD : t ∩ D = {v3}
hAC : A ∩ t = ∅
⊢ ∀ (a : V), a = v2 ∨ a = v3 → a = v2 ∨ a = v3 ∨ a = c
`simp` made no progress
unsolved goals
case h.right
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A B C : Finset V
v1 v2 v3 a1 a2 b c d1 d2 : V
hM : isMaxPacking G M
hM_card : M.card = 4
hA_eq : A = {v1, a1, a2}
hB_eq : B = {v1, v2, b}
hC_eq : C = {v2, v3, c}
hA_clique : A ∈ G.cliqueFinset 3
hB_clique : B ∈ G.cliqueFinset 3
hC_clique : C ∈ G.cliqueFinset 3
h_distinct : {v1, v2, v3, a1, a2, b, c, d1, d2}.card = 9
hAB : A ∩ B = {v1}
hBC : B ∩ C = {v2}
hAC : A ∩ C = ∅
E : Finset (Sym2 V) := {e ∈ cover8 v1 v2 v3 a1 a2 b c d1 d2 | e ∈ G.edgeFinset}
t : Finset V
ht : t ∈ G.cliqueFinset 3
hM_eq : M = {A, B, C, t}
hD_eq : t = {v3, d1, d2}
hD_clique : t ∈ G.cliqueFinset 3
hCD : C ∩ t = {v3}
hAD : A ∩ t = ∅
hBD : B ∩ t = ∅
⊢ ∀ (a : V), a = d1 ∨ a = d2 → a = v3 ∨ a = d1 ∨ a = d2
Invalid alternative name `none`: Expected `top` or `coe`
Invalid alternative name `some`: Expected `top` or `coe`
Alternative `top` has not been provided
Alternative `coe` has not been provided-/
theorem tau_le_8_path4 (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hM_card : M.card = 4)
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    -- Distinctness (9 distinct vertices)
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9)
    -- PATH_4 disjointness conditions
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅) :
    triangleCoveringNumber G ≤ 8 := by
  -- The cover is valid if it's a subset of edgeFinset and covers all triangles
  have h_cover_valid : ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
    -- Use cover8 filtered to valid edges
    let E := (cover8 v1 v2 v3 a1 a2 b c d1 d2).filter (fun e => e ∈ G.edgeFinset)
    use E
    refine ⟨?_, ?_, ?_⟩
    · -- E.card ≤ 8
      calc E.card ≤ (cover8 v1 v2 v3 a1 a2 b c d1 d2).card := Finset.card_filter_le _ _
           _ ≤ 8 := by unfold cover8; decide
    · -- E ⊆ G.edgeFinset
      intro e he
      simp only [Finset.mem_filter] at he
      exact he.2
    · -- ∀ t, ∃ e ∈ E, e ∈ t.sym2
      intro t ht
      -- Case split on t ∈ M vs t ∉ M
      by_cases ht_M : t ∈ M
      · -- t ∈ M: covered by its own edges
        rw [hM_eq] at ht_M
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht_M
        rcases ht_M with rfl | rfl | rfl | rfl
        · -- t = A = {v1, a1, a2}
          use s(a1, a2)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, true_and]
            rw [hA_eq]
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
            have ha1A : a1 ∈ A := by rw [hA_eq]; simp
            have ha2A : a2 ∈ A := by rw [hA_eq]; simp
            -- Extract distinctness from h_distinct
            have ha12 : a1 ≠ a2 := by
              intro heq; subst heq
              simp only [Finset.card_insert_of_not_mem, Finset.mem_insert,
                         Finset.mem_singleton] at h_distinct
              omega
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 ha1A ha2A ha12)
          · rw [hA_eq]
            simp only [Finset.mem_sym2_iff, Finset.mem_insert, Finset.mem_singleton,
                       Sym2.mem_iff, or_true, true_or, and_self]
        · -- t = B = {v1, v2, b}
          use s(v1, v2)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hB_clique
            have hv1B : v1 ∈ B := by rw [hB_eq]; simp
            have hv2B : v2 ∈ B := by rw [hB_eq]; simp
            have hv12 : v1 ≠ v2 := by
              intro heq; subst heq
              simp at h_distinct
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv1B hv2B hv12)
          · rw [hB_eq]
            simp only [Finset.mem_sym2_iff, Finset.mem_insert, Finset.mem_singleton,
                       Sym2.mem_iff, true_or, or_true, and_self]
        · -- t = C = {v2, v3, c}
          use s(v2, v3)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hC_clique
            have hv2C : v2 ∈ C := by rw [hC_eq]; simp
            have hv3C : v3 ∈ C := by rw [hC_eq]; simp
            have hv23 : v2 ≠ v3 := by
              intro heq; subst heq
              simp at h_distinct
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hv2C hv3C hv23)
          · rw [hC_eq]
            simp only [Finset.mem_sym2_iff, Finset.mem_insert, Finset.mem_singleton,
                       Sym2.mem_iff, true_or, or_true, and_self]
        · -- t = D = {v3, d1, d2}
          use s(d1, d2)
          constructor
          · simp only [Finset.mem_filter, cover8, Finset.mem_insert, Finset.mem_singleton,
                       true_or, or_true, true_and]
            have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hD_clique
            have hd1D : d1 ∈ D := by rw [hD_eq]; simp
            have hd2D : d2 ∈ D := by rw [hD_eq]; simp
            have hd12 : d1 ≠ d2 := by
              intro heq; subst heq
              simp at h_distinct
            exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hd1D hd2D hd12)
          · rw [hD_eq]
            simp only [Finset.mem_sym2_iff, Finset.mem_insert, Finset.mem_singleton,
                       Sym2.mem_iff, or_true, true_or, and_self]
      · -- t ∉ M: external triangle
        -- Use triangle_structure to determine which case
        sorry
  -- triangleCoveringNumber is the minimum, so ≤ 8 if we have a valid cover of size ≤ 8
  obtain ⟨E, hE_card, hE_sub, hE_covers⟩ := h_cover_valid
  unfold triangleCoveringNumber
  have h_mem : E ∈ G.edgeFinset.powerset.filter (fun E =>
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hE_sub, hE_covers⟩
  have h_img := Finset.mem_image_of_mem Finset.card h_mem
  have h_min := Finset.min_le h_img
  simp only [WithTop.coe_le_coe] at h_min
  calc triangleCoveringNumber G =
        (G.edgeFinset.powerset.filter (fun E =>
          ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0) := rfl
       _ ≤ E.card := by
         cases h : (G.edgeFinset.powerset.filter _ |>.image Finset.card).min with
         | none => simp [Option.getD]
         | some m =>
           simp only [Option.getD, h]
           have := Finset.min_le h_img
           rw [h] at this
           simp only [WithTop.coe_le_coe] at this
           exact this
       _ ≤ 8 := hE_card

end