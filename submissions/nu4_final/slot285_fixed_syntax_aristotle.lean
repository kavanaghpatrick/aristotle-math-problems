/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f8caa122-c7fb-4922-a360-58d6b172e4c8
-/

/-
  slot285: PATH_4 τ ≤ 8 via ADAPTIVE Cover - FIXED SYNTAX

  DATE: Jan 7, 2026

  FIXES from slot284:
  - Use proven header settings (relaxedAutoImplicit false, autoImplicit false)
  - Use isPath4 predicate instead of structure
  - Explicit vertex parameters throughout
  - Pattern from proven/tuza/nu4/path4_scaffolding_complete.lean

  MATHEMATICAL CONTENT (unchanged):
  - Adaptive cover selects edges based on which private triangles exist
  - Mutual exclusion: A-base-private and A-spoke2-private cannot coexist
  - Total: exactly 8 edges in all cases
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Inhabited V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inhabited V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
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

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

/-! ### PATH_4 as Predicate (not structure) -/

/-- PATH_4 configuration: A-B-C-D with spine vertices v1, v2, v3 -/
def isPath4Config (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (A B C D : Finset V) (v1 v2 v3 : V) : Prop :=
  -- M consists of exactly A, B, C, D
  M = {A, B, C, D} ∧
  -- All are triangles in G
  A ∈ G.cliqueFinset 3 ∧ B ∈ G.cliqueFinset 3 ∧ C ∈ G.cliqueFinset 3 ∧ D ∈ G.cliqueFinset 3 ∧
  -- PATH_4 intersection structure
  A ∩ B = {v1} ∧ B ∩ C = {v2} ∧ C ∩ D = {v3} ∧
  A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ D = ∅ ∧
  -- Spine vertices are distinct
  v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3

/-! ### Helper Lemmas -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- PROVEN: Triangle has 3 vertices
lemma triangle_card_3 (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 := by
  simp only [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff, Finset.mem_filter] at ht
  exact ht.2

-- PROVEN: Edge membership
lemma edge_mem_iff (u w : V) : s(u, w) ∈ G.edgeFinset ↔ G.Adj u w := by
  simp [SimpleGraph.mem_edgeFinset]

-- PROVEN: Edge in triangle
lemma edge_in_triangle_sym2 (t : Finset V) (u w : V) (hu : u ∈ t) (hw : w ∈ t) :
    s(u, w) ∈ t.sym2 := by
  simp only [Finset.mem_sym2_iff]
  exact ⟨hu, hw⟩

-- PROVEN: Maximality implies edge-sharing
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

/-! ### PATH_4 Vertex Extraction -/

-- Given PATH_4, extract the non-spine vertices
-- A = {v1, a1, a2}, B = {v1, v2, b}, C = {v2, v3, c}, D = {v3, d1, d2}

/-- Check if A-base-private triangles exist (triangle through {a1,a2} avoiding v1) -/
def hasBasePrivateA (A : Finset V) (v1 : V) : Prop :=
  ∃ t ∈ G.cliqueFinset 3, (t ∩ A).card ≥ 2 ∧ v1 ∉ t

/-- Check if D-base-private triangles exist -/
def hasBasePrivateD (D : Finset V) (v3 : V) : Prop :=
  ∃ t ∈ G.cliqueFinset 3, (t ∩ D).card ≥ 2 ∧ v3 ∉ t

/-! ### Adaptive Cover Construction -/

/--
ADAPTIVE COVER for PATH_4:

For endpoint A = {v1, a1, a2}:
- If base-private exists: use {v1-a1, a1-a2} (spoke + base)
- Else: use {v1-a1, v1-a2} (both spokes)

For middle B, C: always use both spokes (needed for cross-triangles)

For endpoint D = {v3, d1, d2}: similar to A
-/
noncomputable def adaptivePath4Cover
    (A B C D : Finset V) (v1 v2 v3 : V)
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3) (hD : D.card = 3)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3}) : Finset (Sym2 V) :=
  -- Extract non-spine vertices (using Finset operations)
  let A_rest := A \ {v1}  -- {a1, a2}
  let B_rest := B \ {v1, v2}  -- {b}
  let C_rest := C \ {v2, v3}  -- {c}
  let D_rest := D \ {v3}  -- {d1, d2}
  -- For A: 2 edges
  let coverA := A_rest.sym2.filter (fun e => e ∈ G.edgeFinset)  -- base {a1,a2} if edge
                ∪ (A_rest.biUnion (fun a => {s(v1, a)})).filter (fun e => e ∈ G.edgeFinset)  -- spokes
  -- For B: spokes from b to v1 and v2
  let coverB := (B_rest.biUnion (fun b => {s(v1, b), s(v2, b)})).filter (fun e => e ∈ G.edgeFinset)
  -- For C: spokes from c to v2 and v3
  let coverC := (C_rest.biUnion (fun c => {s(v2, c), s(v3, c)})).filter (fun e => e ∈ G.edgeFinset)
  -- For D: 2 edges
  let coverD := D_rest.sym2.filter (fun e => e ∈ G.edgeFinset)  -- base {d1,d2} if edge
                ∪ (D_rest.biUnion (fun d => {s(v3, d)})).filter (fun e => e ∈ G.edgeFinset)  -- spokes
  -- Select adaptively for A and D
  let finalA := if hasBasePrivateA G A v1
                then (A_rest.sym2 ∪ {s(v1, A_rest.toList.head!)}).filter (fun e => e ∈ G.edgeFinset)
                else (A_rest.biUnion (fun a => {s(v1, a)})).filter (fun e => e ∈ G.edgeFinset)
  let finalD := if hasBasePrivateD G D v3
                then (D_rest.sym2 ∪ {s(v3, D_rest.toList.head!)}).filter (fun e => e ∈ G.edgeFinset)
                else (D_rest.biUnion (fun d => {s(v3, d)})).filter (fun e => e ∈ G.edgeFinset)
  finalA ∪ coverB ∪ coverC ∪ finalD

/-! ### Main Theorems -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  adaptivePath4Cover
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Tactic `unfold` failed: Local variable `adaptivePath4Cover` has no definition-/
/--
PROOF SKETCH for card ≤ 8:
- finalA: 2 edges (either spoke+base or both spokes)
- coverB: 2 edges (spokes from b)
- coverC: 2 edges (spokes from c)
- finalD: 2 edges (either spoke+base or both spokes)
- Total: 8 edges
-/
lemma adaptivePath4Cover_card_le_8
    (A B C D : Finset V) (v1 v2 v3 : V)
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3) (hD : D.card = 3)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3}) :
    (adaptivePath4Cover G A B C D v1 v2 v3 hA hB hC hD hAB hBC hCD).card ≤ 8 := by
  unfold adaptivePath4Cover
  -- Each component has at most 2 edges after filtering
  -- A_rest has 2 elements, B_rest has 1, C_rest has 1, D_rest has 2
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Unknown identifier `G.edgeFinset`
Function expected at
  adaptivePath4Cover
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G-/
/--
PROOF SKETCH for subset edges:
All edges in the cover are filtered to be in G.edgeFinset
-/
lemma adaptivePath4Cover_subset
    (A B C D : Finset V) (v1 v2 v3 : V)
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3) (hD : D.card = 3)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3}) :
    adaptivePath4Cover G A B C D v1 v2 v3 hA hB hC hD hAB hBC hCD ⊆ G.edgeFinset := by
  unfold adaptivePath4Cover
  intro e he
  simp only [Finset.mem_union, Finset.mem_filter] at he
  rcases he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `G.cliqueFinset`
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isPath4Config
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/--
KEY LEMMA: Triangle structure for PATH_4

Every triangle t in G either:
1. Contains a spine vertex (v1, v2, or v3)
2. Is A-base-private (shares base {a1,a2} with A, avoids v1)
3. Is D-base-private (shares base {d1,d2} with D, avoids v3)

PROOF SKETCH:
- By maximality, t shares edge with some M-element
- If t avoids all spine vertices:
  - Can't share edge with B (B = {v1,v2,b}, avoiding v1,v2 leaves only b, need 2 vertices)
  - Can't share edge with C (similar)
  - So t shares edge with A or D
  - Sharing edge with A while avoiding v1 means t ⊇ {a1,a2} (base-private)
  - Similarly for D
-/
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
  · -- t is an M-element
    rw [hPath.1] at ht_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
    rcases ht_in with rfl | rfl | rfl | rfl
    · -- t = A, but A contains v1
      have hv1_in_A : v1 ∈ A := by
        have := hPath.2.2.2.2.1  -- A ∩ B = {v1}
        rw [Finset.ext_iff] at this
        exact (this v1).mpr (by simp) |>.1
      exact hv1 hv1_in_A
    · -- t = B, contains v1
      have hv1_in_B : v1 ∈ B := by
        have := hPath.2.2.2.2.1
        rw [Finset.ext_iff] at this
        exact (this v1).mpr (by simp) |>.2
      exact hv1 hv1_in_B
    · -- t = C, contains v2
      have hv2_in_C : v2 ∈ C := by
        have := hPath.2.2.2.2.2.1  -- B ∩ C = {v2}
        rw [Finset.ext_iff] at this
        exact (this v2).mpr (by simp) |>.2
      exact hv2 hv2_in_C
    · -- t = D, contains v3
      have hv3_in_D : v3 ∈ D := by
        have := hPath.2.2.2.2.2.2.1  -- C ∩ D = {v3}
        rw [Finset.ext_iff] at this
        exact (this v3).mpr (by simp) |>.2
      exact hv3 hv3_in_D
  · -- t ∉ M, by maximality shares edge with some m ∈ M
    obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_in
    rw [hPath.1] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · -- Shares with A
      exact hA_not ⟨h_share, hv1⟩
    · -- Shares with B = {v1, v2, b}
      -- If v1, v2 ∉ t, then t ∩ B ⊆ {b}, card ≤ 1, contradiction
      have hB3 : B.card = 3 := triangle_card_3 G B hPath.2.1.2.1
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
    · -- Shares with C = {v2, v3, c}
      have hC3 : C.card = 3 := triangle_card_3 G C hPath.2.1.2.2.1
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
    · -- Shares with D
      exact hD_not ⟨h_share, hv3⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `G.edgeFinset`
Unknown identifier `G.cliqueFinset`
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isPath4Config
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Invalid field notation: Type of
  t
is not known; cannot resolve field `sym2`
Unknown identifier `triangle_card_3`
Unknown identifier `triangle_card_3`
Unknown identifier `triangle_card_3`
Unknown identifier `triangle_card_3`
Unknown identifier `adaptivePath4Cover`
Unknown identifier `adaptivePath4Cover_card_le_8`
Unknown identifier `adaptivePath4Cover_subset`
Unknown identifier `triangle_structure`-/
/--
MAIN THEOREM: τ ≤ 8 for PATH_4

PROOF SKETCH:
1. Construct adaptive cover (8 edges)
2. Show it covers all triangles using triangle_structure
3. For each case, one of our edges hits the triangle
-/
theorem tau_le_8_path4 (M : Finset (Finset V)) (A B C D : Finset V) (v1 v2 v3 : V)
    (hM : isMaxPacking G M)
    (hPath : isPath4Config G M A B C D v1 v2 v3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Extract cardinality facts
  have hA3 : A.card = 3 := triangle_card_3 G A hPath.2.1.1
  have hB3 : B.card = 3 := triangle_card_3 G B hPath.2.1.2.1
  have hC3 : C.card = 3 := triangle_card_3 G C hPath.2.1.2.2.1
  have hD3 : D.card = 3 := triangle_card_3 G D hPath.2.1.2.2.2
  -- Use adaptive cover
  use adaptivePath4Cover G A B C D v1 v2 v3 hA3 hB3 hC3 hD3 hPath.2.2.2.2.1 hPath.2.2.2.2.2.1 hPath.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 8
    exact adaptivePath4Cover_card_le_8 G A B C D v1 v2 v3 hA3 hB3 hC3 hD3
          hPath.2.2.2.2.1 hPath.2.2.2.2.2.1 hPath.2.2.2.2.2.2.1
  · -- Subset of edges
    exact adaptivePath4Cover_subset G A B C D v1 v2 v3 hA3 hB3 hC3 hD3
          hPath.2.2.2.2.1 hPath.2.2.2.2.2.1 hPath.2.2.2.2.2.2.1
  · -- Covers all triangles
    intro t ht
    have h_struct := triangle_structure G M A B C D v1 v2 v3 hM hPath t ht
    rcases h_struct with hv1 | hv2 | hv3 | ⟨hA_share, hv1_not⟩ | ⟨hD_share, hv3_not⟩
    · -- v1 ∈ t: covered by spoke from A or B
      sorry
    · -- v2 ∈ t: covered by spoke from B or C
      sorry
    · -- v3 ∈ t: covered by spoke from C or D
      sorry
    · -- A-base-private: covered by base edge
      sorry
    · -- D-base-private: covered by base edge
      sorry

end