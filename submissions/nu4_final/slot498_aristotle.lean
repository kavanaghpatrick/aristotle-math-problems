/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2c832a67-5a53-48f7-9951-6b40b8c75f26

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem star_m0_has_safe_edge :
    (∀ t : Tri, ¬isExternal t star_m0 star_m0 star_m1 star_m2 star_m3 e01) ∨
    (∀ t : Tri, ¬isExternal t star_m0 star_m0 star_m1 star_m2 star_m3 e02) ∨
    (∀ t : Tri, ¬isExternal t star_m0 star_m0 star_m1 star_m2 star_m3 e12)
-/

/-
  slot498_concrete_star.lean

  CONCRETE VERIFICATION: Star configuration on Fin 9.

  Star packing: m0={0,1,2}, m1={0,3,4}, m2={0,5,6}, m3={0,7,8}
  All share vertex 0.

  CLAIM: For this specific packing, exists_safe_edge holds.
  Every edge containing vertex 0 has NO external triangles.

  TIER: 1 (pure native_decide)
-/

import Mathlib


set_option maxHeartbeats 2000000

abbrev V9 := Fin 9

def mkE (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

structure Tri where
  a : V9
  b : V9
  c : V9
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  deriving DecidableEq

def Tri.e1 (t : Tri) : V9 × V9 := mkE t.a t.b

def Tri.e2 (t : Tri) : V9 × V9 := mkE t.a t.c

def Tri.e3 (t : Tri) : V9 × V9 := mkE t.b t.c

def Tri.edges (t : Tri) : Finset (V9 × V9) := {t.e1, t.e2, t.e3}

def edgeDisj (t1 t2 : Tri) : Prop := Disjoint t1.edges t2.edges

instance (t1 t2 : Tri) : Decidable (edgeDisj t1 t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

def pack4 (m0 m1 m2 m3 : Tri) : Prop :=
  edgeDisj m0 m1 ∧ edgeDisj m0 m2 ∧ edgeDisj m0 m3 ∧
  edgeDisj m1 m2 ∧ edgeDisj m1 m3 ∧ edgeDisj m2 m3

instance (m0 m1 m2 m3 : Tri) : Decidable (pack4 m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- The star packing
def star_m0 : Tri := ⟨0, 1, 2, by decide, by decide, by decide⟩

def star_m1 : Tri := ⟨0, 3, 4, by decide, by decide, by decide⟩

def star_m2 : Tri := ⟨0, 5, 6, by decide, by decide, by decide⟩

def star_m3 : Tri := ⟨0, 7, 8, by decide, by decide, by decide⟩

lemma star_is_pack4 : pack4 star_m0 star_m1 star_m2 star_m3 := by native_decide

def isExternal (t m m0 m1 m2 m3 : Tri) (e : V9 × V9) : Prop :=
  e ∈ t.edges ∧ e ∈ m.edges ∧ t ≠ m ∧
  edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

instance (t m m0 m1 m2 m3 : Tri) (e : V9 × V9) : Decidable (isExternal t m m0 m1 m2 m3 e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- For the star packing, edge (0,1) of m0 has no external.
-- Any external would be {0,1,x} for x ∉ {2}. But {0,1,x} contains 0,
-- so it must share edge (0,x) or (0,1) with m1={0,3,4}, m2={0,5,6}, m3={0,7,8}.
-- If x ∈ {3,4}, then (0,x) ∈ m1.edges.
-- If x ∈ {5,6}, then (0,x) ∈ m2.edges.
-- If x ∈ {7,8}, then (0,x) ∈ m3.edges.
-- If x = 0, invalid (not a triangle).
-- If x ∉ {0,1,2,3,4,5,6,7,8}, impossible in V9.
-- So no external exists for edge (0,1).

-- The edge (0,1) of star_m0
def e01 : V9 × V9 := mkE 0 1

lemma e01_is_edge_of_m0 : e01 ∈ star_m0.edges := by native_decide

-- Any triangle containing edge (0,1) on V9
-- Let's enumerate all such triangles: {0,1,x} for x ∈ {2,...,8}
def tri_01_2 : Tri := ⟨0, 1, 2, by decide, by decide, by decide⟩

-- = m0
def tri_01_3 : Tri := ⟨0, 1, 3, by decide, by decide, by decide⟩

def tri_01_4 : Tri := ⟨0, 1, 4, by decide, by decide, by decide⟩

def tri_01_5 : Tri := ⟨0, 1, 5, by decide, by decide, by decide⟩

def tri_01_6 : Tri := ⟨0, 1, 6, by decide, by decide, by decide⟩

def tri_01_7 : Tri := ⟨0, 1, 7, by decide, by decide, by decide⟩

def tri_01_8 : Tri := ⟨0, 1, 8, by decide, by decide, by decide⟩

-- None of these are external to star_m0
lemma tri_01_2_not_ext : tri_01_2 = star_m0 := by native_decide

lemma tri_01_3_shares_m1 : ¬edgeDisj tri_01_3 star_m1 := by native_decide

lemma tri_01_4_shares_m1 : ¬edgeDisj tri_01_4 star_m1 := by native_decide

lemma tri_01_5_shares_m2 : ¬edgeDisj tri_01_5 star_m2 := by native_decide

lemma tri_01_6_shares_m2 : ¬edgeDisj tri_01_6 star_m2 := by native_decide

lemma tri_01_7_shares_m3 : ¬edgeDisj tri_01_7 star_m3 := by native_decide

lemma tri_01_8_shares_m3 : ¬edgeDisj tri_01_8 star_m3 := by native_decide

-- Edge (0,2) of m0 also contains 0, so similar analysis
def e02 : V9 × V9 := mkE 0 2

lemma e02_is_edge_of_m0 : e02 ∈ star_m0.edges := by native_decide

-- Edge (1,2) of m0 does NOT contain 0. Let's check if it has externals.
def e12 : V9 × V9 := mkE 1 2

lemma e12_is_edge_of_m0 : e12 ∈ star_m0.edges := by native_decide

-- Triangles containing (1,2): {1,2,x} for x ∈ {0,3,...,8}
def tri_12_0 : Tri := ⟨1, 2, 0, by decide, by decide, by decide⟩

-- = m0 (reordered)
def tri_12_3 : Tri := ⟨1, 2, 3, by decide, by decide, by decide⟩

def tri_12_4 : Tri := ⟨1, 2, 4, by decide, by decide, by decide⟩

def tri_12_5 : Tri := ⟨1, 2, 5, by decide, by decide, by decide⟩

def tri_12_6 : Tri := ⟨1, 2, 6, by decide, by decide, by decide⟩

def tri_12_7 : Tri := ⟨1, 2, 7, by decide, by decide, by decide⟩

def tri_12_8 : Tri := ⟨1, 2, 8, by decide, by decide, by decide⟩

-- Check if these are external (disjoint from m1, m2, m3)
lemma tri_12_3_disj_m1 : edgeDisj tri_12_3 star_m1 := by native_decide

lemma tri_12_3_disj_m2 : edgeDisj tri_12_3 star_m2 := by native_decide

lemma tri_12_3_disj_m3 : edgeDisj tri_12_3 star_m3 := by native_decide

-- So tri_12_3 = {1,2,3} IS external for edge (1,2) of m0!
-- But this doesn't contradict exists_safe_edge.
-- exists_safe_edge says AT LEAST ONE edge has no externals.
-- Edges (0,1) and (0,2) have no externals. That's enough!

theorem star_m0_has_safe_edge :
    (∀ t : Tri, ¬isExternal t star_m0 star_m0 star_m1 star_m2 star_m3 e01) ∨
    (∀ t : Tri, ¬isExternal t star_m0 star_m0 star_m1 star_m2 star_m3 e02) ∨
    (∀ t : Tri, ¬isExternal t star_m0 star_m0 star_m1 star_m2 star_m3 e12) := by
  left
  intro t
  unfold isExternal
  intro ⟨ht_e, ht_m0, ht_ne, ht_m0_disj, ht_m1_disj, ht_m2_disj, ht_m3_disj⟩
  -- t contains edge e01 = (0,1)
  -- t is a triangle, so t = {0, 1, x} for some x ≠ 0, 1
  -- Since e01 ∈ t.edges, t.e1 = (0,1) or t.e2 = (0,1) or t.e3 = (0,1)
  -- Analyze by cases on x
  -- If x ∈ {3,4}, then t shares edge (0,x) with m1
  -- If x ∈ {5,6}, then t shares edge (0,x) with m2
  -- If x ∈ {7,8}, then t shares edge (0,x) with m3
  -- If x = 2, then t = m0, contradicting ht_ne
  -- There are only 9 vertices, so no other cases
  -- t = {t.a, t.b, t.c} with t.a, t.b, t.c distinct
  -- e01 = (0,1) ∈ t.edges means {0,1} ⊆ {t.a, t.b, t.c}
  -- So t has form {0, 1, x} for some x ≠ 0, 1
  -- By finiteness of V9, x ∈ {2,3,4,5,6,7,8}
  -- Case split by x:
  -- Since $t$ shares edge $(0,1)$ with $star_m0$, this contradicts the assumption that $t$ is edge-disjoint from $star_m0$.
  have h_contradiction : e01 ∈ t.edges ∧ e01 ∈ star_m0.edges → ¬edgeDisj t star_m0 := by
    simp +contextual [ Finset.disjoint_left ];
    exact fun h1 h2 => Finset.not_disjoint_iff.mpr ⟨ e01, h1, h2 ⟩;
  exact h_contradiction ⟨ ht_e, ht_m0 ⟩ ht_m0_disj

end