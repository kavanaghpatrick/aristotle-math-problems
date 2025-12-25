/-
Tuza ν=4 Strategy - Slot 53: PATH_4 Avoiding Set is Empty

GOAL: Prove that for PATH_4 configuration, the avoiding set in T_pair is EMPTY.

KEY INSIGHT from slot35 analysis:
- The sorry in avoiding_covered_by_spokes is the blocker
- BUT: For PATH_4 specifically, the structure may force avoiding = ∅

STRUCTURE OF PATH_4:
  M = {A, B, C, D} where A-B-C-D in sharing graph
  A = {v₁, a₁, a₂}
  B = {v₁, v₂, b}    (shares v₁ with A, v₂ with C)
  C = {v₂, v₃, c}    (shares v₂ with B, v₃ with D)
  D = {v₃, d₁, d₂}

For T_pair(A,B) with shared vertex v₁:
- Triangles avoiding v₁ from T_A: {a₁, a₂, w} where w ≠ v₁
- Triangles avoiding v₁ from T_B: must share edge {v₂,b} (only edge of B not containing v₁)
  So form: {v₂, b, x}

KEY: Triangles {v₂, b, x} contain v₂ which is ALSO a shared vertex (with C)!

STRATEGY: Show that in PATH_4, "avoiding v₁" triangles from T_B all contain v₂,
and similarly for other pairs. This creates overlap allowing 4-edge covers.

Includes full scaffolding from slot44.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- PATH_4 specific: elements share vertices in a path pattern
def isPath4Packing (M : Finset (Finset V)) (A B C D : Finset V)
    (v₁ v₂ v₃ : V) : Prop :=
  M = {A, B, C, D} ∧
  A ∩ B = {v₁} ∧ B ∩ C = {v₂} ∧ C ∩ D = {v₃} ∧
  A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ D = ∅ ∧  -- non-adjacent pairs are disjoint
  v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₁ ≠ v₃

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_union_le_sum (from slot35)
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

lemma union_covers_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (XA XB : Finset (Sym2 V))
    (hA : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2)
    (hB : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2) :
    ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htA | htB
  · obtain ⟨e, heXA, het⟩ := hA t htA
    exact ⟨e, Finset.mem_union_left XB heXA, het⟩
  · obtain ⟨e, heXB, het⟩ := hB t htB
    exact ⟨e, Finset.mem_union_right XA heXB, het⟩

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- Full proof in slot35, will be imported

-- ══════════════════════════════════════════════════════════════════════════════
-- V-DECOMPOSITION
-- ══════════════════════════════════════════════════════════════════════════════

lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Structure of avoiding triangles in PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/--
In PATH_4 with A-B-C-D, triangles in T_pair(A,B) that avoid v₁ must contain v₂.

Proof sketch:
- A = {v₁, a₁, a₂}, B = {v₁, v₂, b}
- Triangle t ∈ T_B avoiding v₁ must share edge with B not containing v₁
- Only such edge is {v₂, b}
- So t = {v₂, b, x} for some x, hence v₂ ∈ t
-/
lemma path4_avoiding_v1_from_TB_contains_v2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (hA : A.card = 3) (hB : B.card = 3)
    (hv1 : v₁ ∈ A ∧ v₁ ∈ B) (hv2 : v₂ ∈ B ∧ v₂ ∈ C) (hv2_not_A : v₂ ∉ A)
    (t : Finset V) (ht_triangle : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ B).card ≥ 2) (ht_avoids_v1 : v₁ ∉ t) :
    v₂ ∈ t := by
  -- B = {v₁, v₂, b} for some b
  -- t shares ≥2 vertices with B, but v₁ ∉ t
  -- So t shares ≥2 vertices from B \ {v₁} = {v₂, b}
  -- Since |{v₂, b}| = 2, we have {v₂, b} ⊆ t
  -- Hence v₂ ∈ t
  sorry

/--
Triangles avoiding v₁ from T_A have form {a₁, a₂, w} where a₁, a₂ are the
non-v₁ vertices of A. These are covered by the base edge {a₁, a₂}.
-/
lemma path4_avoiding_v1_from_TA_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v₁ a₁ a₂ : V)
    (hA : A = {v₁, a₁, a₂}) (h_distinct : v₁ ≠ a₁ ∧ v₁ ≠ a₂ ∧ a₁ ≠ a₂)
    (t : Finset V) (ht_triangle : t ∈ G.cliqueFinset 3)
    (ht_shares_A : (t ∩ A).card ≥ 2) (ht_avoids_v1 : v₁ ∉ t) :
    a₁ ∈ t ∧ a₂ ∈ t := by
  -- t shares ≥2 with A = {v₁, a₁, a₂}, but v₁ ∉ t
  -- So t shares ≥2 from {a₁, a₂}, which means {a₁, a₂} ⊆ t
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ(T_pair(A,B)) ≤ 4 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/--
For PATH_4, τ(T_pair(A,B)) ≤ 4.

Cover construction:
- 4 spokes at v₁: {v₁a₁}, {v₁a₂}, {v₁v₂}, {v₁b}

These cover:
1. All triangles containing v₁ (obvious)
2. Triangles avoiding v₁ from T_B contain v₂, covered by spoke {v₁v₂}...
   wait, that doesn't work since v₁ ∉ t!

Actually need different approach:
- Use spokes {v₁a₁}, {v₁a₂} for triangles containing v₁ from T_A
- Use spokes {v₁v₂}, {v₁b} for triangles containing v₁ from T_B
- Use base {a₁a₂} for triangles avoiding v₁ from T_A
- Triangles avoiding v₁ from T_B contain v₂, use edge through v₂

Hmm, this needs 5 edges. Unless there's overlap or the sets are smaller than expected.

ALTERNATIVE: Show T_pair(A,B) ∪ T_pair(C,D) has clever cover of size 8.
-/
theorem tau_pair_le_4_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (hPath : isPath4Packing M A B C D v₁ v₂ v₃)
    (hA_tri : A ∈ G.cliqueFinset 3) (hB_tri : B ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (T_pair G A B) ≤ 4 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- FULL PATH_4 THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (hPath : isPath4Packing M A B C D v₁ v₂ v₃) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- All triangles ⊆ T_pair(A,B) ∪ T_pair(C,D)
  have h_cover : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
    sorry -- Every triangle shares edge with some packing element
  -- Apply bounds
  have h1 : triangleCoveringNumberOn G (T_pair G A B) ≤ 4 :=
    tau_pair_le_4_path4 G M hM A B C D v₁ v₂ v₃ hPath sorry sorry
  have h2 : triangleCoveringNumberOn G (T_pair G C D) ≤ 4 := by
    sorry -- Symmetric
  calc triangleCoveringNumberOn G (G.cliqueFinset 3)
      ≤ triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := by sorry
    _ ≤ triangleCoveringNumberOn G (T_pair G A B) +
        triangleCoveringNumberOn G (T_pair G C D) := tau_union_le_sum G _ _
    _ ≤ 4 + 4 := Nat.add_le_add h1 h2
    _ = 8 := rfl

end
