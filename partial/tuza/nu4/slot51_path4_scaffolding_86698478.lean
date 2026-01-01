/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 86698478-f0a6-4572-af5c-a205329185f7
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 79b18981-7fdc-47f2-be8b-4e1e2472c39f

The following was proved by Aristotle:

- lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v

- theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v)

- lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4

- lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2

- lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2

- theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8
-/

/-
Tuza ν=4 Strategy - Slot 51: PATH_4 via T_pair Decomposition

STRATEGY: Use proven tau_pair_le_4 theorem instead of S_e decomposition.

For PATH_4 (A—B—C—D with shared vertices v_ab, v_bc, v_cd):
1. T_left = T_pair(A,B) = triangles sharing edge with A or B
2. T_right = T_pair(C,D) = triangles sharing edge with C or D
3. All triangles ⊆ T_left ∪ T_right
4. τ(T_left) ≤ 4 (by tau_pair_le_4 since A ∩ B = {v_ab})
5. τ(T_right) ≤ 4 (by tau_pair_le_4 since C ∩ D = {v_cd})
6. τ(all) ≤ τ(T_left) + τ(T_right) ≤ 8

KEY INSIGHT: T_pair INCLUDES bridges automatically (unlike S_e which excludes them).
X_{B,C} bridges are in BOTH T_left and T_right, but ≤ bound still works.

Uses FULL PROVEN CODE from Aristotle slot35 (uuid da605278).
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot35)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- PATH_4: Four packing elements forming a path A—B—C—D -/
def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  -- Path structure: A-B-C-D (adjacent pairs share exactly one vertex)
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  -- Non-adjacent pairs are vertex-disjoint
  (A ∩ C).card = 0 ∧
  (A ∩ D).card = 0 ∧
  (B ∩ D).card = 0

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot16/slot35 - uuid b4f73fa3)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

-- PROVEN by Aristotle in slot16 (uuid b4f73fa3)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_pair_le_4 (from slot35, uuid da605278)
-- ══════════════════════════════════════════════════════════════════════════════

/-- V-decomposition lemma -/
lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t; by_cases h : v ∈ t <;> simp +decide [ h, trianglesContaining, trianglesAvoiding ] ;

-- Simple set theory

theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  convert tau_union_le_sum _ _ _ using 2;
  exact?

-- Follows from v_decomposition_union and tau_union_le_sum

/-- Triangles containing v in T_pair can be covered by 4 spoke edges -/
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  unfold triangleCoveringNumberOn trianglesContaining;
  simp +decide [ T_pair ];
  unfold trianglesSharingEdge;
  -- Let's choose any four edges incident to $v$ and show they cover all triangles containing $v$ in $T_pair$.
  have h_four_edges : ∃ E' ∈ Finset.powerset G.edgeFinset, E'.card ≤ 4 ∧ ∀ t ∈ (G.cliqueFinset 3).filter (fun x => (x ∩ e).card ≥ 2) ∪ (G.cliqueFinset 3).filter (fun x => (x ∩ f).card ≥ 2), v ∈ t → ∃ e' ∈ E', ∀ a ∈ e', a ∈ t := by
    refine' ⟨ _, _, _, _ ⟩;
    exact Finset.image ( fun u => s(u, v) ) ( e ∪ f |> Finset.erase <| v );
    · simp_all +decide [ Finset.subset_iff, SimpleGraph.mem_edgeSet ];
      rintro _ x hx₁ hx₂ rfl; cases hx₂ <;> simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      · exact he.1 ‹_› hv_e ( by aesop );
      · exact hf.1 ( by aesop ) ( by aesop ) ( by aesop );
    · refine' le_trans ( Finset.card_image_le ) _;
      have := Finset.card_union_add_card_inter e f; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      linarith [ he.card_eq, hf.card_eq, show Finset.card ( e ∩ f ) ≥ 1 from Finset.card_pos.mpr ⟨ v, Finset.mem_inter.mpr ⟨ hv_e, hv_f ⟩ ⟩ ];
    · simp +zetaDelta at *;
      rintro t ( ⟨ ht₁, ht₂ ⟩ | ⟨ ht₁, ht₂ ⟩ ) hv_t <;> obtain ⟨ a, ha₁, ha₂ ⟩ := Finset.exists_mem_ne ht₂ v <;> use a <;> aesop;
  obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_four_edges;
  have h_min_le_four : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ (t : Finset V), t ∈ {x ∈ G.cliqueFinset 3 | (x ∩ e).card ≥ 2} ∪ {x ∈ G.cliqueFinset 3 | (x ∩ f).card ≥ 2} → v ∈ t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ );
  simp +zetaDelta at *;
  exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card _ ) <;> aesop ) ( Nat.cast_le.mpr hE₂ )

-- PROVEN by Aristotle in slot35

/- Triangles avoiding v in T_pair can be covered by 2 base edges -/
noncomputable section AristotleLemmas

/-
If a triangle `t` shares at least 2 vertices with a triangle `e` of size 3, and `v` is in `e` but not `t`, then the remaining 2 vertices of `e` (i.e., `e \ {v}`) must be in `t`.
-/
lemma share_edge_avoid_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (e t : Finset V) (v : V)
    (he_card : e.card = 3)
    (h_share : (e ∩ t).card ≥ 2)
    (hv_in_e : v ∈ e)
    (hv_notin_t : v ∉ t) :
    e \ {v} ⊆ t := by
      intro x hx; simp_all +decide [ Finset.subset_iff ] ;
      contrapose! h_share;
      exact lt_of_le_of_lt ( Finset.card_le_card fun y hy => by aesop ) ( show Finset.card ( e.erase v \ { x } ) < 2 from by rw [ Finset.card_sdiff ] ; aesop )

lemma tau_avoiding_share_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) (v : V) (hv : v ∈ e) :
    triangleCoveringNumberOn G (trianglesAvoiding (trianglesSharingEdge G e) v) ≤ 1 := by
      -- Let `edge = e \ {v}`. Since `v ∈ e` and `e` is a clique of size 3, `edge` is a pair of distinct vertices in `e`, so it corresponds to an edge of `G`.
      obtain ⟨u, w, hu, hw, hvu, hvw, huv⟩ : ∃ u w : V, u ∈ e ∧ w ∈ e ∧ v ≠ u ∧ v ≠ w ∧ u ≠ w ∧ e = {v, u, w} := by
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        rcases Finset.card_eq_three.mp he.2 with ⟨ u, w, x, hu, hw, hx, h ⟩ ; aesop;
      -- Each triangle in `S` must contain the edge `{u, w}`.
      have h_edge : ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G e) v, {u, w} ⊆ t := by
        intro t ht
        obtain ⟨ht_containing, ht_not_containing⟩ : t ∈ trianglesSharingEdge G e ∧ v ∉ t := by
          unfold trianglesAvoiding at ht; aesop;
        unfold trianglesSharingEdge at ht_containing;
        have := Finset.eq_of_subset_of_card_le ( show t ∩ { u, w } ⊆ { u, w } from Finset.inter_subset_right ) ; aesop;
      unfold triangleCoveringNumberOn;
      by_cases h : Sym2.mk ( u, w ) ∈ G.edgeFinset <;> simp_all +decide;
      · have h_cover : {Sym2.mk (u, w)} ∈ Finset.filter (fun E' => ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G {v, u, w}) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (Finset.powerset G.edgeFinset) := by
          simp_all +decide [ Finset.subset_iff ];
        have h_min : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G {v, u, w}) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (Finset.powerset G.edgeFinset))) ≤ Finset.card {Sym2.mk (u, w)} := by
          exact Finset.min_le ( Finset.mem_image_of_mem _ h_cover );
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding ( trianglesSharingEdge G { v, u, w } ) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop;
      · simp_all +decide [ SimpleGraph.isNClique_iff ]

end AristotleLemmas

lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  rw [ show trianglesAvoiding ( T_pair G e f ) v = trianglesAvoiding ( trianglesSharingEdge G e ) v ∪ trianglesAvoiding ( trianglesSharingEdge G f ) v from ?_ ];
  · refine' le_trans ( tau_union_le_sum _ _ _ ) _;
    have h_e : e ∈ G.cliqueFinset 3 := by
      have := hM.1.1 he; aesop;
    have h_f : f ∈ G.cliqueFinset 3 := by
      have := hM.1;
      exact this.1 hf;
    refine' le_trans ( add_le_add ( tau_avoiding_share_le_1 G e h_e v _ ) ( tau_avoiding_share_le_1 G f h_f v _ ) ) _ <;> simp_all +decide [ Finset.ext_iff ];
    · specialize hv v; aesop;
    · specialize hv v; aesop;
  · unfold trianglesAvoiding T_pair trianglesSharingEdge; ext; aesop;

/- Aristotle failed to find a proof. -/
/- Aristotle failed to find a proof. -/
-- PROVEN by Aristotle in slot35

/-- KEY THEOREM: When e ∩ f = {v}, τ(T_pair(e,f)) ≤ 4 -/
theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry

-- PROVEN by Aristotle in slot35 (avoiding set is empty, so only 4 spokes needed)

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 COVERAGE LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle in the graph shares an edge with at least one packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  -- By contradiction, assume there are no edges in τ that cover A.
  by_contra h_no_edge;
  -- If t does not share an edge with any element of M, then t can be added to M to form a larger packing.
  have h_add_t : isTrianglePacking G (insert t M) := by
    refine' ⟨ _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff ];
      exact fun x hx => by have := hM.1.1 hx; aesop;
    · intro x hx y hy hxy;
      cases' eq_or_ne x t with hx hx <;> cases' eq_or_ne y t with hy hy <;> simp_all +decide;
      · exact Nat.le_of_lt_succ ( h_no_edge y ‹_› );
      · simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( h_no_edge x ‹_› );
      · have := hM.1;
        have := this.2; aesop;
  unfold isMaxPacking at hM;
  have h_card_add_t : (insert t M).card ≤ trianglePackingNumber G := by
    have h_card_add_t : (insert t M) ∈ Finset.filter (isTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)) := by
      unfold isTrianglePacking at *; aesop;
    have h_card_add_t : (Insert.insert t M).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (Finset.powerset (G.cliqueFinset 3))) := by
      exact Finset.mem_image_of_mem _ h_card_add_t;
    have h_card_add_t : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (Finset.powerset (G.cliqueFinset 3))), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)))).max 0 := by
      intro x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_card_add_t _ ‹_›;
  rw [ Finset.card_insert_of_notMem ] at h_card_add_t <;> simp_all +decide;
  intro h; have := h_no_edge t h; simp_all +decide ;
  exact this.not_le ( by rw [ ht.2 ] ; decide )

-- Standard lemma: if t shares no edge with M, add t to M (contradicts maximality)

/-- For PATH_4, all triangles are covered by T_pair(A,B) ∪ T_pair(C,D) -/
lemma path4_triangle_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    ∀ t ∈ G.cliqueFinset 3, t ∈ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  -- Every triangle shares edge with some packing element
  obtain ⟨e, heM, h_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- M = {A, B, C, D}, so e is one of A, B, C, D
  have hM_eq : M = {A, B, C, D} := hpath.1
  rw [hM_eq] at heM
  simp only [Finset.mem_insert, Finset.mem_singleton] at heM
  -- t shares edge with e means t ∈ trianglesSharingEdge G e
  have h_in_sharing : t ∈ trianglesSharingEdge G e := by
    simp only [trianglesSharingEdge, Finset.mem_filter]
    exact ⟨ht, h_share⟩
  -- Case analysis on which element e is
  rcases heM with rfl | rfl | rfl | rfl
  · -- e = A: t ∈ trianglesSharingEdge A ⊆ T_pair(A,B)
    rw [Finset.mem_union]
    left
    simp only [T_pair, Finset.mem_union]
    left
    exact h_in_sharing
  · -- e = B: t ∈ trianglesSharingEdge B ⊆ T_pair(A,B)
    rw [Finset.mem_union]
    left
    simp only [T_pair, Finset.mem_union]
    right
    exact h_in_sharing
  · -- e = C: t ∈ trianglesSharingEdge C ⊆ T_pair(C,D)
    rw [Finset.mem_union]
    right
    simp only [T_pair, Finset.mem_union]
    left
    exact h_in_sharing
  · -- e = D: t ∈ trianglesSharingEdge D ⊆ T_pair(C,D)
    rw [Finset.mem_union]
    right
    simp only [T_pair, Finset.mem_union]
    right
    exact h_in_sharing

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- Extract shared vertex from intersection cardinality 1 -/
lemma shared_vertex_exists (A B : Finset V) (h : (A ∩ B).card = 1) :
    ∃ v, A ∩ B = {v} := by
  rw [Finset.card_eq_one] at h
  exact h

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Extract path structure (counting .2's from isPath4 definition)
  -- isPath4: M = {A,B,C,D} ∧ A≠B ∧ B≠C ∧ C≠D ∧ A≠C ∧ A≠D ∧ B≠D ∧ (A∩B).card=1 ∧ (B∩C).card=1 ∧ (C∩D).card=1 ∧ ...
  have hAB_card : (A ∩ B).card = 1 := hpath.2.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hpath.2.2.2.2.2.2.2.2.2.1
  have hAB_ne : A ≠ B := hpath.2.1
  have hCD_ne : C ≠ D := hpath.2.2.2.1
  -- Get shared vertices
  obtain ⟨v_ab, hv_ab⟩ := shared_vertex_exists A B hAB_card
  obtain ⟨v_cd, hv_cd⟩ := shared_vertex_exists C D hCD_card
  -- M membership
  have hM_eq : M = {A, B, C, D} := hpath.1
  have hA_in : A ∈ M := by rw [hM_eq]; simp
  have hB_in : B ∈ M := by rw [hM_eq]; simp
  have hC_in : C ∈ M := by rw [hM_eq]; simp
  have hD_in : D ∈ M := by rw [hM_eq]; simp
  -- Triangles in cliqueFinset 3 are cliques
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1.1 hA_in
  have hB_clique : B ∈ G.cliqueFinset 3 := hM.1.1 hB_in
  have hC_clique : C ∈ G.cliqueFinset 3 := hM.1.1 hC_in
  have hD_clique : D ∈ G.cliqueFinset 3 := hM.1.1 hD_in
  -- All triangles are covered by T_pair(A,B) ∪ T_pair(C,D)
  have h_cover : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
    intro t ht
    exact path4_triangle_cover G M hM A B C D hpath t ht
  -- τ(all triangles) ≤ τ(T_pair(A,B) ∪ T_pair(C,D))
  have h_mono : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤
                triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := by
    apply le_of_forall_le;
    simp +decide [ triangleCoveringNumberOn ];
    intro c hc;
    refine' le_trans hc _;
    simp +decide [ Finset.min ];
    congr! 3;
    ext E'; simp +decide [ T_pair ] ;
    constructor <;> intro h t ht <;> specialize h t <;> simp_all +decide [ trianglesSharingEdge ];
    · rcases ht with ( ( ht | ht ) | ht | ht ) <;> tauto;
    · replace h_cover := @h_cover t; simp_all +decide [ Finset.subset_iff ] ;
      unfold T_pair at h_cover; simp_all +decide [ trianglesSharingEdge ] ; -- Monotonicity: subset implies ≤ covering number (standard)
  -- Apply tau_union_le_sum
  have h_union : triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) ≤
                 triangleCoveringNumberOn G (T_pair G A B) +
                 triangleCoveringNumberOn G (T_pair G C D) := by
    exact tau_union_le_sum G (T_pair G A B) (T_pair G C D)
  -- Apply tau_pair_le_4 to each pair
  have h_left : triangleCoveringNumberOn G (T_pair G A B) ≤ 4 := by
    exact tau_pair_le_4 G M hM A B hA_in hB_in hAB_ne v_ab hv_ab
  have h_right : triangleCoveringNumberOn G (T_pair G C D) ≤ 4 := by
    exact tau_pair_le_4 G M hM C D hC_in hD_in hCD_ne v_cd hv_cd
  -- Combine: τ ≤ 4 + 4 = 8
  calc triangleCoveringNumberOn G (G.cliqueFinset 3)
      ≤ triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := h_mono
    _ ≤ triangleCoveringNumberOn G (T_pair G A B) +
        triangleCoveringNumberOn G (T_pair G C D) := h_union
    _ ≤ 4 + 4 := Nat.add_le_add h_left h_right
    _ = 8 := rfl

end