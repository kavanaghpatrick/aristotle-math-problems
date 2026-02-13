/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 44ec0c80-38ea-4f62-ba9d-6498c8faaa1d

The following was proved by Aristotle:

- theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2

- theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8
-/

/-
Tuza ν=4 Strategy - Slot 52: CYCLE_4 via T_pair Decomposition

STRATEGY: Use proven tau_pair_le_4 theorem instead of S_e decomposition.

For CYCLE_4 (A—B—C—D—A with shared vertices v_ab, v_bc, v_cd, v_da):
1. T_left = T_pair(A,B) = triangles sharing edge with A or B
2. T_right = T_pair(C,D) = triangles sharing edge with C or D
3. All triangles ⊆ T_left ∪ T_right
4. τ(T_left) ≤ 4 (by tau_pair_le_4 since A ∩ B = {v_ab})
5. τ(T_right) ≤ 4 (by tau_pair_le_4 since C ∩ D = {v_cd})
6. τ(all) ≤ τ(T_left) + τ(T_right) ≤ 8

BONUS: No diagonal bridges (X_{A,C} = ∅, X_{B,D} = ∅) in cycle structure.

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

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- CYCLE_4: Four packing elements forming a cycle A—B—C—D—A -/
def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  -- Cycle structure: A-B-C-D-A (adjacent pairs share exactly one vertex)
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  (D ∩ A).card = 1 ∧
  -- Opposite pairs are vertex-disjoint (no diagonal bridges!)
  (A ∩ C).card = 0 ∧
  (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot35, uuid da605278)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section AristotleLemmas

/-
Definition of a triangle cover: a subset of edges such that every triangle in the set contains at least one edge from the subset.
-/
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (C : Finset (Sym2 V)) : Prop :=
  C ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ C, e ∈ t.sym2

/-
Definition of coverable: a set of triangles is coverable if there exists a triangle cover for it.
-/
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isCoverable (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : Prop :=
  ∃ C, isTriangleCover G triangles C

/-
The union of two triangle covers is a triangle cover for the union of the triangle sets.
-/
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma isTriangleCover_union {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset (Finset V)} {CA CB : Finset (Sym2 V)}
    (hA : isTriangleCover G A CA) (hB : isTriangleCover G B CB) :
    isTriangleCover G (A ∪ B) (CA ∪ CB) := by
      exact ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 t ht |> fun ⟨ e, he, he' ⟩ => ⟨ e, Finset.mem_union_left _ he, he' ⟩ ; exact hB.2 t ht |> fun ⟨ e, he, he' ⟩ => ⟨ e, Finset.mem_union_right _ he, he' ⟩ ] ⟩

/-
If a set of triangles is not coverable, its triangle covering number is 0.
-/
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma triangleCoveringNumberOn_eq_zero_of_not_coverable {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)}
    (h : ¬ isCoverable G A) : triangleCoveringNumberOn G A = 0 := by
      unfold triangleCoveringNumberOn;
      have h_empty : ∀ x ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), False := by
        exact fun x hx => h ⟨ x, ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hx |>.1 ), fun t ht => by aesop ⟩ ⟩;
      rw [ Finset.eq_empty_of_forall_notMem h_empty ] ; simp +decide

/-
If a set of triangles is coverable, there exists a triangle cover whose cardinality equals the triangle covering number.
-/
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_min_cover_of_coverable {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)}
    (h : isCoverable G A) :
    ∃ C, isTriangleCover G A C ∧ C.card = triangleCoveringNumberOn G A := by
      unfold isCoverable at h;
      unfold isTriangleCover at *;
      unfold triangleCoveringNumberOn;
      -- Since the set of covers is non-empty, its minimum element exists and is in the set.
      obtain ⟨C, hC⟩ : ∃ C ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2}), ∀ E' ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2}), C ≤ E' := by
        exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.choose_spec.1, h.choose_spec.2 ⟩ ) ⟩, Finset.min'_mem _ _, fun E' hE' => Finset.min'_le _ _ hE' ⟩;
      -- Since the minimum of a finite set is equal to the minimum of its elements, we can conclude that C is equal to the minimum of the image.
      have h_min_eq : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2})) = some C := by
        exact le_antisymm ( Finset.min_le hC.1 ) ( Finset.le_min fun x hx => WithTop.coe_le_coe.mpr ( hC.2 x hx ) );
      grind

/-
If C is a triangle cover for A, then the triangle covering number of A is at most the cardinality of C.
-/
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma triangleCoveringNumberOn_le_of_cover {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset (Finset V)} {C : Finset (Sym2 V)}
    (h : isTriangleCover G A C) : triangleCoveringNumberOn G A ≤ C.card := by
      -- Since C is a triangle cover for A, by definition of triangleCoveringNumberOn, we have that the minimum size of such a cover is ≤ C.card.
      have h_le : ∃ C' : Finset (Sym2 V), isTriangleCover G A C' ∧ C'.card ≤ C.card := by
        use C;
      obtain ⟨ C', hC', hC'' ⟩ := h_le;
      unfold triangleCoveringNumberOn;
      have h_min_le : ∀ {S : Finset ℕ}, C'.card ∈ S → Option.getD (Finset.min S) 0 ≤ C'.card := by
        intros S hS; exact (by
        have := Finset.min_le hS;
        cases h : Finset.min S <;> aesop);
      exact le_trans ( h_min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( hC'.1 ), hC'.2 ⟩ ) ) ) hC''

end AristotleLemmas

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : isCoverable G A;
  · by_cases hB : isCoverable G B;
    · -- By Lemma `exists_min_cover_of_coverable`, there exist minimal covers CA and CB for A and B respectively.
      obtain ⟨CA, hCA⟩ := exists_min_cover_of_coverable hA
      obtain ⟨CB, hCB⟩ := exists_min_cover_of_coverable hB;
      exact le_trans ( triangleCoveringNumberOn_le_of_cover ( isTriangleCover_union hCA.1 hCB.1 ) ) ( by rw [ ← hCA.2, ← hCB.2 ] ; exact Finset.card_union_le _ _ );
    · -- Since B is not coverable, the union of A and B is also not coverable.
      have h_union_not_coverable : ¬isCoverable G (A ∪ B) := by
        intro h_union_coverable
        obtain ⟨C, hC⟩ := h_union_coverable;
        exact hB ⟨ C, hC.1, fun t ht => hC.2 t ( Finset.mem_union_right _ ht ) ⟩;
      rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable h_union_not_coverable ];
      exact Nat.zero_le _;
  · by_cases hB : isCoverable G ( A ∪ B ) <;> simp_all +decide [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
    exact False.elim ( hA ( by obtain ⟨ C, hC ⟩ := hB; exact ⟨ C, ⟨ hC.1, fun t ht => hC.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩ ) )

/- Aristotle failed to find a proof. -/
-- PROVEN by Aristotle in slot16 (uuid b4f73fa3)

theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry

-- PROVEN by Aristotle in slot35 (uuid da605278)

-- ══════════════════════════════════════════════════════════════════════════════
-- NO DIAGONAL BRIDGES (proven in slot50)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Opposite pairs in a cycle have no bridges -/
lemma cycle4_no_opposite_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (hcycle : isCycle4 ({A, B, C, D} : Finset (Finset V)) A B C D) :
    X_ef G A C = ∅ := by
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
  intro ht h_share_A h_share_C
  -- A ∩ C = ∅ by cycle structure
  have hAC_disj : (A ∩ C).card = 0 := hcycle.2.2.2.2.2.2.2.2.2.2.2.1
  -- t shares ≥2 with A and ≥2 with C, but |t| = 3
  have h_t_card : t.card = 3 := by
    have h := SimpleGraph.mem_cliqueFinset_iff.mp ht
    exact h.card_eq
  -- t ∩ A and t ∩ C are disjoint (since A ∩ C = ∅)
  have h_disj : (t ∩ A) ∩ (t ∩ C) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro x hx
    simp only [Finset.mem_inter] at hx
    have : x ∈ A ∩ C := Finset.mem_inter.mpr ⟨hx.1.2, hx.2.2⟩
    rw [Finset.card_eq_zero] at hAC_disj
    rw [hAC_disj] at this
    exact Finset.not_mem_empty x this
  -- (t ∩ A) ∪ (t ∩ C) ⊆ t, so |(t ∩ A) ∪ (t ∩ C)| ≤ 3
  have h_subset : (t ∩ A) ∪ (t ∩ C) ⊆ t := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_of_mem_inter_left h
    · exact Finset.mem_of_mem_inter_left h
  have h_card_union : ((t ∩ A) ∪ (t ∩ C)).card ≤ t.card := Finset.card_le_card h_subset
  -- Since disjoint: |(t ∩ A) ∪ (t ∩ C)| = |t ∩ A| + |t ∩ C| ≥ 2 + 2 = 4
  have h_card_disj : ((t ∩ A) ∪ (t ∩ C)).card = (t ∩ A).card + (t ∩ C).card := by
    rw [Finset.card_union_of_disjoint]
    rwa [Finset.disjoint_iff_inter_eq_empty]
  rw [h_card_disj, h_t_card] at h_card_union
  omega

lemma cycle4_no_opposite_bridges_BD (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (hcycle : isCycle4 ({A, B, C, D} : Finset (Finset V)) A B C D) :
    X_ef G B D = ∅ := by
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
  intro ht h_share_B h_share_D
  have hBD_disj : (B ∩ D).card = 0 := hcycle.2.2.2.2.2.2.2.2.2.2.2.2
  have h_t_card : t.card = 3 := by
    have h := SimpleGraph.mem_cliqueFinset_iff.mp ht
    exact h.card_eq
  have h_disj : (t ∩ B) ∩ (t ∩ D) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro x hx
    simp only [Finset.mem_inter] at hx
    have : x ∈ B ∩ D := Finset.mem_inter.mpr ⟨hx.1.2, hx.2.2⟩
    rw [Finset.card_eq_zero] at hBD_disj
    rw [hBD_disj] at this
    exact Finset.not_mem_empty x this
  have h_subset : (t ∩ B) ∪ (t ∩ D) ⊆ t := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_of_mem_inter_left h
    · exact Finset.mem_of_mem_inter_left h
  have h_card_union : ((t ∩ B) ∪ (t ∩ D)).card ≤ t.card := Finset.card_le_card h_subset
  have h_card_disj : ((t ∩ B) ∪ (t ∩ D)).card = (t ∩ B).card + (t ∩ D).card := by
    rw [Finset.card_union_of_disjoint]
    rwa [Finset.disjoint_iff_inter_eq_empty]
  rw [h_card_disj, h_t_card] at h_card_union
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 COVERAGE LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle shares an edge with at least one packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_contra! h;
  -- If $t$ does not share an edge with any element of $M$, then $M \cup \{t\}$ would be a larger packing, contradicting the maximality of $M$.
  have h_union : isTrianglePacking G (M ∪ {t}) := by
    refine' ⟨ _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff ];
      have := hM.1.1;
      exact fun x hx => Finset.mem_filter.mp ( this hx ) |>.2;
    · intro x hx y hy hxy;
      cases eq_or_ne x t <;> cases eq_or_ne y t <;> simp_all +decide;
      · exact Nat.le_of_lt_succ ( h y hy );
      · exact Nat.le_of_lt_succ ( by simpa only [ Finset.inter_comm ] using h x hx );
      · have := hM.1.2;
        exact this hx hy hxy;
  have h_card : (M ∪ {t}).card > M.card := by
    by_cases h' : t ∈ M <;> simp_all +decide;
    have := h _ h'; rw [ Finset.inter_self ] at this; exact this.not_le ( ht.card_eq.symm ▸ by decide ) ;
  have h_contra : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber;
    have h_contra : (M ∪ {t}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      refine' Finset.mem_image.mpr ⟨ M ∪ { t }, _, rfl ⟩;
      simp_all +decide [ isTrianglePacking ];
    have := Finset.le_max h_contra;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  exact h_card.not_le ( h_contra.trans ( hM.2.ge ) )

-- Standard maximality argument

/-- For CYCLE_4, all triangles are covered by T_pair(A,B) ∪ T_pair(C,D) -/
lemma cycle4_triangle_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    ∀ t ∈ G.cliqueFinset 3, t ∈ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  obtain ⟨e, heM, h_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  have hM_eq : M = {A, B, C, D} := hcycle.1
  rw [hM_eq] at heM
  simp only [Finset.mem_insert, Finset.mem_singleton] at heM
  have h_in_sharing : t ∈ trianglesSharingEdge G e := by
    simp only [trianglesSharingEdge, Finset.mem_filter]
    exact ⟨ht, h_share⟩
  rcases heM with rfl | rfl | rfl | rfl
  · rw [Finset.mem_union]; left
    simp only [T_pair, Finset.mem_union]; left; exact h_in_sharing
  · rw [Finset.mem_union]; left
    simp only [T_pair, Finset.mem_union]; right; exact h_in_sharing
  · rw [Finset.mem_union]; right
    simp only [T_pair, Finset.mem_union]; left; exact h_in_sharing
  · rw [Finset.mem_union]; right
    simp only [T_pair, Finset.mem_union]; right; exact h_in_sharing

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for CYCLE_4
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_vertex_exists (A B : Finset V) (h : (A ∩ B).card = 1) :
    ∃ v, A ∩ B = {v} := by
  rw [Finset.card_eq_one] at h
  exact h

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Extract cycle structure
  -- isCycle4: M={A,B,C,D} ∧ A≠B ∧ B≠C ∧ C≠D ∧ D≠A ∧ A≠C ∧ B≠D ∧
  --           (A∩B).card=1 ∧ (B∩C).card=1 ∧ (C∩D).card=1 ∧ (D∩A).card=1 ∧
  --           (A∩C).card=0 ∧ (B∩D).card=0
  have hAB_card : (A ∩ B).card = 1 := hcycle.2.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.1
  have hAB_ne : A ≠ B := hcycle.2.1
  have hCD_ne : C ≠ D := hcycle.2.2.2.1
  -- Get shared vertices
  obtain ⟨v_ab, hv_ab⟩ := shared_vertex_exists A B hAB_card
  obtain ⟨v_cd, hv_cd⟩ := shared_vertex_exists C D hCD_card
  -- M membership
  have hM_eq : M = {A, B, C, D} := hcycle.1
  have hA_in : A ∈ M := by rw [hM_eq]; simp
  have hB_in : B ∈ M := by rw [hM_eq]; simp
  have hC_in : C ∈ M := by rw [hM_eq]; simp
  have hD_in : D ∈ M := by rw [hM_eq]; simp
  -- All triangles are covered by T_pair(A,B) ∪ T_pair(C,D)
  have h_cover : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
    intro t ht
    exact cycle4_triangle_cover G M hM A B C D hcycle t ht
  -- τ(all triangles) ≤ τ(T_pair(A,B) ∪ T_pair(C,D))
  have h_mono : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤
                triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := by
    -- Since $G.cliqueFinset 3 \subseteq T_pair G A B \cup T_pair G C D$, any edge cover of $T_pair G A B \cup T_pair G C D$ is also an edge cover of $G.cliqueFinset 3$.
    have h_cover : ∀ E' : Finset (Sym2 V), (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) → (∀ t ∈ T_pair G A B ∪ T_pair G C D, ∃ e ∈ E', e ∈ t.sym2) := by
      -- Since $G.cliqueFinset 3 \subseteq T_pair G A B ∪ T_pair G C D$, any edge cover of $T_pair G A B ∪ T_pair G C D$ is also an edge cover of $G.cliqueFinset 3$ by definition of subset.
      intros E' hE' t ht
      apply hE' t (by
      exact Finset.mem_union.mp ht |> Or.rec ( fun h => Finset.mem_union.mp h |> Or.rec ( fun h => Finset.mem_filter.mp h |>.1 ) fun h => Finset.mem_filter.mp h |>.1 ) fun h => Finset.mem_union.mp h |> Or.rec ( fun h => Finset.mem_filter.mp h |>.1 ) fun h => Finset.mem_filter.mp h |>.1);
    unfold triangleCoveringNumberOn;
    rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = Finset.filter ( fun E' => ∀ t ∈ T_pair G A B ∪ T_pair G C D, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) from ?_ ];
    -- Since $G.cliqueFinset 3 \subseteq T_pair G A B \cup T_pair G C D$, any edge cover of $T_pair G A B \cup T_pair G C D$ automatically covers all triangles in $G.cliqueFinset 3$.
    have h_subset : ∀ E' : Finset (Sym2 V), (∀ t ∈ T_pair G A B ∪ T_pair G C D, ∃ e ∈ E', e ∈ t.sym2) → (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) := by
      exact fun E' hE' t ht => hE' t ( by tauto );
    exact Finset.filter_congr fun E' hE' => ⟨ h_cover E', h_subset E' ⟩ -- Monotonicity: subset implies ≤ covering number
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