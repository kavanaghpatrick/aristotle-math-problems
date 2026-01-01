/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5a0b26c9-c5b9-4047-af0b-7afbcf830449

The following was proved by Aristotle:

- lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma parker_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 1) :
    triangleCoveringNumber G ≤ 2

- lemma vertex_disjoint_triangles_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    Disjoint (triangleUnionOf G A) (triangleUnionOf G B)

- theorem tau_le_8_vertex_partition_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_card : A.card = 2) (hB_card : B.card = 2)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8

- theorem tau_le_8_disconnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    -- Sharing graph is disconnected: exists partition with no shared vertices
    (h_disconnected : ∃ (A B : Finset (Finset V)),
      A ∪ B = M ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      ∀ a ∈ A, ∀ b ∈ B, Disjoint (a : Set V) (b : Set V)) :
    triangleCoveringNumber G ≤ 8
-/

/-
Tuza ν=4 Portfolio - Slot 30: Vertex Partition Reduction

TARGET: If packing splits into vertex-disjoint blocks, reduce to smaller ν

KEY INSIGHT (from Gemini + Codex consultation 2024-12-23):
When the 4 packing elements can be partitioned into vertex-disjoint groups:
- Group A with k elements has ν = k
- Group B with 4-k elements has ν = 4-k
- Apply Parker's bound to each: τ(A) ≤ 2k, τ(B) ≤ 2(4-k)
- Total: τ ≤ 2k + 2(4-k) = 8

This handles all "disconnected" sharing graphs:
- Empty (all 4 isolated): 4 groups of 1, each τ ≤ 2, total ≤ 8
- Single edge: one pair + two isolated
- Matching: two pairs
- P3 + isolated: one triple + one isolated

SCAFFOLDING:
- tau_union_le_sum (proven in slot16)
- tau_S_le_2 (proven in slot6)
- Parker's inductive bound for ν ≤ 3
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

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

-- Union of all triangles sharing edges with elements in A
def triangleUnionOf (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) : Finset (Finset V) :=
  A.biUnion (trianglesSharingEdge G)

-- Vertex set of a collection of triangles
def vertexSetOf (A : Finset (Finset V)) : Finset V :=
  A.biUnion id

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section AristotleLemmas

/-
Definition of a triangle cover: a set of edges E' covers a set of triangles if E' is a subset of the graph's edges and every triangle in the set contains at least one edge from E'.
-/
def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

/-
An edge set E' is in the filtered powerset defining the covering number if and only if it is a triangle cover for A. This connects the definition of covering number to the predicate `isTriangleCover`.
-/
lemma mem_filter_iff_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E' : Finset (Sym2 V)) :
    E' ∈ G.edgeFinset.powerset.filter (fun E => ∀ t ∈ A, ∃ e ∈ E, e ∈ t.sym2) ↔ isTriangleCover G A E' := by
  unfold isTriangleCover; aesop;

/-
If EA covers A and EB covers B, then the union EA ∪ EB covers the union A ∪ B. This is a key step in proving the subadditivity of the covering number.
-/
lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *;
  grind

/-
The triangle covering number is the minimum cardinality of a triangle cover. Therefore, it is less than or equal to the cardinality of any specific triangle cover E'.
-/
lemma triangleCoveringNumberOn_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E' : Finset (Sym2 V)) (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  have h_triangle_covering : ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
    exact h.2;
  unfold triangleCoveringNumberOn;
  have h_triangle_covering : Finset.card E' ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2}) := by
    exact Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h_triangle_covering ⟩, rfl ⟩;
  have := Finset.min_le h_triangle_covering;
  rw [ WithTop.le_coe_iff ] at this ; aesop

/-
If a triangle cover exists for A, then there exists a 'minimal' triangle cover E whose cardinality is exactly the triangle covering number of A.
-/
lemma exists_min_triangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (h : ∃ E, isTriangleCover G A E) :
    ∃ E, isTriangleCover G A E ∧ E.card = triangleCoveringNumberOn G A := by
  -- Let $E$ be a triangle cover of $A$ of minimum size and calculate its cardinality.
  obtain ⟨E, hE⟩ : ∃ E : Finset (Sym2 V), isTriangleCover G A E ∧ ∀ E' : Finset (Sym2 V), isTriangleCover G A E' → E.card ≤ E'.card := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ G.edgeFinset, fun E hE => hE.1 ⟩;
  unfold triangleCoveringNumberOn;
  have h_min : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2})) = some E.card := by
    refine' le_antisymm _ _;
    · exact Finset.min_le ( Finset.mem_image.mpr ⟨ E, by unfold isTriangleCover at hE; aesop ⟩ );
    · norm_num +zetaDelta at *;
      rintro a x hx₁ hx₂ rfl;
      exact WithTop.coe_le_coe.mpr ( hE.2 x ⟨ fun e he => by simpa using hx₁ he, fun t ht => by simpa using hx₂ t ht ⟩ );
  aesop

end AristotleLemmas

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E, isTriangleCover G A E;
  · by_cases hB : ∃ E, isTriangleCover G B E;
    · obtain ⟨EA, hEA⟩ := exists_min_triangleCover G A hA
      obtain ⟨EB, hEB⟩ := exists_min_triangleCover G B hB;
      exact le_trans ( triangleCoveringNumberOn_le_card G ( A ∪ B ) ( EA ∪ EB ) ( isTriangleCover_union G A B EA EB hEA.1 hEB.1 ) ) ( by rw [ ← hEA.2, ← hEB.2 ] ; exact Finset.card_union_le _ _ );
    · unfold triangleCoveringNumberOn;
      rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from _ ] <;> simp_all +decide [ Finset.min ];
      · simp +decide [ Option.getD ];
        rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from _ ] <;> simp +decide [ Finset.inf ];
        contrapose! hB;
        obtain ⟨ E, hE₁, hE₂ ⟩ := hB;
        refine' ⟨ E, _, _ ⟩ <;> aesop;
      · intro E hE; specialize hB E; unfold isTriangleCover at hB; aesop;
  · refine' Nat.le_trans _ ( Nat.zero_le _ );
    unfold triangleCoveringNumberOn;
    rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2 } = ∅ from _ ];
    · rfl;
    · ext E'
      simp [hA];
      contrapose! hA;
      refine' ⟨ E', _, _ ⟩ <;> aesop

/- Aristotle failed to find a proof. -/
-- Parker's bound for ν ≤ 2: τ ≤ 4
lemma parker_nu_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card ≤ 2) :
    triangleCoveringNumber G ≤ 4 := by
  sorry

-- Parker's bound for ν = 1: τ ≤ 2
noncomputable section AristotleLemmas

/-
If the triangle packing number is 1, then any two triangles must share an edge (intersect in at least 2 vertices).
-/
lemma packing_one_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 1)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3) :
    (t1 ∩ t2).card ≥ 2 := by
      unfold trianglePackingNumber at h_nu;
      contrapose! h_nu;
      -- If $t_1$ and $t_2$ are in the same cliqueFinset 3 and $(t_1 ∩ t_2).card < 2$, then the set $\{t_1, t_2\}$ is a triangle packing.
      have h_packing : isTrianglePacking G {t1, t2} := by
        refine' ⟨ _, _ ⟩;
        · aesop_cat;
        · simp_all +decide [ Set.Pairwise ];
          exact ⟨ fun h => Nat.le_of_lt_succ h_nu, fun h => Nat.le_of_lt_succ ( by rwa [ Finset.inter_comm ] ) ⟩;
      -- Since $\{t_1, t_2\}$ is a triangle packing, its cardinality is at least 2.
      have h_card : 2 ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        simp;
        by_cases h : t1 = t2;
        · simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact absurd h_nu ( by rw [ ht1.2 ] ; decide );
        · exact ⟨ { t1, t2 }, ⟨ Finset.insert_subset_iff.mpr ⟨ ht1, Finset.singleton_subset_iff.mpr ht2 ⟩, h_packing ⟩, by rw [ Finset.card_insert_of_notMem ( by aesop ), Finset.card_singleton ] ⟩;
      rw [ Ne.eq_def, Option.getD_eq_iff ];
      exact fun h => by rcases h with ( h | h ) <;> have := Finset.le_max h_card <;> simp_all +decide ;

/-
Given three triangles $t, t_1, t_2$, if $t$ intersects both $t_1$ and $t_2$ in at least 2 vertices, and $t_1 \cap t_2$ has size 2, then either $t$ contains the intersection of $t_1$ and $t_2$, or $t$ is contained in the union of $t_1$ and $t_2$.
-/
lemma triangle_subset_union_or_contains_inter {V : Type*} [DecidableEq V]
    (t t1 t2 : Finset V)
    (ht : t.card = 3) (ht1 : t1.card = 3) (ht2 : t2.card = 3)
    (h_inter_1 : (t ∩ t1).card ≥ 2)
    (h_inter_2 : (t ∩ t2).card ≥ 2)
    (h_t1_t2_inter : (t1 ∩ t2).card = 2) :
    (t1 ∩ t2) ⊆ t ∨ t ⊆ (t1 ∪ t2) := by
      have := Finset.card_sdiff_add_card_inter t t1; ( have := Finset.card_sdiff_add_card_inter t t2; ( have := Finset.card_union_add_card_inter t1 t2; simp_all +decide ; ) );
      by_contra h_contra;
      simp_all +decide [ Finset.subset_iff ];
      have h_t_subset_t1_t2_union : t ⊆ t1 ∪ t2 := by
        have h_t_subset_t1_t2_union : (t ∩ t1 ∪ t ∩ t2).card ≥ 3 := by
          have h_t_subset_t1_t2_union : (t ∩ t1 ∪ t ∩ t2).card ≥ (t ∩ t1).card + (t ∩ t2).card - (t ∩ t1 ∩ t2).card := by
            rw [ ← Finset.card_union_add_card_inter ];
            simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
          have h_t_subset_t1_t2_union : (t ∩ t1 ∩ t2).card ≤ 1 := by
            have h_t_subset_t1_t2_union : (t ∩ t1 ∩ t2).card ≤ (t1 ∩ t2).card - 1 := by
              refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
              simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
            aesop;
          omega;
        have h_t_subset_t1_t2_union : (t ∩ t1 ∪ t ∩ t2) = t := by
          exact Finset.eq_of_subset_of_card_le ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ( by linarith );
        exact h_t_subset_t1_t2_union ▸ Finset.union_subset ( Finset.inter_subset_right.trans ( Finset.subset_union_left ) ) ( Finset.inter_subset_right.trans ( Finset.subset_union_right ) );
      grind

/-
If a nonempty family of triangles has pairwise intersection size at least 2, then either all triangles share a common edge, or all triangles are contained in a set of 4 vertices.
-/
lemma intersecting_triangles_structure {V : Type*} [DecidableEq V]
    (T : Finset (Finset V))
    (h_nonempty : T.Nonempty)
    (h_card : ∀ t ∈ T, t.card = 3)
    (h_int : ∀ t1 ∈ T, ∀ t2 ∈ T, (t1 ∩ t2).card ≥ 2) :
    (∃ u v : V, u ≠ v ∧ ∀ t ∈ T, {u, v} ⊆ t) ∨
    (∃ S : Finset V, S.card = 4 ∧ ∀ t ∈ T, t ⊆ S) := by
      -- If all triangles are equal, then they share all edges, so Case 1 holds. Otherwise, there exist $t_1, t_2 \in T$ with $t_1 \ne t_2$.
      by_cases h_eq : T.card ≤ 1;
      · cases' h_nonempty with t ht;
        rw [ Finset.card_le_one_iff_subset_singleton ] at h_eq;
        rcases Finset.card_eq_three.mp ( h_card t ht ) with ⟨ u, v, w, h ⟩ ; aesop;
        exact Or.inl ⟨ u, v, left, by simp +decide [ Finset.insert_subset_iff ] ⟩;
      · -- If there exist $t_1, t_2 \in T$ with $t_1 \ne t_2$, then $|t_1 \cap t_2| = 2$ (since $\ge 2$ and $<3$).
        obtain ⟨t1, ht1, t2, ht2, h_distinct⟩ : ∃ t1 ∈ T, ∃ t2 ∈ T, t1 ≠ t2 ∧ (t1 ∩ t2).card = 2 := by
          obtain ⟨ t1, ht1, t2, ht2, hne ⟩ := Finset.one_lt_card.1 ( lt_of_not_ge h_eq );
          refine' ⟨ t1, ht1, t2, ht2, hne, le_antisymm _ _ ⟩;
          · have := Finset.card_le_card ( show t1 ∩ t2 ⊆ t1 from Finset.inter_subset_left ) ; simp_all +decide ;
            interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
            have := Finset.eq_of_subset_of_card_le ( show t1 ∩ t2 ⊆ t1 from Finset.inter_subset_left ) ; have := Finset.eq_of_subset_of_card_le ( show t1 ∩ t2 ⊆ t2 from Finset.inter_subset_right ) ; aesop;
          · exact h_int t1 ht1 t2 ht2;
        -- Let $I = t_1 \cap t_2$ and $S = t_1 \cup t_2$.
        set I := t1 ∩ t2 with hI
        set S := t1 ∪ t2 with hS;
        -- By `triangle_subset_union_or_contains_inter`, for every $t \in T$, either $I \subseteq t$ or $t \subseteq S$.
        have h_cases : ∀ t ∈ T, I ⊆ t ∨ t ⊆ S := by
          intro t ht
          have h_inter_1 : (t ∩ t1).card ≥ 2 := by
            exact h_int t ht t1 ht1
          have h_inter_2 : (t ∩ t2).card ≥ 2 := by
            exact h_int t ht t2 ht2
          have h_t1_t2_inter : (t1 ∩ t2).card = 2 := by
            exact h_distinct.2
          apply triangle_subset_union_or_contains_inter t t1 t2 (h_card t ht) (h_card t1 ht1) (h_card t2 ht2) h_inter_1 h_inter_2 h_t1_t2_inter;
        -- If for all $t \in T$, $t \subseteq S$, then Case 2 holds (since $|S|=4$).
        by_cases h_all_subset_S : ∀ t ∈ T, t ⊆ S;
        · grind;
        · -- Suppose there exists $t^* \in T$ such that $t^* \not\subseteq S$.
          obtain ⟨t_star, ht_star, ht_star_not_subset_S⟩ : ∃ t_star ∈ T, ¬t_star ⊆ S := by
            exact by push_neg at h_all_subset_S; exact h_all_subset_S;
          -- We claim that for all $t \in T$, $I \subseteq t$.
          have h_I_subset_all : ∀ t ∈ T, I ⊆ t := by
            intro t ht;
            cases h_cases t ht <;> simp_all +decide [ Finset.subset_iff ];
            intro x hx1 hx2; specialize h_int t_star ht_star t ht; contrapose! h_int; simp_all +decide [ Finset.ext_iff ] ;
            have h_inter_card : (t_star ∩ t).card ≤ (t_star ∩ S).card - 1 := by
              refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
              simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
              grind;
            have h_inter_card_S : (t_star ∩ S).card ≤ (t_star).card - 1 := by
              exact Nat.le_sub_one_of_lt ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => ht_star_not_subset_S.elim fun x hx => by have := Finset.ext_iff.mp h x; aesop ⟩ ) );
            grind;
          rcases Finset.card_eq_two.mp h_distinct.2 with ⟨ u, v, huv ⟩ ; use Or.inl ⟨ u, v, by aesop ⟩

/-
If all triangles share a common edge, the triangle covering number is at most 1.
-/
lemma case_common_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u ≠ v)
    (h_common : ∀ t ∈ G.cliqueFinset 3, {u, v} ⊆ t) :
    triangleCoveringNumber G ≤ 1 := by
      unfold triangleCoveringNumber;
      by_cases h : ∃ t ∈ G.cliqueFinset 3, u ≠ v <;> simp_all +decide [ Set.subset_def ];
      · have h_edge_in_G : G.Adj u v := by
          obtain ⟨ t, ht ⟩ := h;
          simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
          exact ht.1 ( h_common t ht.1 ht.2 |>.1 ) ( h_common t ht.1 ht.2 |>.2 ) huv;
        -- Since {u, v} is an edge in G and covers all triangles, we can use it as the edge set E'.
        have h_edge_set : {Sym2.mk (u, v)} ∈ Finset.filter (fun E' => (∀ x ∈ E', x ∈ G.edgeSet) ∧ ∀ t, G.IsNClique 3 t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (G.edgeFinset.powerset) := by
          aesop;
        have h_min_card : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => (∀ x ∈ E', x ∈ G.edgeSet) ∧ ∀ t, G.IsNClique 3 t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (G.edgeFinset.powerset))) ≤ 1 := by
          exact Finset.min_le ( Finset.mem_image.mpr ⟨ _, h_edge_set, rfl ⟩ );
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ( ∀ x ∈ E', x ∈ G.edgeSet ) ∧ ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( G.edgeFinset.powerset ) ) ) <;> aesop;
      · have h_min : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ x ∈ E', x ∈ G.edgeSet) (Finset.powerset G.edgeFinset))) = some 0 := by
          refine' le_antisymm _ _ <;> simp_all +decide [ Finset.min ];
          · exact Finset.inf_le ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide ⟩ ) |> le_trans <| by simp +decide ;
          · exact fun _ _ _ => WithTop.coe_le_coe.mpr ( Nat.zero_le _ );
        exact h_min.symm ▸ by decide;

/-
If all triangles are contained in a set of 4 vertices, the triangle covering number is at most 2.
-/
lemma case_subset_of_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS_card : S.card = 4)
    (h_subset : ∀ t ∈ G.cliqueFinset 3, t ⊆ S) :
    triangleCoveringNumber G ≤ 2 := by
      unfold triangleCoveringNumber;
      have h_triangle_covering : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
        -- Let $e_1 = \{a, b\}$ and $e_2 = \{c, d\}$.
        obtain ⟨a, b, c, d, hS⟩ : ∃ a b c d : V, S = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
          simp_rw +decide [ Finset.card_eq_succ ] at hS_card ; aesop;
        by_cases hab : G.Adj a b <;> by_cases hcd : G.Adj c d <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · refine' ⟨ { Sym2.mk ( a, b ), Sym2.mk ( c, d ) }, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
          intro t ht; specialize h_subset t ht; simp_all +decide [ Finset.subset_iff ] ;
          have := Finset.card_eq_three.mp ht.2; obtain ⟨ x, y, z, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
          grind;
        · refine' ⟨ { Sym2.mk ( a, b ) }, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          intro t ht ht'; specialize h_subset t ht ht'; simp_all +decide [ Finset.subset_iff ] ;
          have := Finset.card_eq_three.mp ht'; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ SimpleGraph.isClique_iff, Set.Pairwise ] ;
          grind +ring;
        · refine' ⟨ { Sym2.mk ( c, d ) }, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          intro t ht ht'; specialize h_subset t ht ht'; simp_all +decide [ Finset.subset_iff ] ;
          rw [ Finset.card_eq_three ] at ht'; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := ht'; simp_all +decide [ SimpleGraph.isClique_iff ] ;
          rcases h_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp_all +decide;
          all_goals simp_all +decide [ SimpleGraph.adj_comm ];
        · use ∅; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          intro t ht ht'; specialize h_subset t ht ht'; simp_all +decide [ Finset.subset_iff ] ;
          rw [ Finset.card_eq_three ] at ht' ; obtain ⟨ x, y, z, hx, hy, hz, hxyz ⟩ := ht' ; simp_all +decide [ SimpleGraph.isClique_iff ];
          rcases h_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp_all +decide only [SimpleGraph.adj_comm];
      simp +zetaDelta at *;
      have h_min_le_two : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | (↑E' : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ (t : Finset V), G.IsNClique 3 t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ 2 := by
        obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_triangle_covering;
        exact le_trans ( Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( show E' ⊆ G.edgeFinset from fun x hx => by aesop ), hE₁, hE₃ ⟩ ) ) ) ( by simpa using hE₂ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' : Finset ( Sym2 V ) => ( E' : Set ( Sym2 V ) ) ⊆ G.edgeSet ∧ ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

/-
If every pair of triangles shares an edge, then the triangle covering number is at most 2.
-/
lemma parker_bound_strong (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_intersect : ∀ t1 ∈ G.cliqueFinset 3, ∀ t2 ∈ G.cliqueFinset 3, (t1 ∩ t2).card ≥ 2) :
    triangleCoveringNumber G ≤ 2 := by
      -- Consider two cases: when the cliqueFinset 3 is empty and when it is nonempty.
      by_cases h_empty : G.cliqueFinset 3 = ∅;
      · unfold triangleCoveringNumber; simp +decide [ h_empty ] ;
        simp_all +decide [ Finset.min ];
        rw [ Finset.inf_eq_iInf ];
        rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
        rotate_left;
        exact 0;
        · exact fun _ => zero_le _;
        · exact fun w hw => ⟨ ∅, by simp +decide [ hw ] ⟩;
        · exact Nat.zero_le _;
      · -- Apply `intersecting_triangles_structure` to `G.cliqueFinset 3`.
        obtain ⟨u, v, huv, h_common⟩ | ⟨S, hS_card, h_subset⟩ := intersecting_triangles_structure (G.cliqueFinset 3) (by
        exact Finset.nonempty_of_ne_empty h_empty) (by
        simp +contextual [ SimpleGraph.cliqueFinset ];
        exact fun t ht => ht.2) (by
        assumption);
        · exact le_trans ( case_common_edge G u v huv h_common ) ( by decide );
        · exact?

end AristotleLemmas

lemma parker_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 1) :
    triangleCoveringNumber G ≤ 2 := by
  convert parker_bound_strong G _;
  convert packing_one_implies_intersect G ( show trianglePackingNumber G = 1 from ?_ );
  · aesop;
  · cases hM ; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Vertex-disjoint blocks don't interact
-- ══════════════════════════════════════════════════════════════════════════════

-- If A and B are vertex-disjoint, their triangle neighborhoods don't share triangles
lemma vertex_disjoint_triangles_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    Disjoint (triangleUnionOf G A) (triangleUnionOf G B) := by
  -- A triangle sharing an edge with some a ∈ A has 2 vertices from a
  -- A triangle sharing an edge with some b ∈ B has 2 vertices from b
  -- If A and B are vertex-disjoint, no triangle can do both
  simp_all +decide [ Finset.disjoint_left, triangleUnionOf ];
  -- Assume there exists a triangle $t$ that shares an edge with both $A$ and $B$.
  by_contra h_contra;
  push_neg at h_contra;
  obtain ⟨ a, x, hx, ha, y, hy, hb ⟩ := h_contra; simp_all +decide [ trianglesSharingEdge ] ;
  -- Since $a \cap x$ and $a \cap y$ are both at least 2, there must be a common vertex $v$ in both intersections.
  obtain ⟨v, hv⟩ : ∃ v, v ∈ a ∩ x ∧ v ∈ a ∩ y := by
    have h_common_vertex : (a ∩ x).card + (a ∩ y).card > a.card := by
      have := Finset.card_le_card ( show a ⊆ Finset.univ from Finset.subset_univ a ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      linarith;
    contrapose! h_common_vertex;
    rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr h_common_vertex ) ] ; exact Finset.card_mono ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ;
  exact h_disj ( show v ∈ vertexSetOf A from Finset.mem_biUnion.mpr ⟨ x, hx, Finset.mem_inter.mp hv.1 |>.2 ⟩ ) ( show v ∈ vertexSetOf B from Finset.mem_biUnion.mpr ⟨ y, hy, Finset.mem_inter.mp hv.2 |>.2 ⟩ )

/- Aristotle failed to find a proof. -/
-- τ of disjoint union equals sum
lemma tau_disjoint_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_disj : Disjoint (triangleUnionOf G A) (triangleUnionOf G B)) :
    triangleCoveringNumberOn G (triangleUnionOf G A ∪ triangleUnionOf G B) =
    triangleCoveringNumberOn G (triangleUnionOf G A) + triangleCoveringNumberOn G (triangleUnionOf G B) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Vertex Partition Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- Two vertex-disjoint groups
noncomputable section AristotleLemmas

/-
A maximum triangle packing dominates all triangles in the graph (every triangle shares an edge with some triangle in the packing).
-/
lemma max_packing_dominates (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    G.cliqueFinset 3 ⊆ triangleUnionOf G M := by
      -- Assume there exists a triangle $t \in G.cliqueFinset 3$ such that $t \notin triangleUnionOf G M$.
      by_contra h_contra
      obtain ⟨t, ht⟩ : ∃ t ∈ G.cliqueFinset 3, t ∉ triangleUnionOf G M := by
        exact Set.not_subset.mp h_contra;
      -- Since $t$ does not share an edge with any triangle in $M$, $M \cup \{t\}$ is a triangle packing.
      have h_packing : isTrianglePacking G (M ∪ {t}) := by
        refine' ⟨ _, _ ⟩;
        · exact Finset.union_subset ( hM.1.1 ) ( Finset.singleton_subset_iff.mpr ht.1 );
        · intro x hx y hy hxy; simp_all +decide [ Set.Pairwise ] ;
          cases hx <;> cases hy <;> simp_all +decide [ triangleUnionOf ];
          · exact le_of_not_gt fun h => ht.2 _ ‹_› <| Finset.mem_filter.mpr ⟨ Finset.mem_coe.mpr <| by aesop, h ⟩;
          · simp_all +decide [ trianglesSharingEdge ];
            exact Nat.le_of_lt_succ ( by simpa only [ Finset.inter_comm ] using ht.2 x ‹_› ht.1 );
          · have := hM.1.2; aesop;
      -- Since $M$ is a maximum packing, $|M \cup \{t\}| \leq |M|$.
      have h_card : (M ∪ {t}).card ≤ M.card := by
        have h_card : (M ∪ {t}).card ≤ trianglePackingNumber G := by
          have h_card : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
            intro S hS;
            have h_max : ∀ S ∈ Finset.filter (isTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)), S.card ≤ (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)))).max.getD 0 := by
              intro S hS;
              have := Finset.le_max ( Finset.mem_image_of_mem Finset.card hS );
              cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
            exact h_max S ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( hS.1 ), hS ⟩ );
          exact h_card _ h_packing;
        exact h_card.trans ( hM.2.ge );
      rw [ Finset.card_union ] at h_card ; aesop;
      obtain ⟨ x, hx ⟩ := h_card; simp_all +decide [ Finset.inter_singleton ] ;
      split_ifs at hx <;> simp_all +decide [ isTrianglePacking ];
      exact right ( Finset.mem_biUnion.mpr ⟨ t, by assumption, Finset.mem_filter.mpr ⟨ h_packing.1 ‹_›, by simp +decide [ left.card_eq ] ⟩ ⟩ )

/-
The triangle covering number of the graph is equal to the covering number restricted to the union of triangles dominated by the packing.
-/
lemma tau_eq_tau_on_union (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    triangleCoveringNumber G = triangleCoveringNumberOn G (triangleUnionOf G M) := by
      -- Applying the definition of `triangleCoveringNumber` and `triangleCoveringNumberOn`, we see that they are equal if `G.cliqueFinset 3 = triangleUnionOf G M`.
      have h_eq : G.cliqueFinset 3 = triangleUnionOf G M := by
        refine' subset_antisymm _ _;
        · exact?;
        · exact Finset.biUnion_subset.2 fun t ht => Finset.filter_subset _ _;
      unfold triangleCoveringNumber triangleCoveringNumberOn;
      congr! 2;
      ext; aesop

/-
Definitions for the subgraph induced by a set of triangles, and a lemma stating that the non-diagonal edges of any triangle in the set are contained in the subgraph's edge set.
-/
open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgesInTriangles (T : Finset (Finset V)) : Finset (Sym2 V) :=
  T.biUnion (fun t => t.sym2)

def subgraphFromTriangles (T : Finset (Finset V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (edgesInTriangles T : Set (Sym2 V))

instance (T : Finset (Finset V)) : DecidableRel (subgraphFromTriangles T).Adj :=
  Classical.decRel _

lemma edges_in_subgraph (T : Finset (Finset V)) (t : Finset V) (ht : t ∈ T) :
    ∀ e ∈ t.sym2, ¬ e.IsDiag → e ∈ (subgraphFromTriangles T).edgeFinset := by
      simp_all +decide [ subgraphFromTriangles ];
      unfold edgesInTriangles; aesop;

/-
A triangle cannot share 2 vertices with each of two disjoint triangles.
-/
lemma bridge_triangle_impossible (a b t : Finset V)
    (ha : a.card = 3) (hb : b.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint a b)
    (hat : (a ∩ t).card ≥ 2) (hbt : (b ∩ t).card ≥ 2) : False := by
      have h_union : (a ∩ t) ∪ (b ∩ t) ⊆ t := by
        grind;
      have := Finset.card_mono h_union; simp_all +decide ;
      exact this.not_lt ( by rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp h_disj ( Finset.mem_inter.mp hx₁ |>.1 ) ( Finset.mem_inter.mp hx₂ |>.1 ) ) ] ; linarith )

/-
If $A$ and $B$ are vertex-disjoint sets of triangles, and $P$ is a packing in the subgraph induced by $A$'s neighborhood, then any triangle in $P$ shares at most 1 vertex with any triangle in $B$.
-/
lemma packing_in_subgraph_disjoint_from_other (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B))
    (P : Finset (Finset V))
    (hP : P ⊆ (subgraphFromTriangles (triangleUnionOf G A)).cliqueFinset 3) :
    ∀ t ∈ P, ∀ b ∈ B, (t ∩ b).card ≤ 1 := by
      -- By definition of $triangleUnionOf$, for any $t \in P$ and $b \in B$, if $t \cap b$ has at least 2 elements, then $t$ and $b$ share at least one triangle in $triangleUnionOf G A$.
      intros t ht b hb
      by_contra h_contra
      have h_triangle : ∃ t' ∈ triangleUnionOf G A, 2 ≤ (t' ∩ b).card := by
        have h_triangle : ∀ u v : V, u ∈ t → v ∈ t → u ≠ v → ∃ t' ∈ triangleUnionOf G A, u ∈ t' ∧ v ∈ t' := by
          have := hP ht; simp_all +decide [ SimpleGraph.isClique_iff, Finset.subset_iff ] ;
          intro u v hu hv huv; specialize hP ht; have := hP.1 hu hv; simp_all +decide [ subgraphFromTriangles, SimpleGraph.fromEdgeSet ] ;
          unfold edgesInTriangles at this; aesop;
        obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp ( not_le.mp h_contra );
        obtain ⟨ t', ht', hu', hv' ⟩ := h_triangle u v ( Finset.mem_of_mem_inter_left hu ) ( Finset.mem_of_mem_inter_left hv ) huv;
        exact ⟨ t', ht', Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩ ⟩;
      -- Since $t' \in triangleUnionOf G A$, there exists $a \in A$ such that $|t' \cap a| \ge 2$.
      obtain ⟨t', ht', h_t'_b⟩ : ∃ t' ∈ triangleUnionOf G A, 2 ≤ (t' ∩ b).card := h_triangle
      obtain ⟨a, ha, h_t'_a⟩ : ∃ a ∈ A, 2 ≤ (t' ∩ a).card := by
        unfold triangleUnionOf at ht';
        unfold trianglesSharingEdge at ht'; aesop;
      -- Since $a \subseteq vertexSetOf A$ and $b \subseteq vertexSetOf B$, and $vertexSetOf A$ and $vertexSetOf B$ are disjoint, we have $a \cap b = \emptyset$.
      have h_a_b_disjoint : a ∩ b = ∅ := by
        exact Finset.disjoint_iff_inter_eq_empty.mp ( Finset.disjoint_left.mpr fun x hx_a hx_b => Finset.disjoint_left.mp h_vertex_disj ( Finset.mem_biUnion.mpr ⟨ a, ha, hx_a ⟩ ) ( Finset.mem_biUnion.mpr ⟨ b, hb, hx_b ⟩ ) );
      have h_t'_a_b : t'.card = 3 := by
        unfold triangleUnionOf at ht';
        simp_all +decide [ trianglesSharingEdge ];
        exact ht'.choose_spec.2.1.card_eq;
      have h_t'_a_b : (t' ∩ a).card + (t' ∩ b).card ≤ t'.card := by
        rw [ ← Finset.card_union_of_disjoint ];
        · exact Finset.card_le_card fun x hx => by aesop;
        · simp_all +decide [ Finset.disjoint_left, Finset.ext_iff ];
      grind

/-
The covering number restricted to a set of triangles $T$ is at most the covering number of the subgraph induced by $T$.
-/
lemma tau_on_le_tau_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G T ≤ triangleCoveringNumber (subgraphFromTriangles T) := by
      -- Let $E'$ be a minimum triangle cover of the subgraph induced by $T$.
      obtain ⟨E', hE'⟩ : ∃ E' ⊆ (subgraphFromTriangles T).edgeFinset, (∀ t ∈ (subgraphFromTriangles T).cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = triangleCoveringNumber (subgraphFromTriangles T) := by
        unfold triangleCoveringNumber;
        have := Finset.min_of_mem ( Finset.mem_image_of_mem Finset.card ( show ( subgraphFromTriangles T ).edgeFinset ∈ { E' ∈ ( subgraphFromTriangles T ).edgeFinset.powerset | E' ⊆ ( subgraphFromTriangles T ).edgeFinset ∧ ∀ t ∈ ( subgraphFromTriangles T ).cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 } from ?_ ) );
        · rcases this with ⟨ b, hb ⟩ ; rw [ hb ] ; simp +decide [ Option.getD ] ;
          have := Finset.mem_of_min hb; aesop;
        · simp +decide [ SimpleGraph.cliqueFinset ];
          intro t ht; have := ht.card_eq; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          rcases Finset.card_eq_three.mp this with ⟨ a, b, c, hab, hbc, hac ⟩ ; use s(a, b) ; aesop;
      -- Since $E'$ covers all triangles in $T$, it is a valid cover for $T$.
      have h_valid_cover : ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2 := by
        intro t ht
        have h_t_in_subgraph : t ∈ (subgraphFromTriangles T).cliqueFinset 3 := by
          unfold subgraphFromTriangles;
          unfold edgesInTriangles; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          have := hT ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          intro x hx y hy; aesop;
        exact hE'.2.1 t h_t_in_subgraph;
      unfold triangleCoveringNumberOn;
      have h_E'_in_filter : E' ∈ Finset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset) := by
        simp_all +decide [ Finset.subset_iff ];
        intro e he; specialize hE'; replace hE' := hE'.1 he; simp_all +decide [ subgraphFromTriangles ] ;
        obtain ⟨ t, ht, he ⟩ := Finset.mem_biUnion.mp hE'.1; specialize hT ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        rcases e with ⟨ a, b ⟩ ; aesop;
      have h_E'_in_min : (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset))).min ≤ E'.card := by
        exact Finset.min_le ( Finset.mem_image_of_mem _ h_E'_in_filter );
      simp +zetaDelta at *;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ T, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( G.edgeFinset.powerset ) ) ) <;> aesop

/-
If $A$ and $B$ are vertex-disjoint parts of a max packing $M$, then the packing number of the subgraph induced by $A$'s neighborhood is at most 2 (since $|A|=2$).
-/
lemma nu_subgraph_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset (Finset V)) (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B))
    (h_tri_disj : Disjoint (triangleUnionOf G A) (triangleUnionOf G B))
    (hA_card : A.card = 2) :
    trianglePackingNumber (subgraphFromTriangles (triangleUnionOf G A)) ≤ 2 := by
      -- Suppose for contradiction that $\nu(G_A) > 2$. Then there exists a packing $P$ in $G_A$ with $|P| > 2$.
      by_contra h_contra
      obtain ⟨P, hP⟩ : ∃ P : Finset (Finset V), P ⊆ (subgraphFromTriangles (triangleUnionOf G A)).cliqueFinset 3 ∧ Set.Pairwise (P : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) ∧ P.card > 2 := by
        unfold trianglePackingNumber at h_contra;
        -- By definition of maximum, there exists some $P$ in the image of the cardinality function over the filter of triangle packings in $G_A$ such that $P.card > 2$.
        obtain ⟨P, hP⟩ : ∃ P ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking (subgraphFromTriangles (triangleUnionOf G A))) ((subgraphFromTriangles (triangleUnionOf G A)).cliqueFinset 3).powerset), P > 2 := by
          have h_max : ∃ P ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking (subgraphFromTriangles (triangleUnionOf G A))) ((subgraphFromTriangles (triangleUnionOf G A)).cliqueFinset 3).powerset), ∀ Q ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking (subgraphFromTriangles (triangleUnionOf G A))) ((subgraphFromTriangles (triangleUnionOf G A)).cliqueFinset 3).powerset), P ≥ Q := by
            exact ⟨ Finset.max' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by unfold isTrianglePacking; aesop ⟩ ) ⟩, Finset.max'_mem _ _, fun Q hQ => Finset.le_max' _ _ hQ ⟩;
          obtain ⟨ P, hP₁, hP₂ ⟩ := h_max;
          exact ⟨ P, hP₁, lt_of_not_ge fun h => h_contra <| by rw [ show ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking ( subgraphFromTriangles ( triangleUnionOf G A ) ) ) ( ( subgraphFromTriangles ( triangleUnionOf G A ) ).cliqueFinset 3 ).powerset ) ).max = some P from by
                                                                      exact le_antisymm ( Finset.max_le fun Q hQ => WithBot.coe_le_coe.mpr ( hP₂ Q hQ ) ) ( Finset.le_max hP₁ ) ] ; simp +decide ; linarith ⟩;
        rw [ Finset.mem_image ] at hP;
        rcases hP with ⟨ ⟨ P, hP₁, rfl ⟩, hP₂ ⟩ ; exact ⟨ P, Finset.mem_powerset.mp ( Finset.mem_filter.mp hP₁ |>.1 ), Finset.mem_filter.mp hP₁ |>.2.2, hP₂ ⟩ ;
      -- We claim $P \cup B$ is a valid packing in $G$.
      have hP_union_B : P ∪ B ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (P ∪ B : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
        have hP_union_B : P ∪ B ⊆ G.cliqueFinset 3 := by
          simp_all +decide [ Finset.subset_iff ];
          rintro t ( ht | ht );
          · have := hP.1 ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            have := hP.1 ht;
            unfold subgraphFromTriangles at this; simp_all +decide [ SimpleGraph.isClique_iff ] ;
            intro u hu v hv huv; specialize this hu hv huv; simp_all +decide [ SimpleGraph.fromEdgeSet_adj ] ;
            unfold edgesInTriangles at this; simp_all +decide [ SimpleGraph.fromEdgeSet_adj ] ;
            obtain ⟨ a, ha, hu, hv ⟩ := this; unfold triangleUnionOf at ha; simp_all +decide [ Finset.mem_biUnion ] ;
            obtain ⟨ b, hb, hab ⟩ := ha; unfold trianglesSharingEdge at hab; simp_all +decide [ Finset.mem_filter ] ;
            have := hab.1.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact this hu hv huv;
          · have := hM.1.1 ( hAB ▸ Finset.mem_union_right _ ht ) ; aesop;
        have hP_union_B_pairwise : ∀ t1 ∈ P, ∀ t2 ∈ B, (t1 ∩ t2).card ≤ 1 := by
          apply packing_in_subgraph_disjoint_from_other G A B h_vertex_disj P hP.left;
        simp_all +decide [ Set.Pairwise ];
        rintro x ( hx | hx ) y ( hy | hy ) hxy <;> simp_all +decide [ Finset.disjoint_left ];
        · simpa only [ Finset.inter_comm ] using hP_union_B_pairwise y hy x hx;
        · have := hM.1.2; simp_all +decide [ Finset.subset_iff ] ;
          exact this ( hAB ▸ Finset.mem_union_right _ hx ) ( hAB ▸ Finset.mem_union_right _ hy ) hxy;
      -- Thus $|P \cup B| = |P| + |B| > 2 + |B| = |A| + |B| = |M|$.
      have hP_union_B_card : (P ∪ B).card > M.card := by
        rw [ ← hAB, Finset.card_union_of_disjoint ];
        · rw [ Finset.card_union_of_disjoint hAB_disj ] ; linarith;
        · intro t htP htB;
          have := packing_in_subgraph_disjoint_from_other G A B h_vertex_disj P hP.1;
          simp_all +decide [ Finset.subset_iff ];
          intro x hx; specialize this x ( htP hx ) x ( htB hx ) ; have := hP_union_B.1 ( Or.inl ( htP hx ) ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      -- This contradicts the maximality of $M$.
      have h_contradiction : ∀ (P : Finset (Finset V)), P ⊆ G.cliqueFinset 3 → Set.Pairwise (P : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) → P.card ≤ M.card := by
        intro P hP hP_pairwise
        have hP_card : P.card ≤ trianglePackingNumber G := by
          unfold trianglePackingNumber;
          have hP_card : P ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset := by
            exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hP, ⟨ hP, hP_pairwise ⟩ ⟩;
          have hP_card : P.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            exact Finset.mem_image_of_mem _ hP_card;
          have := Finset.le_max hP_card;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        exact hP_card.trans ( hM.2.ge );
      exact hP_union_B_card.not_le ( h_contradiction _ hP_union_B.1 ( by simpa using hP_union_B.2 ) )

/-
If a maximum packing $M$ splits into two vertex-disjoint parts $A$ and $B$ with $|A|=2$, then the covering number restricted to $A$'s neighborhood is at most 4.
-/
lemma tau_component_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset (Finset V)) (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B))
    (h_tri_disj : Disjoint (triangleUnionOf G A) (triangleUnionOf G B))
    (hA_card : A.card = 2) :
    triangleCoveringNumberOn G (triangleUnionOf G A) ≤ 4 := by
      -- By `tau_on_le_tau_subgraph`, $\tau_G(triangleUnionOf G A) \le \tau(G_A)$.
      have h_tau_le_tau_subgraph : triangleCoveringNumberOn G (triangleUnionOf G A) ≤ triangleCoveringNumber (subgraphFromTriangles (triangleUnionOf G A)) := by
        apply tau_on_le_tau_subgraph;
        exact Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _;
      -- By `nu_subgraph_le_2`, $\nu(G_A) \le 2$.
      have h_nu_le_2 : trianglePackingNumber (subgraphFromTriangles (triangleUnionOf G A)) ≤ 2 := by
        exact?;
      -- By `parker_nu_le_2`, $\tau(G_A) \le 4$.
      have h_tau_subgraph_le_4 : triangleCoveringNumber (subgraphFromTriangles (triangleUnionOf G A)) ≤ 4 := by
        by_contra h_contra;
        -- Let $M_A$ be a maximum triangle packing in $G_A$.
        obtain ⟨M_A, hM_A⟩ : ∃ M_A : Finset (Finset V), isMaxPacking (subgraphFromTriangles (triangleUnionOf G A)) M_A ∧ M_A.card = trianglePackingNumber (subgraphFromTriangles (triangleUnionOf G A)) := by
          unfold isMaxPacking;
          unfold trianglePackingNumber;
          have := Finset.max_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking ( subgraphFromTriangles ( triangleUnionOf G A ) ) ) ( ( subgraphFromTriangles ( triangleUnionOf G A ) ).cliqueFinset 3 ).powerset ) ) from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_max ha; aesop;
          · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by unfold isTrianglePacking; simp +decide ⟩ ) ⟩;
        exact h_contra ( parker_nu_le_2 ( subgraphFromTriangles ( triangleUnionOf G A ) ) M_A hM_A.1 ( by linarith ) );
      exact le_trans h_tau_le_tau_subgraph h_tau_subgraph_le_4

/-
If a maximum packing $M$ splits into two vertex-disjoint parts $A$ and $B$ with $|A|=2$, then the covering number restricted to $A$'s neighborhood is at most 4.
-/
lemma tau_component_bound_v2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset (Finset V)) (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B))
    (h_tri_disj : Disjoint (triangleUnionOf G A) (triangleUnionOf G B))
    (hA_card : A.card = 2) :
    triangleCoveringNumberOn G (triangleUnionOf G A) ≤ 4 := by
      convert tau_component_bound G M hM A B hAB hAB_disj h_vertex_disj h_tri_disj hA_card using 1

end AristotleLemmas

theorem tau_le_8_vertex_partition_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_card : A.card = 2) (hB_card : B.card = 2)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8 := by
  -- Each group has ν = 2, so τ ≤ 4 each
  -- Vertex-disjoint means no interaction
  -- Total: τ ≤ 4 + 4 = 8
  refine' le_trans ( tau_eq_tau_on_union G M hM |> le_of_eq ) _;
  have h_triangle_union : triangleUnionOf G M = triangleUnionOf G A ∪ triangleUnionOf G B := by
    unfold triangleUnionOf; aesop;
  have h_triangle_disjoint : Disjoint (triangleUnionOf G A) (triangleUnionOf G B) := by
    exact vertex_disjoint_triangles_disjoint G A B h_vertex_disj;
  rw [ h_triangle_union, tau_disjoint_eq_sum _ _ _ h_triangle_disjoint ];
  have h_triangle_covering_A : triangleCoveringNumberOn G (triangleUnionOf G A) ≤ 4 := by
    apply tau_component_bound_v2 G M hM A B hAB hAB_disj h_vertex_disj h_triangle_disjoint hA_card
  have h_triangle_covering_B : triangleCoveringNumberOn G (triangleUnionOf G B) ≤ 4 := by
    apply tau_component_bound_v2;
    exact hM;
    rw [ Finset.union_comm, hAB ];
    · exact hAB_disj.symm;
    · exact h_vertex_disj.symm;
    · exact h_triangle_disjoint.symm;
    · exact hB_card
  linarith

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Application type mismatch: The argument
  (↑b : Set V)
has type
  Set V
but is expected to have type
  Finset V
in the application
  Disjoint (vertexSetOf A) (↑b : Set V)-/
-- 3+1 partition
theorem tau_le_8_vertex_partition_3_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset (Finset V)) (b : Finset V)
    (hAb : A ∪ {b} = M) (hb_not_in_A : b ∉ A)
    (hA_card : A.card = 3)
    (h_vertex_disj : Disjoint (vertexSetOf A) (b : Set V)) :
    triangleCoveringNumber G ≤ 8 := by
  -- A has ν = 3, so τ ≤ 6 by Parker
  -- {b} has ν = 1, so τ ≤ 2
  -- Vertex-disjoint means no interaction
  -- Total: τ ≤ 6 + 2 = 8
  sorry

/- Aristotle failed to find a proof. -/
-- General partition (any split of vertex-disjoint groups)
theorem tau_le_8_vertex_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8 := by
  -- |A| + |B| = 4, both nonempty
  -- τ ≤ 2|A| + 2|B| = 8
  sorry

-- Corollary: Disconnected sharing graph implies τ ≤ 8
theorem tau_le_8_disconnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    -- Sharing graph is disconnected: exists partition with no shared vertices
    (h_disconnected : ∃ (A B : Finset (Finset V)),
      A ∪ B = M ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      ∀ a ∈ A, ∀ b ∈ B, Disjoint (a : Set V) (b : Set V)) :
    triangleCoveringNumber G ≤ 8 := by
  obtain ⟨A, B, hAB, hAB_disj, hA_ne, hB_ne, h_all_disj⟩ := h_disconnected
  -- The pairwise disjointness implies vertex set disjointness
  simp_all +decide [ Set.disjoint_iff ];
  contrapose! h_all_disj;
  -- Let $v$ be a vertex that is in both $A$ and $B$.
  obtain ⟨v, hv⟩ : ∃ v : V, v ∈ vertexSetOf A ∧ v ∈ vertexSetOf B := by
    have h_vertex_disj : ¬Disjoint (vertexSetOf A) (vertexSetOf B) := by
      intro h_disjoint;
      exact h_all_disj.not_le ( tau_le_8_vertex_partition G M hM hM_card A B hAB hAB_disj hA_ne hB_ne h_disjoint );
    exact Finset.not_disjoint_iff.mp h_vertex_disj;
  exact ⟨ Finset.mem_biUnion.mp hv.1 |> Classical.choose, Finset.mem_biUnion.mp hv.1 |> Classical.choose_spec |> And.left, Finset.mem_biUnion.mp hv.2 |> Classical.choose, Finset.mem_biUnion.mp hv.2 |> Classical.choose_spec |> And.left, ⟨ v, Finset.mem_biUnion.mp hv.1 |> Classical.choose_spec |> And.right, Finset.mem_biUnion.mp hv.2 |> Classical.choose_spec |> And.right ⟩ ⟩

end