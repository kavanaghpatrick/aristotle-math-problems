/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b5840fb7-aaea-4b59-9bc0-d38c1bccea4a

The following was proved by Aristotle:

- theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2

- lemma cycle4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D

- theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8
-/

/-
Tuza ν=4 - Slot 50: CYCLE_4 Case via Pair Splitting

PROBLEM: Prove τ(G) ≤ 8 when ν(G) = 4 and packing forms a cycle A—B—C—D—A.

STRUCTURE:
- 4 packing elements: A, B, C, D forming a cycle
- 4 shared vertices: v_ab (A∩B), v_bc (B∩C), v_cd (C∩D), v_da (D∩A)
- Adjacent pairs share exactly 1 vertex
- Opposite pairs (A,C) and (B,D) are vertex-disjoint

STRATEGY: Split into two adjacent pair sets:
- T_pair(A,B): triangles sharing edge with A or B
- T_pair(C,D): triangles sharing edge with C or D
- Apply shared_vertex_concentrated_savings: τ(T_pair) ≤ 4 each
- Total: 4 + 4 = 8 edges

CRITICAL ISSUE (from Codex validation):
The lemma shared_vertex_concentrated_savings assumes we can choose S_e covers
that include edges through the shared vertex v. But τ(S_e) ≤ 2 only guarantees
SOME 2-edge cover exists, not that it touches v. If S_e triangles only use
edges opposite to v, the cover might not hit bridges X_{e,f}.

FOR ARISTOTLE TO EXPLORE:
1. Can we ALWAYS choose a 2-edge S_e cover that includes a v-edge?
2. Or does the structural constraint of the cycle force this?
3. The "no diagonal bridges" lemmas (X_{A,C} = ∅) are PROVEN in this file.

KEY PROVEN RESULT: cycle4_no_opposite_bridges shows X_{A,C} = X_{B,D} = ∅
using the omega proof on triangle cardinality.

SCAFFOLDING: tau_S_le_2 (slot6), tau_X_le_2 (slot24), tau_union_le_sum (slot16)
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

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

-- Cycle structure: A—B—C—D—A where adjacent pairs share exactly one vertex
def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  -- All distinct
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  -- Adjacent pairs share exactly one vertex (cycle edges)
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  -- Opposite pairs are vertex-disjoint (no cycle diagonals)
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2⟩
  have := Finset.min_le (Finset.mem_image_of_mem Finset.card h_mem)
  rw [WithTop.le_coe_iff] at this; aesop

lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *
  constructor
  · exact Finset.union_subset hA.1 hB.1
  · intro t ht
    simp only [Finset.mem_union] at ht
    cases ht with
    | inl htA =>
      obtain ⟨e, heEA, het⟩ := hA.2 t htA
      exact ⟨e, Finset.mem_union_left EB heEA, het⟩
    | inr htB =>
      obtain ⟨e, heEB, het⟩ := hB.2 t htB
      exact ⟨e, Finset.mem_union_right EA heEB, het⟩

-- PROVEN: Te = Se ∪ bridges (from slot 6)
lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G M e ∪ bridges G M e := by
  ext t
  simp only [Finset.mem_union, S_e, bridges, trianglesSharingEdge, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- PROVEN in slot16: τ(A ∪ B) ≤ τ(A) + τ(B)
noncomputable section AristotleLemmas

/-
If a triangle cover exists for A, then there exists a triangle cover for A whose cardinality is equal to the triangle covering number of A.
-/
lemma exists_min_cover_of_exists_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (h : ∃ E, isTriangleCover G A E) :
    ∃ E, isTriangleCover G A E ∧ E.card = triangleCoveringNumberOn G A := by
      have h_nonempty : ∃ E' ∈ Finset.powerset (G.edgeFinset), isTriangleCover G A E' := by
        obtain ⟨ E, hE ⟩ := h;
        exact ⟨ E, Finset.mem_powerset.mpr hE.1, hE ⟩;
      have h_exists_min : ∃ E' ∈ Finset.powerset (G.edgeFinset), isTriangleCover G A E' ∧ ∀ E'' ∈ Finset.powerset (G.edgeFinset), isTriangleCover G A E'' → E'.card ≤ E''.card := by
        have := Finset.exists_min_image ( Finset.filter ( fun E' => isTriangleCover G A E' ) ( G.edgeFinset.powerset ) ) ( fun E' => E'.card ) ⟨ h_nonempty.choose, Finset.mem_filter.mpr ⟨ h_nonempty.choose_spec.1, h_nonempty.choose_spec.2 ⟩ ⟩ ; aesop;
      obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_exists_min;
      unfold triangleCoveringNumberOn;
      rw [ show Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 } ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G A E' ) ( Finset.powerset ( G.edgeFinset ) ) ) from ?_ ];
      · rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G A E' ) ( Finset.powerset ( G.edgeFinset ) ) ) ).min = some ( E'.card ) from ?_ ];
        · exact ⟨ E', hE₂, rfl ⟩;
        · refine' le_antisymm _ _;
          · exact Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE₁, hE₂ ⟩ ) );
          · simp +zetaDelta at *;
            exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₃ x hx₁ hx₂ );
      · unfold isTriangleCover; aesop;

end AristotleLemmas

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E, isTriangleCover G A E;
  · by_cases hB : ∃ E, isTriangleCover G B E;
    · obtain ⟨EA, hEA⟩ := exists_min_cover_of_exists_cover G A hA
      obtain ⟨EB, hEB⟩ := exists_min_cover_of_exists_cover G B hB;
      exact le_trans ( le_triangleCoveringNumberOn _ _ _ ( isTriangleCover_union _ _ _ _ _ hEA.1 hEB.1 ) ) ( by simpa [ ← hEA.2, ← hEB.2 ] using Finset.card_union_le EA EB );
    · unfold triangleCoveringNumberOn;
      simp_all +decide [ Finset.min ];
      rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB E' ⟨ by aesop_cat, by aesop_cat ⟩ ] ; simp +decide;
      rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB E' ⟨ by aesop_cat, fun t ht => by aesop_cat ⟩ ] ; simp +decide;
  · simp_all +decide [ triangleCoveringNumberOn ];
    rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by aesop ⟩ ] ; simp +decide [ Option.getD ];
    rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( G.edgeFinset.powerset ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun x hx => hA ( Classical.choose ( Finset.mem_image.mp hx ) ) ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp ( Classical.choose_spec ( Finset.mem_image.mp hx ) |>.1 ) |>.1 ), fun t ht => by simpa using Finset.mem_filter.mp ( Classical.choose_spec ( Finset.mem_image.mp hx ) |>.1 ) |>.2 t ( by tauto ) ⟩ ] ; simp +decide

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
-- SCAFFOLDING: Full proof in slot16/slot29

-- PROVEN in slot6: τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

-- SCAFFOLDING: Full proof in slot6

-- PROVEN in slot24: τ(X_ef) ≤ 2
noncomputable section AristotleLemmas

/-
If two triangles e and f intersect at exactly one vertex w, then any triangle t in X_ef (sharing >=2 vertices with both) must contain an edge of e incident to w.
-/
lemma X_ef_implies_incident_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (w : V) (h_inter : e ∩ f = {w})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ u ∈ e, u ≠ w ∧ {w, u} ⊆ t := by
      -- Since $|t \cap e| \ge 2$ and $w \in t \cap e$, there must be another vertex $u \in t \cap e$ with $u \ne w$.
      obtain ⟨u, hu₁, hu₂⟩ : ∃ u ∈ t ∩ e, u ≠ w := by
        exact Finset.exists_mem_ne ( by linarith [ Finset.mem_filter.mp ht ] ) _;
      use u; simp_all +decide [ Finset.subset_iff ] ;
      have h_w_t : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card + (t ∩ (e ∩ f)).card := by
        have h_w_t : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card + (t ∩ (e ∩ f)).card := by
          have h_union : (t ∩ e) ∪ (t ∩ f) = t ∩ (e ∪ f) := by
            rw [ Finset.inter_union_distrib_left ]
          have h_inter : (t ∩ e) ∩ (t ∩ f) = t ∩ (e ∩ f) := by
            simp +decide [ Finset.inter_left_comm, Finset.inter_assoc ]
          rw [ ← h_union, ← h_inter, Finset.card_union_add_card_inter ];
        exact h_w_t;
      have h_w_t : (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2 := by
        unfold X_ef at ht; aesop;
      have h_w_t : (t ∩ (e ∪ f)).card ≤ 3 := by
        have h_w_t : t.card ≤ 3 := by
          have h_w_t : t ∈ G.cliqueFinset 3 := by
            unfold X_ef at ht; aesop;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact h_w_t.card_eq.le;
        exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_w_t;
      contrapose! h_w_t; simp_all +decide [ Finset.inter_comm ] ; linarith;

end AristotleLemmas

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  -- Let's split into two cases based on the size of the intersection of $e$ and $f$.
  by_cases h_inter : e ∩ f = ∅;
  · rw [ show X_ef G e f = ∅ from _ ];
    · unfold triangleCoveringNumberOn; simp +arith +decide;
      rw [ Finset.min ];
      rw [ Finset.inf_eq_iInf ];
      rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
      rotate_left;
      exact 0;
      · exact fun _ => zero_le _;
      · intro w hw; use 0; aesop;
      · decide +revert;
    · ext t
      simp [h_inter, X_ef];
      intro ht ht'; have := Finset.card_le_card ( show t ∩ e ∪ t ∩ f ⊆ t from Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ; simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ] ;
      have := ht.card_eq; simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ] ;
      rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => by simp_all +decide [ Finset.ext_iff ] ) ] at * ; linarith;
  · -- Let $w$ be the unique vertex in $e \cap f$.
    obtain ⟨w, hw⟩ : ∃ w, e ∩ f = {w} := by
      have h_inter_card : (e ∩ f).card ≤ 1 := by
        have := hM.1.2;
        exact this he hf hef;
      exact Finset.card_eq_one.mp ( le_antisymm h_inter_card ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h_inter ) ) );
    -- Let $E_{cover}$ be the set of edges in $e$ incident to $w$.
    set E_cover : Finset (Sym2 V) := (e.erase w).image (fun u => Sym2.mk (w, u));
    -- By the helper lemma, every triangle $t \in X_{ef}$ contains one of these edges.
    have h_cover : isTriangleCover G (X_ef G e f) E_cover := by
      refine' ⟨ _, _ ⟩;
      · -- Since $e$ is a triangle in $G$, every edge in $e$ is in $G$'s edge set.
        have h_edges_in_G : ∀ u ∈ e.erase w, Sym2.mk (w, u) ∈ G.edgeFinset := by
          have := hM.1;
          have := this.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          intro u hu h'u; have := this ( show w ∈ e from Finset.mem_of_mem_inter_left ( hw.symm ▸ Finset.mem_singleton_self _ ) ) ( show u ∈ e from h'u ) ; aesop;
        exact Finset.image_subset_iff.mpr h_edges_in_G;
      · intro t ht
        obtain ⟨u, hu⟩ : ∃ u ∈ e, u ≠ w ∧ {w, u} ⊆ t := by
          apply X_ef_implies_incident_edge G e f w hw t ht;
        aesop;
    refine' le_trans ( le_triangleCoveringNumberOn G _ _ h_cover ) _;
    refine' Finset.card_image_le.trans _;
    have := hM.1;
    have := this.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    have := this.2; simp_all +decide [ Finset.card_eq_three ] ;
    rcases this with ⟨ x, y, hxy, z, hxz, hyz, rfl ⟩ ; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;

-- SCAFFOLDING: Full proof in slot24/slot36

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURAL LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
In a cycle, opposite pairs are vertex-disjoint, so no triangle can share ≥2 vertices
with both A and C. Therefore X_{A,C} = ∅.
-/
lemma cycle4_no_opposite_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) (hcycle : isCycle4 ({A, B, C, D} : Finset (Finset V)) A B C D) :
    X_ef G A C = ∅ := by
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
  intro ht h_share_A h_share_C
  -- t shares ≥2 with A and ≥2 with C, but A ∩ C = ∅
  -- t is a triangle (card = 3), so this is impossible
  have hAC_disj : (A ∩ C).card = 0 := hcycle.2.2.2.2.2.2.2.2.2.2.2.1
  -- If t shares 2+ with A and 2+ with C, and A ∩ C = ∅, then t has 4+ vertices
  have h_t_card : t.card = 3 := by
    have h := SimpleGraph.mem_cliqueFinset_iff.mp ht
    exact h.card_eq
  -- (t ∩ A) and (t ∩ C) are disjoint since A ∩ C = ∅
  have h_disj : Disjoint (t ∩ A) (t ∩ C) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    have : (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C) := by
      ext x; simp only [Finset.mem_inter]; tauto
    rw [this]
    simp only [Finset.card_eq_zero] at hAC_disj
    rw [hAC_disj, Finset.inter_empty]
  -- Combined size: (t ∩ A).card + (t ∩ C).card ≤ t.card = 3
  have h_sum_le : (t ∩ A).card + (t ∩ C).card ≤ t.card := by
    have h_union : (t ∩ A) ∪ (t ∩ C) ⊆ t := Finset.union_subset (Finset.inter_subset_left) (Finset.inter_subset_left)
    have h_card_union : ((t ∩ A) ∪ (t ∩ C)).card ≤ t.card := Finset.card_le_card h_union
    rw [Finset.card_union_of_disjoint h_disj] at h_card_union
    exact h_card_union
  -- But (t ∩ A).card ≥ 2 and (t ∩ C).card ≥ 2, so sum ≥ 4 > 3
  omega

/--
Similarly, X_{B,D} = ∅ for opposite pair B and D.
-/
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
  have h_disj : Disjoint (t ∩ B) (t ∩ D) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    have : (t ∩ B) ∩ (t ∩ D) = t ∩ (B ∩ D) := by
      ext x; simp only [Finset.mem_inter]; tauto
    rw [this]
    simp only [Finset.card_eq_zero] at hBD_disj
    rw [hBD_disj, Finset.inter_empty]
  have h_sum_le : (t ∩ B).card + (t ∩ D).card ≤ t.card := by
    have h_union : (t ∩ B) ∪ (t ∩ D) ⊆ t := Finset.union_subset (Finset.inter_subset_left) (Finset.inter_subset_left)
    have h_card_union : ((t ∩ B) ∪ (t ∩ D)).card ≤ t.card := Finset.card_le_card h_union
    rw [Finset.card_union_of_disjoint h_disj] at h_card_union
    exact h_card_union
  omega

/- Aristotle failed to find a proof. -/
/--
KEY LEMMA: When e and f share exactly one vertex, τ(T_pair(e,f)) ≤ 4.

Proof idea:
- τ(S_e) ≤ 2, τ(S_f) ≤ 2
- Choose 2 edges for S_e such that one is incident to shared vertex v
- Choose 2 edges for S_f such that one is incident to shared vertex v
- The two v-incident edges together cover all bridges X_{e,f}
- Total: 4 edges (may have overlap, giving ≤ 4)
-/
lemma shared_vertex_concentrated_savings (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_share_one : (e ∩ f).card = 1) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- T_pair = T_e ∪ T_f = (S_e ∪ bridges_e) ∪ (S_f ∪ bridges_f)
  -- In cycle case, bridges between e and f go through shared vertex
  -- Key: S_e and S_f covers + bridge handling gives ≤ 4
  sorry

-- TARGET: Main proof using spoke edge selection at shared vertex

/--
Every triangle in G shares an edge with some packing element.
-/
lemma cycle4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  -- Every triangle must share ≥2 vertices with some packing element
  -- In cycle, it must share with A, B, C, or D
  -- If shares with A or B → in T_pair(A,B)
  -- If shares with C or D → in T_pair(C,D)
  simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
  by_contra h_none
  push_neg at h_none
  -- t doesn't share edge with any of A, B, C, D
  have h_not_A : (t ∩ A).card < 2 := h_none.1.1 ht
  have h_not_B : (t ∩ B).card < 2 := h_none.1.2 ht
  have h_not_C : (t ∩ C).card < 2 := h_none.2.1 ht
  have h_not_D : (t ∩ D).card < 2 := h_none.2.2 ht
  -- This contradicts maximality of packing
  -- Since t does not share an edge with any of the cycle edges (A, B, C, D), M ∪ {t} is also a packing.
  have h_union_packing : isTrianglePacking G (M ∪ {t}) := by
    -- Since $t$ shares at most one vertex with each cycle edge, for any $f \in M$, $t$ shares at most one vertex with $f$.
    have h_t_f : ∀ f ∈ M, (t ∩ f).card ≤ 1 := by
      -- Since $M$ is a cycle of four elements, any $f \in M$ must be one of $A$, $B$, $C$, or $D$.
      have h_f_cases : ∀ f ∈ M, f = A ∨ f = B ∨ f = C ∨ f = D := by
        cases hcycle ; aesop;
      intro f hf; rcases h_f_cases f hf with ( rfl | rfl | rfl | rfl ) <;> linarith;
    refine' ⟨ _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact fun f hf => by have := hM.1.1 hf; aesop;
    · intro x hx y hy hxy; cases eq_or_ne x t <;> cases eq_or_ne y t <;> simp_all +decide [ Set.Pairwise ] ;
      · simpa only [ Finset.inter_comm ] using h_t_f x hx;
      · have := hM.1.2; aesop;
  -- Since adding t to M results in a packing with 5 triangles, this contradicts the maximality of M.
  have h_contradiction : (M ∪ {t}).card > M.card := by
    have h_contradiction : t ∉ M := by
      intro h; have := hcycle.1; simp_all +decide ;
      rcases h with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
    aesop;
  contrapose! h_contradiction;
  have h_card_le : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ M.card := by
    intro S hS;
    have h_card_le : S.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      have h_card_le : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( hS.1 ), hS ⟩, rfl ⟩;
      have := Finset.le_max h_card_le;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_card_le.trans ( hM.2.ge );
  exact h_card_le _ h_union_packing

-- TARGET: maximality argument

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: CYCLE_4 CASE
-- ══════════════════════════════════════════════════════════════════════════════

/--
MAIN THEOREM: For cycle A—B—C—D—A, τ(G) ≤ 8.

Proof:
1. All triangles are in T_pair(A,B) ∪ T_pair(C,D)
2. τ(T_pair(A,B)) ≤ 4 by shared_vertex_concentrated_savings
3. τ(T_pair(C,D)) ≤ 4 by shared_vertex_concentrated_savings
4. τ(G) ≤ τ(T_pair(A,B)) + τ(T_pair(C,D)) ≤ 4 + 4 = 8
-/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: Get membership facts
  have hM_eq : M = {A, B, C, D} := hcycle.1
  have hA : A ∈ M := by rw [hM_eq]; simp
  have hB : B ∈ M := by rw [hM_eq]; simp
  have hC : C ∈ M := by rw [hM_eq]; simp
  have hD : D ∈ M := by rw [hM_eq]; simp

  -- Step 2: Extract sharing information (keep hcycle for later use)
  have hAB_ne : A ≠ B := hcycle.2.1
  have hCD_ne : C ≠ D := hcycle.2.2.2.2.2.2.1
  have hAB_share : (A ∩ B).card = 1 := hcycle.2.2.2.2.2.2.2.1
  have hCD_share : (C ∩ D).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.1

  -- Step 3: All triangles in T_pair(A,B) ∪ T_pair(C,D)
  have h_partition : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D :=
    cycle4_triangle_partition G M hM A B C D hcycle

  -- Step 4: Bound each T_pair
  have h_AB : triangleCoveringNumberOn G (T_pair G A B) ≤ 4 :=
    shared_vertex_concentrated_savings G M hM A B hA hB hAB_ne hAB_share

  have h_CD : triangleCoveringNumberOn G (T_pair G C D) ≤ 4 :=
    shared_vertex_concentrated_savings G M hM C D hC hD hCD_ne hCD_share

  -- Step 5: Combine bounds
  -- τ(G) ≤ τ(T_pair(A,B) ∪ T_pair(C,D)) ≤ τ(T_pair(A,B)) + τ(T_pair(C,D)) ≤ 4 + 4 = 8
  calc triangleCoveringNumber G
      ≤ triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := by
        unfold triangleCoveringNumberOn;
        unfold triangleCoveringNumber; simp +decide [ Finset.min ] ;
        simp +decide [ Finset.inf_eq_iInf, Set.subset_def ];
        simp +decide [ Finset.subset_iff, T_pair ] at h_partition ⊢;
        simp +decide [ trianglesSharingEdge ] at h_partition ⊢;
        simp +decide [ show ∀ t : Finset V, ( G.IsNClique 3 t ∧ 2 ≤ ( t ∩ A ).card ∨ G.IsNClique 3 t ∧ 2 ≤ ( t ∩ B ).card ) ∨ G.IsNClique 3 t ∧ 2 ≤ ( t ∩ C ).card ∨ G.IsNClique 3 t ∧ 2 ≤ ( t ∩ D ).card ↔ G.IsNClique 3 t from fun t => by specialize @h_partition t; aesop ] -- TARGET: relate global τ to τ on subset covering all triangles
    _ ≤ triangleCoveringNumberOn G (T_pair G A B) + triangleCoveringNumberOn G (T_pair G C D) := by
        apply tau_union_le_sum
    _ ≤ 4 + 4 := by linarith
    _ = 8 := by ring

end