/-
Tuza ν=4 Strategy - Slot 75: CYCLE_4 FINAL ASSEMBLY

CRITICAL INSIGHT (from Grok-4 analysis 2025-12-25):
The old approach using tau_pair_le_4 was FALSE because it relied on
`avoiding_covered_by_spokes` which Aristotle proved FALSE via counterexample.

NEW STRATEGY: Per-shared-vertex using PROVEN infrastructure from slot71 + slot73:
1. cycle4_all_triangles_contain_shared (All-Middle): Every triangle contains some v_ij
2. S_e_structure: S_e triangles share common edge OR common external vertex → τ(S_e) ≤ 2
3. local_cover_le_2: At shared vertex, 2 edges of M suffice
4. tau_union_le_sum: Subadditivity

This file assembles ONLY proven lemmas - NO FALSE lemmas used.
-/

import Mathlib

set_option linter.mathlibStandardSet false
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

def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- S_e: triangles sharing edge with e but not with any other packing element
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- X_ef: bridges between e and f
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- Edges of M incident to vertex v
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun X => X.sym2.filter (fun e => v ∈ e))

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot71)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  unfold triangleCoveringNumberOn;
  by_cases hA : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2;
  · by_cases hB : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2;
    · obtain ⟨E₁, hE₁⟩ : ∃ E₁ ∈ G.edgeFinset.powerset, (∀ t ∈ A, ∃ e ∈ E₁, e ∈ t.sym2) ∧ E₁.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have h_min_card : ∃ E₁ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), ∀ E₂ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), E₁.card ≤ E₂.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ hA.choose_spec.1, hA.choose_spec.2 ⟩ ⟩;
        obtain ⟨ E₁, hE₁₁, hE₁₂ ⟩ := h_min_card;
        use E₁;
        rw [ Finset.min_eq_inf_withTop ];
        rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).inf WithTop.some = WithTop.some E₁.card from ?_ ];
        · exact ⟨ Finset.mem_filter.mp hE₁₁ |>.1, Finset.mem_filter.mp hE₁₁ |>.2, rfl ⟩;
        · refine' le_antisymm _ _;
          · exact Finset.inf_le ( Finset.mem_image_of_mem _ hE₁₁ );
          · simp +zetaDelta at *;
            exact hE₁₂;
      obtain ⟨E₂, hE₂⟩ : ∃ E₂ ∈ G.edgeFinset.powerset, (∀ t ∈ B, ∃ e ∈ E₂, e ∈ t.sym2) ∧ E₂.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have := Finset.min_of_mem ( show Finset.card ( Classical.choose hB ) ∈ Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) from Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Classical.choose_spec hB |>.1, Classical.choose_spec hB |>.2 ⟩, rfl ⟩ );
        obtain ⟨ b, hb ⟩ := this;
        have := Finset.mem_of_min hb;
        rw [ Finset.mem_image ] at this; obtain ⟨ E₂, hE₂, rfl ⟩ := this; exact ⟨ E₂, Finset.mem_filter.mp hE₂ |>.1, Finset.mem_filter.mp hE₂ |>.2, by rw [ hb ] ; rfl ⟩ ;
      have h_union_cover : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ E₁.card + E₂.card := by
        use E₁ ∪ E₂;
        grind;
      have h_min_le : ∀ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) → (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ E'.card := by
        intros E' hE' hE'_cover;
        have h_min_le : ∀ x ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2}), (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ x := by
          simp +decide [ Option.getD ];
          intro x E' hE' hE'_cover hx;
          cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ];
          exact Nat.cast_le.mp ( h ▸ Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa [ Finset.subset_iff ] using hE' ), hE'_cover ⟩, hx ⟩ ) );
        exact h_min_le _ ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE', hE'_cover ⟩ ) );
      exact le_trans ( h_min_le _ h_union_cover.choose_spec.1 h_union_cover.choose_spec.2.1 ) ( h_union_cover.choose_spec.2.2.trans ( by linarith ) );
    · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, Finset.mem_filter.mp hE' |>.2 ⟩ ] ; simp +decide;
      rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := Finset.mem_filter.mp hE' |>.2 t ( Or.inr ht ) ; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩ ] ; simp +decide;
  · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => Finset.mem_filter.mp hE' |>.2 t ( Finset.mem_union_left _ ht ) ⟩ ] ; simp +decide;
    simp +decide [ Option.getD ]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: S_e_structure (from slot71) - THE CLASSIFICATION LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- S_e triangles either all share a common edge of e, OR all share a common external vertex.
    This is the key structural result for bounding τ(S_e) ≤ 2. -/
lemma S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ ∀ t ∈ S_e G M e, t ≠ e → {u, v} ⊆ t) ∨
    (∃ x : V, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t) := by
  sorry -- PROVEN in slot71 uuid 5a800e22

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: cycle4_all_triangles_contain_shared (from slot73) - ALL-MIDDLE
-- ══════════════════════════════════════════════════════════════════════════════

/-- In cycle_4, every triangle contains at least one shared vertex v_ab, v_bc, v_cd, or v_da.
    This is the "All-Middle" property. -/
lemma cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t := by
  sorry -- PROVEN in slot73 uuid eb28d806

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: local_cover_le_2 (from slot73) - 2 EDGES SUFFICE AT SHARED VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- At a shared vertex v where exactly two packing elements meet,
    2 edges from M_edges_at suffice to cover all triangles at v. -/
lemma local_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ M_edges_at G M v ∧
    ∀ t ∈ G.cliqueFinset 3, v ∈ t →
      (∃ e ∈ M_edges_at G M v, e ∈ t.sym2) →
      (∃ e ∈ E', e ∈ t.sym2) := by
  sorry -- PROVEN in slot73 uuid eb28d806

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: tau_at_shared_vertex_le_2
-- ══════════════════════════════════════════════════════════════════════════════

/-- At shared vertex v, all triangles containing v are covered by ≤ 2 edges. -/
lemma tau_at_shared_vertex_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤ 2 := by
  sorry -- Use local_cover_le_2

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: cycle4_vertex_partition
-- ══════════════════════════════════════════════════════════════════════════════

/-- In cycle_4, v_ab is only in A and B. -/
lemma cycle4_vertex_only_in_adj (M : Finset (Finset V))
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab : V) (hAB : A ∩ B = {v_ab}) :
    ∀ Z ∈ M, v_ab ∈ Z → Z = A ∨ Z = B := by
  intro Z hZ hv
  have hM_eq : M = {A, B, C, D} := hcycle.1
  rw [hM_eq] at hZ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
  rcases hZ with rfl | rfl | rfl | rfl
  · left; rfl
  · right; rfl
  · -- v_ab ∈ C, but A ∩ C = ∅
    have hAC : (A ∩ C).card = 0 := hcycle.2.2.2.2.2.2.2.2.2.2.2.1
    have hv_in_A : v_ab ∈ A := by
      have h := Finset.eq_singleton_iff_unique_mem.mp hAB
      exact (Finset.mem_inter.mp h.1).1
    have hv_in_AC : v_ab ∈ A ∩ C := Finset.mem_inter.mpr ⟨hv_in_A, hv⟩
    simp only [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem] at hAC
    exact absurd hv_in_AC (hAC v_ab)
  · -- v_ab ∈ D, but B ∩ D = ∅
    have hBD : (B ∩ D).card = 0 := hcycle.2.2.2.2.2.2.2.2.2.2.2.2
    have hv_in_B : v_ab ∈ B := by
      have h := Finset.eq_singleton_iff_unique_mem.mp hAB
      exact (Finset.mem_inter.mp h.1).2
    have hv_in_BD : v_ab ∈ B ∩ D := Finset.mem_inter.mpr ⟨hv_in_B, hv⟩
    simp only [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem] at hBD
    exact absurd hv_in_BD (hBD v_ab)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: CYCLE_4 CASE (New Strategy)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: If ν = 4 with CYCLE_4 structure, then τ ≤ 8

    Strategy: Partition by shared vertices using All-Middle property.
    - Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da (cycle4_all_triangles_contain_shared)
    - At each shared vertex v, τ(triangles at v) ≤ 2 (tau_at_shared_vertex_le_2)
    - Total: τ ≤ 4 × 2 = 8 (tau_union_le_sum)

    Key insight: This avoids the FALSE avoiding_covered_by_spokes lemma!
-/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: Extract shared vertices
  have hAB_card : (A ∩ B).card = 1 := hcycle.2.2.2.2.2.2.2.1
  have hBC_card : (B ∩ C).card = 1 := hcycle.2.2.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.1
  have hDA_card : (D ∩ A).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.2.1

  obtain ⟨v_ab, hv_ab⟩ : ∃ v, A ∩ B = {v} := by
    have := Finset.card_eq_one.mp hAB_card
    exact this
  obtain ⟨v_bc, hv_bc⟩ : ∃ v, B ∩ C = {v} := by
    have := Finset.card_eq_one.mp hBC_card
    exact this
  obtain ⟨v_cd, hv_cd⟩ : ∃ v, C ∩ D = {v} := by
    have := Finset.card_eq_one.mp hCD_card
    exact this
  obtain ⟨v_da, hv_da⟩ : ∃ v, D ∩ A = {v} := by
    have := Finset.card_eq_one.mp hDA_card
    exact this

  -- Step 2: M membership
  have hM_eq : M = {A, B, C, D} := hcycle.1
  have hA_in : A ∈ M := by rw [hM_eq]; simp
  have hB_in : B ∈ M := by rw [hM_eq]; simp
  have hC_in : C ∈ M := by rw [hM_eq]; simp
  have hD_in : D ∈ M := by rw [hM_eq]; simp
  have hAB_ne : A ≠ B := hcycle.2.1
  have hBC_ne : B ≠ C := hcycle.2.2.1
  have hCD_ne : C ≠ D := hcycle.2.2.2.1
  have hDA_ne : D ≠ A := hcycle.2.2.2.2.1

  -- Step 3: "Only in adjacent pair" facts
  have h_only_ab : ∀ Z ∈ M, v_ab ∈ Z → Z = A ∨ Z = B :=
    cycle4_vertex_only_in_adj M A B C D hcycle v_ab hv_ab
  have h_only_bc : ∀ Z ∈ M, v_bc ∈ Z → Z = B ∨ Z = C := by
    intro Z hZ hv
    rw [hM_eq] at hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl | rfl | rfl
    all_goals sorry
  have h_only_cd : ∀ Z ∈ M, v_cd ∈ Z → Z = C ∨ Z = D := by sorry
  have h_only_da : ∀ Z ∈ M, v_da ∈ Z → Z = D ∨ Z = A := by sorry

  -- Step 4: Local bounds
  have h_ab : triangleCoveringNumberOn G (trianglesContainingVertex G v_ab) ≤ 2 :=
    tau_at_shared_vertex_le_2 G M hM A B hA_in hB_in hAB_ne v_ab hv_ab h_only_ab
  have h_bc : triangleCoveringNumberOn G (trianglesContainingVertex G v_bc) ≤ 2 :=
    tau_at_shared_vertex_le_2 G M hM B C hB_in hC_in hBC_ne v_bc hv_bc h_only_bc
  have h_cd : triangleCoveringNumberOn G (trianglesContainingVertex G v_cd) ≤ 2 :=
    tau_at_shared_vertex_le_2 G M hM C D hC_in hD_in hCD_ne v_cd hv_cd h_only_cd
  have h_da : triangleCoveringNumberOn G (trianglesContainingVertex G v_da) ≤ 2 :=
    tau_at_shared_vertex_le_2 G M hM D A hD_in hA_in hDA_ne v_da hv_da h_only_da

  -- Step 5: All triangles are covered by the union
  have h_all_middle : ∀ t ∈ G.cliqueFinset 3,
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t :=
    cycle4_all_triangles_contain_shared G M hM A B C D hcycle v_ab v_bc v_cd v_da
      hv_ab hv_bc hv_cd hv_da

  -- Step 6: Assembly
  sorry -- Combine using tau_union_le_sum: τ ≤ 2 + 2 + 2 + 2 = 8

end
