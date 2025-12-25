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
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- SCAFFOLDING: Full proof in slot16/slot29

-- PROVEN in slot6: τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- SCAFFOLDING: Full proof in slot6

-- PROVEN in slot24: τ(X_ef) ≤ 2
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- SCAFFOLDING: Full proof in slot24/slot36

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
  sorry -- TARGET: Main proof using spoke edge selection at shared vertex

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
  sorry -- TARGET: maximality argument

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
        sorry -- TARGET: relate global τ to τ on subset covering all triangles
    _ ≤ triangleCoveringNumberOn G (T_pair G A B) + triangleCoveringNumberOn G (T_pair G C D) := by
        apply tau_union_le_sum
    _ ≤ 4 + 4 := by linarith
    _ = 8 := by ring

end
