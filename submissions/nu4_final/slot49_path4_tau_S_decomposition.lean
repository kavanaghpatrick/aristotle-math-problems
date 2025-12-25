/-
Tuza ν=4 - Slot 49: PATH_4 Case via tau_S_le_2 Decomposition

PROBLEM: Prove τ(G) ≤ 8 when ν(G) = 4 and packing forms a path A—B—C—D.

STRUCTURE:
- 4 packing elements: A, B, C, D
- 3 shared vertices: v_ab (A∩B), v_bc (B∩C), v_cd (C∐D)
- Non-adjacent pairs (A,C) and (B,D) are vertex-disjoint

CRITICAL ISSUE (from Codex validation):
Bridges are NOT in S_e by definition! S_e excludes triangles that share
≥2 vertices with OTHER packing elements. So bridges need explicit handling.

REVISED STRATEGY:
Use T_pair decomposition instead of per-element:
- T_pair(A,B): all triangles sharing edge with A OR B (includes X_{A,B})
- T_pair(C,D): all triangles sharing edge with C OR D (includes X_{C,D})
- Bound each T_pair using shared_vertex_concentrated_savings

ALTERNATIVE (leaf removal):
- A and D are leaves (share vertex with only one neighbor)
- If τ(T_leaf) ≤ 2, then τ(G) ≤ 2 + τ(ν=3 residual) ≤ 2 + 6 = 8

FOR ARISTOTLE TO EXPLORE:
1. Can we prove τ(T_pair(e,f)) ≤ 4 when e ∩ f = {v}?
2. Or can we prove τ(T_leaf) ≤ 2 for leaves?
3. What's the correct bridge accounting?

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

def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

-- Path structure: A—B—C—D where adjacent pairs share exactly one vertex
def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  -- A distinct from B, C, D
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  -- Adjacent pairs share exactly one vertex
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  -- Non-adjacent pairs are vertex-disjoint
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slots 6, 16, 24)
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
-- PATH_4 STRUCTURAL LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
In a path A—B—C—D, bridges from A only go to B (the unique neighbor).
-/
lemma path4_A_bridges_only_to_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) :
    bridges G M A ⊆ X_ef G A B := by
  intro t ht
  simp only [bridges, Finset.mem_filter] at ht
  obtain ⟨h_share_A, f, hfM, hfne, h_share_f⟩ := ht
  -- f must be B since A only shares vertex with B
  simp only [X_ef, Finset.mem_filter]
  constructor
  · -- t is a triangle
    simp only [trianglesSharingEdge, Finset.mem_filter] at h_share_A
    exact h_share_A.1
  constructor
  · -- t shares ≥2 vertices with A
    simp only [trianglesSharingEdge, Finset.mem_filter] at h_share_A
    exact h_share_A.2
  · -- t shares ≥2 vertices with B
    -- Since f ∈ M, f ≠ A, and (t ∩ f).card ≥ 2, we need f = B
    -- Because A is disjoint from C and D in path4
    -- Extract disjointness facts from path structure BEFORE case split
    obtain ⟨hM_eq, hAB, hAC_ne, hAD_ne, hBC_ne, hBD_ne, hCD_ne,
            hAB_share, hBC_share, hCD_share, hAC_disj, hAD_disj, hBD_disj⟩ := hpath
    have hfM' : f ∈ ({A, B, C, D} : Finset (Finset V)) := by rw [← hM_eq]; exact hfM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfM'
    rcases hfM' with rfl | rfl | rfl | rfl
    · exact absurd rfl hfne
    · exact h_share_f
    · -- f = C: but (A ∩ C).card = 0, so (t ∩ C).card ≥ 2 impossible for t sharing edge with A
      exfalso
      -- t shares ≥2 with A and ≥2 with C, but A ∩ C = ∅
      -- t has only 3 vertices, so this is impossible
      sorry -- TARGET: derive contradiction from disjointness (use hAC_disj, h_share_f)
    · -- f = D: similar
      exfalso
      sorry -- TARGET: derive contradiction from disjointness (use hAD_disj, h_share_f)

/--
Bridges X_{A,B} are contained in trianglesSharingEdge A ∪ trianglesSharingEdge B.
This means they're covered when we cover S_A and S_B.
-/
lemma bridges_in_T_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) :
    X_ef G e f ⊆ trianglesSharingEdge G e ∪ trianglesSharingEdge G f := by
  intro t ht
  simp only [X_ef, Finset.mem_filter] at ht
  simp only [Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
  left
  exact ⟨ht.1, ht.2.1⟩

/--
All triangles in G are covered by T_A ∪ T_B ∪ T_C ∪ T_D.
-/
lemma path4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    G.cliqueFinset 3 ⊆
      trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D := by
  intro t ht
  -- Every triangle must share an edge with some packing element (by maximality)
  by_contra h_none
  simp only [Finset.mem_union, not_or] at h_none
  -- h_none has structure (((¬A) ∧ (¬B)) ∧ (¬C)) ∧ (¬D)
  have h_not_A := h_none.1.1.1
  have h_not_B := h_none.1.1.2
  have h_not_C := h_none.1.2
  have h_not_D := h_none.2
  -- Extract: t doesn't share edge with any element
  have h_disj_A : (t ∩ A).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_A
    by_contra h; push_neg at h; exact (h_not_A ht) (Nat.lt_of_succ_le h)
  have h_disj_B : (t ∩ B).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_B
    by_contra h; push_neg at h; exact (h_not_B ht) (Nat.lt_of_succ_le h)
  have h_disj_C : (t ∩ C).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_C
    by_contra h; push_neg at h; exact (h_not_C ht) (Nat.lt_of_succ_le h)
  have h_disj_D : (t ∩ D).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_D
    by_contra h; push_neg at h; exact (h_not_D ht) (Nat.lt_of_succ_le h)
  -- Now show this contradicts maximality: we could add t to M
  sorry -- TARGET: maximality argument

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PATH_4 CASE
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ(T_A) ≤ 2 + τ(bridges from A).
Since bridges from A only go to B, and X_{A,B} ⊆ T_A ∪ T_B, the bridge cost is shared.
-/
lemma tau_Te_le_4_for_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (trianglesSharingEdge G A) ≤ 4 := by
  -- T_A = S_A ∪ bridges(A)
  rw [Te_eq_Se_union_bridges G M A]
  -- bridges(A) ⊆ X_{A,B}
  have h_bridges : bridges G M A ⊆ X_ef G A B := path4_A_bridges_only_to_B G M A B C D hpath
  -- τ(S_A ∪ bridges) ≤ τ(S_A) + τ(bridges) ≤ 2 + 2 = 4
  calc triangleCoveringNumberOn G (S_e G M A ∪ bridges G M A)
      ≤ triangleCoveringNumberOn G (S_e G M A) + triangleCoveringNumberOn G (bridges G M A) := by
        apply tau_union_le_sum
    _ ≤ 2 + triangleCoveringNumberOn G (bridges G M A) := by
        have hA : A ∈ M := by rw [hpath.1]; simp
        linarith [tau_S_le_2 G M hM A hA]
    _ ≤ 2 + triangleCoveringNumberOn G (X_ef G A B) := by
        sorry -- TARGET: monotonicity from h_bridges
    _ ≤ 2 + 2 := by
        have hA : A ∈ M := by rw [hpath.1]; simp
        have hB : B ∈ M := by rw [hpath.1]; simp
        linarith [tau_X_le_2 G M hM A B hA hB hpath.2.1]
    _ = 4 := by ring

/--
MAIN THEOREM: For path A—B—C—D, τ(G) ≤ 8.

Proof: Apply tau_S_le_2 to each of A, B, C, D.
Total: 2 + 2 + 2 + 2 = 8 edges.

Alternative view: τ(T_A) + τ(T_B) + τ(T_C) + τ(T_D) with overlaps handled.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Strategy: Cover all triangles using 2 edges per packing element
  -- Step 1: Get membership facts
  have hA : A ∈ M := by rw [hpath.1]; simp
  have hB : B ∈ M := by rw [hpath.1]; simp
  have hC : C ∈ M := by rw [hpath.1]; simp
  have hD : D ∈ M := by rw [hpath.1]; simp

  -- Step 2: All triangles are in T_A ∪ T_B ∪ T_C ∪ T_D
  have h_cover : G.cliqueFinset 3 ⊆
      trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D :=
    path4_triangle_partition G M hM A B C D hpath

  -- Step 3: Bound covering number
  -- τ(G) = τ(all triangles) ≤ τ(T_A ∪ T_B ∪ T_C ∪ T_D)
  -- ≤ τ(T_A) + τ(T_B) + τ(T_C) + τ(T_D)
  -- But this gives 4+4+4+4 = 16, too loose!

  -- BETTER: Use S_e decomposition directly
  -- Each S_e needs 2 edges, and bridges are covered by adjacent S_e covers
  sorry -- MAIN TARGET: Construct 8-edge cover explicitly

end
