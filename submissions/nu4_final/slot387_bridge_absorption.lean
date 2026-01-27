/-
Tuza ν=4 PATH_4 - Slot 387: Bridge Absorption Lemma

DEBATE CONSENSUS (Grok, Gemini, Codex - 3 rounds):
  The proof gap is NOT definitional - it's MATHEMATICAL.
  - slot384 provides coverage for trianglesSharingEdge (T_e = S_e ∪ bridges)
  - slot257 provides τ(S_e) ≤ 2 (excludes bridges)
  - slot383 needs τ(T_e) ≤ 2 (includes bridges)

  THE MISSING PIECE: Bridge absorption
  - Show that S_e covers ALSO hit bridges X_{e,f}
  - Or equivalently: τ(S_e ∪ X_{e,f}) ≤ 2 for adjacent e, f

KEY MATHEMATICAL INSIGHT:
  For adjacent packing elements e and f sharing vertex v = e ∩ f:
  - ALL bridges X_{e,f} contain vertex v
  - S_e's structure shows covers can use spokes from v
  - Spoke edges from v hit both S_e triangles AND bridges

APPROACH:
  1. Prove bridges all contain the shared vertex (X_ef_mem_inter - already in slot257)
  2. Prove S_e ∪ X_{e,f} can be covered by 2 edges (NEW)
  3. Use this to construct 8-edge cover for all triangles

TIER: 2 (Bridge absorption - key structural lemma)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot257)
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

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot257)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridges X_{e,f} contain the shared vertex -/
lemma X_ef_mem_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  by_contra hv_not_in_t
  have h_disj : Disjoint (t ∩ e) (t ∩ f) := by
    rw [Finset.disjoint_left]
    intro x hxe hxf
    have hx_in_ef : x ∈ e ∩ f := mem_inter.mpr ⟨mem_of_mem_inter_right hxe, mem_of_mem_inter_right hxf⟩
    rw [hv] at hx_in_ef
    simp only [mem_singleton] at hx_in_ef
    rw [hx_in_ef] at hxe
    exact hv_not_in_t (mem_of_mem_inter_left hxe)
  have ht_card : t.card = 3 := by
    have ht_tri : t ∈ G.cliqueFinset 3 := by
      simp only [X_ef, mem_filter] at ht
      exact ht.1
    exact (G.mem_cliqueFinset_iff.mp ht_tri).2
  have h_ge : (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2 := by
    simp only [X_ef, mem_filter] at ht
    exact ht.2
  have h_union : (t ∩ e ∪ t ∩ f).card ≤ t.card := card_le_card (union_subset inter_subset_left inter_subset_left)
  rw [card_union_of_disjoint h_disj] at h_union
  omega

/-- Helper: edge cover bound -/
lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2⟩
  have := Finset.min_le (Finset.mem_image_of_mem Finset.card h_mem)
  rw [WithTop.le_coe_iff] at this; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: S_e ∪ X_{e,f} can be covered by 2 edges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
For e = {v, a, b} and f adjacent to e (sharing vertex v):
1. X_{e,f} triangles all contain v (by X_ef_mem_inter)
2. X_{e,f} triangles share at least 2 vertices with e = {v, a, b}
3. Since they contain v, they must also contain a or b
4. So X_{e,f} ⊆ {triangles containing {v,a}} ∪ {triangles containing {v,b}}
5. The 2 edges {v,a} and {v,b} cover all of X_{e,f}

For S_e:
6. Either S_e has common edge structure (1 edge suffices), OR
7. S_e has star structure with external vertex x
8. In star case, all S_e triangles contain x, and 2 edges from e's vertices to x suffice

Combined:
9. If S_e uses common edge of e, we need 1 edge for S_e + 2 spoke edges for X_{e,f} = need to optimize
10. Key: spoke edges {v,a}, {v,b} can cover BOTH S_e (if v is involved) AND X_{e,f}
11. If S_e uses base edge {a,b} (avoiding v), we need {a,b} for S_e and {v,a},{v,b} for bridges = 3 edges!
12. BUT: we can choose a cover that uses spokes, not the base
-/

/-- Bridges and S_e together can be covered by 2 edges using spokes from shared vertex -/
lemma tau_S_union_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adj : (e ∩ f).card = 1) :
    triangleCoveringNumberOn G (S_e G M e ∪ X_ef G e f) ≤ 2 := by
  -- Get the shared vertex v
  obtain ⟨v, hv⟩ : ∃ v, e ∩ f = {v} := card_eq_one.mp h_adj
  -- Get e's structure: e = {v, a, b}
  have he_card : e.card = 3 := by
    have := hM.1.1 he
    exact (G.mem_cliqueFinset_iff.mp this).2
  have hv_in_e : v ∈ e := by
    have : v ∈ e ∩ f := by rw [hv]; exact mem_singleton_self v
    exact mem_of_mem_inter_left this
  -- Extract other vertices of e
  obtain ⟨a, b, c, hab, hac, hbc, he_eq⟩ := card_eq_three.mp he_card
  -- Identify which vertex is v
  rw [he_eq] at hv_in_e
  simp only [mem_insert, mem_singleton] at hv_in_e
  -- The 2-edge cover uses spokes from v
  -- Need to show: {v,x}, {v,y} where x,y are the other two vertices of e
  -- covers both S_e and X_{e,f}
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: 8-edge cover for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

/-
For PATH_4 A-v₁-B-v₂-C-v₃-D:
- τ(S_A ∪ X_{A,B}) ≤ 2 (endpoint A, bridges only to B)
- τ(S_B ∪ X_{B,C}) ≤ 2 (B's non-A bridges; X_{A,B} covered by A's cover)
- τ(S_C ∪ X_{B,C}) ≤ 2 (C's non-D bridges; overlaps with B on X_{B,C})
- τ(S_D ∪ X_{C,D}) ≤ 2 (endpoint D, bridges only to C)

But wait - we're double-counting X_{B,C}! We need a more careful analysis.

Actually, the correct partition is:
- E_A: 2 edges covering S_A ∪ X_{A,B}
- E_B: 2 edges covering S_B (X_{A,B} already covered, X_{B,C} might be partially covered)
- E_C: 2 edges covering S_C (X_{B,C} and X_{C,D} might be partially covered)
- E_D: 2 edges covering S_D ∪ X_{C,D}

We need to show E_A ∪ E_B ∪ E_C ∪ E_D covers ALL triangles.
-/

/-- For endpoint A, S_A and its bridges to B can be covered by 2 edges -/
lemma tau_endpoint_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (S_e G M A ∪ X_ef G A B) ≤ 2 := by
  have hA : A ∈ M := by rw [hpath.1]; simp
  have hB : B ∈ M := by rw [hpath.1]; simp
  have hAB : A ≠ B := hpath.2.1
  -- isPath4 structure: (A ∩ B).card = 1 is at position 2.2.2.2.2.2.2.1
  have h_adj : (A ∩ B).card = 1 := by
    unfold isPath4 at hpath
    exact hpath.2.2.2.2.2.2.2.1
  exact tau_S_union_X_le_2 G M hM A B hA hB hAB h_adj

/-- All triangles in PATH_4 are covered by S_A ∪ S_B ∪ S_C ∪ S_D ∪ bridges -/
lemma path4_triangle_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    G.cliqueFinset 3 = S_e G M A ∪ S_e G M B ∪ S_e G M C ∪ S_e G M D ∪
                        X_ef G A B ∪ X_ef G B C ∪ X_ef G C D := by
  sorry -- This should follow from maximality: every triangle shares edge with some M-element

/-- Main theorem: τ ≤ 8 for PATH_4 using bridge absorption -/
theorem tau_le_8_path4_bridge_absorption (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Decompose triangles
  -- Use τ(S_A ∪ X_{A,B}) ≤ 2, τ(S_B) ≤ 2, τ(S_C) ≤ 2, τ(S_D ∪ X_{C,D}) ≤ 2
  -- Key: X_{B,C} is covered by either B's or C's edges through shared vertex v₂
  sorry

end
