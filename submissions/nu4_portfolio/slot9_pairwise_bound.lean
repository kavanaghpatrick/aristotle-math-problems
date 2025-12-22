/-
Tuza ν=4 Portfolio - Slot 9: τ(T_e ∪ T_f) ≤ 4 (Pairwise Bound)

TARGET: Prove τ(T_e ∪ T_f) ≤ 4 for any pair of packing elements e, f ∈ M

WHY THIS MATTERS:
If τ(T_e ∪ T_f) ≤ 4, then for ν=4:
- Pair up: {e₁,e₂} and {e₃,e₄}
- Cover T_{e₁} ∪ T_{e₂} with ≤ 4 edges
- Cover T_{e₃} ∪ T_{e₄} with ≤ 4 edges
- Total: τ(G) ≤ 8

NOTE: τ(T_e) ≤ 2 is FALSE (flower counterexample), but pairwise bound may still hold
because bridges X(e,f) overlap between T_e and T_f.

PROVEN FACTS:
1. τ(S_e) ≤ 2 for any e ∈ M
2. S_e triangles pairwise share edges
3. Common edge → τ ≤ 1; K4 → τ ≤ 2
4. X(e,f) triangles all contain shared vertex v = e ∩ f (when it exists)

DECOMPOSITION:
T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) ∪ O
where O = other bridges (to packing elements g ∉ {e,f})

KEY INSIGHT:
- τ(S_e) ≤ 2, τ(S_f) ≤ 2
- X(e,f) shares edges with both S_e and S_f covers
- Overlap may reduce total from 4+ to ≤ 4

STRATEGY: Boris Minimal - let Aristotle explore the pairwise structure
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma S_e_pairwise_shareEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    Set.Pairwise (S_e G e M : Set (Finset V)) shareEdge := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean

lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING PAIR STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_intersection_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (e ∩ f).card ≤ 1 :=
  hM.1.2 he hf hef

lemma packing_pair_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (∃ v : V, e ∩ f = {v}) ∨ (e ∩ f = ∅) := by
  have h_card := packing_intersection_le_1 G M hM e f he hf hef
  interval_cases h : (e ∩ f).card
  · right; exact Finset.card_eq_zero.mp h
  · left; exact Finset.card_eq_one.mp h

-- ══════════════════════════════════════════════════════════════════════════════
-- DECOMPOSITION
-- ══════════════════════════════════════════════════════════════════════════════

-- T_e ∪ T_f contains S_e, S_f, and X(e,f) (bridges between e and f)
lemma union_contains_Se_Sf_X (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) :
    S_e G e M ∪ S_e G f M ∪ X_ef G e f ⊆ trianglesSharingEdge G e ∪ trianglesSharingEdge G f := by
  intro t ht
  simp only [Finset.mem_union, S_e, X_ef, trianglesSharingEdge, Finset.mem_filter,
             Finset.mem_inter] at ht ⊢
  rcases ht with ((⟨h1, _⟩ | ⟨h1, _⟩) | ⟨h1, h2⟩)
  · left; exact h1
  · right; exact h1
  · left; exact h1

-- X(e,f) triangles contain shared vertex when e ∩ f = {v}
lemma X_ef_triangles_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (h_inter : e ∩ f = {v})
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3) :
    ∀ t ∈ X_ef G e f, v ∈ t := by
  sorry  -- Proved via: |t ∩ e| ≥ 2, |t ∩ f| ≥ 2, |t| = 3, e ∩ f = {v} forces v ∈ t

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERING NUMBER BOUNDS
-- ══════════════════════════════════════════════════════════════════════════════

-- Monotonicity: S ⊆ T implies τ(S) ≤ τ(T)
lemma tau_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) (hST : S ⊆ T) :
    triangleCoveringNumberOn G S ≤ triangleCoveringNumberOn G T := by
  sorry  -- Cover for T also covers S

-- Subadditivity: τ(S ∪ T) ≤ τ(S) + τ(T)
lemma tau_subadditive (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) :
    triangleCoveringNumberOn G (S ∪ T) ≤ triangleCoveringNumberOn G S + triangleCoveringNumberOn G T := by
  sorry  -- Union of covers is a cover

-- ══════════════════════════════════════════════════════════════════════════════
-- CASE ANALYSIS: SHARED VERTEX vs DISJOINT
-- ══════════════════════════════════════════════════════════════════════════════

-- CASE 1: e ∩ f = {v} (shared vertex)
-- X(e,f) triangles all contain v, so structure is constrained
lemma tau_union_shared_vertex_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

-- CASE 2: e ∩ f = ∅ (disjoint)
-- X(e,f) = ∅, so T_e and T_f are "independent"
lemma tau_union_disjoint_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_disjoint : e ∩ f = ∅) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN TARGETS
-- ══════════════════════════════════════════════════════════════════════════════

-- TARGET 1: τ(T_e ∪ T_f) ≤ 4 for any pair e, f ∈ M
theorem tau_pairwise_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  rcases packing_pair_cases G M hM e f he hf hef with ⟨v, hv⟩ | h_disj
  · exact tau_union_shared_vertex_case G M hM e f he hf hef v hv
  · exact tau_union_disjoint_case G M hM e f he hf hef h_disj

-- TARGET 2: Tuza ν=4 via pairwise descent
theorem tuza_nu4_via_pairwise (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  sorry

end
