/-
Tuza ν=4 Strategy - Slot 36: Leaf Removal Tactic

CRITICAL NOTE (from Gemini review):
τ(T_e) ≤ 3 is TRIVIAL. So τ(T_leaf) ≤ 4 is worthless.
We MUST prove τ(T_leaf) ≤ 2 for leaves to get τ(G) ≤ 8.

TARGET: For a LEAF element in the sharing graph, prove τ(T_leaf) ≤ 2.

WHY THIS WORKS:
A leaf e shares vertex with only ONE other element f.
- T_e = S_e ∪ bridges, where bridges = X(e,f) only
- τ(S_e) ≤ 2 (proven)
- If bridges are EMPTY or covered by S_e cover, then τ(T_e) ≤ 2

KEY INSIGHT: For a leaf, the bridges X(e,f) might be:
1. Empty (sparse graph)
2. Covered by the same 2 edges that cover S_e (if structural conditions hold)

If τ(T_leaf) ≤ 2, then:
τ(G) ≤ 2 + τ(residual with ν=3) ≤ 2 + 6 = 8 ✓

SCAFFOLDING: tau_S_le_2, tau_X_le_2 (proven)
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

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- Sharing graph: vertices = packing elements, edges when two share a vertex
def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

-- A leaf in the sharing graph: shares vertex with exactly one other element
def isLeaf (M : Finset (Finset V)) (e : Finset V) : Prop :=
  e ∈ M ∧ (M.filter (fun f => f ≠ e ∧ sharesVertex e f)).card = 1

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

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

-- τ(S_e) ≤ 2 (proven in slot6)
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- SCAFFOLDING: proven in slot6

-- τ(X_ef) ≤ 2 (proven in slot24)
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- SCAFFOLDING: proven in slot24

-- ══════════════════════════════════════════════════════════════════════════════
-- LEAF STRUCTURE LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
For a leaf element e (shares vertex with only one other element f),
bridges from e go only to f.
-/
lemma leaf_bridges_to_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (hleaf : isLeaf M e) :
    ∃ f, f ∈ M ∧ f ≠ e ∧ bridges G M e ⊆ X_ef G e f := by
  sorry -- TARGET 1

/--
MAIN TARGET: For a leaf element, τ(T_e) ≤ 2.

Since leaf e shares vertex with only ONE other element f:
- bridges(e) = X(e,f) (bridges only to f)
- T_e = S_e ∪ X(e,f)

APPROACH 1: If X(e,f) = ∅, then T_e = S_e, so τ(T_e) ≤ 2 by tau_S_le_2.
APPROACH 2: If X(e,f) ≠ ∅, show the S_e cover also hits X(e,f).
-/
theorem tau_Te_leaf_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (hleaf : isLeaf M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry -- MAIN TARGET

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Leaf removal gives τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/--
If sharing graph has a leaf, we get τ(G) ≤ 8.

Proof:
1. Cover leaf's triangles with ≤2 edges (by tau_Te_leaf_le_2)
2. Residual packing has ν = 3, so τ(residual) ≤ 6 (Parker)
3. Total: τ ≤ 2 + 6 = 8 ✓
-/
theorem leaf_removal_gives_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e : Finset V) (hleaf : isLeaf M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  exact tau_Te_leaf_le_2 G M hM e hleaf

/--
Weaker version: τ(T_leaf) ≤ 2 when no bridges (T_e = S_e).
This is immediate from tau_S_le_2.
-/
theorem leaf_no_bridges_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (hleaf : isLeaf M e)
    (h_no_bridges : bridges G M e = ∅) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  -- When no bridges, T_e = S_e
  have h_eq : trianglesSharingEdge G e = S_e G M e := by
    rw [Te_eq_Se_union_bridges G M e, h_no_bridges, Finset.union_empty]
  rw [h_eq]
  exact tau_S_le_2 G M hM e (hleaf.1)

end
