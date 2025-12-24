/-
Tuza ν=4 Strategy - Slot 42: Local Reduction Lemma (CORRECTED)

KEY INSIGHT (from Gemini consultation):
Don't prove τ(G) ≤ 8 globally. Just prove we can always make a "good move".

CORRECTED STATEMENT (after AI review):
The original τ(T_e) ≤ 2 target was TOO STRONG. The correct bounds are:

(A) For ISOLATED elements (no sharing): τ(T_e) = τ(S_e) ≤ 2
(B) For LEAF elements: τ(T_e) ≤ τ(S_e) + τ(X) ≤ 2 + 2 = 4
(C) For any pair: τ(T_pair) ≤ τ(T_e) + τ(T_f) ≤ 8 (loose)

THE KEY: We need cost per element ≤ 2 for the induction to work.

SHARING GRAPH CASE ANALYSIS:
- Empty K̄₄: All isolated → 4 × τ(S_e) ≤ 4 × 2 = 8 ✓
- Path P₄: 2 leaves → leaf has τ(T_e) ≤ 4, remove → ν=3 → τ ≤ 4+6=10 (TOO LOOSE!)
- Star K₁,₃: 3 leaves → same issue
- Cycle C₄: No leaves → need pair analysis
- K₄-e, K₄: Dense → need pair analysis

THE REAL STRATEGY:
Prove that for SOME choice of reduction, cost per element ≤ 2.
This requires sharing graph case analysis.

SCAFFOLDING: Full proofs from slots 6, 16, 24
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

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

def sharingDegree (M : Finset (Finset V)) (e : Finset V) : ℕ :=
  (M.filter (fun f => f ≠ e ∧ sharesVertex e f)).card

def isIsolated (M : Finset (Finset V)) (e : Finset V) : Prop :=
  e ∈ M ∧ sharingDegree M e = 0

def isLeaf (M : Finset (Finset V)) (e : Finset V) : Prop :=
  e ∈ M ∧ sharingDegree M e = 1

-- Sharing graph types for ν=4
def hasIsolatedElement (M : Finset (Finset V)) : Prop :=
  ∃ e ∈ M, isIsolated M e

def hasLeaf (M : Finset (Finset V)) : Prop :=
  ∃ e ∈ M, isLeaf M e

def allDegreeAtLeast2 (M : Finset (Finset V)) : Prop :=
  ∀ e ∈ M, sharingDegree M e ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: tau_union_le_sum (from slot16, uuid b4f73fa3)
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

lemma union_covers_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (XA XB : Finset (Sym2 V))
    (hA : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2)
    (hB : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2) :
    ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htA | htB
  · obtain ⟨e, heXA, het⟩ := hA t htA
    exact ⟨e, Finset.mem_union_left XB heXA, het⟩
  · obtain ⟨e, heXB, het⟩ := hB t htB
    exact ⟨e, Finset.mem_union_right XA heXB, het⟩

-- PROVEN in slot16 (uuid b4f73fa3) - full proof works in Aristotle's Mathlib version
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  let coversAB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2)
  let coversA := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)
  let coversB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2)
  let sizesAB := coversAB.image Finset.card
  let sizesA := coversA.image Finset.card
  let sizesB := coversB.image Finset.card
  by_cases hAB : sizesAB.Nonempty
  case pos =>
    have coversAB_sub_coversA : coversAB ⊆ coversA := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_left G A B E' hE'.2⟩
    have coversAB_sub_coversB : coversAB ⊆ coversB := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_right G A B E' hE'.2⟩
    have hA : sizesA.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversA)
    have hB : sizesB.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversB)
    have h_tauAB : triangleCoveringNumberOn G (A ∪ B) = sizesAB.min' hAB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauA : triangleCoveringNumberOn G A = sizesA.min' hA := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauB : triangleCoveringNumberOn G B = sizesB.min' hB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have minA_mem : sizesA.min' hA ∈ sizesA := Finset.min'_mem sizesA hA
    have minB_mem : sizesB.min' hB ∈ sizesB := Finset.min'_mem sizesB hB
    obtain ⟨XA, hXA_mem, hXA_card⟩ := Finset.mem_image.mp minA_mem
    obtain ⟨XB, hXB_mem, hXB_card⟩ := Finset.mem_image.mp minB_mem
    have hXA_sub : XA ⊆ G.edgeFinset := (Finset.mem_filter.mp hXA_mem).1 |> Finset.mem_powerset.mp
    have hXA_covers : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2 := (Finset.mem_filter.mp hXA_mem).2
    have hXB_sub : XB ⊆ G.edgeFinset := (Finset.mem_filter.mp hXB_mem).1 |> Finset.mem_powerset.mp
    have hXB_covers : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2 := (Finset.mem_filter.mp hXB_mem).2
    have hUnion_covers : ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 :=
      union_covers_union G A B XA XB hXA_covers hXB_covers
    have hUnion_sub : XA ∪ XB ⊆ G.edgeFinset := Finset.union_subset hXA_sub hXB_sub
    have hUnion_mem : XA ∪ XB ∈ coversAB := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hUnion_sub, hUnion_covers⟩
    have card_union_mem : (XA ∪ XB).card ∈ sizesAB :=
      Finset.mem_image_of_mem Finset.card hUnion_mem
    have min_le_card : sizesAB.min' hAB ≤ (XA ∪ XB).card :=
      Finset.min'_le sizesAB (XA ∪ XB).card card_union_mem
    have card_union_le : (XA ∪ XB).card ≤ XA.card + XB.card := Finset.card_union_le XA XB
    calc triangleCoveringNumberOn G (A ∪ B)
        = sizesAB.min' hAB := h_tauAB
      _ ≤ (XA ∪ XB).card := min_le_card
      _ ≤ XA.card + XB.card := card_union_le
      _ = sizesA.min' hA + sizesB.min' hB := by rw [hXA_card, hXB_card]
      _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [← h_tauA, ← h_tauB]
  case neg =>
    have h_empty : sizesAB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAB
    have h_tau_zero : triangleCoveringNumberOn G (A ∪ B) = 0 := by
      simp only [triangleCoveringNumberOn]
      rw [h_empty]
      simp
    rw [h_tau_zero]
    exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: Te_eq_Se_union_bridges (from slot6)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING: tau_S_le_2 and tau_X_le_2 (from slots 6 and 24)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- SCAFFOLDING: Full proof in slot6_Se_lemmas.lean

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- SCAFFOLDING: Full proof in slot24_tau_X_le_2.lean

-- AXIOM: Parker's ν≤3 result (proven in literature, imported for induction)
axiom parker_nu3 : ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
  trianglePackingNumber G ≤ 3 → triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 6

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN TARGETS (CORRECTED BOUNDS)
-- ══════════════════════════════════════════════════════════════════════════════

/--
CASE 1: Isolated element reduction - τ(T_e) = τ(S_e) ≤ 2

When e shares NO vertices with other packing elements, bridges(e) = ∅.
So T_e = S_e and τ(T_e) ≤ 2.
-/
lemma isolated_element_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) (h_isolated : isIsolated M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry -- TARGET: Use bridges = ∅ when isolated

/--
CASE 2: Leaf element bound - τ(T_e) ≤ 4

When e is a leaf (shares with exactly 1 other element f):
- T_e = S_e ∪ X(e,f)
- τ(T_e) ≤ τ(S_e) + τ(X(e,f)) ≤ 2 + 2 = 4

NOTE: This is NOT enough for cost ≤ 2 per element!
We need better analysis of the leaf case.
-/
lemma leaf_element_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) (h_leaf : isLeaf M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 4 := by
  sorry -- TARGET: Use Te = Se ∪ X(e,f) for single neighbor f

/--
CASE 3: Leaf with shared vertex overlap - τ(T_e) ≤ 3

STRONGER CLAIM: When e is a leaf sharing vertex v with f:
- All bridges in X(e,f) contain v
- S_e can share the edge cover with bridges through v
- Total: τ(T_e) ≤ 3

This gives cost 3 for 1 element, so 3 + 5 = 8 for ν=4 → ν=3.
-/
lemma leaf_shared_vertex_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) (h_leaf : isLeaf M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 3 := by
  sorry -- TARGET: Exploit shared vertex structure

/--
CASE 4: Adjacent pair in dense sharing graph - τ(T_pair) ≤ 6

For adjacent pairs (e,f) that share a vertex v:
- T_e ∪ T_f includes triangles on ≤6 vertices (e∪f has 5 vertices)
- Bridges X(e,f) all contain v
- τ(T_pair) ≤ τ(S_e) + τ(S_f) + τ(X(e,f)) ≤ 2 + 2 + 2 = 6
-/
lemma adjacent_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_share : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 6 := by
  sorry -- TARGET: Use union bound with scaffolding

/--
CASE 5: Pair covers remaining after removing pair - Cost analysis

If we remove pair (e,f), we reduce to ν ≤ 2.
τ(ν ≤ 2) ≤ 4 (trivial or by same techniques)
So τ(G) ≤ τ(T_pair) + 4

For adjacent pair: τ(G) ≤ 6 + 4 = 10 (NOT TIGHT ENOUGH!)
Need: τ(T_pair) ≤ 4 for dense cases.
-/
lemma pair_reduction_cost (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_pair_bound : triangleCoveringNumberOn G (T_pair G e f) ≤ 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  sorry -- TARGET: Use pair bound + ν≤2 result

/--
MAIN THEOREM: Sharing graph case split

By exhaustive case analysis on sharing graph type:

1. Has isolated element → τ(T_e) ≤ 2, reduce to ν=3 → τ ≤ 2 + 6 = 8
2. Has leaf → τ(T_e) ≤ 3, reduce to ν=3 → τ ≤ 3 + 6 = 9 (need tighter!)
3. All degree ≥ 2 (C₄, K₄-e, K₄) → pair analysis needed

For case 3, we need slot41 (C₄) or slot43 (adjacent pair dense).
-/
theorem tuza_nu4_by_sharing_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  sorry -- MAIN TARGET: Case split by sharing graph type

/--
Alternative: Prove good reduction exists for SOME structure

Instead of proving for all graphs, prove existence:
Either isolated/leaf case works OR some pair has τ ≤ 4.
-/
theorem good_reduction_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    (∃ e ∈ M, triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2) ∨
    (∃ e ∈ M, triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 3 ∧ isLeaf M e) ∨
    (∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ triangleCoveringNumberOn G (T_pair G e f) ≤ 4) := by
  sorry -- MAIN TARGET: Disjunction covers all cases

end
