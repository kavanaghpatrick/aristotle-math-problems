/-
Tuza ν=4 Strategy - Slot 41: Cycle Sharing Graph Attack (CORRECTED)

THE HARDEST CASE (all three AIs agree):
C₄ is the "Goldilocks zone" - enough structure to prevent leaf reduction,
sparse enough to avoid massive overlap savings.

CORRECTED AFTER AI REVIEW:

KEY ISSUES IDENTIFIED:
1. "Diagonal bridges" - triangles connecting non-adjacent pairs (e₁,e₃) and (e₂,e₄)
   MUST be handled explicitly. Negation #8 says opposite pairs CAN share vertices.

2. The partition c4_complementary_pairs was incomplete - missed triangles
   touching 3+ packing elements or diagonal bridges.

3. τ(T_pair) ≤ 4 may be too tight. Start with τ(T_pair) ≤ 6 and tighten.

CORRECTED STRUCTURE:
For C₄ sharing graph e₁-e₂-e₃-e₄-e₁:
- Adjacent pairs: (e₁,e₂), (e₂,e₃), (e₃,e₄), (e₄,e₁) share vertices
- Diagonal pairs: (e₁,e₃), (e₂,e₄) may or may not share vertices (Neg #8)

TRIANGLE CLASSIFICATION relative to C₄:
1. S_eᵢ: Triangles touching only eᵢ (not sharing with others)
2. X(eᵢ,eⱼ) for adjacent pairs: Bridges between adjacent elements
3. X(e₁,e₃) and X(e₂,e₄): DIAGONAL bridges (if they share vertices)
4. Triangles touching 3+ elements: Rare but possible

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

-- C₄ structure: exactly 4 edges forming a cycle, degree 2 for all
def isCycleSharingGraph (M : Finset (Finset V)) (e₁ e₂ e₃ e₄ : Finset V) : Prop :=
  M = {e₁, e₂, e₃, e₄} ∧
  -- Adjacent pairs share vertices
  sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧
  sharesVertex e₃ e₄ ∧ sharesVertex e₄ e₁ ∧
  -- All have degree exactly 2 in sharing graph
  sharingDegree M e₁ = 2 ∧ sharingDegree M e₂ = 2 ∧
  sharingDegree M e₃ = 2 ∧ sharingDegree M e₄ = 2

-- Diagonal pairs: (e₁,e₃) and (e₂,e₄) - may or may not share (Negation #8)
def diagonalPair (e₁ e₂ e₃ e₄ eᵢ eⱼ : Finset V) : Prop :=
  (eᵢ = e₁ ∧ eⱼ = e₃) ∨ (eᵢ = e₂ ∧ eⱼ = e₄) ∨
  (eᵢ = e₃ ∧ eⱼ = e₁) ∨ (eᵢ = e₄ ∧ eⱼ = e₂)

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

-- PROVEN in slot16 (uuid b4f73fa3)
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
-- PROVEN SCAFFOLDING from slots 6 and 24
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

-- PROVEN: All bridges X(e,f) contain the shared vertex
lemma mem_X_implies_shared_vertex_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ v ∈ e ∩ f, v ∈ t := by
  sorry -- SCAFFOLDING: Full proof in slot24_tau_X_le_2.lean

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN TARGETS: C₄ Sharing Graph Specific Lemmas (CORRECTED)
-- ══════════════════════════════════════════════════════════════════════════════

/--
DIAGONAL BRIDGE HANDLING (KEY FIX)

In a C₄, diagonal pairs (e₁,e₃) and (e₂,e₄) may share vertices per Negation #8.
If they do, there are diagonal bridges X(e₁,e₃) and X(e₂,e₄).

Key insight: If diagonal pairs DON'T share, X(diagonal) = ∅.
If they DO share, τ(X(diagonal)) ≤ 2 by tau_X_le_2.
-/
lemma diagonal_bridges_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₃ : Finset V) (he₁ : e₁ ∈ M) (he₃ : e₃ ∈ M) (h_ne : e₁ ≠ e₃) :
    triangleCoveringNumberOn G (X_ef G e₁ e₃) ≤ 2 := by
  sorry -- TARGET: Same as tau_X_le_2

/--
COMPLETE TRIANGLE PARTITION for C₄

All triangles in G partition into:
1. Non-touching triangles (don't share edge with any packing element)
2. S_eᵢ for each i (touch only eᵢ)
3. X(eᵢ, eⱼ) for adjacent pairs (touch two adjacent elements)
4. X(e₁, e₃), X(e₂, e₄) for diagonal pairs (may be empty)
5. Triangles touching 3+ elements (rare, constrained)
-/
lemma c4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_cycle : isCycleSharingGraph M e₁ e₂ e₃ e₄) :
    G.cliqueFinset 3 =
      (G.cliqueFinset 3).filter (fun t => ∀ e ∈ M, (t ∩ e).card ≤ 1) ∪  -- non-touching
      S_e G M e₁ ∪ S_e G M e₂ ∪ S_e G M e₃ ∪ S_e G M e₄ ∪              -- pure S sets
      X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄ ∪ X_ef G e₄ e₁ ∪      -- adjacent bridges
      X_ef G e₁ e₃ ∪ X_ef G e₂ e₄ := by                                 -- diagonal bridges
  sorry -- TARGET: Partition lemma

/--
Adjacent pair bound - CORRECTED to τ ≤ 6

For adjacent pair (e,f) in C₄:
τ(T_pair(e,f)) ≤ τ(S_e) + τ(S_f) + τ(X(e,f)) ≤ 2 + 2 + 2 = 6

This is looser than original ≤4 but provable.
-/
lemma c4_adjacent_pair_bound_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adjacent : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 6 := by
  sorry -- TARGET: Union bound with scaffolding

/--
TIGHT BOUND ATTEMPT: τ(T_pair) ≤ 4 for adjacent pairs

This requires showing edges can be SHARED between S_e and X(e,f).
Key insight: X(e,f) bridges all contain shared vertex v.
If cover of S_e uses edges through v, they may also hit bridges.
-/
lemma c4_adjacent_pair_bound_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adjacent : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry -- TARGET: Tight bound using shared vertex

/--
MAIN THEOREM: C₄ sharing graph → τ ≤ 8

STRATEGY: Use two complementary adjacent pairs
- Cover T_pair(e₁,e₂) with ≤4 edges (if tight bound holds) or ≤6
- Cover T_pair(e₃,e₄) with ≤4 edges (if tight bound holds) or ≤6
- Non-touching triangles don't need covering (they don't share packing edges)
- Diagonal bridges: Either covered by above OR add ≤2 each

CASE ANALYSIS:
1. If tight ≤4 works: τ ≤ 4 + 4 = 8 ✓
2. If only ≤6 works: τ ≤ 6 + 6 = 12 (TOO LOOSE!)
   Need: shared edges between pairs reduce total
-/
theorem tuza_nu4_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_cycle : isCycleSharingGraph M e₁ e₂ e₃ e₄) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  sorry -- MAIN TARGET

/--
Alternative: All degree-2 sharing graphs have τ ≤ 8

This covers C₄ case and is more general.
Note: In ν=4, degree-2 for all means exactly C₄ structure.
-/
theorem tuza_nu4_degree2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_all_deg2 : ∀ e ∈ M, sharingDegree M e = 2) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  sorry -- ALTERNATIVE TARGET

end
