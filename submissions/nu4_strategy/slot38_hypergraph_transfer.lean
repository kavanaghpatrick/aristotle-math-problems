/-
Tuza ν=4 Strategy - Slot 38: Hypergraph Transfer Attack (CORRECTED)

NOVEL APPROACH (from Codex consultation):
Reinterpret the triangle problem in hypergraph terms.

CORRECTED AFTER AI REVIEW:

KEY ISSUES IDENTIFIED:
1. τ(allBridges) ≤ 4 was FALSE - per-pair bounds give ≤12, not ≤4
2. Double-counting in bridge union - each bridge belongs to exactly one X(eᵢ,eⱼ)
3. No actual hypergraph lemma was imported

CORRECTED BOUNDS:
- 6 pairs × τ(X) ≤ 2 = 12 edges for ALL bridges (worst case, no overlap)
- But bridges OVERLAP through shared vertices, so actual bound is better
- Key: Bridges X(eᵢ,eⱼ) all contain shared vertex vᵢⱼ

HYPERGRAPH VIEW:
For ν=4 packing M = {e₁, e₂, e₃, e₄}:
- Create "bridge hypergraph" H on hypervertices {1,2,3,4}
- Hyperedge {i,j} for each pair that shares a vertex
- Weight = τ(X(eᵢ,eⱼ)) ≤ 2

THE REAL INSIGHT:
In the worst case (complete sharing K₄), we have 6 pairs.
But edges covering bridges can OVERLAP through shared vertices.
Need to prove: actual overlap saves at least 4 edges (12-8=4).

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

-- CORRECTED: All bridges as DISJOINT UNION of X(eᵢ,eⱼ) sets
-- Each bridge belongs to EXACTLY ONE X set (the pair it bridges)
def allBridgesDisjoint (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- All S_e sets unioned
def allS (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  M.biUnion (fun e => S_e G M e)

-- Number of sharing pairs
def numSharingPairs (M : Finset (Finset V)) : ℕ :=
  (M.powerset.filter (fun S => S.card = 2)).filter (fun S =>
    ∃ e f, e ∈ S ∧ f ∈ S ∧ e ≠ f ∧ sharesVertex e f).card

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
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
-- MAIN TARGETS (CORRECTED BOUNDS)
-- ══════════════════════════════════════════════════════════════════════════════

/--
CORRECTED: Naive bridge bound - τ(allBridges) ≤ 12

With 6 pairs and τ(X) ≤ 2 per pair, worst case is 12 edges.
This is provable but NOT tight enough for Tuza.
-/
lemma tau_all_bridges_naive (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (allBridgesDisjoint G M) ≤ 12 := by
  sorry -- TARGET: Sum over 6 pairs × 2 each

/--
CORRECTED: τ(allS) ≤ 8 (not disjoint, but bounded)

The S_e sets can OVERLAP (a triangle in S_e₁ might also be in S_e₂).
But with ν=4, we still get τ(allS) ≤ 4 × 2 = 8 by union bound.
Actually better: S_e sets partition triangles that DON'T bridge.
-/
lemma tau_all_S_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (allS G M) ≤ 8 := by
  sorry -- TARGET: Union of 4 S_e sets, each ≤ 2

/--
KEY INSIGHT: Bridge overlap through shared vertices

When two pairs (e₁,e₂) and (e₂,e₃) both involve e₂:
- X(e₁,e₂) bridges contain v₁₂ (shared vertex of e₁,e₂)
- X(e₂,e₃) bridges contain v₂₃ (shared vertex of e₂,e₃)
- If v₁₂ = v₂₃, edges through this vertex cover BOTH bridge sets

This is where the hypergraph view helps: overlapping hypervertices
share edge covers.
-/
lemma shared_vertex_bridge_overlap (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₂ e₃ : Finset V) (he₁ : e₁ ∈ M) (he₂ : e₂ ∈ M) (he₃ : e₃ ∈ M)
    (h12 : e₁ ≠ e₂) (h23 : e₂ ≠ e₃) (h13 : e₁ ≠ e₃)
    (h_share12 : sharesVertex e₁ e₂) (h_share23 : sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (X_ef G e₁ e₂ ∪ X_ef G e₂ e₃) ≤ 4 := by
  sorry -- TARGET: Show overlap saves edges

/--
TIGHTER BOUND ATTEMPT: τ(allBridges) ≤ 8 for specific sharing graphs

For certain sharing graph structures, bridge covers overlap significantly.
Example: Star K₁,₃ - center shares with all 3 leaves, all bridges through center.
-/
lemma tau_bridges_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center : Finset V) (he : e_center ∈ M)
    (h_star : ∀ f ∈ M, f ≠ e_center → sharesVertex e_center f) :
    triangleCoveringNumberOn G (allBridgesDisjoint G M) ≤ 6 := by
  sorry -- TARGET: Star case - all bridges through center

/--
MAIN THEOREM: Hypergraph transfer gives τ ≤ 8 (REQUIRES TIGHT BRIDGE BOUND)

Strategy:
1. All triangles = allS ∪ allBridges ∪ non-touching
2. Non-touching don't need coverage (they don't share edges with M)
3. τ(allS) ≤ 8 (loose) but overlaps with bridges
4. τ(allBridges) ≤ ? (depends on sharing graph structure)

ISSUE: With naive bounds, τ ≤ 8 + 12 = 20 (way too loose!)
Need: Either overlaps save 12+ edges, or different approach.
-/
theorem tuza_nu4_hypergraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  sorry -- MAIN TARGET: Requires proving tight overlaps

/--
ALTERNATIVE: Direct vertex-based covering

Instead of summing over pairs, pick edges incident to shared vertices.
With ≤6 shared vertices (at most 1 per pair), and 2 edges per vertex:
τ ≤ 12 for bridges (still not tight enough).

But if we count actual vertices used...
-/
lemma vertex_cover_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    ∃ (V_shared : Finset V), V_shared.card ≤ 6 ∧
    ∀ t ∈ allBridgesDisjoint G M, ∃ v ∈ V_shared, v ∈ t := by
  sorry -- TARGET: All bridges hit by ≤6 shared vertices

end
