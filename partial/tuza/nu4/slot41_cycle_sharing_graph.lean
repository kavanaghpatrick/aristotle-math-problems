/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8cb99e9b-d0ff-43d9-9518-7b370faaefee

The following was proved by Aristotle:

- lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2

- lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2

- lemma mem_X_implies_shared_vertex_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ v ∈ e ∩ f, v ∈ t

- lemma diagonal_bridges_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₃ : Finset V) (he₁ : e₁ ∈ M) (he₃ : e₃ ∈ M) (h_ne : e₁ ≠ e₃) :
    triangleCoveringNumberOn G (X_ef G e₁ e₃) ≤ 2

- lemma c4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_cycle : isCycleSharingGraph M e₁ e₂ e₃ e₄) :
    G.cliqueFinset 3 =
      (G.cliqueFinset 3).filter (fun t => ∀ e ∈ M, (t ∩ e).card ≤ 1) ∪  -- non-touching
      S_e G M e₁ ∪ S_e G M e₂ ∪ S_e G M e₃ ∪ S_e G M e₄ ∪              -- pure S sets
      X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄ ∪ X_ef G e₄ e₁ ∪      -- adjacent bridges
      X_ef G e₁ e₃ ∪ X_ef G e₂ e₄

- lemma c4_adjacent_pair_bound_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adjacent : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 6

- theorem tuza_nu4_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_cycle : isCycleSharingGraph M e₁ e₂ e₃ e₄) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8

- theorem tuza_nu4_degree2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_all_deg2 : ∀ e ∈ M, sharingDegree M e = 2) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8
-/

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

noncomputable section AristotleLemmas

/-
It is impossible to have two edge-disjoint triangles in S_e (because we could replace e with them to get a larger packing).
-/
lemma S_e_disjoint_pair_impossible (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (h1 : t1 ∈ S_e G M e) (h2 : t2 ∈ S_e G M e)
    (h_disj : (t1 ∩ t2).card ≤ 1) (h_neq : t1 ≠ t2) :
    False := by
      -- Consider M' = (M \ {e}) ∪ {t1, t2}.
      set M' : Finset (Finset V) := (M \ {e}) ∪ {t1, t2};
      -- We claim M' is a triangle packing.
      have hM'_packing : isTrianglePacking G M' := by
        -- We need to show that M' is a subset of the cliqueFinset of G and that any two distinct elements in M' have an intersection of at most one element.
        apply And.intro;
        · -- Since $M$ is a triangle packing, all elements of $M$ are in the cliqueFinset.
          have hM_subset : M ⊆ G.cliqueFinset 3 := by
            exact hM.1.1;
          have hS_e_subset : ∀ t ∈ S_e G M e, t ∈ G.cliqueFinset 3 := by
            exact fun t ht => Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.union_subset ( Finset.Subset.trans ( Finset.sdiff_subset ) hM_subset ) ( Finset.insert_subset_iff.mpr ⟨ hS_e_subset t1 h1, Finset.singleton_subset_iff.mpr ( hS_e_subset t2 h2 ) ⟩ );
        · intro x hx y hy hxy;
          norm_num +zetaDelta at *;
          rcases hx with ( rfl | rfl | ⟨ hx, hxe ⟩ ) <;> rcases hy with ( rfl | rfl | ⟨ hy, hye ⟩ ) <;> simp_all +decide [ S_e ];
          · rwa [ Finset.inter_comm ];
          · exact h1.2 x hx hxe |> le_trans ( by rw [ Finset.inter_comm ] );
          · have := h2.2 x hx hxe; have := h1.2 x hx hxe; simp_all +decide [ Finset.inter_comm ] ;
          · have := hM.1.2;
            exact this hx hy hxy;
      -- The size of M' is |M| - 1 + 2 = |M| + 1.
      have hM'_size : M'.card = M.card + 1 := by
        -- Since $t1$ and $t2$ are not in $M \setminus \{e\}$, they are new elements added to $M'$.
        have h_not_in_M_minus_e : t1 ∉ M \ {e} ∧ t2 ∉ M \ {e} := by
          constructor <;> intro h <;> simp_all +decide [ S_e ];
          · have := h1.2 t1 h.1 h.2; simp_all +decide [ trianglesSharingEdge ] ;
            exact this.not_lt ( by rw [ G.isNClique_iff ] at h1; aesop );
          · have := h2.2 t2 h.1 h.2; simp_all +decide [ trianglesSharingEdge ] ;
            exact this.not_lt ( by rw [ h2.1.1.card_eq ] ; decide );
        grind;
      -- Since $M'$ is a triangle packing and $|M'| > |M|$, this contradicts the assumption that $M$ is a maximum packing.
      have h_contradiction : M'.card > trianglePackingNumber G := by
        cases hM ; aesop;
      contrapose! h_contradiction;
      have hM'_card : M'.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        unfold isTrianglePacking at *; aesop;
      have h_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
        intro x hx;
        have := Finset.le_max hx;
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
      exact h_max _ hM'_card

/-
If three triangles pairwise intersect in at least 2 vertices, and the third doesn't contain the intersection of the first two, they form a K4 subset.
-/
lemma intersecting_triangles_structure_step (t1 t2 t3 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3)
    (h12 : (t1 ∩ t2).card = 2)
    (h13 : (t1 ∩ t3).card ≥ 2)
    (h23 : (t2 ∩ t3).card ≥ 2)
    (h_not_subset : ¬ (t1 ∩ t2 ⊆ t3)) :
    (t1 ∪ t2 ∪ t3).card = 4 ∧ t3 ⊆ t1 ∪ t2 := by
      -- Since $|t1 \cap t2| = 2$, we can write $t1 \cap t2 = \{u, v\}$ for some vertices $u$ and $v$.
      obtain ⟨u, v, huv⟩ : ∃ u v : V, t1 ∩ t2 = {u, v} ∧ u ≠ v := by
        rw [ Finset.card_eq_two ] at h12; tauto;
      -- Since $t1 \cap t2 = \{u, v\}$, we have $t1 = \{u, v, x\}$ and $t2 = \{u, v, y\}$ for some vertices $x$ and $y$.
      obtain ⟨x, hx⟩ : ∃ x : V, t1 = {u, v, x} ∧ x ∉ t2 := by
        rw [ Finset.card_eq_three ] at h1;
        simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
        grind
      obtain ⟨y, hy⟩ : ∃ y : V, t2 = {u, v, y} ∧ y ∉ t1 := by
        have h_card_t2 : t2 = {u, v} ∪ (t2 \ {u, v}) := by
          grind;
        -- Since $t2 \ {u, v}$ has cardinality 1, there exists a unique $y$ such that $t2 \ {u, v} = {y}$.
        obtain ⟨y, hy⟩ : ∃ y : V, t2 \ {u, v} = {y} := by
          have h_card_t2_minus : (t2 \ {u, v}).card = 1 := by
            grind;
          exact Finset.card_eq_one.mp h_card_t2_minus;
        refine' ⟨ y, _, _ ⟩ <;> simp_all +singlePass [ Finset.ext_iff ];
        · tauto;
        · specialize huv y; specialize hy y; aesop;
      by_cases hu : u ∈ t3 <;> by_cases hv : v ∈ t3 <;> simp_all +decide [ Finset.subset_iff ];
      · grind;
      · by_cases hv : x ∈ t3 <;> by_cases hw : y ∈ t3 <;> simp_all +decide [ Finset.inter_comm ];
        rw [ Finset.card_eq_three ] at h3 ; aesop;
      · by_cases hy : y ∈ t3 <;> by_cases hx : x ∈ t3 <;> simp_all +decide [ Finset.inter_singleton ];
        intro z hz; have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hx ( Finset.insert_subset hy ( Finset.singleton_subset_iff.mpr hv ) ) ) ; aesop;
      · grind

/-
The intersection of any 3 distinct triangles in a K4 (set of 4 vertices) has size at most 1.
-/
lemma K4_subset_intersection_property (A : Finset V) (hA : A.card = 4)
    (t1 t2 t3 : Finset V)
    (h_sub : t1 ⊆ A ∧ t2 ⊆ A ∧ t3 ⊆ A)
    (h_card : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3)
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3) :
    (t1 ∩ t2 ∩ t3).card ≤ 1 := by
      -- Since $t1$, $t2$, and $t3$ are distinct triangles in $A$, each has exactly 3 elements.
      have h_t1 : ∃ x1, t1 = A \ {x1} := by
        have h_t1 : t1 = A \ (A \ t1) := by
          rw [ Finset.sdiff_sdiff_eq_self h_sub.1 ];
        have h_t1_card : (A \ t1).card = 1 := by
          grind;
        obtain ⟨ x1, hx1 ⟩ := Finset.card_eq_one.mp h_t1_card; use x1; simpa [ hx1 ] using h_t1;
      obtain ⟨x1, hx1⟩ := h_t1
      have h_t2 : ∃ x2, t2 = A \ {x2} := by
        have h_t2 : ∃ x2, t2 = A \ {x2} := by
          have h_t2_card : (A \ t2).card = 1 := by
            grind
          obtain ⟨ x2, hx2 ⟩ := Finset.card_eq_one.mp h_t2_card; use x2; ext y; simp +decide [ hx2.symm ] ; aesop;
        exact h_t2
      obtain ⟨x2, hx2⟩ := h_t2
      have h_t3 : ∃ x3, t3 = A \ {x3} := by
        have hA_card : (A \ t3).card = 1 := by
          grind;
        obtain ⟨ x3, hx3 ⟩ := Finset.card_eq_one.mp hA_card;
        exact ⟨ x3, by rw [ ← hx3, Finset.sdiff_sdiff_eq_self h_sub.2.2 ] ⟩
      obtain ⟨x3, hx3⟩ := h_t3;
      by_cases hx1x2 : x1 = x2 <;> by_cases hx1x3 : x1 = x3 <;> by_cases hx2x3 : x2 = x3 <;> simp_all +decide;
      rw [ show A \ { x1 } ∩ ( A \ { x2 } ∩ ( A \ { x3 } ) ) = A \ { x1, x2, x3 } by ext; aesop ] ; rw [ Finset.card_sdiff ] ; simp +decide [ *, Finset.subset_iff ] ;
      grind

/-
If a triangle $t$ intersects three other triangles (forming a K4 subset) in at least 2 vertices each, then $t$ must be contained in the union of the first two.
-/
lemma intersecting_triangles_K4_closure (t1 t2 t3 t : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3) (ht : t.card = 3)
    (h12 : (t1 ∩ t2).card = 2)
    (h3_sub : t3 ⊆ t1 ∪ t2)
    (h3_not_e : ¬ (t1 ∩ t2 ⊆ t3))
    (ht1 : (t ∩ t1).card ≥ 2)
    (ht2 : (t ∩ t2).card ≥ 2)
    (ht3 : (t ∩ t3).card ≥ 2) :
    t ⊆ t1 ∪ t2 := by
      by_contra h_contra;
      -- Let $z \in t$ such that $z \notin t1 \cup t2$.
      obtain ⟨z, hz⟩ : ∃ z ∈ t, z ∉ t1 ∪ t2 := by
        exact Finset.not_subset.mp h_contra;
      -- Since $|t|=3$, $|t \cap (t1 \cup t2)| = 2$. Let $t \cap (t1 \cup t2) = \{x, y\}$.
      obtain ⟨x, y, hxy⟩ : ∃ x y, x ∈ t ∧ y ∈ t ∧ x ∈ t1 ∪ t2 ∧ y ∈ t1 ∪ t2 ∧ x ≠ y ∧ t = {x, y, z} := by
        have h_inter_card : (t ∩ (t1 ∪ t2)).card = 2 := by
          have h_inter_card : (t ∩ (t1 ∪ t2)).card ≤ 2 := by
            exact Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, by aesop_cat ⟩ ) ) ( by linarith ) );
          refine' le_antisymm h_inter_card ( le_trans ht1 ( Finset.card_mono fun x hx => by aesop ) );
        have h_inter_eq : t ∩ (t1 ∪ t2) = t \ {z} := by
          rw [ Finset.eq_of_subset_of_card_le ( show t ∩ ( t1 ∪ t2 ) ⊆ t \ { z } from fun x hx => by aesop ) ( by rw [ Finset.card_sdiff ] ; aesop ) ];
        simp_all +decide [ Finset.ext_iff ];
        obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp h_inter_card;
        simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
        exact ⟨ x, hxy.2.2.1.1, y, hxy.2.2.2.1, by specialize h_inter_eq x; aesop, by specialize h_inter_eq y; aesop, hxy.1, fun a => ⟨ fun ha => by specialize h_inter_eq a; by_cases ha' : a = z <;> aesop, fun ha => by aesop ⟩ ⟩;
      -- Since $|t \cap t1| \geq 2$, we have $\{x, y\} \subseteq t1$.
      have hxy_t1 : x ∈ t1 ∧ y ∈ t1 := by
        grind;
      -- Since $|t \cap t2| \geq 2$, we have $\{x, y\} \subseteq t2$.
      have hxy_t2 : x ∈ t2 ∧ y ∈ t2 := by
        grind;
      -- Since $|t \cap t3| \geq 2$, we have $\{x, y\} \subseteq t3$.
      have hxy_t3 : x ∈ t3 ∧ y ∈ t3 := by
        grind;
      have hxy_t3_subset : t1 ∩ t2 = {x, y} := by
        rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ Finset.mem_inter.mpr ⟨ hxy_t1.1, hxy_t2.1 ⟩, Finset.singleton_subset_iff.mpr ( Finset.mem_inter.mpr ⟨ hxy_t1.2, hxy_t2.2 ⟩ ) ⟩ ) ] ; aesop;
      simp_all +decide [ Finset.subset_iff ]

/-
A set of triangles that pairwise intersect in at least 2 vertices is either a star (all share an edge) or a subset of K4.
-/
lemma structure_of_intersecting_triangles (S : Finset (Finset V))
    (h_nonempty : S.Nonempty)
    (h_tri : ∀ t ∈ S, t.card = 3)
    (h_inter : ∀ t1 ∈ S, ∀ t2 ∈ S, (t1 ∩ t2).card ≥ 2) :
    (∃ u v : V, u ≠ v ∧ ∀ t ∈ S, {u, v} ⊆ t) ∨
    (∃ A : Finset V, A.card = 4 ∧ ∀ t ∈ S, t ⊆ A) := by
      by_cases hS : S.card = 1;
      · obtain ⟨ t, ht ⟩ := Finset.card_eq_one.mp hS;
        obtain ⟨ u, v, w, h ⟩ := Finset.card_eq_three.mp ( h_tri t ( ht.symm ▸ Finset.mem_singleton_self t ) ) ; use Or.inl ⟨ u, v, by aesop_cat, fun t' ht' => by aesop_cat ⟩ ;
      · -- Let t1, t2 be distinct elements in S.
        obtain ⟨t1, ht1, t2, ht2, h_distinct⟩ : ∃ t1 ∈ S, ∃ t2 ∈ S, t1 ≠ t2 := by
          exact Finset.one_lt_card.1 ( lt_of_le_of_ne ( Finset.card_pos.2 h_nonempty ) ( Ne.symm hS ) );
        -- If $t1 \cap t2$ is not contained in any other triangle in $S$, then $S$ is a subset of $K4$.
        by_cases h_not_subset : ∃ t3 ∈ S, ¬(t1 ∩ t2 ⊆ t3);
        · obtain ⟨t3, ht3, h_not_subset⟩ : ∃ t3 ∈ S, ¬(t1 ∩ t2 ⊆ t3) := h_not_subset
          have h_inter_t3 : (t1 ∩ t2).card = 2 := by
            have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
            interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
            · linarith [ h_inter t1 ht1 t2 ht2 ];
            · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; aesop;
          have h_inter_t1_t3 : (t1 ∩ t3).card ≥ 2 := by
            exact h_inter t1 ht1 t3 ht3
          have h_inter_t2_t3 : (t2 ∩ t3).card ≥ 2 := by
            exact h_inter t2 ht2 t3 ht3
          have h_inter_t3_subset : t3 ⊆ t1 ∪ t2 := by
            have := intersecting_triangles_structure_step t1 t2 t3 ( h_tri t1 ht1 ) ( h_tri t2 ht2 ) ( h_tri t3 ht3 ) h_inter_t3 h_inter_t1_t3 h_inter_t2_t3 h_not_subset; aesop;
          have h_inter_t3_card : (t1 ∪ t2).card = 4 := by
            have := Finset.card_union_add_card_inter t1 t2; simp_all +decide ;
          have h_inter_t3_subset_A : ∀ t ∈ S, t ⊆ t1 ∪ t2 := by
            intro t ht
            have h_inter_t1_t : (t ∩ t1).card ≥ 2 := by
              exact h_inter t ht t1 ht1
            have h_inter_t2_t : (t ∩ t2).card ≥ 2 := by
              exact h_inter t ht t2 ht2
            have h_inter_t3_t : (t ∩ t3).card ≥ 2 := by
              exact h_inter t ht t3 ht3
            exact intersecting_triangles_K4_closure t1 t2 t3 t (h_tri t1 ht1) (h_tri t2 ht2) (h_tri t3 ht3) (h_tri t ht) h_inter_t3 h_inter_t3_subset h_not_subset h_inter_t1_t h_inter_t2_t h_inter_t3_t
          use Or.inr ⟨t1 ∪ t2, by
            exact h_inter_t3_card, by
            assumption⟩;
        · -- Since $t1 \cap t2$ is contained in every triangle in $S$, $S$ is a star.
          left
          obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v ∧ {u, v} ⊆ t1 ∩ t2 := by
            obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.1 ( by linarith [ h_inter t1 ht1 t2 ht2 ] ) ; exact ⟨ u, v, by aesop_cat, by aesop_cat ⟩ ;
          exact ⟨ u, v, huv.1, fun t ht => Finset.Subset.trans huv.2 ( by aesop ) ⟩

/-
Any set of triangles contained in a set of 4 vertices can be covered by at most 2 edges.
-/
lemma covering_number_le_2_of_subset_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (A : Finset V) (hA : A.card = 4)
    (hS : ∀ t ∈ S, t ⊆ A)
    (hS_tri : ∀ t ∈ S, t.card = 3)
    (hS_in_G : S ⊆ G.cliqueFinset 3) :
    triangleCoveringNumberOn G S ≤ 2 := by
      rw [ triangleCoveringNumberOn ];
      -- Let's choose any two edges from the complete graph on A, say {u, v} and {w, x}.
      obtain ⟨u, v, w, x, hu, hv, hw, hx, h_distinct⟩ : ∃ u v w x : V, u ∈ A ∧ v ∈ A ∧ w ∈ A ∧ x ∈ A ∧ u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x := by
        rcases Finset.card_eq_succ.mp hA with ⟨ u, hu ⟩;
        rcases hu with ⟨ t, hut, rfl, ht ⟩ ; rcases Finset.card_eq_three.mp ht with ⟨ v, w, x, hv, hw, hx, h ⟩ ; use u, v, w, x; aesop;
      -- We need to show that the set of edges { (u, v), (w, x) } covers all triangles in S.
      have h_cover : ∀ t ∈ S, ∃ e ∈ ({(Sym2.mk (u, v)), (Sym2.mk (w, x))} : Finset (Sym2 V)), e ∈ t.sym2 := by
        intro t ht
        have h_triangle : t = {u, v, w} ∨ t = {u, v, x} ∨ t = {u, w, x} ∨ t = {v, w, x} := by
          have h_triangle : t ⊆ {u, v, w, x} := by
            have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hu ( Finset.insert_subset hv ( Finset.insert_subset hw ( Finset.singleton_subset_iff.mpr hx ) ) ) ) ; aesop;
          have h_card : t.card = 3 := hS_tri t ht;
          rw [ Finset.card_eq_three ] at h_card; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := h_card; simp_all +decide [ Finset.subset_iff ] ;
          rcases h_triangle with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at ha hb hc ⊢;
        rcases h_triangle with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ *, Finset.mem_sym2_iff ];
      have h_min : ∃ E' ∈ Finset.filter (fun E' => ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset), E'.card ≤ 2 := by
        use {s(u, v), s(w, x)} ∩ G.edgeFinset;
        simp_all +decide [ Finset.subset_iff ];
        refine' ⟨ _, _ ⟩;
        · intro t ht; specialize h_cover t ht; rcases h_cover with ( ⟨ hu, hv ⟩ | ⟨ hw, hx ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          · exact ⟨ s(u, v), ⟨ Or.inl rfl, by have := hS_in_G ht hu hv; aesop ⟩, by aesop ⟩;
          · have := hS_in_G ht hw hx; aesop;
        · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_insert_le _ _ );
      cases' h_min with E' hE';
      have h_min : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2})).min ≤ E'.card := by
        exact Finset.min_le ( Finset.mem_image_of_mem _ hE'.1 );
      norm_num +zetaDelta at *;
      exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE'.2

end AristotleLemmas

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  by_cases hS_nonempty : (S_e G M e).Nonempty;
  · -- Since S_e is non-empty, let S = S_e. We know every t in S has cardinality 3.
    set S := S_e G M e
    have hS_card : ∀ t ∈ S, t.card = 3 := by
      intros t ht
      have ht_clique : t ∈ G.cliqueFinset 3 := by
        exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1;
      norm_num +zetaDelta at *;
      exact ht_clique.card_eq;
    -- We claim that for any distinct $t1, t2 \in S$, $|t1 \cap t2| \geq 2$.
    have hS_inter : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≥ 2 := by
      intros t1 ht1 t2 ht2 hneq
      by_contra h_contra;
      exact S_e_disjoint_pair_impossible G M hM e he t1 t2 ht1 ht2 ( by linarith ) hneq;
    -- By `structure_of_intersecting_triangles`, we have two cases:
    obtain ⟨u, v, huv, hS_subset⟩ | ⟨A, hA_card, hS_subset⟩ := structure_of_intersecting_triangles S hS_nonempty hS_card (by
    intro t1 ht1 t2 ht2; by_cases h : t1 = t2 <;> aesop;);
    · -- Since S is non-empty, pick t in S. {u, v} is a subset of t.
      obtain ⟨t, ht⟩ : ∃ t ∈ S, {u, v} ⊆ t := by
        exact ⟨ hS_nonempty.choose, hS_nonempty.choose_spec, hS_subset _ hS_nonempty.choose_spec ⟩;
      -- Since {u, v} is a subset of t and t is a triangle in G, {u, v} is an edge in G.
      have h_edge : (Sym2.mk (u, v)) ∈ G.edgeFinset := by
        have h_edge : t ∈ G.cliqueFinset 3 := by
          exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht.1 |>.1 ) |>.1;
        simp_all +decide [ SimpleGraph.isClique_iff, Finset.subset_iff ];
        have := h_edge.1; aesop;
      unfold triangleCoveringNumberOn;
      have h_min_le_1 : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2})) ≤ 1 := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ { s(u, v) }, by aesop ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2 } ) ) <;> simp_all +decide;
      interval_cases ( ‹_› : ℕ ) <;> trivial;
    · apply covering_number_le_2_of_subset_K4 G S A hA_card hS_subset hS_card;
      exact fun t ht => Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1;
  · simp_all +decide [ Finset.ext_iff, triangleCoveringNumberOn ];
    rw [ Finset.min_eq_inf_withTop ];
    rw [ Finset.inf_eq_iInf ];
    rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
    rotate_left;
    exact 0;
    · exact fun _ => zero_le _;
    · exact fun w hw => ⟨ 0, by aesop ⟩;
    · decide +revert

-- SCAFFOLDING: Full proof in slot6_Se_lemmas.lean

noncomputable section AristotleLemmas

/-
If two triangles `e` and `f` are disjoint (share no vertices), then the set `X_ef` (triangles sharing ≥2 vertices with both) is empty. This is because any such triangle would need to have at least 2+2=4 vertices, but triangles only have 3.
-/
lemma X_ef_empty_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (h : Disjoint e f) :
    X_ef G e f = ∅ := by
      -- Any triangle `t` in `X_ef G e f` would have to intersect both `e` and `f` in at least two vertices.
      ext t
      simp [X_ef];
      intro ht hte; have := Finset.card_le_card ( Finset.inter_subset_right : t ∩ e ⊆ e ) ; have := Finset.card_le_card ( Finset.inter_subset_right : t ∩ f ⊆ f ) ; simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ] ;
      have h_card : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
        have h_card : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ e ∪ t ∩ f).card := by
          rw [ Finset.card_union_of_disjoint ];
          exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.notMem_empty x <| h ▸ Finset.mem_inter.mpr ⟨ Finset.mem_inter.mp hx₁ |>.2, Finset.mem_inter.mp hx₂ |>.2 ⟩;
        exact h_card.trans ( Finset.card_mono <| Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) );
      have := ht.card_eq; linarith;

/-
If `t` is a triangle sharing at least 2 vertices with `e` and at least 2 vertices with `f`, then `t` must contain the intersection of `e` and `f`. This relies on `e` and `f` being distinct triangles in a packing (so they share at most 1 vertex).
-/
lemma X_ef_inter_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    e ∩ f ⊆ t := by
      unfold X_ef at ht;
      -- Since $e$ and $f$ are distinct triangles in a packing, $(e ∩ f).card ≤ 1$.
      have h_inter_card : (e ∩ f).card ≤ 1 := by
        cases hM ; aesop;
      have h_inter_subset : (t ∩ (e ∩ f)).card ≥ 1 := by
        have h_inter_subset : (t ∩ e).card + (t ∩ f).card = (t ∩ (e ∪ f)).card + (t ∩ (e ∩ f)).card := by
          rw [ ← Finset.card_union_add_card_inter ];
          simp +decide [ Finset.inter_union_distrib_left, Finset.inter_comm, Finset.inter_left_comm, Finset.inter_assoc ];
        have h_inter_subset : (t ∩ (e ∪ f)).card ≤ 3 := by
          simp +zetaDelta at *;
          exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht.1.card_eq.le;
        linarith [ Finset.mem_filter.mp ht ];
      interval_cases _ : Finset.card ( e ∩ f ) <;> simp_all +decide [ Finset.card_eq_one ];
      grind

/-
If `e` and `f` intersect at exactly one vertex `w`, then every triangle `t` in `X_ef` (which shares ≥2 vertices with `e`) must contain an edge incident to `w` that is also in `e`. This is because `t` must contain `w` (by previous lemma) and another vertex `u` from `e`.
-/
lemma X_ef_covered_by_incident (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (w : V) (hw : e ∩ f = {w}) :
    let edges := (e.erase w).image (fun u => Sym2.mk (u, w))
    ∀ t ∈ X_ef G e f, ∃ edge ∈ edges, edge ∈ t.sym2 := by
      intro edges t ht;
      -- Since $t \in X_{ef}$, we have $t \cap e \geq 2$.
      have h_t_inter_e : (t ∩ e).card ≥ 2 := by
        exact Finset.mem_filter.mp ht |>.2.1;
      -- Since $t \cap e \geq 2$, there exists $u \in t \cap e$ such that $u \neq w$.
      obtain ⟨u, hu⟩ : ∃ u ∈ t ∩ e, u ≠ w := by
        exact Finset.exists_mem_ne h_t_inter_e w;
      simp +zetaDelta at *;
      exact ⟨ u, ⟨ hu.2, hu.1.2 ⟩, hu.1.1, by have := X_ef_inter_subset G M hM e f he hf hef t ht; rw [ Finset.eq_singleton_iff_unique_mem ] at hw; aesop ⟩

/-
The number of edges in a triangle `e` incident to a vertex `w` is at most 2. Specifically, we are counting edges of the form `(u, w)` where `u` is in `e \ {w}`. Since `e` has 3 vertices, `e \ {w}` has 2, so there are at most 2 such edges.
-/
lemma card_incident_edges_le_2 (e : Finset V) (w : V) (he : e.card = 3) (hw : w ∈ e) :
    ((e.erase w).image (fun u => Sym2.mk (u, w))).card ≤ 2 := by
      exact Finset.card_image_le.trans ( by simp +decide [ *, Finset.card_erase_of_mem ] )

end AristotleLemmas

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  -- Apply the lemma X_ef_covered_by_incident to conclude the proof.
  have h_covered : ∃ edges : Finset (Sym2 V), edges ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ edge ∈ edges, edge ∈ t.sym2) ∧ edges.card ≤ 2 := by
    by_cases h_disjoint : Disjoint e f;
    · use ∅;
      have h_empty : X_ef G e f = ∅ := by
        exact?;
      aesop;
    · -- Since `e` and `f` are not disjoint, they must share exactly one vertex `w`.
      obtain ⟨w, hw⟩ : ∃ w : V, e ∩ f = {w} := by
        have h_card : (e ∩ f).card ≤ 1 := by
          have := hM.1;
          cases this ; aesop;
        exact Finset.card_eq_one.mp ( le_antisymm h_card ( Finset.card_pos.mpr ( Finset.not_disjoint_iff_nonempty_inter.mp h_disjoint ) ) );
      refine' ⟨ ( e.erase w ).image ( fun u => Sym2.mk ( u, w ) ), _, _, _ ⟩;
      · intro x hx;
        have := hM.1;
        have := this.1 he; simp_all +decide [ Finset.subset_iff ] ;
        rcases this with ⟨ he₁, he₂ ⟩ ; rcases hx with ⟨ u, ⟨ hu₁, hu₂ ⟩, rfl ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        exact he₁ hu₂ ( show w ∈ e from Finset.mem_of_mem_inter_left ( hw.symm ▸ Finset.mem_singleton_self _ ) ) hu₁;
      · have := hM.1;
        exact X_ef_covered_by_incident G M this e f he hf hef w hw;
      · have h_card_e : e.card = 3 := by
          have := hM.1;
          have := this.1;
          have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.2;
        exact le_trans ( Finset.card_image_le ) ( by rw [ Finset.card_erase_of_mem ( Finset.mem_of_mem_inter_left ( hw.symm ▸ Finset.mem_singleton_self _ ) ), h_card_e ] );
  obtain ⟨ edges, hedges₁, hedges₂, hedges₃ ⟩ := h_covered;
  refine' le_trans _ hedges₃;
  have h_covered : edges ∈ Finset.filter (fun E' => ∀ t ∈ X_ef G e f, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset) := by
    grind;
  have h_min_le_edges_card : ∀ {s : Finset ℕ}, s.Nonempty → ∀ x ∈ s, x ≥ s.min.getD 0 := by
    intros s hs x hx; exact (by
    have := Finset.min_le hx;
    cases h : Finset.min s <;> aesop);
  exact h_min_le_edges_card ⟨ _, Finset.mem_image_of_mem _ h_covered ⟩ _ ( Finset.mem_image_of_mem _ h_covered )

-- SCAFFOLDING: Full proof in slot24_tau_X_le_2.lean

-- PROVEN: All bridges X(e,f) contain the shared vertex
lemma mem_X_implies_shared_vertex_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ v ∈ e ∩ f, v ∈ t := by
  rw [ X_ef ] at ht;
  norm_num +zetaDelta at *;
  -- Since $t \cap e$ and $t \cap f$ are both subsets of $t$ and have at least two elements, their intersection must be non-empty.
  have h_inter_nonempty : Finset.Nonempty (t ∩ e ∩ t ∩ f) := by
    have h_inter_nonempty : (t ∩ e ∩ t ∩ f).card ≥ (t ∩ e).card + (t ∩ f).card - 3 := by
      have h_inter_nonempty : (t ∩ e ∩ t ∩ f).card ≥ (t ∩ e).card + (t ∩ f).card - (t ∩ e ∪ t ∩ f).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
      exact le_trans ( Nat.sub_le_sub_left ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) |> le_trans <| by simp +decide [ ht.1.card_eq ] ) _ ) h_inter_nonempty;
    exact Finset.card_pos.mp ( lt_of_lt_of_le ( by omega ) h_inter_nonempty );
  exact h_inter_nonempty.imp fun x hx => by aesop;

-- SCAFFOLDING: Full proof in slot24_tau_X_le_2.lean

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
  exact?

-- TARGET: Same as tau_X_le_2

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
  apply Finset.ext
  intro t
  simp [S_e, X_ef];
  constructor;
  · by_cases h₁ : (t ∩ e₁).card ≥ 2 <;> by_cases h₂ : (t ∩ e₂).card ≥ 2 <;> by_cases h₃ : (t ∩ e₃).card ≥ 2 <;> by_cases h₄ : (t ∩ e₄).card ≥ 2 <;> simp +decide [ *, trianglesSharingEdge ];
    all_goals intro ht; simp_all +decide [ isCycleSharingGraph ];
    · exact Or.inr ⟨ fun _ => Nat.le_of_lt_succ h₂, fun _ => Nat.le_of_lt_succ h₃, fun _ => Nat.le_of_lt_succ h₄ ⟩;
    · exact Or.inr ⟨ fun _ => Nat.le_of_lt_succ h₁, fun _ => Nat.le_of_lt_succ h₃, fun _ => Nat.le_of_lt_succ h₄ ⟩;
    · exact Or.inr ⟨ fun _ => Nat.le_of_lt_succ h₁, fun _ => Nat.le_of_lt_succ h₂, fun _ => Nat.le_of_lt_succ h₄ ⟩;
    · exact Or.inr ⟨ fun _ => Nat.le_of_lt_succ h₁, fun _ => Nat.le_of_lt_succ h₂, fun _ => Nat.le_of_lt_succ h₃ ⟩;
    · exact ⟨ Nat.le_of_lt_succ h₁, Nat.le_of_lt_succ h₂, Nat.le_of_lt_succ h₃, Nat.le_of_lt_succ h₄ ⟩;
  · unfold trianglesSharingEdge; aesop;

-- TARGET: Partition lemma

/-
Adjacent pair bound - CORRECTED to τ ≤ 6

For adjacent pair (e,f) in C₄:
τ(T_pair(e,f)) ≤ τ(S_e) + τ(S_f) + τ(X(e,f)) ≤ 2 + 2 + 2 = 6

This is looser than original ≤4 but provable.
-/
noncomputable section AristotleLemmas

/-
The covering number of the set of triangles sharing an edge with a triangle `e` is at most 3.
-/
lemma tau_trianglesSharingEdge_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 3 := by
      obtain ⟨ v₁, v₂, v₃, hv ⟩ : ∃ v₁ v₂ v₃, e = { v₁, v₂, v₃ } ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
        simp_all +decide [ Finset.mem_powersetCard, SimpleGraph.isNClique_iff ];
        rcases Finset.card_eq_three.mp he.2 with ⟨ v₁, v₂, v₃, h₁, h₂, h₃ ⟩ ; use v₁, v₂, v₃ ; aesop;
      -- The set of edges contained in `e` (which is a triangle) has size 3. Any triangle `t` in `trianglesSharingEdge G e` shares at least 2 vertices with `e`, so it contains at least one edge of `e`. Thus, the edges of `e` form a cover of size 3.
      have h_cover : ∀ t ∈ trianglesSharingEdge G e, ∃ e' ∈ ({Sym2.mk (v₁, v₂), Sym2.mk (v₁, v₃), Sym2.mk (v₂, v₃)} : Finset (Sym2 V)), e' ∈ t.sym2 := by
        intro t ht;
        simp_all +decide [ Finset.subset_iff, trianglesSharingEdge ];
        have := Finset.one_lt_card.1 ht.2; aesop;
      unfold triangleCoveringNumberOn;
      have h_cover : ({Sym2.mk (v₁, v₂), Sym2.mk (v₁, v₃), Sym2.mk (v₂, v₃)} : Finset (Sym2 V)) ∈ Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset) := by
        simp_all +decide [ SimpleGraph.isNClique_iff, Set.subset_def ];
      have h_min : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset))) ≤ Finset.card ({Sym2.mk (v₁, v₂), Sym2.mk (v₁, v₃), Sym2.mk (v₂, v₃)} : Finset (Sym2 V)) := by
        exact Finset.min_le ( Finset.mem_image_of_mem _ h_cover );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesSharingEdge G { v₁, v₂, v₃ }, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( G.edgeFinset.powerset ) ) ) <;> aesop

end AristotleLemmas

lemma c4_adjacent_pair_bound_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adjacent : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 6 := by
  -- By definition of `isMaxPacking`, we know that `e ∈ G.cliqueFinset 3` and `f ∈ G.cliqueFinset 3`.
  have he_clique : e ∈ G.cliqueFinset 3 := by
    exact hM.1.1 he
  have hf_clique : f ∈ G.cliqueFinset 3 := by
    exact hM.1.1 hf;
  exact le_trans ( tau_union_le_sum G _ _ ) ( add_le_add ( tau_trianglesSharingEdge_le_3 G e he_clique ) ( tau_trianglesSharingEdge_le_3 G f hf_clique ) )

/- Aristotle failed to find a proof. -/
-- TARGET: Union bound with scaffolding

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
  sorry

-- TARGET: Tight bound using shared vertex

/-
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
noncomputable section AristotleLemmas

/-
The set of all triangles is the union of the sets of triangles sharing an edge with each triangle in a maximum packing.
-/
lemma clique_eq_union_of_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    G.cliqueFinset 3 = M.biUnion (trianglesSharingEdge G) := by
      -- Let t be a triangle in G.cliqueFinset 3.
      -- Since M is a maximal packing, t must share an edge with some m in M.
      have h_maximal : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
        by_contra! h;
        obtain ⟨ t, ht₁, ht₂ ⟩ := h;
        have h_add_t : isTrianglePacking G (M ∪ {t}) := by
          have h_contradiction : M ∪ {t} ⊆ G.cliqueFinset 3 := by
            simp_all +decide [ Finset.subset_iff ];
            have := hM.1;
            exact fun x hx => by have := this.1 hx; aesop;
          refine' ⟨ h_contradiction, _ ⟩;
          intro x hx y hy hxy; by_cases hx' : x = t <;> by_cases hy' : y = t <;> simp_all +decide ;
          · exact Nat.le_of_lt_succ ( ht₂ y hy );
          · simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( ht₂ x hx );
          · have := hM.1.2; aesop;
        have h_add_t_card : (M ∪ {t}).card > M.card := by
          norm_num +zetaDelta at *;
          rw [ Finset.card_insert_of_notMem ] ; aesop;
          intro h; specialize ht₂ t h; simp_all +decide [ Finset.inter_comm ] ;
          exact ht₂.not_le ( by rw [ ht₁.card_eq ] ; decide );
        have h_add_t_card : (M ∪ {t}).card ≤ trianglePackingNumber G := by
          unfold trianglePackingNumber;
          have h_add_t_card : (M ∪ {t}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            simp +zetaDelta at *;
            refine' ⟨ Insert.insert t M, ⟨ _, h_add_t ⟩, rfl ⟩;
            exact h_add_t.1;
          have := Finset.le_max h_add_t_card;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 ).powerset ) ) <;> aesop;
        linarith [ hM.2 ];
      unfold trianglesSharingEdge; ext t; aesop;

/-
There are no triangles in the graph that do not share an edge with any triangle in the maximum packing.
-/
lemma no_isolated_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    (G.cliqueFinset 3).filter (fun t => ∀ e ∈ M, (t ∩ e).card ≤ 1) = ∅ := by
      ext t;
      -- By definition of cliqueFinset, if $t$ is in the cliqueFinset of $G$ with size 3, then $t$ is a triangle in $G$.
      simp [clique_eq_union_of_sharing G M hM];
      exact fun x hx hx' => ⟨ x, hx, Finset.mem_filter.mp hx' |>.2 ⟩

/-
The union of the triangle sets for the two pairs (e1, e2) and (e3, e4) covers all triangles in the graph.
-/
lemma union_of_pairs_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_cycle : isCycleSharingGraph M e₁ e₂ e₃ e₄) :
    G.cliqueFinset 3 = T_pair G e₁ e₂ ∪ T_pair G e₃ e₄ := by
      have h_union : G.cliqueFinset 3 = M.biUnion (trianglesSharingEdge G) := by
        exact?;
      rcases h_cycle with ⟨ rfl, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈ ⟩;
      simp +decide [ h_union, T_pair ]

/-
The covering number of the set of triangles sharing an edge with a given triangle is at most 3.
-/
lemma tau_sharing_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 3 := by
      -- Since $e$ has size 3, any such $t$ must contain an edge of $e$. The set of edges of $e$ (which has size 3) covers all such triangles.
      obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ e = {a, b, c} := by
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        have := Finset.card_eq_three.mp he.2; aesop;
      -- The set of edges of $e$ (which has size 3) covers all such triangles.
      have h_edges : ∀ t ∈ trianglesSharingEdge G e, ∃ e' ∈ ({Sym2.mk (a, b), Sym2.mk (a, c), Sym2.mk (b, c)} : Finset (Sym2 V)), e' ∈ t.sym2 := by
        intro t ht
        have h_inter : (t ∩ e).card ≥ 2 := by
          unfold trianglesSharingEdge at ht; aesop;
        have := Finset.one_lt_card.1 h_inter; aesop;
      unfold triangleCoveringNumberOn;
      have h_edges_card : ({Sym2.mk (a, b), Sym2.mk (a, c), Sym2.mk (b, c)} : Finset (Sym2 V)) ∈ Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset := by
        simp_all +decide [ Finset.subset_iff ];
        exact?;
      have h_min_card : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset)) ≤ Finset.card ({Sym2.mk (a, b), Sym2.mk (a, c), Sym2.mk (b, c)} : Finset (Sym2 V)) := by
        exact Finset.min_le ( Finset.mem_image_of_mem _ h_edges_card );
      simp_all +decide [ Sym2.mk ];
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesSharingEdge G { a, b, c }, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) G.edgeFinset.powerset ) ) <;> aesop

/-
The covering number of the union of triangles sharing an edge with e or f is at most 6.
-/
lemma c4_adjacent_pair_bound_6_proven (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adjacent : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 6 := by
      exact?

/-
For two adjacent triangles in a maximum packing of size 4, the set of triangles sharing an edge with either of them can be covered by at most 4 edges.
-/
lemma c4_adjacent_pair_bound_4_proven (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adjacent : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
      apply c4_adjacent_pair_bound_4 G M hM hM_card e f he hf hef h_adjacent

/-
If the maximum packing has size 3, the triangle covering number is at most 8.
-/
lemma k3_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (h_card : M.card = 3) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
      -- Since $M$ is a maximum packing of size 3, let $M = \{t1, t2, t3\}$.
      obtain ⟨t1, t2, t3, ht1, ht2, ht3, hM_eq⟩ : ∃ t1 t2 t3 : Finset V, t1 ∈ M ∧ t2 ∈ M ∧ t3 ∈ M ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧ M = {t1, t2, t3} := by
        rw [ Finset.card_eq_three ] at h_card; obtain ⟨ t1, t2, t3, ht1, ht2, ht3 ⟩ := h_card; use t1, t2, t3; aesop;
      -- The set of all triangles is the union of `trianglesSharingEdge` for t1, t2, t3.
      have h_union : G.cliqueFinset 3 = trianglesSharingEdge G t1 ∪ trianglesSharingEdge G t2 ∪ S_e G M t3 := by
        have h_union : G.cliqueFinset 3 = trianglesSharingEdge G t1 ∪ trianglesSharingEdge G t2 ∪ trianglesSharingEdge G t3 := by
          have := clique_eq_union_of_sharing G M hM;
          aesop;
        have h_bridges_subset : bridges G M t3 ⊆ trianglesSharingEdge G t1 ∪ trianglesSharingEdge G t2 := by
          simp_all +decide [ Finset.subset_iff ];
          unfold bridges trianglesSharingEdge; aesop;
        have h_bridges_subset : trianglesSharingEdge G t3 ⊆ S_e G M t3 ∪ (trianglesSharingEdge G t1 ∪ trianglesSharingEdge G t2) := by
          intro t ht;
          by_cases h : ∃ f ∈ M, f ≠ t3 ∧ (t ∩ f).card ≥ 2 <;> simp_all +decide [ bridges, S_e ];
          · exact Or.inr ( by simpa using h_bridges_subset ( Finset.mem_filter.mpr ⟨ ht, h ⟩ ) );
          · exact Or.inl ⟨ Nat.le_of_lt_succ h.1, Nat.le_of_lt_succ h.2 ⟩;
        ext t; simp [h_union, h_bridges_subset];
        by_cases ht3 : t ∈ trianglesSharingEdge G t3 <;> simp_all +decide;
        · grind +ring;
        · unfold S_e; aesop;
      -- We decompose `sharing t3` into `S_t3` and `bridges t3`.
      have h_decomp : triangleCoveringNumberOn G (trianglesSharingEdge G t1 ∪ trianglesSharingEdge G t2 ∪ S_e G M t3) ≤ triangleCoveringNumberOn G (trianglesSharingEdge G t1) + triangleCoveringNumberOn G (trianglesSharingEdge G t2) + triangleCoveringNumberOn G (S_e G M t3) := by
        have h_decomp : ∀ (A B C : Finset (Finset V)), triangleCoveringNumberOn G (A ∪ B ∪ C) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B + triangleCoveringNumberOn G C := by
          intros A B C;
          exact le_trans ( tau_union_le_sum _ _ _ ) ( add_le_add ( tau_union_le_sum _ _ _ ) le_rfl );
        exact h_decomp _ _ _;
      -- We know that `tau(sharing t1) <= 3`, `tau(sharing t2) <= 3`, and `tau(S_t3) <= 2`.
      have h_bounds : triangleCoveringNumberOn G (trianglesSharingEdge G t1) ≤ 3 ∧ triangleCoveringNumberOn G (trianglesSharingEdge G t2) ≤ 3 ∧ triangleCoveringNumberOn G (S_e G M t3) ≤ 2 := by
        refine' ⟨ tau_sharing_le_3 G t1 _, tau_sharing_le_3 G t2 _, tau_S_le_2 G M hM t3 ht3 ⟩;
        · have := hM.1;
          exact this.1 ht1;
        · have := hM.1;
          exact this.1 ht2;
      grind

/-
The covering number of the union of triangles sharing an edge with e or f is at most 4.
-/
lemma c4_adjacent_pair_bound_4_valid (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_adjacent : sharesVertex e f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
      exact?

end AristotleLemmas

theorem tuza_nu4_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_cycle : isCycleSharingGraph M e₁ e₂ e₃ e₄) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  by_cases hM_card : M.card = 4;
  · have h_union : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ triangleCoveringNumberOn G (T_pair G e₁ e₂) + triangleCoveringNumberOn G (T_pair G e₃ e₄) := by
      have h_union : triangleCoveringNumberOn G (T_pair G e₁ e₂ ∪ T_pair G e₃ e₄) ≤ triangleCoveringNumberOn G (T_pair G e₁ e₂) + triangleCoveringNumberOn G (T_pair G e₃ e₄) := by
        apply tau_union_le_sum;
      rw [ union_of_pairs_covers_all G M hM e₁ e₂ e₃ e₄ h_cycle ] at * ; aesop;
    refine le_trans h_union ?_;
    refine' le_trans ( add_le_add ( c4_adjacent_pair_bound_4 G M hM hM_card e₁ e₂ _ _ _ _ ) ( c4_adjacent_pair_bound_4 G M hM hM_card e₃ e₄ _ _ _ _ ) ) _ <;> simp_all +decide [ isCycleSharingGraph ];
    · rintro rfl; simp_all +decide ;
      exact hM_card.not_lt ( lt_of_le_of_lt ( Finset.card_insert_le _ _ ) ( lt_of_le_of_lt ( add_le_add_right ( Finset.card_insert_le _ _ ) _ ) ( by simp +decide ) ) );
    · rintro rfl; simp_all +decide ;
      exact hM_card.not_lt ( lt_of_le_of_lt ( Finset.card_insert_le _ _ ) ( lt_of_le_of_lt ( add_le_add_right ( Finset.card_insert_le _ _ ) _ ) ( by simp +decide ) ) );
  · have hM_card_lt_3 : M.card ≤ 3 := by
      unfold isCycleSharingGraph at h_cycle;
      grind;
    interval_cases _ : M.card <;> simp_all +decide;
    · have := h_cycle.1.symm; aesop;
    · have := h_cycle.2;
      unfold sharesVertex at this; unfold sharingDegree at this; simp_all +decide [ Finset.filter_eq' ] ;
      grind;
    · -- Since $M$ has cardinality 2, we can write $M = \{e_1, e_2\}$.
      obtain ⟨e₁, e₂, he₁, he₂, he₁e₂⟩ : ∃ e₁ e₂ : Finset V, e₁ ∈ M ∧ e₂ ∈ M ∧ e₁ ≠ e₂ ∧ M = {e₁, e₂} := by
        rw [ Finset.card_eq_two ] at *; aesop;
      obtain ⟨he₁, he₂⟩ : e₁ ∈ G.cliqueFinset 3 ∧ e₂ ∈ G.cliqueFinset 3 := by
        have := hM.1;
        exact ⟨ this.1 he₁, this.1 he₂ ⟩;
      have h_union : G.cliqueFinset 3 = trianglesSharingEdge G e₁ ∪ trianglesSharingEdge G e₂ := by
        have := clique_eq_union_of_sharing G M hM; aesop;
      rw [ h_union ];
      exact le_trans ( tau_union_le_sum G _ _ ) ( by linarith [ tau_sharing_le_3 G e₁ he₁, tau_sharing_le_3 G e₂ he₂ ] );
    · exact?

-- MAIN TARGET

/-
Alternative: All degree-2 sharing graphs have τ ≤ 8

This covers C₄ case and is more general.
Note: In ν=4, degree-2 for all means exactly C₄ structure.
-/
noncomputable section AristotleLemmas

/-
If a collection of 4 triangles has the property that every triangle shares a vertex with exactly 2 others, then the sharing graph is a 4-cycle.
-/
lemma exists_cycle_of_degree2_on_4 (M : Finset (Finset V))
    (hM_card : M.card = 4)
    (h_all_deg2 : ∀ e ∈ M, sharingDegree M e = 2) :
    ∃ e₁ e₂ e₃ e₄, isCycleSharingGraph M e₁ e₂ e₃ e₄ := by
      revert M;
      intro M hM h_all_deg2
      obtain ⟨e₁, e₂, e₃, e₄, heM⟩ : ∃ e₁ e₂ e₃ e₄, M = {e₁, e₂, e₃, e₄} ∧ e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₁ ≠ e₄ ∧ e₂ ≠ e₃ ∧ e₂ ≠ e₄ ∧ e₃ ≠ e₄ := by
        rw [ Finset.card_eq_succ ] at hM;
        obtain ⟨ a, t, hat, rfl, ht ⟩ := hM; rw [ Finset.card_eq_three ] at ht; obtain ⟨ e₁, e₂, e₃, he₁, he₂, he₃ ⟩ := ht; use a, e₁, e₂, e₃; aesop;
      -- By examining all possible adjacency patterns, we can conclude that the sharing graph must be a 4-cycle.
      have h_adj_pattern : (sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧ sharesVertex e₄ e₁) ∨ (sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₄ ∧ sharesVertex e₄ e₃ ∧ sharesVertex e₃ e₁) ∨ (sharesVertex e₁ e₃ ∧ sharesVertex e₃ e₂ ∧ sharesVertex e₂ e₄ ∧ sharesVertex e₄ e₁) := by
        unfold sharingDegree at h_all_deg2;
        simp_all +decide [ Finset.filter_ne', Finset.filter_and ];
        simp_all +decide [ Finset.inter_filter, Finset.card_erase_of_mem ];
        simp_all +decide [ Finset.filter_insert, sharesVertex ];
        by_cases h₁ : e₁.Nonempty <;> by_cases h₂ : e₂.Nonempty <;> simp_all +decide [ Finset.filter_singleton, sharesVertex ];
        by_cases h₃ : e₃.Nonempty <;> by_cases h₄ : e₄.Nonempty <;> simp_all +decide [ Finset.inter_comm ];
        by_cases h₅ : ( e₁ ∩ e₂ ).Nonempty <;> by_cases h₆ : ( e₁ ∩ e₃ ).Nonempty <;> by_cases h₇ : ( e₁ ∩ e₄ ).Nonempty <;> by_cases h₈ : ( e₂ ∩ e₃ ).Nonempty <;> by_cases h₉ : ( e₂ ∩ e₄ ).Nonempty <;> by_cases h₁₀ : ( e₃ ∩ e₄ ).Nonempty <;> simp_all +decide;
      obtain h | h | h := h_adj_pattern <;> simp_all +decide only [isCycleSharingGraph];
      · exact ⟨ e₁, e₂, e₃, e₄, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2, h_all_deg2 e₁ ( by simp +decide ), h_all_deg2 e₂ ( by simp +decide ), h_all_deg2 e₃ ( by simp +decide ), h_all_deg2 e₄ ( by simp +decide ) ⟩;
      · use e₁, e₂, e₄, e₃;
        grind;
      · use e₁, e₃, e₂, e₄;
        grind

end AristotleLemmas

theorem tuza_nu4_degree2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_all_deg2 : ∀ e ∈ M, sharingDegree M e = 2) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Apply `exists_cycle_of_degree2_on_4` to obtain the cycle `e₁, e₂, e₃, e₄` such that `isCycleSharingGraph M e₁ e₂ e₃ e₄`.
  obtain ⟨e₁, e₂, e₃, e₄, h_cycle⟩ : ∃ e₁ e₂ e₃ e₄, isCycleSharingGraph M e₁ e₂ e₃ e₄ := exists_cycle_of_degree2_on_4 M hM_card h_all_deg2;
  exact tuza_nu4_cycle G M hM e₁ e₂ e₃ e₄ h_cycle

-- ALTERNATIVE TARGET

end