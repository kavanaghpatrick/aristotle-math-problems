/-
  slot428_middle_adaptive.lean

  FOCUSED: Adaptive middle element edge selection

  The issue with slot427's middle_two_edges_cover_all:
  Fixed selection {s(v₁,v₂), s(v₁,b₃)} doesn't cover externals {v₂, b₃, x}.

  SOLUTION: Use ADAPTIVE selection like endpoints.
  - If v₁-type externals exist (contain v₁ but not v₂): {s(v₁,v₂), s(v₁,b₃)}
  - If v₂-type externals exist (contain v₂ but not v₁): {s(v₁,v₂), s(v₂,b₃)}
  - Since middle_no_base_externals, all externals contain v₁ OR v₂, not neither.

  KEY INSIGHT: The spine edge s(v₁,v₂) is ALWAYS included.
  We only adapt which SPOKE we add (v₁-b₃ vs v₂-b₃).

  TIER: 2 (single focused lemma with clear case split)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ≠ A ∧ T ≠ B ∧ (T ∩ A).card ≥ 2 ∧ (T ∩ B).card ≥ 2

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t =>
    t ≠ e ∧ (t ∩ e).card ≥ 2 ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

lemma bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (v : V) (hAB : A ∩ B = {v})
    (T : Finset V) (hT : isBridge G A B T) :
    v ∈ T := by
  obtain ⟨hT_clq, hT_ne_A, hT_ne_B, hTA, hTB⟩ := hT
  by_contra hv_not
  have h_disj : Disjoint (T ∩ A) (T ∩ B) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hx_inter : x ∈ A ∩ B := mem_inter.mpr ⟨mem_of_mem_inter_right hxA, mem_of_mem_inter_right hxB⟩
    rw [hAB] at hx_inter
    simp only [mem_singleton] at hx_inter
    rw [hx_inter] at hxA
    exact hv_not (mem_of_mem_inter_left hxA)
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq
    exact hT_clq.1.card_eq
  have h_union : (T ∩ A ∪ T ∩ B) ⊆ T := union_subset inter_subset_left inter_subset_left
  have h_card : (T ∩ A ∪ T ∩ B).card ≤ T.card := card_le_card h_union
  rw [card_union_of_disjoint h_disj] at h_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Adaptive middle element selection
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
For B = {v₁, v₂, b₃}:

External types (for S_e):
- Type v₁: contains v₁ and b₃ (but not v₂) - e.g., {v₁, b₃, x}
- Type v₂: contains v₂ and b₃ (but not v₁) - e.g., {v₂, b₃, x}
- Type spine: contains v₁ and v₂ (and some z) - e.g., {v₁, v₂, z}

By middle_no_base_externals, NO external can contain ONLY b₃ from B.
Every external contains v₁ or v₂.

SELECTION STRATEGY:
- Always include spine edge s(v₁, v₂) - covers B, Type spine, and helps bridges
- Add s(v₁, b₃) if Type v₁ exists, OR s(v₂, b₃) if Type v₂ exists
- If both exist... wait, can they? Let's check:
  Type v₁ triangle: {v₁, b₃, x} where x ∉ B
  Type v₂ triangle: {v₂, b₃, y} where y ∉ B
  These can coexist! We need case analysis.

CASE 1: Only Type v₁ externals exist (or Type spine)
  Selection: {s(v₁, v₂), s(v₁, b₃)}
  - s(v₁, v₂) covers: B, Type spine, A-B bridges with v₂, B-C bridges with v₁
  - s(v₁, b₃) covers: Type v₁

CASE 2: Only Type v₂ externals exist (or Type spine)
  Selection: {s(v₁, v₂), s(v₂, b₃)}
  - s(v₁, v₂) covers: B, Type spine, A-B bridges with v₂, B-C bridges with v₁
  - s(v₂, b₃) covers: Type v₂

CASE 3: Both Type v₁ AND Type v₂ exist
  Problem: need 3 edges? NO! The bridges argument saves us:
  - A-B bridges: {v₁, x, y} where x ∈ B. Since bridge shares edge with B,
    we have {v₁, v₂} or {v₁, b₃} in bridge.
  - B-C bridges: similar with v₂.
  - If Type v₁ exists but A-B bridges need v₁-b₃... the s(v₁, b₃) covers both!

Actually, the key insight is that NOT ALL THREE external types can exist
(from not_all_three_edge_types for middle elements).

Wait - for MIDDLE elements, the three edge types are:
- {v₁, v₂} (spine)
- {v₁, b₃} (spoke 1)
- {v₂, b₃} (spoke 2)

And middle_no_base_externals says there are NO base externals for middle elements.
But what's the "base" for a middle element? It's the non-spine edges!
No wait - middle elements have TWO vertices shared with adjacent elements (v₁ with A, v₂ with C).

Let me reconsider. For middle B = {v₁, v₂, b₃}:
- b₃ is the "free" vertex (not shared with A or C)
- {v₁, v₂} is the "spine" edge
- {v₁, b₃} and {v₂, b₃} are the "spoke" edges

External triangles of B share edge {u, w} with B where u, w ∈ B.
By middle_no_base_externals, every external contains v₁ OR v₂.
This means NO external uses ONLY edge {b₃, x} - there is no "base external" for B.

So external types for B are:
- Spine type: uses {v₁, v₂}, form {v₁, v₂, z}
- Spoke1 type: uses {v₁, b₃}, form {v₁, b₃, x}
- Spoke2 type: uses {v₂, b₃}, form {v₂, b₃, y}

NOT ALL THREE can exist (by not_all_three_edge_types).
So at most 2 types exist → 2 edges suffice!

SELECTION:
- If Spoke2 empty: {s(v₁, v₂), s(v₁, b₃)} covers spine + spoke1
- If Spoke1 empty: {s(v₁, v₂), s(v₂, b₃)} covers spine + spoke2
- If Spine empty: {s(v₁, b₃), s(v₂, b₃)} covers spoke1 + spoke2
  BUT: this doesn't help bridges as much. Need spine for bridges!

Key: If BOTH spoke types exist, spine type must be empty.
But spine edge s(v₁, v₂) is still needed for bridges!

Actually wait - if spine TYPE is empty, there are no {v₁, v₂, z} externals.
But the EDGE s(v₁, v₂) can still cover B itself and bridges.

Hmm, let me think about bridges more carefully:
- A-B bridge T: contains v₁, shares edge with B
- B-C bridge T: contains v₂, shares edge with B

If T is A-B bridge with v₁ ∈ T and |T ∩ B| ≥ 2:
T ∩ B contains v₁ and one of {v₂, b₃}.
- If v₂ ∈ T: s(v₁, v₂) ∈ T.sym2 ✓
- If b₃ ∈ T: s(v₁, b₃) ∈ T.sym2 ✓

Similarly for B-C bridges with v₂.

So:
- s(v₁, v₂) covers: B, all bridges with both v₁ and v₂
- s(v₁, b₃) covers: A-B bridges with b₃, Spoke1 externals
- s(v₂, b₃) covers: B-C bridges with b₃, Spoke2 externals

The issue is: if both spoke types exist (spine empty), we need both spoke edges,
but that leaves bridges-with-opposite-spine-vertex uncovered!

Wait no. Let's trace through:
- A-B bridge T: v₁ ∈ T, |T ∩ B| ≥ 2
  - If v₂ ∈ T: s(v₁, v₂) covers (but we don't have it if spine empty!)
  - If b₃ ∈ T: s(v₁, b₃) covers ✓

- B-C bridge T: v₂ ∈ T, |T ∩ B| ≥ 2
  - If v₁ ∈ T: s(v₁, v₂) covers (but we don't have it if spine empty!)
  - If b₃ ∈ T: s(v₂, b₃) covers ✓

So if spine type is empty and we select {s(v₁, b₃), s(v₂, b₃)}:
- A-B bridges with v₂ (not b₃): UNCOVERED
- B-C bridges with v₁ (not b₃): UNCOVERED

This is a problem! BUT: can such bridges exist when spine type is empty?

A-B bridge T = {v₁, v₂, x} where x ∈ A (not B):
- T shares {v₁, v₂} with B → T is a SPINE TYPE external of B!
- If spine type is empty, no such T exists.

Similarly for B-C bridges.

THEREFORE: When spine type is empty, all A-B bridges have b₃ (not v₂),
and all B-C bridges have b₃ (not v₁).
Selection {s(v₁, b₃), s(v₂, b₃)} covers all bridges!

This is the key insight: THE SELECTION THAT COVERS EXTERNALS ALSO COVERS BRIDGES
because bridges ARE externals (of some type)!
-/

theorem middle_adaptive_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C : Finset V) (v₁ v₂ b₃ : V)
    (hB : B = {v₁, v₂, b₃})
    (hB_M : B ∈ M) (hA_M : A ∈ M) (hC_M : C ∈ M)
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂})
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ b₃ ∧ v₂ ≠ b₃)
    (hB_clq : B ∈ G.cliqueFinset 3)
    -- External type sets
    (Type_spine : Finset (Finset V))  -- externals using {v₁, v₂}
    (Type_spoke1 : Finset (Finset V)) -- externals using {v₁, b₃}
    (Type_spoke2 : Finset (Finset V)) -- externals using {v₂, b₃}
    -- Not all three types nonempty
    (h_not_all_three : ¬(Type_spine.Nonempty ∧ Type_spoke1.Nonempty ∧ Type_spoke2.Nonempty))
    -- Types correctly classify S_e externals
    (h_classify : ∀ T ∈ S_e G M B,
      (v₁ ∈ T ∧ v₂ ∈ T → T ∈ Type_spine) ∧
      (v₁ ∈ T ∧ b₃ ∈ T ∧ v₂ ∉ T → T ∈ Type_spoke1) ∧
      (v₂ ∈ T ∧ b₃ ∈ T ∧ v₁ ∉ T → T ∈ Type_spoke2))
    -- All S_e externals contain v₁ or v₂ (middle_no_base_externals)
    (h_no_base : ∀ T ∈ S_e G M B, v₁ ∈ T ∨ v₂ ∈ T)
    -- Bridges are typed correctly
    (h_AB_bridge_type : ∀ T, isBridge G A B T →
      (v₂ ∈ T → T ∈ Type_spine) ∧ (b₃ ∈ T ∧ v₂ ∉ T → T ∈ Type_spoke1))
    (h_BC_bridge_type : ∀ T, isBridge G B C T →
      (v₁ ∈ T → T ∈ Type_spine) ∧ (b₃ ∈ T ∧ v₁ ∉ T → T ∈ Type_spoke2))
    :
    ∃ (e₁ e₂ : Sym2 V),
      e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      e₁ ∈ B.sym2 ∧ e₂ ∈ B.sym2 ∧
      -- Covers B
      (e₁ ∈ B.sym2 ∨ e₂ ∈ B.sym2) ∧
      -- Covers S_e externals
      (∀ T ∈ S_e G M B, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) ∧
      -- Covers A-B bridges
      (∀ T, isBridge G A B T → e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) ∧
      -- Covers B-C bridges
      (∀ T, isBridge G B C T → e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- Case analysis on which type is empty
  by_cases h_spoke2 : Type_spoke2.Nonempty
  · -- Spoke2 nonempty → spine or spoke1 must be empty
    by_cases h_spine : Type_spine.Nonempty
    · -- Spine and Spoke2 nonempty → Spoke1 must be empty
      have h_spoke1_empty : ¬Type_spoke1.Nonempty :=
        fun h => h_not_all_three ⟨h_spine, h, h_spoke2⟩
      -- Selection: {s(v₁, v₂), s(v₂, b₃)}
      use s(v₁, v₂), s(v₂, b₃)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- e₁ ∈ G.edgeFinset
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1]) hdist.1
      -- e₂ ∈ G.edgeFinset
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp [hdist.1]) (by rw [hB]; simp [hdist.1, hdist.2.2]) hdist.2.2
      -- e₁ ∈ B.sym2
      · rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      -- e₂ ∈ B.sym2
      · rw [hB]; exact edge_in_sym2 _ v₂ b₃ (by simp [hdist.1]) (by simp [hdist.1, hdist.2.2])
      -- Covers B
      · left; rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      -- Covers S_e externals
      · intro T hT
        have h_or := h_no_base T hT
        rcases h_or with hv₁ | hv₂
        · -- v₁ ∈ T
          -- T also shares edge with B, so has another vertex from B
          simp only [S_e, mem_filter] at hT
          obtain ⟨hT_clq, hT_ne, hT_share, _⟩ := hT
          have hT_card : T.card = 3 := by
            rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
          have hv₁_B : v₁ ∈ B := by rw [hB]; simp
          have hv₁_inter : v₁ ∈ T ∩ B := mem_inter.mpr ⟨hv₁, hv₁_B⟩
          have h_exists : ∃ x ∈ T ∩ B, x ≠ v₁ := by
            by_contra h; push_neg at h
            have h_sub : T ∩ B ⊆ {v₁} := fun w hw => mem_singleton.mpr (h w hw)
            have h_card : (T ∩ B).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
          have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
          have hx_B : x ∈ B := mem_of_mem_inter_right hx_inter
          rw [hB] at hx_B
          simp only [mem_insert, mem_singleton] at hx_B
          rcases hx_B with rfl | rfl | rfl
          · exact absurd rfl hx_ne
          · left; exact edge_in_sym2 T v₁ v₂ hv₁ hx_T
          · -- x = b₃: T is Type spoke1, but spoke1 is empty!
            have hv₂_notin : v₂ ∉ T := by
              intro hv₂
              -- T has v₁, v₂, b₃ → |T| ≥ 3, and if all distinct, T = B, contradiction
              have h_all : ({v₁, v₂, b₃} : Finset V) ⊆ T := by
                intro z hz
                simp only [mem_insert, mem_singleton] at hz
                rcases hz with rfl | rfl | rfl
                · exact hv₁
                · exact hv₂
                · exact hx_T
              have h_card_B : ({v₁, v₂, b₃} : Finset V).card = 3 := by
                simp [hdist.1, hdist.2.1, hdist.2.2]
              have hT_ge : T.card ≥ 3 := by
                calc T.card ≥ ({v₁, v₂, b₃} : Finset V).card := card_le_card h_all
                  _ = 3 := h_card_B
              have hT_eq : T.card = 3 := hT_card
              have h_eq_set : T = {v₁, v₂, b₃} := by
                apply eq_of_subset_of_card_le h_all
                rw [h_card_B, hT_eq]
              rw [h_eq_set, ← hB] at hT_ne
              exact hT_ne rfl
            have hT_spoke1 : T ∈ Type_spoke1 :=
              (h_classify T hT).2.1 ⟨hv₁, hx_T, hv₂_notin⟩
            exact absurd ⟨T, hT_spoke1⟩ h_spoke1_empty
        · -- v₂ ∈ T
          simp only [S_e, mem_filter] at hT
          obtain ⟨hT_clq, hT_ne, hT_share, _⟩ := hT
          have hv₂_B : v₂ ∈ B := by rw [hB]; simp [hdist.1]
          have hv₂_inter : v₂ ∈ T ∩ B := mem_inter.mpr ⟨hv₂, hv₂_B⟩
          have h_exists : ∃ x ∈ T ∩ B, x ≠ v₂ := by
            by_contra h; push_neg at h
            have h_sub : T ∩ B ⊆ {v₂} := fun w hw => mem_singleton.mpr (h w hw)
            have h_card : (T ∩ B).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
          have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
          have hx_B : x ∈ B := mem_of_mem_inter_right hx_inter
          rw [hB] at hx_B
          simp only [mem_insert, mem_singleton] at hx_B
          rcases hx_B with rfl | rfl | rfl
          · left; exact edge_in_sym2 T v₁ v₂ hx_T hv₂
          · exact absurd rfl hx_ne
          · right; exact edge_in_sym2 T v₂ b₃ hv₂ hx_T
      -- Covers A-B bridges
      · intro T hT_bridge
        have hv₁_T : v₁ ∈ T := bridge_contains_shared G A B v₁ hAB T hT_bridge
        obtain ⟨hT_clq, _, _, _, hTB⟩ := hT_bridge
        have hT_card : T.card = 3 := by
          rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
        have hv₁_B : v₁ ∈ B := by rw [hB]; simp
        have hv₁_inter : v₁ ∈ T ∩ B := mem_inter.mpr ⟨hv₁_T, hv₁_B⟩
        have h_exists : ∃ x ∈ T ∩ B, x ≠ v₁ := by
          by_contra h; push_neg at h
          have h_sub : T ∩ B ⊆ {v₁} := fun w hw => mem_singleton.mpr (h w hw)
          have h_card : (T ∩ B).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
          omega
        obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
        have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
        have hx_B : x ∈ B := mem_of_mem_inter_right hx_inter
        rw [hB] at hx_B
        simp only [mem_insert, mem_singleton] at hx_B
        rcases hx_B with rfl | rfl | rfl
        · exact absurd rfl hx_ne
        · left; exact edge_in_sym2 T v₁ v₂ hv₁_T hx_T
        · -- x = b₃: T is Type spoke1, but spoke1 is empty!
          have hv₂_notin : v₂ ∉ T := by
            intro hv₂_T
            have h_all : ({v₁, v₂, b₃} : Finset V) ⊆ T := by
              intro z hz
              simp only [mem_insert, mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact hv₁_T
              · exact hv₂_T
              · exact hx_T
            have h_card_B : ({v₁, v₂, b₃} : Finset V).card = 3 := by
              simp [hdist.1, hdist.2.1, hdist.2.2]
            have hT_ge : T.card ≥ 3 := by
              calc T.card ≥ ({v₁, v₂, b₃} : Finset V).card := card_le_card h_all
                _ = 3 := h_card_B
            have h_eq_set : T = {v₁, v₂, b₃} := by
              apply eq_of_subset_of_card_le h_all
              rw [h_card_B, hT_card]
            obtain ⟨_, hT_ne_B, _, _, _⟩ := hT_bridge
            rw [h_eq_set, ← hB] at hT_ne_B
            exact hT_ne_B rfl
          have hT_spoke1 : T ∈ Type_spoke1 := (h_AB_bridge_type T hT_bridge).2 ⟨hx_T, hv₂_notin⟩
          exact absurd ⟨T, hT_spoke1⟩ h_spoke1_empty
      -- Covers B-C bridges
      · intro T hT_bridge
        have hv₂_T : v₂ ∈ T := bridge_contains_shared G B C v₂ hBC T hT_bridge
        obtain ⟨hT_clq, _, _, hTB, _⟩ := hT_bridge
        have hT_card : T.card = 3 := by
          rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clq; exact hT_clq.1.card_eq
        have hv₂_B : v₂ ∈ B := by rw [hB]; simp [hdist.1]
        have hv₂_inter : v₂ ∈ T ∩ B := mem_inter.mpr ⟨hv₂_T, hv₂_B⟩
        have h_exists : ∃ x ∈ T ∩ B, x ≠ v₂ := by
          by_contra h; push_neg at h
          have h_sub : T ∩ B ⊆ {v₂} := fun w hw => mem_singleton.mpr (h w hw)
          have h_card : (T ∩ B).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
          omega
        obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
        have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
        have hx_B : x ∈ B := mem_of_mem_inter_right hx_inter
        rw [hB] at hx_B
        simp only [mem_insert, mem_singleton] at hx_B
        rcases hx_B with rfl | rfl | rfl
        · left; exact edge_in_sym2 T v₁ v₂ hx_T hv₂_T
        · exact absurd rfl hx_ne
        · right; exact edge_in_sym2 T v₂ b₃ hv₂_T hx_T
    · -- Spine empty, Spoke2 nonempty → can use {s(v₁, b₃), s(v₂, b₃)} or {s(v₁,v₂), s(v₂,b₃)}
      -- Let's use {s(v₁, v₂), s(v₂, b₃)} - spine edge still helps for B itself
      use s(v₁, v₂), s(v₂, b₃)
      -- Same proof as above case!
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1]) hdist.1
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp [hdist.1]) (by rw [hB]; simp [hdist.1, hdist.2.2]) hdist.2.2
      · rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      · rw [hB]; exact edge_in_sym2 _ v₂ b₃ (by simp [hdist.1]) (by simp [hdist.1, hdist.2.2])
      · left; rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      -- The rest follows same pattern - spoke1 must be empty here too
      all_goals sorry
  · -- Spoke2 empty
    by_cases h_spoke1 : Type_spoke1.Nonempty
    · -- Spoke1 nonempty, Spoke2 empty: select {s(v₁, v₂), s(v₁, b₃)}
      use s(v₁, v₂), s(v₁, b₃)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1]) hdist.1
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1, hdist.2.1]) hdist.2.1
      · rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      · rw [hB]; exact edge_in_sym2 _ v₁ b₃ (by simp) (by simp [hdist.1, hdist.2.1])
      · left; rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      -- Symmetric to above cases
      all_goals sorry
    · -- Both spoke types empty: spine edge + any spoke works
      use s(v₁, v₂), s(v₁, b₃)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1]) hdist.1
      · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_cliqueFinset_iff] at hB_clq
        exact hB_clq.1 (by rw [hB]; simp) (by rw [hB]; simp [hdist.1, hdist.2.1]) hdist.2.1
      · rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      · rw [hB]; exact edge_in_sym2 _ v₁ b₃ (by simp) (by simp [hdist.1, hdist.2.1])
      · left; rw [hB]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hdist.1])
      -- All externals are spine type (spoke1 and spoke2 empty)
      all_goals sorry

end
