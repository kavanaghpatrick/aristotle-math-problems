/-
  slot433_coordinated_cover.lean

  COORDINATED COVER: τ ≤ 8 for PATH_4 (ν = 4)

  KEY INSIGHT (from Grok analysis):
  The cover is NOT independent per-element but COORDINATED across adjacent elements.

  For endpoint A:
  - Case 1 (no base externals): spokes s(a₁,v₁), s(a₂,v₁) cover A + bridges
  - Case 2 (base externals exist): s(a₁,a₂) + one spoke, B covers remaining bridges

  The 8-edge budget works because adjacent elements share bridge responsibility.

  TIER: 2-3 (case analysis + coordination)
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

/-- S_e external: shares edge with E but NOT with any other packing element -/
def isSeExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (others : List (Finset V)) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  2 ≤ (T ∩ E).card ∧
  ∀ F ∈ others, (T ∩ F).card ≤ 1

/-- Base external of A: S_e external using base edge s(a₁, a₂) -/
def isBaseExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (a₁ a₂ v₁ : V) (others : List (Finset V)) (T : Finset V) : Prop :=
  isSeExternal G A others T ∧
  a₁ ∈ T ∧ a₂ ∈ T ∧ v₁ ∉ T

/-- Bridge between A and B: shares edge with both -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ 2 ≤ (T ∩ A).card ∧ 2 ≤ (T ∩ B).card

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Bridge Contains Shared (from slot441)
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    ext x; simp only [mem_inter, mem_singleton]; constructor
    · intro ⟨⟨hxT, hxE⟩, _, hxF⟩
      have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE, hxF⟩
      rw [hEF] at hx_both
      exact ⟨hxT, mem_singleton.mp hx_both⟩
    · intro ⟨hxT, hxv⟩
      have hv_mem : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      rw [hxv]
      exact ⟨⟨hxT, (mem_inter.mp hv_mem).1⟩, hxT, (mem_inter.mp hv_mem).2⟩
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx; simp only [mem_union, mem_inter] at hx
    cases hx with | inl h => exact h.1 | inr h => exact h.1
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
      calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
        _ = 3 := hT_card
    omega
  rw [card_pos] at h_pos
  obtain ⟨x, hx⟩ := h_pos
  simp only [mem_inter, mem_singleton] at hx
  exact hx.2 ▸ hx.1

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_of_three_with_one_known (T : Finset V) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_inter : 2 ≤ (T ∩ {a, b, c}).card) (hc : c ∈ T) :
    a ∈ T ∨ b ∈ T := by
  by_contra h_neither
  push_neg at h_neither
  have ha_not : a ∉ T := h_neither.1
  have hb_not : b ∉ T := h_neither.2
  have h_sub : T ∩ {a, b, c} ⊆ {c} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 ha_not
    · exact absurd hx.1 hb_not
    · simp
  have h_card : (T ∩ {a, b, c}).card ≤ 1 := by
    calc (T ∩ {a, b, c}).card ≤ ({c} : Finset V).card := card_le_card h_sub
      _ = 1 := card_singleton c
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE STRUCTURE LEMMA
-- For A-B bridges: T = {v₁, aᵢ, bⱼ} where aᵢ ∈ {a₁,a₂}, bⱼ ∈ {b,v₂}
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Bridge T has |T ∩ A| ≥ 2 and |T ∩ B| ≥ 2
2. A ∩ B = {v₁} (spine intersection)
3. T has exactly 3 vertices
4. v₁ ∈ T (by bridge_contains_shared)
5. T must contain one more from A\{v₁} = {a₁,a₂} and one more from B\{v₁} = {b,v₂}
6. So T = {v₁, aᵢ, bⱼ}
-/
lemma bridge_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ b v₂ : V)
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_v1_ne_b : v₁ ≠ b) (h_v1_ne_v2 : v₁ ≠ v₂) (h_b_ne_v2 : b ≠ v₂)
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ {v₁, b, v₂} = {v₁})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTA : 2 ≤ (T ∩ {a₁, a₂, v₁}).card)
    (hTB : 2 ≤ (T ∩ {v₁, b, v₂}).card) :
    v₁ ∈ T ∧ (a₁ ∈ T ∨ a₂ ∈ T) ∧ (b ∈ T ∨ v₂ ∈ T) := by
  have hv₁T : v₁ ∈ T := bridge_contains_shared G {a₁, a₂, v₁} {v₁, b, v₂} v₁ hAB T hT hTA hTB
  refine ⟨hv₁T, ?_, ?_⟩
  · exact two_of_three_with_one_known T a₁ a₂ v₁ h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 hTA hv₁T
  · exact two_of_three_with_one_known T v₁ b v₂ h_v1_ne_b h_v1_ne_v2 h_b_ne_v2 hTB hv₁T

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: B's spoke covers A-B bridges not hit by A's spoke
-- If A uses s(a₁,a₂) + s(a₁,v₁), then B's s(v₁,b) covers bridges {v₁,a₂,b}
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Bridges containing a₂ but not a₁ have form {v₁, a₂, bⱼ}
2. These are covered by spokes through v₁ from B's side
3. s(v₁, b) covers {v₁, a₂, b}
4. s(v₁, v₂) covers {v₁, a₂, v₂}
-/
lemma b_spoke_covers_remaining_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ v₁ b v₂ : V)
    (h_v1_ne_b : v₁ ≠ b) (h_v1_ne_v2 : v₁ ≠ v₂)
    (T : Finset V)
    (hv₁T : v₁ ∈ T) (ha₂T : a₂ ∈ T) (hbT : b ∈ T) :
    s(v₁, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hv₁T, hbT⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COORDINATED COVER STRATEGY
-- ══════════════════════════════════════════════════════════════════════════════

/-
STRATEGY:
For PATH_4: A--v₁--B--v₂--C--v₃--D

Cover selection depends on base externals:

CASE 1: A has no base externals
  A: s(a₁,v₁), s(a₂,v₁)        -- both spokes
  B: s(v₁,v₂), s(b,v₂)         -- spine + right spoke
  C: s(v₂,v₃), s(c,v₃)         -- spine + right spoke
  D: s(v₃,d₁), s(v₃,d₂)        -- both spokes

CASE 2: A has base externals
  A: s(a₁,a₂), s(a₁,v₁)        -- base + left spoke
  B: s(v₁,b), s(v₁,v₂)         -- left spoke + spine (covers {v₁,a₂,b} and {v₁,a₂,v₂})
  C: s(v₂,v₃), s(c,v₃)         -- spine + right spoke
  D: s(v₃,d₁), s(v₃,d₂)        -- both spokes

(Similar cases for D having base externals, or middle elements needing adjustment)

The key: 8 edges total in all cases!
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Existence of coordinated 8-edge cover
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_path4_coordinated (G : SimpleGraph V) [DecidableRel G.Adj]
    -- Vertices (9 distinct)
    (a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V)
    -- Distinctness within triangles
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_v1_ne_b : v₁ ≠ b) (h_v1_ne_v2 : v₁ ≠ v₂) (h_b_ne_v2 : b ≠ v₂)
    (h_v2_ne_c : v₂ ≠ c) (h_v2_ne_v3 : v₂ ≠ v₃) (h_c_ne_v3 : c ≠ v₃)
    (h_v3_ne_d1 : v₃ ≠ d₁) (h_v3_ne_d2 : v₃ ≠ d₂) (h_d1_ne_d2 : d₁ ≠ d₂)
    -- Triangle membership
    (hA : {a₁, a₂, v₁} ∈ G.cliqueFinset 3)
    (hB : {v₁, b, v₂} ∈ G.cliqueFinset 3)
    (hC : {v₂, c, v₃} ∈ G.cliqueFinset 3)
    (hD : {v₃, d₁, d₂} ∈ G.cliqueFinset 3)
    -- Spine intersections
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ {v₁, b, v₂} = {v₁})
    (hBC : ({v₁, b, v₂} : Finset V) ∩ {v₂, c, v₃} = {v₂})
    (hCD : ({v₂, c, v₃} : Finset V) ∩ {v₃, d₁, d₂} = {v₃})
    -- Edge-disjointness (non-adjacent pairs share ≤ 1 vertex)
    (hAC : (({a₁, a₂, v₁} : Finset V) ∩ {v₂, c, v₃}).card ≤ 1)
    (hAD : (({a₁, a₂, v₁} : Finset V) ∩ {v₃, d₁, d₂}).card ≤ 1)
    (hBD : (({v₁, b, v₂} : Finset V) ∩ {v₃, d₁, d₂}).card ≤ 1)
    -- Maximality: every triangle shares edge with some packing element
    (h_max : ∀ T ∈ G.cliqueFinset 3,
      2 ≤ (T ∩ {a₁, a₂, v₁}).card ∨
      2 ≤ (T ∩ {v₁, b, v₂}).card ∨
      2 ≤ (T ∩ {v₂, c, v₃}).card ∨
      2 ≤ (T ∩ {v₃, d₁, d₂}).card) :
    -- Conclusion: 8-edge cover exists
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by

  -- Define base external condition for A
  let hasBaseExternalA := ∃ T ∈ G.cliqueFinset 3,
    isSeExternal G {a₁, a₂, v₁} [{v₁, b, v₂}, {v₂, c, v₃}, {v₃, d₁, d₂}] T ∧
    a₁ ∈ T ∧ a₂ ∈ T ∧ v₁ ∉ T

  -- Define base external condition for D
  let hasBaseExternalD := ∃ T ∈ G.cliqueFinset 3,
    isSeExternal G {v₃, d₁, d₂} [{a₁, a₂, v₁}, {v₁, b, v₂}, {v₂, c, v₃}] T ∧
    d₁ ∈ T ∧ d₂ ∈ T ∧ v₃ ∉ T

  -- Case analysis on whether base externals exist
  by_cases hA_base : hasBaseExternalA
  · -- Case A.2: A has base externals
    by_cases hD_base : hasBaseExternalD
    · -- A.2, D.2: Both endpoints have base externals
      let Cover : Finset (Sym2 V) := {
        s(a₁, a₂), s(a₁, v₁),   -- A: base + left spoke
        s(v₁, b), s(v₁, v₂),     -- B: left spoke + spine (covers A-B bridges)
        s(v₂, v₃), s(v₂, c),     -- C: spine + left spoke
        s(d₁, d₂), s(d₂, v₃)     -- D: base + right spoke
      }
      use Cover
      refine ⟨?_, ?_, ?_⟩
      · -- Card ≤ 8
        sorry
      · -- Subset of G.edgeFinset
        sorry
      · -- Covers all triangles
        sorry

    · -- A.2, D.1: A has base externals, D doesn't
      let Cover : Finset (Sym2 V) := {
        s(a₁, a₂), s(a₁, v₁),   -- A: base + left spoke
        s(v₁, b), s(v₁, v₂),     -- B: covers remaining A-B bridges
        s(v₂, v₃), s(v₂, c),     -- C: spine + left spoke
        s(v₃, d₁), s(v₃, d₂)     -- D: both spokes
      }
      use Cover
      refine ⟨?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry

  · -- Case A.1: A has no base externals (all A-externals contain v₁)
    by_cases hD_base : hasBaseExternalD
    · -- A.1, D.2: D has base externals
      let Cover : Finset (Sym2 V) := {
        s(a₁, v₁), s(a₂, v₁),   -- A: both spokes
        s(v₁, v₂), s(b, v₂),     -- B: spine + right spoke
        s(v₂, v₃), s(c, v₃),     -- C: covers remaining C-D bridges
        s(d₁, d₂), s(d₁, v₃)     -- D: base + left spoke
      }
      use Cover
      refine ⟨?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry

    · -- A.1, D.1: No base externals at either endpoint
      -- This is the "easy" case: spokes suffice for endpoints
      let Cover : Finset (Sym2 V) := {
        s(a₁, v₁), s(a₂, v₁),   -- A: both spokes
        s(v₁, v₂), s(v₁, b),     -- B: spine + left spoke
        s(v₂, v₃), s(v₂, c),     -- C: spine + left spoke
        s(v₃, d₁), s(v₃, d₂)     -- D: both spokes
      }
      use Cover
      refine ⟨?_, ?_, ?_⟩
      · -- Card ≤ 8
        sorry
      · -- Subset of G.edgeFinset
        intro e he
        simp only [mem_insert, mem_singleton] at he
        rw [SimpleGraph.mem_edgeFinset]
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals {
          rw [SimpleGraph.mem_cliqueFinset_iff] at hA hB hC hD
          first
          | exact hA.1 (by simp) (by simp) (by assumption)
          | exact hB.1 (by simp) (by simp) (by assumption)
          | exact hC.1 (by simp) (by simp) (by assumption)
          | exact hD.1 (by simp) (by simp) (by assumption)
        }
      · -- Covers all triangles
        intro T hT
        obtain hTA | hTB | hTC | hTD := h_max T hT

        -- T shares edge with A
        · by_cases hTB' : 2 ≤ (T ∩ {v₁, b, v₂}).card
          · -- Bridge A-B: v₁ ∈ T, plus one of {a₁,a₂}
            have hv₁T : v₁ ∈ T := bridge_contains_shared G {a₁, a₂, v₁} {v₁, b, v₂} v₁ hAB T hT hTA hTB'
            obtain ha1 | ha2 := two_of_three_with_one_known T a₁ a₂ v₁ h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 hTA hv₁T
            · use s(a₁, v₁); refine ⟨by simp, ?_⟩
              simp only [Finset.mk_mem_sym2_iff]; exact ⟨ha1, hv₁T⟩
            · use s(a₂, v₁); refine ⟨by simp, ?_⟩
              simp only [Finset.mk_mem_sym2_iff]; exact ⟨ha2, hv₁T⟩
          · -- S_e external of A: no base externals, so v₁ ∈ T
            -- By ¬hasBaseExternalA: no T with a₁,a₂ ∈ T and v₁ ∉ T
            -- So if |T ∩ A| ≥ 2 and it's not a bridge, then v₁ must be in T
            have hv₁T : v₁ ∈ T := by
              by_contra h_v1_notin
              -- T ∩ A ⊆ {a₁, a₂} since v₁ ∉ T
              -- |T ∩ A| ≥ 2 means {a₁, a₂} ⊆ T
              have ha1_in : a₁ ∈ T := by
                have h_sub : T ∩ {a₁, a₂, v₁} ⊆ {a₁, a₂} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl
                  · left; rfl
                  · right; rfl
                  · exact absurd hx.1 h_v1_notin
                by_contra ha1_not
                have h_sub' : T ∩ {a₁, a₂, v₁} ⊆ {a₂} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl
                  · exact absurd hx.1 ha1_not
                  · rfl
                  · exact absurd hx.1 h_v1_notin
                have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
                  calc (T ∩ {a₁, a₂, v₁}).card ≤ ({a₂} : Finset V).card := card_le_card h_sub'
                    _ = 1 := card_singleton _
                omega
              have ha2_in : a₂ ∈ T := by
                by_contra ha2_not
                have h_sub' : T ∩ {a₁, a₂, v₁} ⊆ {a₁} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl
                  · rfl
                  · exact absurd hx.1 ha2_not
                  · exact absurd hx.1 h_v1_notin
                have : (T ∩ {a₁, a₂, v₁}).card ≤ 1 := by
                  calc (T ∩ {a₁, a₂, v₁}).card ≤ ({a₁} : Finset V).card := card_le_card h_sub'
                    _ = 1 := card_singleton _
                omega
              -- Now we have a₁, a₂ ∈ T and v₁ ∉ T
              -- Check it's not a bridge (already done: hTB' says ¬bridge)
              -- Check it's S_e: shares edge with A, not with B,C,D
              -- T ∩ B: T contains v₁? No. T contains v₂? Maybe.
              -- Since ¬hTB', |T ∩ B| ≤ 1, so T shares at most 1 vertex with B
              -- Similarly for C, D (need to check)
              -- This makes T an S_e external with a₁,a₂ ∈ T, v₁ ∉ T
              -- But ¬hasBaseExternalA says no such T exists!
              exfalso
              apply hA_base
              use T, hT
              refine ⟨⟨hT, hTA, ?_⟩, ha1_in, ha2_in, h_v1_notin⟩
              intro F hF
              simp only [List.mem_cons, List.mem_singleton] at hF
              rcases hF with rfl | rfl | rfl
              · -- F = B
                omega
              · -- F = C
                by_contra h_TC
                push_neg at h_TC
                -- |T ∩ C| ≥ 2
                -- But T has a₁, a₂ and |T ∩ A| ≥ 2
                -- A and C share ≤ 1 vertex (hAC)
                -- T = {a₁, a₂, x} for some x
                -- If |T ∩ C| ≥ 2, then x ∈ C and at least one of a₁,a₂ ∈ C
                -- But A ∩ C has card ≤ 1, and a₁ ≠ a₂ are in A
                -- So at most one of a₁,a₂ can be in C
                sorry
              · -- F = D
                sorry

            -- Now we have v₁ ∈ T
            obtain ha1 | ha2 := two_of_three_with_one_known T a₁ a₂ v₁ h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 hTA hv₁T
            · use s(a₁, v₁); refine ⟨by simp, ?_⟩
              simp only [Finset.mk_mem_sym2_iff]; exact ⟨ha1, hv₁T⟩
            · use s(a₂, v₁); refine ⟨by simp, ?_⟩
              simp only [Finset.mk_mem_sym2_iff]; exact ⟨ha2, hv₁T⟩

        -- T shares edge with B
        · by_cases hTA' : 2 ≤ (T ∩ {a₁, a₂, v₁}).card
          · -- Bridge A-B (handled above)
            have hv₁T : v₁ ∈ T := bridge_contains_shared G {a₁, a₂, v₁} {v₁, b, v₂} v₁ hAB T hT hTA' hTB
            obtain ha1 | ha2 := two_of_three_with_one_known T a₁ a₂ v₁ h_a1_ne_a2 h_a1_ne_v1 h_a2_ne_v1 hTA' hv₁T
            · use s(a₁, v₁); refine ⟨by simp, ?_⟩
              simp only [Finset.mk_mem_sym2_iff]; exact ⟨ha1, hv₁T⟩
            · use s(a₂, v₁); refine ⟨by simp, ?_⟩
              simp only [Finset.mk_mem_sym2_iff]; exact ⟨ha2, hv₁T⟩
          · by_cases hTC' : 2 ≤ (T ∩ {v₂, c, v₃}).card
            · -- Bridge B-C: v₂ ∈ T
              have hv₂T : v₂ ∈ T := bridge_contains_shared G {v₁, b, v₂} {v₂, c, v₃} v₂ hBC T hT hTB hTC'
              use s(v₁, v₂); refine ⟨by simp, ?_⟩
              -- Need v₁ ∈ T: from |T ∩ B| ≥ 2 and v₂ ∈ T
              obtain hv1 | hb := two_of_three_with_one_known T v₁ b v₂ h_v1_ne_b h_v1_ne_v2 h_b_ne_v2 hTB hv₂T
              · simp only [Finset.mk_mem_sym2_iff]; exact ⟨hv1, hv₂T⟩
              · -- b ∈ T, v₂ ∈ T, need v₁... use s(v₁, b) instead
                use s(v₁, b); refine ⟨by simp, ?_⟩
                -- Need v₁ ∈ T from |T ∩ B| ≥ 2 with b, v₂ ∈ T
                -- |T| = 3, if T = {b, v₂, x}, |T ∩ B| = |{b, v₂} ∩ {v₁, b, v₂}| + ?
                -- B = {v₁, b, v₂}, so T ∩ B = {b, v₂} if v₁ ∉ T, which has card 2. OK.
                sorry
            · -- S_e external of B
              -- T contains ≥ 2 of {v₁, b, v₂}
              -- Our cover has s(v₁, v₂) and s(v₁, b)
              sorry

        -- T shares edge with C
        · sorry

        -- T shares edge with D
        · sorry

end
