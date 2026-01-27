/-
  slot396_no_bad_externals.lean

  Tuza ν=4 PATH_4: Externals Must Be Coverable by 8-Edge Cover

  KEY INSIGHT: If T ∈ S_B with T = {v₁, b₃, x} existed for exterior x,
  then we could potentially swap B for T in the packing, getting a
  different PATH_4 or increasing ν.

  CLAIM: For a MAXIMAL PATH_4 packing with ν=4, every external T ∈ S_B
  either:
  (a) Contains both v₁ AND v₂ (covered by spine edge), or
  (b) Shares edge with A (so T ∉ S_B by definition)

  PROOF STRATEGY:
  Suppose T = {v₁, b₃, x} ∈ S_B with x ∉ A ∪ B ∪ C ∪ D.
  Then T shares edge {v₁, b₃} with B.
  - T ∩ A = {v₁} (since x ∉ A, b₃ ∉ A)
  - T ∩ C = {} (since v₁ ∉ C, b₃ ∉ C, x ∉ C)
  - T ∩ D = {} (similar)

  Consider the packing {A, T, C, D}:
  - A ∩ T = {v₁} ✓
  - T ∩ C = {} ✓
  - C ∩ D = {v₃} ✓

  This is a valid packing! So ν ≥ 4.
  BUT: This packing is NOT PATH_4 (T and C don't share a vertex).

  This suggests: Either ν > 4, or T doesn't exist.
  Since we assume ν = 4 exactly, such T shouldn't exist.

  TIER: 2 (Structural constraint from maximality)
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

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: B-externals containing v₁ but not v₂ must overlap with A
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T ∈ S_B contains v₁ but not v₂, and T ∉ M, then T shares edge with A -/
theorem B_external_v1_only_shares_with_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₁ v₂ : V) (hv₁ : A ∩ B = {v₁}) (hv₂ : B ∩ C = {v₂})
    (T : Finset V)
    (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_not_M : T ∉ M)
    (hT_share_B : (T ∩ B).card ≥ 2)
    (hv₁_in_T : v₁ ∈ T)
    (hv₂_not_T : v₂ ∉ T)
    (hT_not_share_A : (T ∩ A).card ≤ 1)
    (hT_not_share_C : (T ∩ C).card ≤ 1)
    (hT_not_share_D : (T ∩ D).card ≤ 1) :
    False := by
  -- T = {v₁, b₃, x} for some b₃ ∈ B, x ∉ A ∪ B
  -- Since T ∩ B ≥ 2 and v₁ ∈ T ∩ B, v₂ ∉ T, there exists b₃ ∈ B \ {v₁, v₂} with b₃ ∈ T
  have hB_card : B.card = 3 := by
    have hB : B ∈ M := by rw [hpath.1]; simp
    exact (G.mem_cliqueFinset_iff.mp (hM.1 hB)).2
  have hv₁_in_B : v₁ ∈ B := by
    have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
    exact mem_of_mem_inter_right this
  have hv₂_in_B : v₂ ∈ B := by
    have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
    exact mem_of_mem_inter_left this
  -- Get the third vertex b₃ of B
  have hv₁_ne_v₂ : v₁ ≠ v₂ := by
    intro heq
    have hv₁_in_A : v₁ ∈ A := by
      have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
      exact mem_of_mem_inter_left this
    have hv₂_in_C : v₂ ∈ C := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
      exact mem_of_mem_inter_right this
    rw [heq] at hv₁_in_A
    have : v₂ ∈ A ∩ C := mem_inter.mpr ⟨hv₁_in_A, hv₂_in_C⟩
    have hAC : (A ∩ C).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.1
    rw [card_eq_zero.mp hAC] at this
    exact not_mem_empty _ this
  have hB_sdiff_card : (B \ {v₁, v₂}).card = 1 := by
    have hsub : {v₁, v₂} ⊆ B := by
      intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
    have h2 : ({v₁, v₂} : Finset V).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]; simp [hv₁_ne_v₂]
    rw [card_sdiff hsub, hB_card, h2]
  obtain ⟨b₃, hb₃_eq⟩ := card_eq_one.mp hB_sdiff_card
  have hb₃_in_B : b₃ ∈ B := by
    have : b₃ ∈ B \ {v₁, v₂} := by rw [hb₃_eq]; simp
    exact mem_of_mem_sdiff this
  have hb₃_ne_v₁ : b₃ ≠ v₁ := by
    have : b₃ ∈ B \ {v₁, v₂} := by rw [hb₃_eq]; simp
    simp at this; exact this.2.1
  have hb₃_ne_v₂ : b₃ ≠ v₂ := by
    have : b₃ ∈ B \ {v₁, v₂} := by rw [hb₃_eq]; simp
    simp at this; exact this.2.2
  -- T ∩ B ≥ 2, v₁ ∈ T ∩ B, v₂ ∉ T
  -- So T ∩ B contains v₁ and some other element of B \ {v₂} = {v₁, b₃}
  -- Since v₁ already counted, T ∩ B must contain b₃
  have hv₁_in_TB : v₁ ∈ T ∩ B := mem_inter.mpr ⟨hv₁_in_T, hv₁_in_B⟩
  have hTB_subset : T ∩ B ⊆ {v₁, b₃} := by
    intro x hx
    have hx_in_T : x ∈ T := mem_of_mem_inter_left hx
    have hx_in_B : x ∈ B := mem_of_mem_inter_right hx
    by_cases hx_v2 : x = v₂
    · rw [hx_v2] at hx_in_T; exact absurd hx_in_T hv₂_not_T
    · have hx_in_sdiff : x ∈ B \ {v₂} := mem_sdiff.mpr ⟨hx_in_B, by simp [hx_v2]⟩
      have hB_minus_v2 : B \ {v₂} = {v₁, b₃} := by
        ext z; simp
        constructor
        · intro ⟨hz_B, hz_ne_v2⟩
          by_cases hz_v1 : z = v₁
          · left; exact hz_v1
          · right
            have : z ∈ B \ {v₁, v₂} := mem_sdiff.mpr ⟨hz_B, by simp [hz_v1, hz_ne_v2]⟩
            rw [hb₃_eq] at this
            exact mem_singleton.mp this
        · intro hz
          rcases hz with rfl | rfl
          · exact ⟨hv₁_in_B, hv₁_ne_v₂⟩
          · exact ⟨hb₃_in_B, hb₃_ne_v₂⟩
      rw [hB_minus_v2] at hx_in_sdiff
      exact hx_in_sdiff
  -- T ∩ B has card ≥ 2 and is subset of {v₁, b₃} which has card ≤ 2
  have h_v1b3_card : ({v₁, b₃} : Finset V).card ≤ 2 := by
    rw [card_insert_of_not_mem, card_singleton]; simp [hb₃_ne_v₁]
  have hTB_eq : T ∩ B = {v₁, b₃} := by
    apply eq_of_subset_of_card_le hTB_subset
    calc ({v₁, b₃} : Finset V).card ≤ 2 := h_v1b3_card
      _ ≤ (T ∩ B).card := hT_share_B
  -- So b₃ ∈ T
  have hb₃_in_T : b₃ ∈ T := by
    have : b₃ ∈ T ∩ B := by rw [hTB_eq]; simp
    exact mem_of_mem_inter_left this
  -- T = {v₁, b₃, x} for some x
  have hT_card : T.card = 3 := (G.mem_cliqueFinset_iff.mp hT_tri).2
  have hT_contains_v1b3 : {v₁, b₃} ⊆ T := by
    intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  have hT_sdiff_card : (T \ {v₁, b₃}).card = 1 := by
    rw [card_sdiff hT_contains_v1b3, hT_card]
    have h2 : ({v₁, b₃} : Finset V).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]; simp [hb₃_ne_v₁]
    omega
  obtain ⟨x, hx_eq⟩ := card_eq_one.mp hT_sdiff_card
  have hx_in_T : x ∈ T := by
    have : x ∈ T \ {v₁, b₃} := by rw [hx_eq]; simp
    exact mem_of_mem_sdiff this
  have hx_ne_v₁ : x ≠ v₁ := by
    have : x ∈ T \ {v₁, b₃} := by rw [hx_eq]; simp
    simp at this; exact this.2.1
  have hx_ne_b₃ : x ≠ b₃ := by
    have : x ∈ T \ {v₁, b₃} := by rw [hx_eq]; simp
    simp at this; exact this.2.2
  -- T = {v₁, b₃, x}
  have hT_eq : T = {v₁, b₃, x} := by
    ext z; simp
    constructor
    · intro hz
      by_cases hz_v1 : z = v₁
      · left; exact hz_v1
      · by_cases hz_b3 : z = b₃
        · right; left; exact hz_b3
        · right; right
          have : z ∈ T \ {v₁, b₃} := mem_sdiff.mpr ⟨hz, by simp [hz_v1, hz_b3]⟩
          rw [hx_eq] at this
          exact mem_singleton.mp this
    · intro hz
      rcases hz with rfl | rfl | rfl <;> assumption
  -- Now check T ∩ A
  -- A ∩ B = {v₁}, so v₁ ∈ A and b₃ ∉ A
  have hv₁_in_A : v₁ ∈ A := by
    have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
    exact mem_of_mem_inter_left this
  have hb₃_not_A : b₃ ∉ A := by
    intro hb₃_A
    have : b₃ ∈ A ∩ B := mem_inter.mpr ⟨hb₃_A, hb₃_in_B⟩
    rw [hv₁] at this
    simp at this
    exact hb₃_ne_v₁ this
  -- T ∩ A = {v₁} ∪ (if x ∈ A then {x} else {})
  -- We're told T ∩ A ≤ 1, and v₁ ∈ T ∩ A, so T ∩ A = {v₁}
  have hv₁_in_TA : v₁ ∈ T ∩ A := mem_inter.mpr ⟨hv₁_in_T, hv₁_in_A⟩
  have hTA_eq_v1 : T ∩ A = {v₁} := by
    apply eq_of_subset_of_card_le _ (by simp; exact hT_not_share_A)
    intro z hz
    simp
    have hz_T : z ∈ T := mem_of_mem_inter_left hz
    have hz_A : z ∈ A := mem_of_mem_inter_right hz
    rw [hT_eq] at hz_T
    simp at hz_T
    rcases hz_T with rfl | rfl | rfl
    · rfl
    · exact absurd hz_A hb₃_not_A
    · -- z = x ∈ A, but then T ∩ A ⊇ {v₁, x} has card ≥ 2, contradiction
      have hx_in_A : x ∈ A := hz_A
      have h2 : ({v₁, x} : Finset V).card = 2 := by
        rw [card_insert_of_not_mem, card_singleton]; simp [hx_ne_v₁]
      have hsub : {v₁, x} ⊆ T ∩ A := by
        intro w hw; simp at hw
        rcases hw with rfl | rfl
        · exact hv₁_in_TA
        · exact mem_inter.mpr ⟨hx_in_T, hx_in_A⟩
      have : (T ∩ A).card ≥ 2 := by
        calc (T ∩ A).card ≥ ({v₁, x} : Finset V).card := card_le_card hsub
          _ = 2 := h2
      omega
  -- So x ∉ A
  have hx_not_A : x ∉ A := by
    intro hx_A
    have : x ∈ T ∩ A := mem_inter.mpr ⟨hx_in_T, hx_A⟩
    rw [hTA_eq_v1] at this
    simp at this
    exact hx_ne_v₁ this
  -- Similarly, x ∉ B (since T ∩ B = {v₁, b₃})
  have hx_not_B : x ∉ B := by
    intro hx_B
    have : x ∈ T ∩ B := mem_inter.mpr ⟨hx_in_T, hx_B⟩
    rw [hTB_eq] at this
    simp at this
    rcases this with rfl | rfl
    · exact hx_ne_v₁ rfl
    · exact hx_ne_b₃ rfl
  -- x ∉ C (since T ∩ C ≤ 1 and we need to check)
  have hv₂_in_C : v₂ ∈ C := by
    have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
    exact mem_of_mem_inter_right this
  have hv₁_not_C : v₁ ∉ C := by
    intro hv₁_C
    have : v₁ ∈ A ∩ C := mem_inter.mpr ⟨hv₁_in_A, hv₁_C⟩
    have hAC : (A ∩ C).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.1
    rw [card_eq_zero.mp hAC] at this
    exact not_mem_empty _ this
  have hb₃_not_C : b₃ ∉ C := by
    intro hb₃_C
    have : b₃ ∈ B ∩ C := mem_inter.mpr ⟨hb₃_in_B, hb₃_C⟩
    rw [hv₂] at this
    simp at this
    exact hb₃_ne_v₂ this
  -- T ∩ C: v₁ ∉ C, b₃ ∉ C, so T ∩ C ⊆ {x} ∩ C
  have hTC_subset : T ∩ C ⊆ {x} := by
    intro z hz
    have hz_T : z ∈ T := mem_of_mem_inter_left hz
    have hz_C : z ∈ C := mem_of_mem_inter_right hz
    rw [hT_eq] at hz_T; simp at hz_T
    rcases hz_T with rfl | rfl | rfl
    · exact absurd hz_C hv₁_not_C
    · exact absurd hz_C hb₃_not_C
    · simp
  -- So x ∉ C (otherwise T ∩ C = {x} has card 1, which is fine... wait)
  -- Actually T ∩ C ≤ 1 is already assumed, so x could be in C
  -- Let me check D
  have hv₃_in_C : v₃ ∈ C := by
    have : v₃ ∈ C ∩ D := by rw [hpath.2.2.2.2.2.2.2.2.2.1 |> card_eq_one.mp |>.choose_spec]; simp
    sorry -- Need to extract v₃
  sorry -- The full argument needs more structure

end
