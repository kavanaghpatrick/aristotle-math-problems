/-
Tuza ν=4: Spoke Covers Externals (Slot 202)

GOAL: If v is the fan apex of A's externals, then spoke edges from v cover all externals.

STRATEGY:
  - Each external T contains the fan apex v (from slot201)
  - T also shares an edge with A, so T ∩ A ≥ 2
  - Since T is a 3-set containing v, T = {v, w₁, w₂}
  - The edge T shares with A is {v, wᵢ} for some wᵢ ∈ A (since v ∈ A too!)
  - Wait: v ∈ A ∩ T, and T shares edge with A
  - So the shared edge uses v and one other A-vertex
  - Therefore spoke {v, other_A_vertex} ∈ T.sym2

PROVEN INFRASTRUCTURE:
  - slot201: common_spoke_vertex (fan apex exists)
  - slot139: triangle_shares_edge_with_packing
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM FROM SLOT 201
-- ══════════════════════════════════════════════════════════════════════════════

axiom common_spoke_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (h_nonempty : (externalsOf G M A).Nonempty) :
    ∃ v : V, v ∈ A ∧ ∀ T ∈ externalsOf G M A, v ∈ T

-- ══════════════════════════════════════════════════════════════════════════════
-- SPOKE COVERAGE
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T shares edge with A and contains fan apex v ∈ A,
    then one of the spoke edges {v, a} where a ∈ A is in T -/
lemma spoke_in_external (A T : Finset V) (v : V)
    (hA : A.card = 3) (hT : T.card = 3)
    (h_share : sharesEdgeWith T A)
    (hv_A : v ∈ A) (hv_T : v ∈ T) :
    ∃ a : V, a ∈ A ∧ a ≠ v ∧ s(v, a) ∈ T.sym2 := by
  -- T shares edge {u, w} with A where u, w ∈ T ∩ A
  obtain ⟨u, w, huw, hu_T, hw_T, hu_A, hw_A⟩ := h_share
  -- v ∈ A ∩ T, and {u, w} ⊆ A ∩ T
  -- Either v = u, v = w, or v is a third vertex
  by_cases huv : u = v
  · -- u = v, so {v, w} is an edge in T with w ∈ A, w ≠ v
    use w
    refine ⟨hw_A, ?_, ?_⟩
    · intro heq; rw [huv] at huw; exact huw heq.symm
    · rw [Finset.mem_sym2_iff]
      exact ⟨hv_T, hw_T, by intro heq; rw [huv] at huw; exact huw heq.symm⟩
  · by_cases hwv : w = v
    · -- w = v, so {u, v} is an edge in T with u ∈ A, u ≠ v
      use u
      refine ⟨hu_A, huv, ?_⟩
      rw [Finset.mem_sym2_iff]
      exact ⟨hv_T, hu_T, huv⟩
    · -- u ≠ v and w ≠ v, so v, u, w are three vertices in T (which has 3 vertices)
      -- T = {v, u, w} and {u, w} ⊆ A
      -- So s(v, u) ∈ T.sym2 with u ∈ A
      use u
      refine ⟨hu_A, huv, ?_⟩
      rw [Finset.mem_sym2_iff]
      exact ⟨hv_T, hu_T, huv⟩

/-- The spokes from fan apex v cover all externals of A -/
theorem spoke_covers_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (v : V) (hv_A : v ∈ A)
    (hv_all : ∀ T ∈ externalsOf G M A, v ∈ T) :
    ∀ T ∈ externalsOf G M A, ∃ a ∈ A, a ≠ v ∧ s(v, a) ∈ T.sym2 := by
  intro T hT
  have hT_ext : isExternalOf G M A T := by
    simp only [externalsOf, Finset.mem_filter] at hT
    exact hT.2
  have hA_card : A.card = 3 := by
    have : A ∈ G.cliqueFinset 3 := hM.1.1 hA
    exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
  have hT_card : T.card = 3 := by
    have : T ∈ G.cliqueFinset 3 := hT_ext.1
    exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
  have hv_T := hv_all T hT
  exact spoke_in_external A T v hA_card hT_card hT_ext.2.2.1 hv_A hv_T

/-- Set of spoke edges from v to other vertices of A -/
def spokesFrom (A : Finset V) (v : V) : Finset (Sym2 V) :=
  (A.erase v).image (fun a => s(v, a))

/-- Spokes from fan apex have at most 2 edges -/
lemma spokesFrom_card (A : Finset V) (v : V) (hA : A.card = 3) (hv : v ∈ A) :
    (spokesFrom A v).card ≤ 2 := by
  simp only [spokesFrom]
  calc (A.erase v).image (fun a => s(v, a)) |>.card
      ≤ (A.erase v).card := Finset.card_image_le
    _ = A.card - 1 := Finset.card_erase_of_mem hv
    _ = 3 - 1 := by rw [hA]
    _ = 2 := by norm_num

/-- Spokes from fan apex cover all externals -/
theorem spokesFrom_covers_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (v : V) (hv_A : v ∈ A)
    (hv_all : ∀ T ∈ externalsOf G M A, v ∈ T) :
    ∀ T ∈ externalsOf G M A, ∃ e ∈ spokesFrom A v, e ∈ T.sym2 := by
  intro T hT
  obtain ⟨a, ha_A, ha_ne, ha_spoke⟩ := spoke_covers_externals G M hM hM_card hν A hA v hv_A hv_all T hT
  use s(v, a)
  constructor
  · simp only [spokesFrom, Finset.mem_image, Finset.mem_erase]
    exact ⟨a, ⟨ha_ne.symm, ha_A⟩, rfl⟩
  · exact ha_spoke

end
