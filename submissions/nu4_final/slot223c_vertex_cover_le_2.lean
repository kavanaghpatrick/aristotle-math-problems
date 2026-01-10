/-
  slot223c_vertex_cover_le_2.lean

  LEMMA: A graph on ≤ 4 vertices with independence number ≥ 2 has vertex cover ≤ 2.

  PREVIOUS VERSION WAS FALSE!
  The old statement tried to cover edges "touching S" which can cross boundaries.

  CORRECTED VERSION:
  This is pure graph theory about VERTEX COVERS of the graph itself.
  No boundary-crossing issue because we cover the graph's own edges.

  PROOF IDEA:
  - A graph H on n ≤ 4 vertices with α(H) ≥ 2 is NOT complete (not K_n)
  - For n ≤ 4 and α ≥ 2:
    - If n ≤ 2: τ ≤ 1 ≤ 2 trivially
    - If n = 3: α ≥ 2 means at most 2 edges, so τ ≤ 2
    - If n = 4: α ≥ 2 means H ≠ K₄, so τ ≤ 2 (K₄ is the only 4-vertex graph with τ = 3)

  Alternatively: Take independent set {u, w} with u ≠ w.
  Then V \ {u, w} is a vertex cover of size n - 2 ≤ 2.

  1 SORRY: The vertex cover construction
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA (CORRECTED)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A graph with α ≥ 2 on at most 4 vertices has a vertex cover of size ≤ 2.

    KEY INSIGHT (why the old version was wrong):
    Old: "Cover all edges touching S with C ⊆ S" - FALSE for star graphs
    New: "Cover all edges of the induced subgraph H[S]" - TRUE

    PROOF:
    Let {u, w} be an independent set (exists by α ≥ 2).
    Claim: S \ {u, w} is a vertex cover.

    For any edge {a, b} in H:
    - We cannot have a = u AND b = w (since u, w are non-adjacent)
    - We cannot have a = w AND b = u (same reason)
    - So at least one of a, b is in S \ {u, w}

    Size: |S \ {u, w}| = |S| - 2 ≤ 4 - 2 = 2. ∎ -/
theorem vertex_cover_from_independence (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (hS : S.card ≤ 4)
    (h_ind : ∃ u w, u ∈ S ∧ w ∈ S ∧ u ≠ w ∧ ¬H.Adj u w) :
    ∃ C : Finset V, C.card ≤ 2 ∧ C ⊆ S ∧
      -- C is a vertex cover of H restricted to S
      ∀ a b, a ∈ S → b ∈ S → H.Adj a b → a ∈ C ∨ b ∈ C := by
  obtain ⟨u, w, hu, hw, hne, h_not_adj⟩ := h_ind
  use S \ {u, w}
  refine ⟨?_, sdiff_subset, ?_⟩
  · -- |S \ {u, w}| ≤ 2
    have h1 : ({u, w} : Finset V).card = 2 := by
      rw [card_pair hne]
    have h2 : {u, w} ⊆ S := by
      simp [hu, hw]
    calc (S \ {u, w}).card
        = S.card - ({u, w} ∩ S).card := by rw [card_sdiff_add_card]; ring
        _ = S.card - {u, w}.card := by rw [inter_eq_left.mpr h2]
        _ = S.card - 2 := by rw [h1]
        _ ≤ 4 - 2 := by omega
        _ = 2 := by norm_num
  · -- C covers all edges within S
    intro a b ha hb h_adj
    -- If both a, b ∈ {u, w}, then H.Adj a b, but u, w are non-adjacent
    by_cases ha' : a ∈ ({u, w} : Finset V)
    · by_cases hb' : b ∈ ({u, w} : Finset V)
      · -- Both in {u, w}: must be u-w edge, contradiction
        simp only [mem_insert, mem_singleton] at ha' hb'
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl (H.loopless a h_adj)
        · exact absurd h_adj h_not_adj
        · exact absurd (H.symm h_adj) h_not_adj
        · exact absurd rfl (H.loopless b h_adj)
      · -- a ∈ {u,w}, b ∉ {u,w}, so b ∈ S \ {u,w}
        right
        exact mem_sdiff.mpr ⟨hb, hb'⟩
    · -- a ∉ {u,w}, so a ∈ S \ {u,w}
      left
      exact mem_sdiff.mpr ⟨ha, ha'⟩

end
