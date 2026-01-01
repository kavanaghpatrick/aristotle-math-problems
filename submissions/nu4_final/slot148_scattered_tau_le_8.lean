/-
Tuza ν=4 Strategy - Slot 148: Scattered Case τ ≤ 8

TARGET: When all 4 M-elements are pairwise vertex-disjoint (scattered),
        prove τ(G) ≤ 8.

CONTEXT:
- All three AIs (Grok, Gemini, Codex) recommend this as the easiest next win
- PROVEN infrastructure:
  - scattered_ig_empty (slot67): IG has NO edges in scattered case
  - scattered_unique_parent (slot67): Each external has unique M-element parent
  - no_bridge_disjoint (slot67): No triangle bridges disjoint M-elements
  - M_edges_card_bound (slot64b): |M_edges| ≤ 3 * |M| = 12

PROOF STRATEGY:
1. In scattered case, triangles partition by their unique parent M-element
2. Triangles owned by M-element A = {A itself} ∪ {externals sharing edge with A}
3. Key insight: A's 3 edges cover all triangles owned by A (at most 2 edges suffice)
4. Total: 4 M-elements × 2 edges each = 8 edges

WHY THIS WORKS:
- scattered_ig_empty proves no external shares edges with multiple M-elements
- So each external triangle T has exactly one parent M ∈ M
- T shares at least one edge with M (by definition of external)
- Cover: pick 2 edges from each M-element that hit all edges used by its externals

ALTERNATIVE (simpler): Since each M-element's triangles are independent,
- τ(triangles at A) ≤ 2 (any 2 of A's 3 edges form a vertex cover of A's triangles)
- By subadditivity: τ ≤ 4 × 2 = 8

STATUS: High confidence - all three AIs agree this should compile
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING FROM PROVEN SLOTS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- M is a maximum triangle packing (can't add more vertex-disjoint triangles) -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

def externalTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M ∧ ∃ e ∈ M_edges G M, e ∈ t.sym2)

/-- A triangle shares an edge with a set if some edge is in both sym2s -/
def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ e, e ∈ t.sym2 ∧ e ∈ S.sym2

/-- Triangles owned by M-element A: A itself plus externals sharing edge with A -/
def trianglesOwnedBy (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t = A ∨ (t ∉ M ∧ sharesEdgeWith t A))

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot67_bridge_absorption_PROVEN.lean)
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN by Aristotle (UUID: c522a35a): No triangle can share edge with two disjoint triangles -/
lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  have ha1_A : a₁ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h_a2_ne_b2, h_a2_ne_b1]
    · simp [h_a1_ne_b2, h_a1_ne_b1]
    · simp [ha12]
  have h_sub : ({a₁, a₂, b₁, b₂} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

/-- PROVEN by Aristotle: In scattered case, each external has unique M-element parent -/
theorem scattered_unique_parent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M)
    (A : Finset V) (hA : A ∈ M) (h_share_A : sharesEdgeWith t A) :
    ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B := by
  intro B hB hBA h_share_B
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hB)).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint A B t hA_card hB_card ht_card (h_scattered A B hA hB hBA.symm) h_share_A h_share_B

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: SCATTERED CASE COVERING BOUND
-- ══════════════════════════════════════════════════════════════════════════════

/-- An edge set covers a triangle if at least one edge of the triangle is in the set -/
def edgeSetCovers (E : Finset (Sym2 V)) (t : Finset V) : Prop :=
  ∃ e ∈ E, e ∈ t.sym2

/-- Triangle covering number: minimum edges to hit all triangles -/
def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ E ⊆ G.edgeFinset, E.card = n ∧ ∀ t ∈ G.cliqueFinset 3, edgeSetCovers E t}

/-- Key lemma: Triangles owned by A are covered by A's edges -/
lemma owned_triangles_covered_by_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∀ t ∈ trianglesOwnedBy G M A, sharesEdgeWith t A := by
  intro t ht
  simp only [trianglesOwnedBy, Finset.mem_filter] at ht
  obtain ⟨_, ht_eq_or_ext⟩ := ht
  rcases ht_eq_or_ext with rfl | ⟨_, h_share⟩
  · -- Case: t = A, so A shares all its edges with itself
    have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
    -- A has 3 elements, so A.sym2 is nonempty
    have h_ne : A.sym2.Nonempty := by
      rw [Finset.sym2_nonempty]
      omega
    obtain ⟨e, he⟩ := h_ne
    exact ⟨e, he, he⟩
  · exact h_share

/-- Key insight: Any 2 edges of a triangle cover all triangles sharing an edge with it -/
lemma two_edges_cover_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hA : A ∈ G.cliqueFinset 3)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ A.sym2) (he₂ : e₂ ∈ A.sym2) (hne : e₁ ≠ e₂) :
    ∀ t ∈ G.cliqueFinset 3, sharesEdgeWith t A →
      (e₁ ∈ t.sym2 ∨ e₂ ∈ t.sym2) := by
  intro t ht h_share
  obtain ⟨e, he_t, he_A⟩ := h_share
  -- t shares edge e with A
  -- If e = e₁ or e = e₂, we're done
  by_cases h1 : e = e₁
  · left; rw [← h1]; exact he_t
  by_cases h2 : e = e₂
  · right; rw [← h2]; exact he_t
  -- Otherwise, e is the third edge of A, and t shares it with A
  -- But t is a 3-clique, so t.sym2 has 3 elements
  -- The shared edge e ∈ t.sym2, and e ∈ A.sym2
  -- Since A is a clique, A.sym2 = {e₁, e₂, e₃} for some e₃
  -- If e ≠ e₁ and e ≠ e₂, then e = e₃
  -- Now, any triangle sharing edge e with A must contain both endpoints of e
  -- Those endpoints are 2 vertices of A
  -- Since A.sym2 = {e₁, e₂, e₃}, and e₁, e₂ share a common vertex of A
  -- (because A has 3 vertices and 3 edges form a triangle)
  -- Actually, let me think more carefully...
  -- A = {a, b, c}, A.sym2 = {s(a,b), s(b,c), s(a,c)}
  -- e₁, e₂ are two of these, e is the third
  -- t shares edge e with A, so t contains both endpoints of e
  -- But t also has a third vertex x ∉ A (since t ≠ A in the external case)
  -- Actually, in the general case t could equal A
  -- Let's use that t shares edge e, and e has 2 endpoints from A
  -- One of those endpoints is also an endpoint of e₁ or e₂
  -- (since A has 3 vertices and any two edges share a vertex)
  -- Hmm, this requires more careful reasoning about the structure
  sorry

/-- The M-edges from A form a cover of triangles owned by A -/
lemma A_edges_cover_owned (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∃ E ⊆ A.sym2, E.card ≤ 2 ∧
      ∀ t ∈ trianglesOwnedBy G M A, edgeSetCovers E t := by
  -- Pick any 2 edges of A
  have hA_clique := hM.1 hA
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hA_clique).card_eq
  have hA_sym2_card : A.sym2.card = 3 := by rw [Finset.card_sym2]; omega
  -- A.sym2 has 3 elements, so we can pick 2
  obtain ⟨e₁, he₁⟩ := A.sym2.nonempty_of_ne_empty (by
    rw [Finset.sym2_nonempty]; omega)
  have hA_sym2_card' : (A.sym2.erase e₁).card = 2 := by
    rw [Finset.card_erase_of_mem he₁, hA_sym2_card]
  obtain ⟨e₂, he₂⟩ := (A.sym2.erase e₁).nonempty_of_ne_empty (by
    intro h; rw [h] at hA_sym2_card'; omega)
  have he₂_A : e₂ ∈ A.sym2 := (Finset.mem_erase.mp he₂).2
  have hne : e₁ ≠ e₂ := fun h => (Finset.mem_erase.mp he₂).1 h.symm
  use {e₁, e₂}
  constructor
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> assumption
  constructor
  · simp [Finset.card_pair hne]
  · intro t ht
    have h_share := owned_triangles_covered_by_A G M hM A hA t ht
    unfold edgeSetCovers
    have ht_clique : t ∈ G.cliqueFinset 3 := by
      simp only [trianglesOwnedBy, Finset.mem_filter] at ht
      exact ht.1
    obtain h := two_edges_cover_sharing G A hA_clique e₁ e₂ he₁ he₂_A hne t ht_clique h_share
    rcases h with h1 | h2
    · exact ⟨e₁, Finset.mem_insert_self _ _, h1⟩
    · exact ⟨e₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h2⟩

/-- In scattered case, triangles partition by owner -/
lemma scattered_triangles_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) :
    G.cliqueFinset 3 = M.biUnion (trianglesOwnedBy G M) := by
  ext t
  constructor
  · intro ht
    -- Every triangle is owned by some M-element
    by_cases ht_M : t ∈ M
    · -- t is itself an M-element, owned by itself
      simp only [Finset.mem_biUnion]
      use t, ht_M
      simp only [trianglesOwnedBy, Finset.mem_filter]
      exact ⟨ht, Or.inl rfl⟩
    · -- t is external; by maximality, shares edge with some M-element
      have h_max := hM.2 t ht ht_M
      obtain ⟨m, hm, h_inter⟩ := h_max
      -- Intersection ≥ 2 means they share at least an edge
      have h_share : sharesEdgeWith t m := by
        have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
        have hm_card : m.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hm)).card_eq
        -- If |t ∩ m| ≥ 2, there are two common vertices, forming an edge
        have h_two : (t ∩ m).Nonempty := by
          rw [Finset.Nonempty]; omega
        obtain ⟨v, hv⟩ := h_two
        have hv_t := (Finset.mem_inter.mp hv).1
        have hv_m := (Finset.mem_inter.mp hv).2
        -- Get second vertex
        have h_two' : ((t ∩ m).erase v).Nonempty := by
          rw [Finset.card_erase_of_mem hv]
          omega
        obtain ⟨w, hw⟩ := h_two'
        have hw' := Finset.mem_erase.mp hw
        have hw_t := (Finset.mem_inter.mp hw'.2).1
        have hw_m := (Finset.mem_inter.mp hw'.2).2
        have hvw : v ≠ w := hw'.1.symm
        use s(v, w)
        constructor
        · rw [Finset.mem_sym2_iff]
          exact ⟨v, w, hvw, hv_t, hw_t, rfl⟩
        · rw [Finset.mem_sym2_iff]
          exact ⟨v, w, hvw, hv_m, hw_m, rfl⟩
      simp only [Finset.mem_biUnion]
      use m, hm
      simp only [trianglesOwnedBy, Finset.mem_filter]
      exact ⟨ht, Or.inr ⟨ht_M, h_share⟩⟩
  · intro ht
    simp only [Finset.mem_biUnion, trianglesOwnedBy, Finset.mem_filter] at ht
    exact ht.2.1

/-- MAIN THEOREM: In scattered case, τ ≤ 8 -/
theorem tau_le_8_scattered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) :
    triangleCoveringNumber G ≤ 8 := by
  -- Strategy: 2 edges per M-element, 4 M-elements → 8 edges total
  -- Each M-element A contributes 2 edges that cover trianglesOwnedBy A
  -- By partition lemma, this covers all triangles
  sorry

end
