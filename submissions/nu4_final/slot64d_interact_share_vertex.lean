/-
Tuza ν=4 Strategy - Slot 64d: Interacting Edges Share a Vertex

TARGET: If two M-edges interact, they share a vertex.

PROOF STRATEGY:
- Two edges interact iff they both appear in some external triangle T
- T has 3 vertices, so any two edges in T share at least one vertex
- This is because edges are pairs of vertices from the same 3-set

STATUS: TRUE - verified by all three AIs
This is KEY for bounding interaction graph degree!
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

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

def externalTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M ∧ ∃ e ∈ M_edges G M, e ∈ t.sym2)

def edgesInteract (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (e₁ e₂ : Sym2 V) : Prop :=
  e₁ ≠ e₂ ∧
  e₁ ∈ M_edges G M ∧
  e₂ ∈ M_edges G M ∧
  ∃ t ∈ externalTriangles G M, e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2

def InteractionGraph (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) :
    SimpleGraph (Sym2 V) where
  Adj := edgesInteract G M
  symm := by
    intro e₁ e₂ ⟨hne, he₁, he₂, t, ht, ht₁, ht₂⟩
    exact ⟨hne.symm, he₂, he₁, t, ht, ht₂, ht₁⟩
  loopless := by
    intro e ⟨hne, _, _, _, _, _, _⟩
    exact hne rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Two edges in a 3-set share a vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two distinct edges in a triangle's sym2 share a vertex.
    This is because a triangle has 3 vertices, and any two edges
    from 3 vertices must share one. -/
lemma edges_in_triangle_share_vertex (t : Finset V) (ht : t.card = 3)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ t.sym2) (he₂ : e₂ ∈ t.sym2) (hne : e₁ ≠ e₂) :
    ∃ v ∈ t, v ∈ e₁.toFinset ∧ v ∈ e₂.toFinset := by
  -- t has 3 vertices, e₁ and e₂ are each pairs from t
  -- Any two pairs from a 3-set share exactly one element
  rw [Finset.mem_sym2_iff] at he₁ he₂
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := he₁
  obtain ⟨c, d, hcd, hc, hd, rfl⟩ := he₂
  -- Direct case analysis: check if any vertex is shared
  by_cases h1 : a = c
  · exact ⟨a, ha, by simp, by simp [h1]⟩
  by_cases h2 : a = d
  · exact ⟨a, ha, by simp, by simp [h2]⟩
  by_cases h3 : b = c
  · exact ⟨b, hb, by simp, by simp [h3]⟩
  by_cases h4 : b = d
  · exact ⟨b, hb, by simp, by simp [h4]⟩
  -- All four are distinct, so {a,b,c,d} has 4 elements but ⊆ t which has 3
  exfalso
  have h_four : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h4, h3]
    · simp [h2, h1]
    · simp [hab]
  have h_sub : ({a, b, c, d} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- If two M-edges interact, they share a vertex.
    This is crucial for bounding the degree in the Interaction Graph. -/
lemma interact_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : (InteractionGraph G M).Adj e₁ e₂) :
    ∃ v, v ∈ e₁.toFinset ∧ v ∈ e₂.toFinset := by
  obtain ⟨hne, _, _, t, ht, ht₁, ht₂⟩ := h
  -- t is an external triangle, so t ∈ G.cliqueFinset 3
  simp only [externalTriangles, Finset.mem_filter] at ht
  have ht_clique := ht.1
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht_clique).card_eq
  -- Use the helper lemma
  obtain ⟨v, hv_in_t, hv_e1, hv_e2⟩ := edges_in_triangle_share_vertex t ht_card e₁ e₂ ht₁ ht₂ hne
  exact ⟨v, hv_e1, hv_e2⟩

/-- Corollary: Interacting edges can be written as sharing a vertex -/
lemma interact_common_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : (InteractionGraph G M).Adj e₁ e₂) :
    ∃ v a b, e₁ = s(v, a) ∧ e₂ = s(v, b) := by
  obtain ⟨v, hv₁, hv₂⟩ := interact_share_vertex G M e₁ e₂ h
  -- e₁ = s(v, a) for some a
  rw [Sym2.mem_toFinset_iff] at hv₁ hv₂
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := Sym2.mem_iff.mp hv₁
  · obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := Sym2.mem_iff.mp hv₂
    · exact ⟨v, a, b, rfl, rfl⟩
    · exact ⟨v, a, b, rfl, Sym2.eq_swap⟩
  · obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := Sym2.mem_iff.mp hv₂
    · exact ⟨v, a, b, Sym2.eq_swap, rfl⟩
    · exact ⟨v, a, b, Sym2.eq_swap, Sym2.eq_swap⟩

end
