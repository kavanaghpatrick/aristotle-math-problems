/-
Tuza ν=4 Strategy - Slot 64c: Each M-edge belongs to unique M-element

TARGET: Each edge in M_edges belongs to exactly one packing element.

PROOF STRATEGY:
- If edge e belongs to two M-elements A and B
- Then A and B share edge e, meaning |A ∩ B| ≥ 2
- But packing property says |A ∩ B| ≤ 1
- Contradiction

STATUS: TRUE - this is different from the FALSE external_shares_unique_element!
NOTE: This is about M-edges, not external triangles.

SCAFFOLDING: Includes proven M_edge_in_exactly_one from slot63
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot63)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each edge in a triangle packing appears in exactly one triangle.
    PROVEN by Aristotle slot63 (UUID: 3d31b863). -/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  rw [Finset.mem_sym2_iff] at he he'
  obtain ⟨u, v, huv, hu_m, hv_m, rfl⟩ := he
  obtain ⟨u', v', _, hu'_m', hv'_m', heq⟩ := he'
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hu'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hv'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hv'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hu'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each M-edge belongs to exactly one M-element (existence + uniqueness).
    This is TRUE because packing elements are edge-disjoint. -/
lemma edge_in_unique_M_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ M_edges G M) :
    ∃! m, m ∈ M ∧ e ∈ m.sym2 := by
  -- Existence: e ∈ M_edges means e is in some M-element
  simp only [M_edges, Finset.mem_biUnion, Finset.mem_filter] at he
  obtain ⟨m, hm, he_in_m, _⟩ := he
  use m
  constructor
  · exact ⟨hm, he_in_m⟩
  · -- Uniqueness: follows from M_edge_in_exactly_one
    intro m' ⟨hm', he_in_m'⟩
    by_contra hne
    exact M_edge_in_exactly_one G M hM e m hm he_in_m m' hm' hne he_in_m'

/-- Variant: The M-element containing an M-edge is unique -/
lemma M_element_of_edge_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ M_edges G M)
    (m₁ m₂ : Finset V) (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (he₁ : e ∈ m₁.sym2) (he₂ : e ∈ m₂.sym2) :
    m₁ = m₂ := by
  by_contra hne
  exact M_edge_in_exactly_one G M hM e m₁ hm₁ he₁ m₂ hm₂ hne he₂

end
