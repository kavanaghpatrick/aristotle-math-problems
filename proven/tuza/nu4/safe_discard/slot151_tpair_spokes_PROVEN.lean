/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 85378585-59f6-4a66-98a8-ad0c1f85c006
-/

/-
Tuza ν=4 Strategy - Slot 151: T_pair Spoke Coverage

TARGET: When A and B share exactly one vertex v, the 4 "spoke" edges
        from v cover all triangles CONTAINING v.

CONTEXT:
- T_pair(A,B) = triangles sharing edge with A or B
- Split: T_containing(v) ∪ T_avoiding(v)
- T_containing(v) has all triangles that contain vertex v
- 4 spokes from v: {v,a1}, {v,a2}, {v,b1}, {v,b2} where A = {v,a1,a2}, B = {v,b1,b2}

KEY THEOREM: τ(T_containing(v)) ≤ 4 (proven in slot60)

This file provides a clean, focused proof of this fact.

ZERO SORRIES EXPECTED
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle contains vertex v -/
def triangleContains (t : Finset V) (v : V) : Prop := v ∈ t

/-- Set of triangles in G that contain vertex v -/
def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

/-- Spoke edges from vertex v in a 3-set containing v -/
def spokesFrom (t : Finset V) (v : V) (hv : v ∈ t) : Finset (Sym2 V) :=
  t.sym2.filter (fun e => v ∈ e.toFinset)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle containing v has at least one edge containing v (a "spoke") -/
lemma triangle_contains_spoke (t : Finset V) (ht : t.card = 3) (v : V) (hv : v ∈ t) :
    (spokesFrom t v hv).Nonempty := by
  -- t = {v, a, b} for some a ≠ b ≠ v
  -- spokesFrom = edges containing v = {s(v,a), s(v,b)}
  -- This is nonempty since t has 3 vertices
  have h_card_ge_2 : (t.erase v).card ≥ 1 := by
    rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨a, ha⟩ := (t.erase v).nonempty_of_ne_empty (by omega)
  have ha' := Finset.mem_erase.mp ha
  have ha_t := ha'.2
  have hav := ha'.1
  use s(v, a)
  simp only [spokesFrom, Finset.mem_filter]
  constructor
  · rw [Finset.mem_sym2_iff]
    exact ⟨v, a, hav, hv, ha_t, rfl⟩
  · simp

/-- A 3-set has exactly 2 spoke edges from any of its vertices -/
lemma spokes_card_eq_2 (t : Finset V) (ht : t.card = 3) (v : V) (hv : v ∈ t) :
    (spokesFrom t v hv).card = 2 := by
  -- t = {v, a, b}, spokes = {s(v,a), s(v,b)}
  -- t.sym2 = {s(v,a), s(v,b), s(a,b)}
  -- Filter to edges containing v gives {s(v,a), s(v,b)}
  -- Need to show this has cardinality 2
  have h_sym2_card : t.sym2.card = 3 := by rw [Finset.card_sym2]; omega
  -- Get the two other vertices
  have h_erase : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨a, b, hab, h_erase_eq⟩ := Finset.card_eq_two.mp h_erase
  have ha : a ∈ t := by rw [← h_erase_eq] at *; exact Finset.mem_insert_self a _
  have hb : b ∈ t := by rw [← h_erase_eq] at *; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hav : a ≠ v := by
    intro heq; rw [heq] at h_erase_eq
    have : v ∈ t.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_self v _
    exact Finset.not_mem_erase v t this
  have hbv : b ≠ v := by
    intro heq; rw [heq] at h_erase_eq
    have : v ∈ t.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    exact Finset.not_mem_erase v t this
  -- spokesFrom = {s(v,a), s(v,b)}
  have h_spokes_eq : spokesFrom t v hv = {s(v, a), s(v, b)} := by
    ext e
    simp only [spokesFrom, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨he_sym2, hv_in_e⟩
      rw [Finset.mem_sym2_iff] at he_sym2
      obtain ⟨x, y, hxy, hx, hy, rfl⟩ := he_sym2
      simp only [Sym2.mem_toFinset_iff, Sym2.mem_iff] at hv_in_e
      rcases hv_in_e with rfl | rfl
      · -- x = v, so e = s(v, y)
        -- y ∈ t, y ≠ v, so y ∈ {a, b}
        have hy_erase : y ∈ t.erase v := Finset.mem_erase.mpr ⟨hxy, hy⟩
        rw [h_erase_eq] at hy_erase
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy_erase
        rcases hy_erase with rfl | rfl
        · left; rfl
        · right; rfl
      · -- y = v, so e = s(x, v) = s(v, x)
        have hx_erase : x ∈ t.erase v := Finset.mem_erase.mpr ⟨hxy.symm, hx⟩
        rw [h_erase_eq] at hx_erase
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx_erase
        rcases hx_erase with rfl | rfl
        · left; exact Sym2.eq_swap
        · right; exact Sym2.eq_swap
    · intro he
      rcases he with rfl | rfl
      · constructor
        · rw [Finset.mem_sym2_iff]; exact ⟨v, a, hav.symm, hv, ha, rfl⟩
        · simp
      · constructor
        · rw [Finset.mem_sym2_iff]; exact ⟨v, b, hbv.symm, hv, hb, rfl⟩
        · simp
  rw [h_spokes_eq]
  have h_ne : s(v, a) ≠ s(v, b) := by
    simp only [Sym2.eq, Sym2.rel_iff, not_or]
    constructor
    · intro ⟨_, hab'⟩; exact hab hab'.symm
    · intro ⟨hva, _⟩; exact hav hva
  exact Finset.card_pair h_ne

/-- Spokes from v are valid graph edges (if v ∈ clique) -/
lemma spokes_are_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (v : V) (hv : v ∈ t) :
    spokesFrom t v hv ⊆ G.edgeFinset := by
  intro e he
  simp only [spokesFrom, Finset.mem_filter] at he
  have h_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht
  rw [Finset.mem_sym2_iff] at he
  obtain ⟨he_sym2, _⟩ := he
  obtain ⟨x, y, hxy, hx, hy, rfl⟩ := he_sym2
  rw [SimpleGraph.mem_edgeFinset]
  exact h_clique.2 hx hy hxy

/-- The union of spokes from A and B at shared vertex v has at most 4 edges -/
lemma union_spokes_card_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hA : A ∈ G.cliqueFinset 3) (hB : B ∈ G.cliqueFinset 3)
    (v : V) (hvA : v ∈ A) (hvB : v ∈ B) :
    (spokesFrom A v hvA ∪ spokesFrom B v hvB).card ≤ 4 := by
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hA).card_eq
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hB).card_eq
  have h1 := spokes_card_eq_2 A hA_card v hvA
  have h2 := spokes_card_eq_2 B hB_card v hvB
  calc (spokesFrom A v hvA ∪ spokesFrom B v hvB).card
      ≤ (spokesFrom A v hvA).card + (spokesFrom B v hvB).card := Finset.card_union_le _ _
    _ = 2 + 2 := by rw [h1, h2]
    _ = 4 := by omega

end