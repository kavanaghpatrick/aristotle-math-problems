/-
Tuza ν=4 Strategy - Slot 372: Two Edges Cover X and All X-Externals

DEPENDS ON:
  - slot370 (triangle_helly_vertex) - PROVEN
  - slot371 (fan_apex_exists)
  - slot182 (two_externals_share_edge) - PROVEN

THEOREM: For any M-element X, there exist 2 edges e₁, e₂ of X such that
every X-external contains e₁ or e₂.

PROOF SKETCH:
Case 1: X has 0 externals
  - Any 2 edges of X work (vacuously true)

Case 2: X has 1 external T
  - T shares some edge e with X
  - Pick e and any other edge of X
  - T contains e ✓

Case 3: X has 2 externals T₁, T₂
  - By two_externals_share_edge, T₁ and T₂ share an edge f
  - f must involve vertices of X (since both share edges with X)
  - If f is an edge of X: pick f and any other edge
  - If f is not an edge of X: both T₁, T₂ contain some vertex v of X
    Pick the two edges of X containing v

Case 4: X has ≥3 externals
  - By fan_apex_exists (slot371), all externals share a common vertex v
  - v must be in X (since externals share edges with X)
  - Pick the two edges of X containing v
  - Every external contains v, so contains one of these edges

TIER: 2 (Depends on fan_apex_exists)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangle (T : Finset V) : Prop := T.card = 3

def sharesEdgeWith (T S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ T ∧ v ∈ T ∧ u ∈ S ∧ v ∈ S

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ∉ M ∧ sharesEdgeWith T X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y

/-- An edge of a triangle X = {a,b,c} is a 2-element subset -/
def isEdgeOf (e : Finset V) (X : Finset V) : Prop :=
  e.card = 2 ∧ e ⊆ X

/-- A triangle T contains edge e if e ⊆ T -/
def containsEdge (T e : Finset V) : Prop := e ⊆ T

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Triangle edge structure
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle has exactly 3 edges -/
lemma triangle_has_three_edges (X : Finset V) (hX : X.card = 3) :
    ∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ X = {a, b, c} := by
  obtain ⟨a, ha, X', hX'_eq, hX'_card⟩ := card_eq_succ.mp hX
  obtain ⟨b, hb, X'', hX''_eq, hX''_card⟩ := card_eq_succ.mp hX'_card
  rw [card_eq_one] at hX''_card
  obtain ⟨c, hc_eq⟩ := hX''_card
  have hab : a ≠ b := by
    intro h; rw [h, hX'_eq] at ha; simp at ha
  have hbc : b ≠ c := by
    intro h; rw [h, hX''_eq, hc_eq] at hb; simp at hb
  have hac : a ≠ c := by
    intro h; rw [h, hX'_eq, hX''_eq, hc_eq] at ha; simp at ha
  refine ⟨a, b, c, hab, hbc, hac, ?_⟩
  rw [hX'_eq, hX''_eq, hc_eq]
  ext x; simp [mem_insert, mem_singleton]

/-- The three edges of triangle {a,b,c} are {a,b}, {b,c}, {a,c} -/
lemma edges_of_triangle (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    let X := ({a, b, c} : Finset V)
    let e1 := ({a, b} : Finset V)
    let e2 := ({b, c} : Finset V)
    let e3 := ({a, c} : Finset V)
    isEdgeOf e1 X ∧ isEdgeOf e2 X ∧ isEdgeOf e3 X := by
  simp only [isEdgeOf]
  constructor
  · constructor
    · simp [card_insert_of_not_mem, hab]
    · intro x; simp [mem_insert, mem_singleton]; intro h; rcases h with rfl | rfl <;> simp
  constructor
  · constructor
    · simp [card_insert_of_not_mem, hbc]
    · intro x; simp [mem_insert, mem_singleton]; intro h; rcases h with rfl | rfl <;> simp
  · constructor
    · simp [card_insert_of_not_mem, hac]
    · intro x; simp [mem_insert, mem_singleton]; intro h; rcases h with rfl | rfl <;> simp

/-- If v is a vertex of triangle X, then X has exactly 2 edges containing v -/
lemma two_edges_through_vertex (X : Finset V) (hX : X.card = 3) (v : V) (hv : v ∈ X) :
    ∃ e₁ e₂ : Finset V, e₁ ≠ e₂ ∧ isEdgeOf e₁ X ∧ isEdgeOf e₂ X ∧ v ∈ e₁ ∧ v ∈ e₂ ∧
    (∀ e, isEdgeOf e X → v ∈ e → e = e₁ ∨ e = e₂) := by
  obtain ⟨a, b, c, hab, hbc, hac, hX_eq⟩ := triangle_has_three_edges X hX
  rw [hX_eq] at hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  -- v = a: edges {a,b} and {a,c}
  · use {a, b}, {a, c}
    constructor
    · intro h; have : b ∈ ({a, c} : Finset V) := h ▸ (by simp : b ∈ ({a, b} : Finset V))
      simp at this; rcases this with rfl | rfl <;> [exact hab rfl; exact hbc.symm rfl]
    constructor
    · exact (edges_of_triangle a b c hab hbc hac).1
    constructor
    · exact (edges_of_triangle a b c hab hbc hac).2.2
    simp
  -- v = b: edges {a,b} and {b,c}
  · use {a, b}, {b, c}
    constructor
    · intro h; have : a ∈ ({b, c} : Finset V) := h ▸ (by simp : a ∈ ({a, b} : Finset V))
      simp at this; rcases this with rfl | rfl <;> [exact hab rfl; exact hac rfl]
    constructor
    · exact (edges_of_triangle a b c hab hbc hac).1
    constructor
    · exact (edges_of_triangle a b c hab hbc hac).2.1
    simp
  -- v = c: edges {b,c} and {a,c}
  · use {b, c}, {a, c}
    constructor
    · intro h; have : b ∈ ({a, c} : Finset V) := h ▸ (by simp : b ∈ ({b, c} : Finset V))
      simp at this; rcases this with rfl | rfl <;> [exact hab.symm rfl; exact hbc rfl]
    constructor
    · exact (edges_of_triangle a b c hab hbc hac).2.1
    constructor
    · exact (edges_of_triangle a b c hab hbc hac).2.2
    simp

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External contains shared edge means contains edge of X
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T shares edge with X, T contains some edge of X -/
lemma external_contains_X_edge (X T : Finset V) (hX : X.card = 3) (hT : T.card = 3)
    (h_share : sharesEdgeWith T X) :
    ∃ e, isEdgeOf e X ∧ containsEdge T e := by
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := h_share
  use {u, v}
  constructor
  · constructor
    · simp [card_insert_of_not_mem, huv]
    · intro x; simp [mem_insert, mem_singleton]
      intro h; rcases h with rfl | rfl <;> assumption
  · intro x; simp [mem_insert, mem_singleton]
    intro h; rcases h with rfl | rfl <;> assumption

-- ══════════════════════════════════════════════════════════════════════════════
-- IMPORTED THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Fan apex exists for ≥3 externals (from slot371) -/
theorem fan_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_card : externals.card ≥ 3) :
    ∃ v ∈ X, ∀ T ∈ externals, v ∈ T := by
  sorry -- From slot371

/-- Two externals share edge (from slot182) -/
theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  sorry -- Proven in slot182

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Two Edges Cover All X-Externals
-- ══════════════════════════════════════════════════════════════════════════════

/-- For any M-element X, 2 edges of X suffice to cover X and all X-externals.

PROOF SKETCH:
- If X has ≥3 externals: fan apex v exists, pick 2 edges through v
- If X has ≤2 externals: case analysis on shared structure
-/
theorem two_edges_cover_X_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T) :
    ∃ e₁ e₂ : Finset V, isEdgeOf e₁ X ∧ isEdgeOf e₂ X ∧
      (∀ T ∈ externals, containsEdge T e₁ ∨ containsEdge T e₂) := by
  sorry

/-- Corollary: X itself is covered by its own edges -/
theorem X_covered_by_own_edges (X : Finset V) (hX : X.card = 3) :
    ∃ e₁ e₂ : Finset V, isEdgeOf e₁ X ∧ isEdgeOf e₂ X ∧ containsEdge X e₁ := by
  obtain ⟨a, b, c, hab, hbc, hac, hX_eq⟩ := triangle_has_three_edges X hX
  use {a, b}, {b, c}
  constructor
  · rw [hX_eq]; exact (edges_of_triangle a b c hab hbc hac).1
  constructor
  · rw [hX_eq]; exact (edges_of_triangle a b c hab hbc hac).2.1
  · rw [hX_eq]; intro x; simp [mem_insert, mem_singleton]
    intro h; rcases h with rfl | rfl <;> simp

end
