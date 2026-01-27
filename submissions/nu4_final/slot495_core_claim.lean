/-
  slot495_core_claim.lean

  FOCUSED: The core combinatorial claim for τ ≤ 8.

  SETTING: G is a graph with ν(G) = 4 (max packing size is 4).
  M = {m0, m1, m2, m3} is a maximum packing.

  CLAIM: We can select ≤2 edges from each m_i such that the
  8 selected edges cover all triangles in G.

  APPROACH: Direct construction without the 6-packing argument.

  For each triangle t in G:
  - By maximality of M, t shares an edge with some m_i ∈ M
  - If t shares edges with multiple M-elements (bridge), any shared edge covers t
  - If t shares edge with exactly one m_i (external), that edge covers t

  KEY: Each M-element has ≤3 edges. If we select 2, we might miss some externals.
  RESOLUTION: The "missed" externals must be bridges (share with another M-element).

  TIER: 2 (structural argument)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

abbrev V9 := Fin 9

def mkE (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

structure Tri where
  a : V9
  b : V9
  c : V9
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  deriving DecidableEq

def Tri.e1 (t : Tri) : V9 × V9 := mkE t.a t.b
def Tri.e2 (t : Tri) : V9 × V9 := mkE t.a t.c
def Tri.e3 (t : Tri) : V9 × V9 := mkE t.b t.c
def Tri.edges (t : Tri) : Finset (V9 × V9) := {t.e1, t.e2, t.e3}

def edgeDisj (t1 t2 : Tri) : Prop := Disjoint t1.edges t2.edges

instance (t1 t2 : Tri) : Decidable (edgeDisj t1 t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

def pack4 (m0 m1 m2 m3 : Tri) : Prop :=
  edgeDisj m0 m1 ∧ edgeDisj m0 m2 ∧ edgeDisj m0 m3 ∧
  edgeDisj m1 m2 ∧ edgeDisj m1 m3 ∧ edgeDisj m2 m3

/-- Triangle t shares edge with triangle m -/
def sharesEdge (t m : Tri) : Prop := ¬edgeDisj t m

instance (t m : Tri) : Decidable (sharesEdge t m) :=
  inferInstanceAs (Decidable (¬edgeDisj t m))

-- ══════════════════════════════════════════════════════════════════════════════
-- CLASSIFICATION: Every triangle is packing, external, or bridge
-- ══════════════════════════════════════════════════════════════════════════════

/-- t is a packing element -/
def isPacking (t m0 m1 m2 m3 : Tri) : Prop :=
  t = m0 ∨ t = m1 ∨ t = m2 ∨ t = m3

/-- t is external to m (shares with m only, not with others) -/
def isExternalTo (t m m0 m1 m2 m3 : Tri) : Prop :=
  sharesEdge t m ∧
  (m = m0 → edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3) ∧
  (m = m1 → edgeDisj t m0 ∧ edgeDisj t m2 ∧ edgeDisj t m3) ∧
  (m = m2 → edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m3) ∧
  (m = m3 → edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2)

/-- t is a bridge (shares edge with 2+ M-elements) -/
def isBridge (t m0 m1 m2 m3 : Tri) : Prop :=
  (sharesEdge t m0 ∧ sharesEdge t m1) ∨
  (sharesEdge t m0 ∧ sharesEdge t m2) ∨
  (sharesEdge t m0 ∧ sharesEdge t m3) ∨
  (sharesEdge t m1 ∧ sharesEdge t m2) ∨
  (sharesEdge t m1 ∧ sharesEdge t m3) ∨
  (sharesEdge t m2 ∧ sharesEdge t m3)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Classification is complete
-- ══════════════════════════════════════════════════════════════════════════════

/--
Every triangle sharing edge with M is either:
1. A packing element (in M)
2. External to exactly one M-element
3. A bridge (shares with 2+ M-elements)
-/
lemma triangle_classification (t m0 m1 m2 m3 : Tri)
    (h : sharesEdge t m0 ∨ sharesEdge t m1 ∨ sharesEdge t m2 ∨ sharesEdge t m3) :
    isPacking t m0 m1 m2 m3 ∨
    (∃ m, (m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) ∧ isExternalTo t m m0 m1 m2 m3) ∨
    isBridge t m0 m1 m2 m3 := by
  -- Classify based on how many M-elements t shares edges with
  by_cases hb : isBridge t m0 m1 m2 m3
  · right; right; exact hb
  · -- Not a bridge, so shares with at most 1 M-element
    push_neg at hb
    unfold isBridge sharesEdge at hb
    simp only [not_or, not_and, not_not] at hb
    -- Now we know: for each pair (mi, mj), t doesn't share with both
    -- Combined with h (shares with at least one), t shares with exactly one
    rcases h with h0 | h1 | h2 | h3
    · -- t shares with m0
      have h1' := hb.1 h0
      have h2' := hb.2.1 h0
      have h3' := hb.2.2.1 h0
      right; left
      use m0
      constructor
      · left; rfl
      · constructor
        · exact h0
        · constructor
          · intro _; exact ⟨h1', h2', h3'⟩
          · constructor
            · intro h; subst h; exact ⟨h1', h2', h3'⟩
            · constructor
              · intro h; subst h; exact ⟨h1', h2', h3'⟩
              · intro h; subst h; exact ⟨h1', h2', h3'⟩
    · sorry -- Similar for m1
    · sorry -- Similar for m2
    · sorry -- Similar for m3

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: Bridges are covered by M-edges automatically
-- ══════════════════════════════════════════════════════════════════════════════

/--
A bridge shares edge with 2+ M-elements.
The shared edge is in multiple M-elements, so ANY edge from ANY of those
M-elements that we include in the cover will hit the bridge.
-/
lemma bridge_covered_by_any_shared (t m0 m1 m2 m3 mi mj : Tri)
    (hi : mi = m0 ∨ mi = m1 ∨ mi = m2 ∨ mi = m3)
    (hj : mj = m0 ∨ mj = m1 ∨ mj = m2 ∨ mj = m3)
    (hij : mi ≠ mj)
    (hbi : sharesEdge t mi) (hbj : sharesEdge t mj) :
    ∃ e ∈ mi.edges ∪ mj.edges, e ∈ t.edges := by
  -- t shares edge with mi → ∃ e ∈ t.edges ∩ mi.edges
  unfold sharesEdge edgeDisj at hbi
  simp only [Set.not_disjoint_iff] at hbi
  obtain ⟨e, he_t, he_mi⟩ := hbi
  exact ⟨e, mem_union_left _ he_mi, he_t⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: Externals are covered by their shared edge
-- ══════════════════════════════════════════════════════════════════════════════

/--
An external triangle t for m shares exactly one edge with m.
That edge covers t.
-/
lemma external_covered_by_shared (t m m0 m1 m2 m3 : Tri)
    (h : isExternalTo t m m0 m1 m2 m3) :
    ∃ e ∈ m.edges, e ∈ t.edges := by
  unfold isExternalTo sharesEdge edgeDisj at h
  obtain ⟨hshare, _, _, _, _⟩ := h
  simp only [Set.not_disjoint_iff] at hshare
  obtain ⟨e, he_t, he_m⟩ := hshare
  exact ⟨e, he_m, he_t⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: τ ≤ 12 (baseline) - every triangle covered by M-edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
All M-edges (12 edges total) cover all triangles sharing edge with M.
-/
theorem all_M_edges_cover (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∀ t : Tri, (sharesEdge t m0 ∨ sharesEdge t m1 ∨ sharesEdge t m2 ∨ sharesEdge t m3) →
      ∃ e ∈ (m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges), e ∈ t.edges := by
  intro t ht
  rcases ht with h0 | h1 | h2 | h3
  · -- t shares with m0
    unfold sharesEdge edgeDisj at h0
    simp only [Set.not_disjoint_iff] at h0
    obtain ⟨e, he_t, he_m0⟩ := h0
    exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_left _ he_m0)), he_t⟩
  · -- t shares with m1
    unfold sharesEdge edgeDisj at h1
    simp only [Set.not_disjoint_iff] at h1
    obtain ⟨e, he_t, he_m1⟩ := h1
    exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_right _ he_m1)), he_t⟩
  · -- t shares with m2
    unfold sharesEdge edgeDisj at h2
    simp only [Set.not_disjoint_iff] at h2
    obtain ⟨e, he_t, he_m2⟩ := h2
    exact ⟨e, mem_union_left _ (mem_union_right _ he_m2), he_t⟩
  · -- t shares with m3
    unfold sharesEdge edgeDisj at h3
    simp only [Set.not_disjoint_iff] at h3
    obtain ⟨e, he_t, he_m3⟩ := h3
    exact ⟨e, mem_union_right _ he_m3, he_t⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- TOWARD τ ≤ 8: Identify redundant edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
Edge e of m is "redundant" if every external for e is also covered by another edge.

CLAIM: At least 1 edge of each m is redundant (giving τ ≤ 8).
STRONGER: Exactly 1 edge per m is redundant IFF the 6-packing constraint is tight.
-/

/-- Triangles that share edge e with m but are disjoint from other M-elements -/
def externalsForEdge (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∃ t : Tri, e ∈ t.edges ∧ e ∈ m.edges ∧ t ≠ m ∧
    edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

/-- Edge e is "safe to remove" if its externals are bridges -/
def edgeSafeToRemove (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, e ∈ t.edges → e ∈ m.edges → t ≠ m →
    ¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3

/--
CLAIM: For each m ∈ M, at least one edge is safe to remove.

PROOF SKETCH (from 6-packing):
If all 3 edges have "pure" externals (disjoint from all other M-elements),
and we can find 3 pairwise-disjoint such externals, we get a 6-packing.
Contradiction with ν = 4.
Therefore, at least one edge has no pure external (all its sharers are bridges).
-/
theorem exists_safe_edge (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    edgeSafeToRemove m m.e1 m0 m1 m2 m3 ∨
    edgeSafeToRemove m m.e2 m0 m1 m2 m3 ∨
    edgeSafeToRemove m m.e3 m0 m1 m2 m3 := by
  sorry

end
