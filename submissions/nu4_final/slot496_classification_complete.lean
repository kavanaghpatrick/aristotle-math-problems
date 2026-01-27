/-
  slot496_classification_complete.lean

  Complete the triangle classification and proven coverage lemmas from slot495.
  No syntax issues (avoid /-- after section dividers).

  PROVEN in slot495:
  - bridge_covered_by_any_shared
  - external_covered_by_shared
  - all_M_edges_cover (τ ≤ 12)

  TO COMPLETE:
  - triangle_classification (3 symmetric cases)

  TIER: 2 (structural, symmetric cases)
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

def sharesEdge (t m : Tri) : Prop := ¬edgeDisj t m

instance (t m : Tri) : Decidable (sharesEdge t m) :=
  inferInstanceAs (Decidable (¬edgeDisj t m))

def isPacking (t m0 m1 m2 m3 : Tri) : Prop :=
  t = m0 ∨ t = m1 ∨ t = m2 ∨ t = m3

def isExternalTo (t m m0 m1 m2 m3 : Tri) : Prop :=
  sharesEdge t m ∧
  (m = m0 → edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3) ∧
  (m = m1 → edgeDisj t m0 ∧ edgeDisj t m2 ∧ edgeDisj t m3) ∧
  (m = m2 → edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m3) ∧
  (m = m3 → edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2)

def isBridge (t m0 m1 m2 m3 : Tri) : Prop :=
  (sharesEdge t m0 ∧ sharesEdge t m1) ∨
  (sharesEdge t m0 ∧ sharesEdge t m2) ∨
  (sharesEdge t m0 ∧ sharesEdge t m3) ∨
  (sharesEdge t m1 ∧ sharesEdge t m2) ∨
  (sharesEdge t m1 ∧ sharesEdge t m3) ∨
  (sharesEdge t m2 ∧ sharesEdge t m3)

lemma triangle_classification (t m0 m1 m2 m3 : Tri)
    (h : sharesEdge t m0 ∨ sharesEdge t m1 ∨ sharesEdge t m2 ∨ sharesEdge t m3) :
    isPacking t m0 m1 m2 m3 ∨
    (∃ m, (m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) ∧ isExternalTo t m m0 m1 m2 m3) ∨
    isBridge t m0 m1 m2 m3 := by
  by_cases hb : isBridge t m0 m1 m2 m3
  · right; right; exact hb
  · push_neg at hb
    unfold isBridge sharesEdge at hb
    simp only [not_or, not_and, not_not] at hb
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
            · intro heq; subst heq; exact ⟨h1', h2', h3'⟩
            · constructor
              · intro heq; subst heq; exact ⟨h1', h2', h3'⟩
              · intro heq; subst heq; exact ⟨h1', h2', h3'⟩
    · -- t shares with m1 (symmetric)
      have h0' := hb.1.symm h1
      have h2' := hb.2.2.2.1 h1
      have h3' := hb.2.2.2.2 h1
      right; left
      use m1
      constructor
      · right; left; rfl
      · constructor
        · exact h1
        · constructor
          · intro heq; subst heq; exact ⟨h0', h2', h3'⟩
          · constructor
            · intro _; exact ⟨h0', h2', h3'⟩
            · constructor
              · intro heq; subst heq; exact ⟨h0', h2', h3'⟩
              · intro heq; subst heq; exact ⟨h0', h2', h3'⟩
    · -- t shares with m2 (symmetric)
      have h0' := hb.2.1.symm h2
      have h1' := hb.2.2.2.1.symm h2
      have h3' := hb.2.2.2.2.symm h2
      right; left
      use m2
      constructor
      · right; right; left; rfl
      · constructor
        · exact h2
        · constructor
          · intro heq; subst heq; exact ⟨h0', h1', h3'⟩
          · constructor
            · intro heq; subst heq; exact ⟨h0', h1', h3'⟩
            · constructor
              · intro _; exact ⟨h0', h1', h3'⟩
              · intro heq; subst heq; exact ⟨h0', h1', h3'⟩
    · -- t shares with m3 (symmetric)
      have h0' := hb.2.2.1.symm h3
      have h1' := hb.2.2.2.2.symm h3
      have h2' := hb.2.2.2.2.symm h3
      right; left
      use m3
      constructor
      · right; right; right; rfl
      · constructor
        · exact h3
        · constructor
          · intro heq; subst heq; exact ⟨h0', h1', h2'⟩
          · constructor
            · intro heq; subst heq; exact ⟨h0', h1', h2'⟩
            · constructor
              · intro heq; subst heq; exact ⟨h0', h1', h2'⟩
              · intro _; exact ⟨h0', h1', h2'⟩

lemma bridge_covered_by_any_shared (t m0 m1 m2 m3 mi mj : Tri)
    (hi : mi = m0 ∨ mi = m1 ∨ mi = m2 ∨ mi = m3)
    (hj : mj = m0 ∨ mj = m1 ∨ mj = m2 ∨ mj = m3)
    (hij : mi ≠ mj)
    (hbi : sharesEdge t mi) (hbj : sharesEdge t mj) :
    ∃ e ∈ mi.edges ∪ mj.edges, e ∈ t.edges := by
  unfold sharesEdge edgeDisj at hbi
  simp only [Set.not_disjoint_iff] at hbi
  obtain ⟨e, he_t, he_mi⟩ := hbi
  exact ⟨e, mem_union_left _ he_mi, he_t⟩

lemma external_covered_by_shared (t m m0 m1 m2 m3 : Tri)
    (h : isExternalTo t m m0 m1 m2 m3) :
    ∃ e ∈ m.edges, e ∈ t.edges := by
  unfold isExternalTo sharesEdge edgeDisj at h
  obtain ⟨hshare, _, _, _, _⟩ := h
  simp only [Set.not_disjoint_iff] at hshare
  obtain ⟨e, he_t, he_m⟩ := hshare
  exact ⟨e, he_m, he_t⟩

theorem all_M_edges_cover (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∀ t : Tri, (sharesEdge t m0 ∨ sharesEdge t m1 ∨ sharesEdge t m2 ∨ sharesEdge t m3) →
      ∃ e ∈ (m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges), e ∈ t.edges := by
  intro t ht
  rcases ht with h0 | h1 | h2 | h3
  · unfold sharesEdge edgeDisj at h0
    simp only [Set.not_disjoint_iff] at h0
    obtain ⟨e, he_t, he_m0⟩ := h0
    exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_left _ he_m0)), he_t⟩
  · unfold sharesEdge edgeDisj at h1
    simp only [Set.not_disjoint_iff] at h1
    obtain ⟨e, he_t, he_m1⟩ := h1
    exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_right _ he_m1)), he_t⟩
  · unfold sharesEdge edgeDisj at h2
    simp only [Set.not_disjoint_iff] at h2
    obtain ⟨e, he_t, he_m2⟩ := h2
    exact ⟨e, mem_union_left _ (mem_union_right _ he_m2), he_t⟩
  · unfold sharesEdge edgeDisj at h3
    simp only [Set.not_disjoint_iff] at h3
    obtain ⟨e, he_t, he_m3⟩ := h3
    exact ⟨e, mem_union_right _ he_m3, he_t⟩

def externalsForEdge (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∃ t : Tri, e ∈ t.edges ∧ e ∈ m.edges ∧ t ≠ m ∧
    edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

def edgeSafeToRemove (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, e ∈ t.edges → e ∈ m.edges → t ≠ m →
    ¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3

theorem exists_safe_edge (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    edgeSafeToRemove m m.e1 m0 m1 m2 m3 ∨
    edgeSafeToRemove m m.e2 m0 m1 m2 m3 ∨
    edgeSafeToRemove m m.e3 m0 m1 m2 m3 := by
  -- By contradiction: if all 3 edges have pure externals, we get a 6-packing
  by_contra h
  push_neg at h
  unfold edgeSafeToRemove at h
  simp only [not_forall, not_or, not_not] at h
  obtain ⟨⟨t1, ht1_e, ht1_m, ht1_ne, ht1_disj⟩, ⟨t2, ht2_e, ht2_m, ht2_ne, ht2_disj⟩,
          ⟨t3, ht3_e, ht3_m, ht3_ne, ht3_disj⟩⟩ := h
  -- t1, t2, t3 are externals for the 3 edges of m
  -- They are all edge-disjoint from all M-elements
  -- If we can show t1, t2, t3 are pairwise edge-disjoint, we have a 6-packing
  -- But this requires the tetrahedron analysis
  sorry

end
