/-
  slot483_spoke_extraction.lean

  FOCUSED: Extract spoke edges from bridge structure.

  Given: t bridges m1 and m2 with common vertex v
  Prove: ∃ a b, s(v,a) ∈ t.sym2 ∩ m1.sym2 and s(v,b) ∈ t.sym2 ∩ m2.sym2

  KEY INSIGHT: Since t ∩ m1 has ≥2 elements including v, there exists a ≠ v
  in t ∩ m1. The edge {v, a} is in both t.sym2 and m1.sym2.

  TIER: 2 (cardinality + membership)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Extract second element from card ≥ 2 set
-- ══════════════════════════════════════════════════════════════════════════════

/--
If S has ≥2 elements and v ∈ S, there exists a ∈ S with a ≠ v.
-/
lemma exists_other_in_card_ge_two (S : Finset V) (hcard : S.card ≥ 2) (v : V) (hv : v ∈ S) :
    ∃ a ∈ S, a ≠ v := by
  have h : (S.erase v).Nonempty := by
    have h1 : (S.erase v).card = S.card - 1 := card_erase_of_mem hv
    have h2 : S.card - 1 ≥ 1 := by omega
    rw [h1] at h2
    exact card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := h
  use a
  simp only [mem_erase] at ha
  exact ⟨ha.2, ha.1⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Edge in both t.sym2 and m.sym2
-- ══════════════════════════════════════════════════════════════════════════════

/--
If t ∩ m has ≥2 elements, there exists an edge (as Sym2) in both t.sym2 and m.sym2.

Moreover, if v ∈ t ∩ m, we can find an edge through v.
-/
lemma exists_shared_edge_through_v (t m : Finset V)
    (ht_card : t.card = 3) (hm_card : m.card = 3)
    (hshare : (t ∩ m).card ≥ 2) (v : V) (hv_t : v ∈ t) (hv_m : v ∈ m) :
    ∃ a, a ∈ t ∧ a ∈ m ∧ a ≠ v ∧ s(v, a) ∈ t.sym2 ∧ s(v, a) ∈ m.sym2 := by
  -- v ∈ t ∩ m
  have hv_inter : v ∈ t ∩ m := mem_inter.mpr ⟨hv_t, hv_m⟩
  -- t ∩ m has ≥2 elements, so there's another besides v
  obtain ⟨a, ha_inter, ha_ne⟩ := exists_other_in_card_ge_two (t ∩ m) hshare v hv_inter
  simp only [mem_inter] at ha_inter
  use a
  refine ⟨ha_inter.1, ha_inter.2, ha_ne, ?_, ?_⟩
  · -- s(v, a) ∈ t.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨hv_t, ha_inter.1⟩
  · -- s(v, a) ∈ m.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨hv_m, ha_inter.2⟩

/--
BRIDGE SPOKE EXTRACTION:
If t bridges m1 and m2 (shares ≥2 with each, with common vertex v),
then t has spoke edges {v, a} ∈ m1 and {v, b} ∈ m2.
-/
lemma bridge_has_spoke_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t m1 m2 : Finset V)
    (ht : t ∈ G.cliqueFinset 3) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (hm1_tri : m1 ∈ G.cliqueFinset 3) (hm2_tri : m2 ∈ G.cliqueFinset 3)
    (hne : m1 ≠ m2)
    (h1 : (t ∩ m1).card ≥ 2) (h2 : (t ∩ m2).card ≥ 2)
    (v : V) (hv_t : v ∈ t) (hv_m1 : v ∈ m1) (hv_m2 : v ∈ m2) :
    ∃ a b, a ∈ t ∧ b ∈ t ∧ a ≠ v ∧ b ≠ v ∧
      s(v, a) ∈ t.sym2 ∧ s(v, a) ∈ m1.sym2 ∧
      s(v, b) ∈ t.sym2 ∧ s(v, b) ∈ m2.sym2 := by
  -- Get card = 3 for all triangles
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have hm1_card : m1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hm1_tri).card_eq
  have hm2_card : m2.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hm2_tri).card_eq
  -- Extract spoke edge for m1
  obtain ⟨a, ha_t, ha_m1, ha_ne, ha_t_sym, ha_m1_sym⟩ :=
    exists_shared_edge_through_v t m1 ht_card hm1_card h1 v hv_t hv_m1
  -- Extract spoke edge for m2
  obtain ⟨b, hb_t, hb_m2, hb_ne, hb_t_sym, hb_m2_sym⟩ :=
    exists_shared_edge_through_v t m2 ht_card hm2_card h2 v hv_t hv_m2
  exact ⟨a, b, ha_t, hb_t, ha_ne, hb_ne, ha_t_sym, ha_m1_sym, hb_t_sym, hb_m2_sym⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: At least one spoke edge covers the bridge
-- ══════════════════════════════════════════════════════════════════════════════

/--
If we pick edge s(v, a) from m1 (which is in both t.sym2 and m1.sym2),
then t is covered.

This is the key insight: the spoke edge is simultaneously:
1. An edge of m1 (so we might pick it from m1)
2. An edge of t (so picking it covers t)
-/
lemma spoke_edge_covers_bridge (t m1 : Finset V) (v a : V)
    (ha_t : a ∈ t) (hv_t : v ∈ t) (hva : v ≠ a)
    (ha_t_sym : s(v, a) ∈ t.sym2) :
    s(v, a) ∈ t.sym2 := ha_t_sym  -- trivial, but makes the point

/--
MAIN COVERAGE THEOREM:
If t bridges m1 and m2, and we pick the spoke edge s(v, a) from m1,
then t is covered (since s(v, a) ∈ t.sym2).
-/
theorem bridge_covered_by_spoke (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t m1 m2 : Finset V)
    (ht : t ∈ G.cliqueFinset 3) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (hm1_tri : m1 ∈ G.cliqueFinset 3) (hm2_tri : m2 ∈ G.cliqueFinset 3)
    (hne : m1 ≠ m2)
    (h1 : (t ∩ m1).card ≥ 2) (h2 : (t ∩ m2).card ≥ 2)
    (v : V) (hv_t : v ∈ t) (hv_m1 : v ∈ m1) (hv_m2 : v ∈ m2)
    (E : Finset (Sym2 V)) (hE_sub : E ⊆ m1.sym2) :
    (∃ a ∈ t ∩ m1, a ≠ v ∧ s(v, a) ∈ E) → ∃ e ∈ E, e ∈ t.sym2 := by
  intro ⟨a, ha_inter, ha_ne, ha_E⟩
  simp only [mem_inter] at ha_inter
  use s(v, a)
  constructor
  · exact ha_E
  · rw [Finset.mem_sym2_iff]
    exact ⟨hv_t, ha_inter.1⟩

end
