/-
slot58: Focus on M_edge_in_exactly_one

This is the ONLY remaining gap for τ ≤ 8 in Cycle_4.

PROVEN in slot147_v2 (UUID f38edf58):
- triangle_shares_edge_with_packing
- M_char_is_fractional
- M_char_weight_eq_4
- nu_star_le_4

REMAINING: M_edge_in_exactly_one
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- If two distinct triangles share an edge {u,v}, they share at least 2 vertices.
    But edge-disjoint packings have intersection ≤ 1.
    Therefore, no two triangles in a packing share an edge. -/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  -- If e = {u, v} is in both m.sym2 and m'.sym2, then u, v ∈ m ∩ m'
  obtain ⟨u, v⟩ := e
  -- u and v are both in m (since e ∈ m.sym2)
  have hu_m : u ∈ m := by
    simp only [Finset.mem_sym2, Sym2.mem_iff] at he
    exact he.1.elim id id
  have hv_m : v ∈ m := by
    simp only [Finset.mem_sym2, Sym2.mem_iff] at he
    exact he.2.elim id id
  -- u and v are both in m' (since e ∈ m'.sym2)
  have hu_m' : u ∈ m' := by
    simp only [Finset.mem_sym2, Sym2.mem_iff] at he'
    exact he'.1.elim id id
  have hv_m' : v ∈ m' := by
    simp only [Finset.mem_sym2, Sym2.mem_iff] at he'
    exact he'.2.elim id id
  -- Therefore u, v ∈ m ∩ m'
  have hu_inter : u ∈ m ∩ m' := Finset.mem_inter.mpr ⟨hu_m, hu_m'⟩
  have hv_inter : v ∈ m ∩ m' := Finset.mem_inter.mpr ⟨hv_m, hv_m'⟩
  -- Since m and m' are distinct elements of the packing, (m ∩ m').card ≤ 1
  have h_inter : (m ∩ m').card ≤ 1 := hM.2 hm hm' hne
  -- But we have u, v ∈ m ∩ m', and u ≠ v (since e is an edge in the graph)
  -- First, let's get that e is actually an edge (u ≠ v)
  have he_edge : e ∈ G.edgeFinset := by
    -- m is a triangle in G, so its edges are in G.edgeFinset
    have hm_clique := hM.1 hm
    have := SimpleGraph.mem_cliqueFinset_iff.mp hm_clique
    -- e ∈ m.sym2, so e is an edge of the clique m
    sorry -- edges of a clique are graph edges
  have huv_ne : u ≠ v := by
    have := SimpleGraph.not_isDiag_of_mem_edgeFinset he_edge
    simp only [Sym2.isDiag_iff_proj_eq] at this
    exact this
  -- Now we have u ≠ v, u ∈ m ∩ m', v ∈ m ∩ m', but (m ∩ m').card ≤ 1
  -- This is a contradiction
  have h_two : 2 ≤ (m ∩ m').card := by
    apply Finset.one_lt_card.mp
    exact ⟨u, hu_inter, v, hv_inter, huv_ne⟩
  omega

/-- Alternative formulation using the pairwise edge-disjoint property directly -/
lemma M_edge_in_exactly_one' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  -- Edge in both triangles means at least 2 shared vertices
  rcases e with ⟨u, v⟩
  simp only [Finset.mem_sym2, Sym2.mem_iff] at he he'
  have h_inter_card : 2 ≤ (m ∩ m').card := by
    refine Finset.one_lt_card.mp ⟨u, ?_, v, ?_, ?_⟩
    · exact Finset.mem_inter.mpr ⟨he.1.elim id id, he'.1.elim id id⟩
    · exact Finset.mem_inter.mpr ⟨he.2.elim id id, he'.2.elim id id⟩
    · -- u ≠ v because m is a triangle (card 3) in the graph
      have hm_clique := hM.1 hm
      have hm_card := (SimpleGraph.mem_cliqueFinset_iff.mp hm_clique).card_eq
      -- If u = v, then {u, v} = {u}, but triangles have 3 distinct vertices
      intro huv
      subst huv
      -- m.sym2 contains only proper pairs from a 3-element set
      -- Actually sym2 includes diagonal, so need to exclude
      simp only [Finset.mem_sym2] at he
      -- he says u ∈ m and u ∈ m, which is fine
      -- The issue is that {u,u} should not be a valid edge
      sorry -- need: e ∈ m.sym2 with m a triangle implies u ≠ v
  -- Contradiction with packing property
  have h_packing := hM.2 hm hm' hne
  omega

end
