/-
Tuza ν=2: FIXED with Dichotomy Approach

The original `exists_good_packing_nu2` is FALSE - not all ν=2 graphs have vertex-disjoint packings.

Counterexample: Graph with only triangles {1,2,3} and {1,4,5} sharing vertex 1.

CORRECT APPROACH (Dichotomy):
For ν=2 with M = {e, f}:
- Case A: e and f are vertex-disjoint → use Te = Se, τ(Te) ≤ 2
- Case B: e = {v,a,b}, f = {v,c,d} share vertex v
  - Subcase B1: ∃ triangle {a,b,z} with z ∉ f → switch to vertex-disjoint packing {a,b,z}, f}
  - Subcase B2: All triangles on edge {a,b} contain v → all Te triangles contain v → τ(Te) ≤ 2

Both cases give τ(Te) ≤ 2, similarly τ(Tf) ≤ 2, so τ(G) ≤ 4 = 2ν.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

-- FIXED: Use G.edgeFinset restriction for covering number
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E
  ) |>.image Finset.card |>.min |>.getD 0

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ m ∈ M, m ≠ e → (t ∩ m).card ≤ 1)

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def vertexDisjoint (t1 t2 : Finset V) : Prop := Disjoint t1 t2

-- FIXED: Covering number restricted to actual graph edges
def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) E
  ) |>.image Finset.card |>.min |>.getD 0

-- PROVEN in 2fe95b81: For vertex-disjoint packing, T_e = S_e
lemma Te_eq_Se_of_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_disj : ∀ f ∈ M, f ≠ e → vertexDisjoint e f) :
    T_e G e = S_e G e M := by
  sorry -- Proven in 2fe95b81

-- PROVEN in 2fe95b81: If all Te triangles contain v, τ(Te) ≤ 2
lemma cover_with_v_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v a b : V) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (he_eq : e = {v, a, b})
    (h_all_v : ∀ t ∈ T_e G e, v ∈ t) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry -- Proven in 2fe95b81

-- THE KEY DICHOTOMY: For ν=2, either vertex-disjoint packing exists OR all Te contain shared vertex
lemma nu2_dichotomy (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    -- Case A: e and f are vertex-disjoint
    (vertexDisjoint e f) ∨
    -- Case B: They share exactly one vertex v, and either:
    (∃ v ∈ e ∩ f,
      -- B1: Can switch to vertex-disjoint packing
      (∃ (e' : Finset V), e' ∈ G.cliqueFinset 3 ∧
        ¬Disjoint (triangleEdges e') (triangleEdges e) ∧ vertexDisjoint e' f) ∨
      -- B2: All Te triangles contain v
      (∀ t ∈ T_e G e, v ∈ t)) := by
  sorry

-- τ(Te) ≤ 2 for some element in any max packing with ν = 2
lemma tau_Te_le_2_for_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2) :
    ∃ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Main theorem: τ ≤ 4 when ν = 2
theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4 := by
  sorry

end
