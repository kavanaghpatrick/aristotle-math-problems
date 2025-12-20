/-
Tuza ν≤3: The Key Insight

For ν ≤ 3, we can always find a packing element e such that τ(T_e) ≤ 2.

The insight: Either find a vertex-disjoint packing, or the structure forces τ(T_e) ≤ 2.

For ν = 2 with e = {v,a,b}, f = {v,c,d} sharing vertex v:
- If no {a,b,z} triangle exists (z ≠ v): All T_e triangles contain v → covered by 2 edges
- If {a,b,z} exists: {a,b,z} and f are vertex-disjoint → use M' = {{a,b,z}, f}
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

def IsTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ IsTriangleCover G E}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ m ∈ M, m ≠ e → (t ∩ m).card ≤ 1)

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def vertexDisjoint (t1 t2 : Finset V) : Prop := Disjoint t1 t2

def hasVertexDisjointElement (M : Finset (Finset V)) : Prop :=
  ∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f

def allTrianglesContainVertex (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) (v : V) : Prop :=
  ∀ t ∈ S, v ∈ t

-- KEY LEMMA 1: If all triangles in a set contain vertex v, covering number ≤ 2
-- (can cover with 2 edges incident to v from a triangle containing v)
lemma tau_le_2_of_all_contain_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (e : Finset V) (he : e ∈ S) (he_card : e.card = 3)
    (v : V) (hv : v ∈ e) (h_all : allTrianglesContainVertex G S v) :
    coveringNumberOn G S ≤ 2 := by
  sorry

-- KEY LEMMA 2: For ν = 2 with shared vertex, either vertex-disjoint packing exists
-- or all T_e triangles contain the shared vertex
lemma nu2_shared_vertex_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f)
    (v : V) (hve : v ∈ e) (hvf : v ∈ f) (hshare : e ∩ f = {v}) :
    (∃ M' : Finset (Finset V), IsMaxPacking G M' ∧ M'.card = 2 ∧ hasVertexDisjointElement M') ∨
    allTrianglesContainVertex G (T_e G e) v := by
  sorry

-- KEY LEMMA 3: Vertex-disjoint element implies T_e = S_e
lemma vertex_disjoint_implies_Te_eq_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) (h_disj : ∀ f ∈ M, f ≠ e → vertexDisjoint e f) :
    T_e G e = S_e G e M := by
  sorry

-- MAIN LEMMA: For ν ≤ 3, exists e with τ(T_e) ≤ 2
lemma exists_e_tau_Te_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3) (hpos : M.Nonempty) :
    ∃ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Using tau_S_le_2 (already proven) + exists_e_tau_Te_le_2 → complete proof
theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  sorry

end
