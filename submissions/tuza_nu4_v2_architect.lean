/-
Tuza ν=4: The Architect
Pure definitions, zero comments, vocabulary for Parker obstruction
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Triangle (V : Type*) where
  vertices : Finset V
  card_eq : vertices.card = 3

def Triangle.edges (t : Triangle V) : Finset (Sym2 V) :=
  t.vertices.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def Triangle.sharesEdge (t1 t2 : Triangle V) : Prop :=
  ¬Disjoint t1.edges t2.edges

structure TrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] where
  triangles : Finset (Triangle V)
  edge_disjoint : (triangles : Set (Triangle V)).PairwiseDisjoint Triangle.edges
  valid : ∀ t ∈ triangles, G.IsClique t.vertices

def TrianglePacking.size (P : TrianglePacking G) : ℕ := P.triangles.card

structure TriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] where
  edges : Finset (Sym2 V)
  covers : ∀ t : Finset V, t ∈ G.cliqueFinset 3 → ¬Disjoint (t.offDiag.image (fun x => Sym2.mk (x.1, x.2))) edges

def TriangleCover.size (C : TriangleCover G) : ℕ := C.edges.card

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Triangle V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (t.offDiag.image (fun x => Sym2.mk (x.1, x.2))) e.edges)

def maxPackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {P.size | P : TrianglePacking G}

def minCoverNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {C.size | C : TriangleCover G}

theorem tuza_nu4_architect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : maxPackingNumber G = 4) : minCoverNumber G ≤ 8 := by
  sorry

end
