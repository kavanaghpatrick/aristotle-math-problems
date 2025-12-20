/-
Tuza ν=2: Direct Proof

Key insight: For ν=2 with M = {e, f}, either:
1. e, f vertex-disjoint → T_e = S_e → τ(T_e) ≤ 2
2. e, f share vertex v → either find vertex-disjoint packing OR all T_e triangles contain v

Case 2 detail: If e = {v,a,b}, f = {v,c,d} share vertex v:
- T_e \ S_e = triangles sharing ≥2 vertices with BOTH e and f
- These must contain v (the only shared vertex)
- If {a,b,z} exists for z ≠ v, then {a,b,z} is vertex-disjoint from f
- Use M' = {{a,b,z}, f} as vertex-disjoint packing
- Otherwise, no {a,b,z} exists, so ALL triangles in T_e contain v
- Triangles containing v are covered by 2 edges incident to v
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ (M : Set (Finset V)).PairwiseDisjoint (fun t => t.offDiag.image (fun x => Sym2.mk (x.1, x.2)))

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

-- For ν=2, every triangle shares an edge with e or f
lemma nu2_all_triangles_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    ∀ t ∈ G.cliqueFinset 3, (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2 := by
  sorry

-- If e, f are vertex-disjoint and share a vertex with some triangle t,
-- t can share edge with at most one of them
lemma vertex_disjoint_share_exclusive (e f t : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint e f) :
    ¬((t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2) := by
  sorry

-- Key: If all triangles with edge in e contain vertex v, cover with 2 edges
lemma cover_through_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v : V) (hv : v ∈ e)
    (h_all : ∀ t ∈ T_e G e, v ∈ t) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ T_e G e, ∃ edge ∈ E, edge ∈ t.sym2 := by
  sorry

-- Main theorem: τ ≤ 4 when ν = 2
theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4 := by
  sorry

end
