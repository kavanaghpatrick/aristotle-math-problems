/-
Tuza ν ≤ 3: FIXED coveringNumberOn definition

CRITICAL FIX: coveringNumberOn now restricted to G.edgeFinset
Previous bug: allowed edges not in G
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Triangles represented as 3-element vertex sets
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3

-- Two triangles share an edge iff they share ≥ 2 vertices
def shareEdge (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

-- Edge-disjoint = pairwise share at most 1 vertex
def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  Set.Pairwise (T : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

-- T_e = triangles sharing an edge with e (share ≥ 2 vertices)
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

-- S_e = triangles sharing edge with e but NOT with any other f ∈ M
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- FIXED: coveringNumberOn restricts to G.edgeFinset
noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0

-- Parker Lemma 2.2: S_e triangles pairwise share edges
lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e) (hne : t1 ≠ t2) :
    shareEdge t1 t2 := by
  sorry

-- Pairwise sharing implies τ ≤ 2 (star or K4 structure)
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

-- When ν = 1, T_e = S_e
lemma Te_eq_Se_when_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    T_e G e = S_e G M e := by
  sorry

-- Key lemma: τ(T_e) ≤ 2 for e ∈ M when ν ≤ 3
lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Main theorem
theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  sorry

end
