/-
Tuza ν=4: CYCLE_4 Case - Disjoint Petals Impossibility
Slot 112

STRATEGY (from Gemini):
Directly attack the only case that would break the Sunflower Lemma:
the existence of 4 edge-disjoint triangles sharing only vertex v.

If this is impossible in cycle_4, the Sunflower Lemma is trivial!

KEY OBSERVATION:
- The Codex counterexample has T1, T2, T3, T4 at v_ab using 4 different M-edges
- BUT they all share the non-M edge {v_ab, x}
- So they are NOT edge-disjoint!

CLAIM: In cycle_4, you CANNOT have 4 triangles at a shared vertex v
that are pairwise edge-disjoint (sharing only vertex v).

WHY: Each triangle at v must share an M-edge with A or B.
There are only 4 M-edges at v (2 from A, 2 from B).
If triangles are edge-disjoint, each uses a unique M-edge.
But then the 4 triangles would need 4 distinct "external" vertices,
and these would form a K_4 structure forcing additional packing elements.

RISK LEVEL: MEDIUM
- Proving False requires careful analysis
- If premise is actually possible, proof fails
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- M-edges incident to vertex v -/
def M_edges_at (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun X => X.sym2.filter (fun e => v ∈ e))

/-- Triangles that share an M-edge containing v -/
def trianglesSharingMEdgeAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e ∈ M_edges_at M v, e ∈ t.sym2)

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN: Every triangle shares edge with some packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  sorry -- SCAFFOLDING (maximality)

-- ══════════════════════════════════════════════════════════════════════════════
-- THE DISJOINT PETALS IMPOSSIBILITY LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/--
## No Four Disjoint Petals

In a cycle_4 configuration, it is IMPOSSIBLE to have 4 triangles at a shared
vertex v that are pairwise edge-disjoint (sharing only vertex v).

Proof sketch:
1. Assume 4 such triangles t1, t2, t3, t4 exist at v
2. They use 8 distinct edges incident to v (2 per triangle)
3. Analyze the M-edges at v: there are only 4 (2 from each adjacent element)
4. By triangle_shares_edge_with_packing, each ti shares an M-edge
5. So each ti uses exactly 1 M-edge (since they're edge-disjoint)
6. But then they must use 4 non-M edges total
7. These 4 non-M edges connect v to 4 distinct external vertices x1, x2, x3, x4
8. The 4 triangles + 4 external vertices create a structure
   that either violates ν = 4 or forces edge-sharing

This lemma, if true, guarantees that at most 3 edge-disjoint triangles
can exist at any shared vertex, immediately giving τ(at v) ≤ 3 < 4.
-/
lemma no_four_disjoint_petals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da)
    (t1 t2 t3 t4 : Finset V)
    (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (ht3 : t3 ∈ G.cliqueFinset 3) (ht4 : t4 ∈ G.cliqueFinset 3)
    (h_at_v : v ∈ t1 ∧ v ∈ t2 ∧ v ∈ t3 ∧ v ∈ t4)
    (h_shares_M : (∃ e ∈ M_edges_at M v, e ∈ t1.sym2) ∧
                  (∃ e ∈ M_edges_at M v, e ∈ t2.sym2) ∧
                  (∃ e ∈ M_edges_at M v, e ∈ t3.sym2) ∧
                  (∃ e ∈ M_edges_at M v, e ∈ t4.sym2))
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t1 ≠ t4 ∧ t2 ≠ t3 ∧ t2 ≠ t4 ∧ t3 ≠ t4)
    (h_disjoint_12 : (t1 ∩ t2).card = 1)
    (h_disjoint_13 : (t1 ∩ t3).card = 1)
    (h_disjoint_14 : (t1 ∩ t4).card = 1)
    (h_disjoint_23 : (t2 ∩ t3).card = 1)
    (h_disjoint_24 : (t2 ∩ t4).card = 1)
    (h_disjoint_34 : (t3 ∩ t4).card = 1) :
    False := by
  -- The pairwise intersection is exactly {v} since all contain v and card = 1
  -- Each triangle ti = {v, ai, bi} for distinct vertices ai, bi
  -- ti shares M-edge with A or B at v
  -- Count: 4 M-edges available, 4 triangles needing M-edges
  -- If each uses a distinct M-edge, we get a rigid structure
  -- Analyze this structure to find a contradiction
  sorry

/--
## Corollary: At Most 3 Edge-Disjoint Triangles at Any Shared Vertex

Since 4 disjoint petals is impossible, we can have at most 3.
This means at most 3 edges suffice to cover all triangles at v
(one per edge-disjoint group).

But actually, this is weaker than the sunflower lemma claims (2 edges).
The sunflower lemma uses the fact that even 3 triangles share an edge
in the cycle_4 setting.
-/
lemma at_most_three_disjoint_at_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da)
    (S : Finset (Finset V))
    (hS_triangles : S ⊆ trianglesSharingMEdgeAt G M v)
    (hS_disjoint : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card = 1) :
    S.card ≤ 3 := by
  -- If S.card ≥ 4, pick any 4 elements and apply no_four_disjoint_petals
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CONNECTION TO TAU BOUND
-- ══════════════════════════════════════════════════════════════════════════════

/--
## From Disjoint Bound to Cover Bound

If at most 3 edge-disjoint triangles exist at v, then:
- Triangles at v can be partitioned into ≤3 edge-sharing groups
- Each group shares an edge (by definition of edge-disjoint classes)
- So ≤3 edges cover all triangles at v

But we want τ ≤ 2. This requires showing that in cycle_4,
even 3 edge-disjoint triangles cannot occur, OR
that some structural property reduces the count.

The sunflower lemma handles this via the observation that
triangles in cycle_4 must share non-M edges through external vertices.
-/
lemma tau_at_v_le_3_from_disjoint_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    ∃ E : Finset (Sym2 V), E.card ≤ 3 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ trianglesSharingMEdgeAt G M v, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Partition triangles into edge-disjoint classes
  -- By at_most_three_disjoint_at_shared_vertex, ≤ 3 classes
  -- Pick one representative edge from each class
  sorry

end
