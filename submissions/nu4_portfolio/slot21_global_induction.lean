/-
Tuza ν=4 Portfolio - Slot 21: Global Induction Approach

STRATEGY (from Grok + Gemini consultation):
1. Take e ∈ M (any packing triangle in max packing)
2. Find transversal S_e of T_e with |S_e| ≤ 2 (by tau_S_le_2)
3. Remove S_e from G to get G'
4. Prove: ν(G') ≤ 3 (key lemma - removing T_e's transversal drops packing number)
5. Apply ν≤3 result: τ(G') ≤ 6
6. Total: τ(G) ≤ 2 + 6 = 8 ✓

KEY INSIGHT: The transversal S_e destroys triangle e AND all triangles sharing edges with e.
Therefore, any packing M' in G' is edge-disjoint from e, so M' ∪ {e} can't be a packing
of size 5 in G (would contradict ν=4). Hence ν(G') ≤ 3.

This bypasses the messy pairwise bounds (τ ≤ 6 for sharing pairs) by using induction.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- Graph with edges removed
def graphMinusEdges (G : SimpleGraph V) (E' : Finset (Sym2 V)) : SimpleGraph V :=
  { Adj := fun u v => G.Adj u v ∧ s(u, v) ∉ E'
    symm := fun u v ⟨h1, h2⟩ => ⟨G.symm h1, by simp [Sym2.eq_swap]; exact h2⟩
    loopless := fun v h => G.loopless v h.1 }

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSUMED: τ(S_e) ≤ 2 (PROVEN by Parker, already in database)
-- ══════════════════════════════════════════════════════════════════════════════

def S (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

axiom tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S G e M) ≤ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSUMED: Tuza for ν ≤ 3 (PROVEN by Parker)
-- ══════════════════════════════════════════════════════════════════════════════

axiom tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Removing T_e's transversal reduces packing number
-- ══════════════════════════════════════════════════════════════════════════════

/-- If S_e is a transversal for T_e (triangles sharing edge with e),
    then removing S_e from G destroys e and drops ν by at least 1.

    Proof sketch: After removing S_e, triangle e is destroyed.
    Any packing M' in G' = G - S_e is edge-disjoint from e.
    But if |M'| ≥ ν(G), then M' ∪ {e} would be a larger packing in G. Contradiction. -/
lemma packing_number_drops (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M)
    (S_e : Finset (Sym2 V)) (hS_e : ∀ t ∈ trianglesSharingEdge G e, ∃ s ∈ S_e, s ∈ t.sym2)
    (hS_e_sub : S_e ⊆ G.edgeFinset) :
    trianglePackingNumber (graphMinusEdges G S_e) ≤ trianglePackingNumber G - 1 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA: τ(G) ≤ τ(T_e) + τ(G - S_e) where S_e is transversal for T_e
-- ══════════════════════════════════════════════════════════════════════════════

/-- The covering number of G is at most the size of T_e's transversal
    plus the covering number of the remaining graph. -/
lemma tau_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M)
    (S_e : Finset (Sym2 V)) (hS_e : ∀ t ∈ trianglesSharingEdge G e, ∃ s ∈ S_e, s ∈ t.sym2)
    (hS_e_sub : S_e ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S_e.card + triangleCoveringNumber (graphMinusEdges G S_e) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/-- Tuza's Conjecture for ν = 4: τ(G) ≤ 8 -/
theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  -- Get a maximum packing M
  -- Pick e ∈ M
  -- Get transversal S_e of T_e with |S_e| ≤ 2 (by tau_S_le_2)
  -- Apply packing_number_drops: ν(G - S_e) ≤ 3
  -- Apply tuza_nu_le_3: τ(G - S_e) ≤ 6
  -- Apply tau_decomposition: τ(G) ≤ |S_e| + τ(G - S_e) ≤ 2 + 6 = 8
  sorry

end
