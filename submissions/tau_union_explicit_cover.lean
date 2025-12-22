/-
Tuza ν=4: τ(T_e ∪ T_f) ≤ 4 via Explicit Cover Construction

KEY INSIGHT: We don't need to COUNT bridges. We need to COVER them.

PROVEN STRUCTURAL FACTS (from Aristotle):
1. bridges_to_f_subset_inter: Every bridge contains the shared vertex v
2. bridges_to_f_inter_card_eq_one: When bridges exist, (e ∩ f).card = 1
3. tau_S_le_2: τ(S_e) ≤ 2 for any packing element e

PROOF STRATEGY:
Let e = {v, a, b} and f = {v, c, d} where e ∩ f = {v}.

Decomposition: T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f)

Cover construction:
- τ(S_e) ≤ 2: exists 2-edge cover C_e for S_e
- τ(S_f) ≤ 2: exists 2-edge cover C_f for S_f
- X(e,f) triangles all contain v AND share edges with both e and f

KEY CLAIM: C_e ∪ C_f covers all of T_e ∪ T_f
- C_e covers S_e by definition
- C_f covers S_f by definition
- For t ∈ X(e,f): t shares edge with e, so if that edge is in C_e, t is covered
  Otherwise t shares edge with f, and if that edge is in C_f, t is covered

The only way t ∈ X(e,f) is NOT covered is if:
- t's edge with e is NOT in C_e
- t's edge with f is NOT in C_f

But X(e,f) ⊆ S_e ∪ X'(e) where X'(e) = bridges from e.
Since C_e covers S_e and t ∈ X(e,f) shares edge with e, we need to check...

Actually the overlap is subtle. Let Aristotle find the path.

Pattern: Boris Minimal with structural scaffolding
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- PROVEN (from bridge_saboteur): When bridges exist, (e ∩ f).card = 1
lemma bridges_inter_card_eq_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_nonempty : (X_ef G e f).Nonempty) :
    (e ∩ f).card = 1 := by
  sorry

-- PROVEN (from bridge_saboteur): Every bridge contains the shared vertex
lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  sorry

-- PROVEN: τ(S_e) ≤ 2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry

-- KEY: Bridges can be covered by edges at v
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry

-- STRUCTURAL: Decomposition T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) (up to some overlap)
lemma Te_Tf_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) :
    trianglesSharingEdge G e ∪ trianglesSharingEdge G f ⊆
      S_e G e M ∪ S_e G f M ∪ X_ef G e f ∪
      (trianglesSharingEdge G e).filter (fun t => ∃ g ∈ M, g ≠ e ∧ g ≠ f ∧ (t ∩ g).card ≥ 2) ∪
      (trianglesSharingEdge G f).filter (fun t => ∃ g ∈ M, g ≠ e ∧ g ≠ f ∧ (t ∩ g).card ≥ 2) := by
  sorry

-- For ν = 2 case: only e and f in packing, so no other bridges
lemma Te_Tf_eq_for_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    trianglesSharingEdge G e ∪ trianglesSharingEdge G f = S_e G e M ∪ S_e G f M ∪ X_ef G e f := by
  sorry

-- TARGET: τ(T_e ∪ T_f) ≤ 4 when e, f share exactly one vertex
theorem tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

end
