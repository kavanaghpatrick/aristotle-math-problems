/-
slot264: cover_hits_sharing_B - ISOLATED 1-SORRY SUBMISSION

This lemma is INDEPENDENT - can be proven without the other sorries.
Goal: Prove triangles sharing ≥2 vertices with B (but ≤1 with A) are covered.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  hM_card : M.card = 4
  v1 : V
  v2 : V
  v3 : V
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅
  h_v1_A : v1 ∈ A
  h_v1_B : v1 ∈ B
  h_v2_B : v2 ∈ B
  h_v2_C : v2 ∈ C
  h_v3_C : v3 ∈ C
  h_v3_D : v3 ∈ D

/-- The explicit 8-edge cover for PATH_4 -/
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (fun e => e ∈ G.edgeFinset) ∪
  ({s(cfg.v1, cfg.v2)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  ({s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (fun e => e ∈ G.edgeFinset)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS (from Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma M_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X : Finset V) (hX : X ∈ M) : X.card = 3 := by
  have := hM.1 hX
  exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET LEMMA (1 SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any triangle sharing an edge with B (but not A) is covered via spine edge {v1, v2} -/
lemma cover_hits_sharing_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_B : (t ∩ cfg.B).card ≥ 2) (ht_not_A : (t ∩ cfg.A).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  /-
  Key insight: B = {v1, v2, b} for some third vertex b.
  t shares ≥2 vertices with B, so t contains two of {v1, v2, b}.
  t shares ≤1 vertex with A, and A ∩ B = {v1}.

  Case analysis on which two vertices of B are in t:
  - {v1, v2} ⊆ t: Then s(v1, v2) ∈ t.sym2 and s(v1, v2) is in path4_cover
  - {v1, b} ⊆ t: Since t shares ≤1 with A and v1 ∈ A, we have b ∉ A.
                 The edge {v1, b} is in B.sym2. But we need it in our cover...
                 Actually, if t = {v1, b, x} for some x, and t is a triangle,
                 we need to show some edge of t is in the cover.

  The cover includes: edges(A), {v1,v2}, {v2,v3}, edges(D).

  For {v1, v2} ⊆ t: spine edge {v1, v2} covers t. ✓

  For {v1, b} ⊆ t or {v2, b} ⊆ t where neither gives us a spine edge:
  - t must share an edge with some M-element by maximality
  - If t ∉ M and t shares {v1, b} with B, then...
  - Actually if t = B, then t ∈ M and t shares all of B with itself

  Wait, we need to handle t = B specially:
  - If t = B, then v1, v2 ∈ t, so s(v1, v2) covers it ✓

  For t ≠ B with (t ∩ B).card ≥ 2:
  - t shares edge with B
  - If {v1, v2} ⊆ t, spine covers it
  - If {v1, b} ⊆ t (and v2 ∉ t): t = {v1, b, x} for some x ∉ B
    Since t is a triangle in G, all three pairs are adjacent.
    t ∩ A contains at most v1 (since ht_not_A).
    So b ∉ A and x ∉ A.
    For this triangle to exist, we need G.Adj v1 b, G.Adj v1 x, G.Adj b x.
    The edge {v1, x} or {b, x} might help...

  Actually the key is: if t contains v1 and v2, we're done (spine edge).
  If t contains exactly one of v1, v2 plus b, then t = {v1, b, x} or {v2, b, x}.

  For {v2, b} ⊆ t: t = {v2, b, x}.
  - If x = v3, then {v2, v3} is spine edge in cover ✓
  - If x ≠ v3, need more analysis...

  This is getting complex. Let Aristotle work it out.
  -/
  sorry

end
