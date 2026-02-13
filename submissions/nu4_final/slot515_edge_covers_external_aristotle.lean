/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cadb6f5f-d265-400f-9365-9743e51b7bc6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot515_edge_covers_external.lean

  SINGLE TARGET: The shared edge {a,b} = T ∩ e covers external T

  If T shares vertices a, b with e, then edge Sym2.mk a b ∈ T.sym2

  TIER: 1 (sym2 membership)
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Sym2.mk ?m.12
but this term has type
  Sym2 ?m.11

Note: Expected a function because this term is being applied to the argument
  b
Application type mismatch: The argument
  a
has type
  V
but is expected to have type
  ?m.11 × ?m.11
in the application
  Sym2.mk a
Function expected at
  Sym2.mk ?m.16
but this term has type
  Sym2 ?m.15

Note: Expected a function because this term is being applied to the argument
  b
Function expected at
  Sym2.mk ?m.23
but this term has type
  Sym2 ?m.22

Note: Expected a function because this term is being applied to the argument
  b
Application type mismatch: The argument
  a
has type
  V
but is expected to have type
  ?m.22 × ?m.22
in the application
  Sym2.mk a-/
set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: Two elements in set → edge in sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_sym2_of_mem_mem (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    Sym2.mk a b ∈ T.sym2 := by
  rw [Finset.mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Intersection membership
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_mem_left (A B : Finset V) (x : V) (hx : x ∈ A ∩ B) : x ∈ A :=
  mem_inter.mp hx |>.1

lemma inter_mem_right (A B : Finset V) (x : V) (hx : x ∈ A ∩ B) : x ∈ B :=
  mem_inter.mp hx |>.2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: card 2 gives two distinct elements
-- ══════════════════════════════════════════════════════════════════════════════

lemma card_2_two_elems (S : Finset V) (h : S.card = 2) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ S = {a, b} := by
  rw [card_eq_two] at h
  obtain ⟨a, b, hab, hs⟩ := h
  exact ⟨a, b, by rw [hs]; simp, by rw [hs]; simp, hab, hs⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: Edge from inter is in both sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_edge_in_both_sym2 (T e : Finset V) (a b : V)
    (ha : a ∈ T ∩ e) (hb : b ∈ T ∩ e) :
    Sym2.mk a b ∈ T.sym2 ∧ Sym2.mk a b ∈ e.sym2 := by
  constructor
  · exact mem_sym2_of_mem_mem T a b (inter_mem_left T e a ha) (inter_mem_left T e b hb)
  · exact mem_sym2_of_mem_mem e a b (inter_mem_right T e a ha) (inter_mem_right T e b hb)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Shared edge covers external
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. (T ∩ e).card = 2, so get a, b with T ∩ e = {a, b}
2. a ∈ T and a ∈ e (from intersection)
3. b ∈ T and b ∈ e (from intersection)
4. Sym2.mk a b ∈ T.sym2 (a, b both in T)
5. Sym2.mk a b ∈ e.sym2 (a, b both in e)
-/
theorem shared_edge_covers_external (T e : Finset V) (h_inter : (T ∩ e).card = 2) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  obtain ⟨a, b, ha, hb, hab, _⟩ := card_2_two_elems (T ∩ e) h_inter
  obtain ⟨h_in_T, h_in_e⟩ := inter_edge_in_both_sym2 T e a b ha hb
  exact ⟨Sym2.mk a b, h_in_e, h_in_T⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: For S_e externals
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

-- From slot513
axiom external_inter_card_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (hT : T ∈ S_e G M e) :
    (T ∩ e).card = 2

theorem Se_external_covered_by_e_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (hT : T ∈ S_e G M e) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  exact shared_edge_covers_external T e (external_inter_card_eq_2 G M hM e T he hT)

end