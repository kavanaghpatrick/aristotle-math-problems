/-
Tuza ν ≤ 3: Case Split by ν value (Grok strategy)

Explicit cases for ν=1, ν=2, ν=3 with structural lemmas for each.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3

def shareEdge (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  Set.Pairwise (T : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    T_e G e = S_e G M e ∪ bridges G M e := by
  ext t
  simp only [Finset.mem_union, S_e, bridges, T_e, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

lemma Te_eq_Se_when_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    T_e G e = S_e G M e := by
  ext t
  simp only [S_e, Finset.mem_filter]
  constructor
  · intro ht
    refine ⟨ht, ?_⟩
    intro f hf hne
    rw [Finset.card_eq_one] at hnu
    obtain ⟨x, hx⟩ := hnu
    simp only [hx, Finset.mem_singleton] at he hf
    exact absurd (hf.trans he.symm) hne
  · intro ⟨ht, _⟩; exact ht

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

lemma tau_Te_le_2_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  rw [Te_eq_Se_when_nu_1 G M hM hnu e he]
  exact tau_S_le_2 G M hM e he

lemma bridges_to_single_f_in_K4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (B : Finset (Finset V)) (hB : B ⊆ bridges G M e)
    (hBf : ∀ t ∈ B, (t ∩ f).card ≥ 2) :
    ∃ K : Finset V, K.card ≤ 4 ∧ ∀ t ∈ B, t ⊆ K := by
  sorry

lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  have hpos : M.card ≥ 1 := Finset.card_pos.mpr ⟨e, he⟩
  rcases Nat.lt_or_eq_of_le hnu with h | h
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · have h1 : M.card = 1 := by omega
      exact tau_Te_le_2_nu_1 G M hM h1 e he
    · exact tau_Te_le_2_nu_2 G M hM h' e he
  · exact tau_Te_le_2_nu_3 G M hM h e he

end
