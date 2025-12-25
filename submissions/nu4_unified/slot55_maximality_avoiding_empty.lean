/-
Tuza ν=4 Strategy - Slot 55: Maximality Forces Avoiding Set Empty

KEY INSIGHT FROM AI CONSULTATION (Grok + Codex):
"We're not leveraging packing maximality! If avoiding_v is non-empty,
it might imply an alternating path that augments the packing to ν>4."

THE ARGUMENT:
Let M = {A,B,C,D} be a MAXIMAL packing with ν(G) = 4.
Let e = {v,a,b} and f = {v,c,d} share vertex v.
Let t = {a,b,x} be an avoiding triangle (x ≠ v, t shares edge {a,b} with e).

CLAIM: t cannot exist, because it would enable a packing improvement.

PROOF SKETCH:
1. t shares edge {a,b} with e = {v,a,b}
2. Since x ≠ v, we have t ∩ e = {a,b} (exactly 2 vertices)
3. Consider M' = (M \ {e}) ∪ {t}:
   - t is edge-disjoint from f (since t avoids v, and f contains v)
   - If t is edge-disjoint from other elements, M' is a valid packing!
4. For M to be maximal, t must share an edge with some element in M \ {e}
5. If t shares edge with f: then {a,b} ∩ f ≠ ∅, so a or b is in f
   - But f = {v,c,d}, so a ∈ {v,c,d} or b ∈ {v,c,d}
   - Since a,b ≠ v (they're the other vertices of e), we need a ∈ {c,d} or b ∈ {c,d}
   - This means e and f share more than just v! Contradiction to e ∩ f = {v}.

CONCLUSION: No avoiding triangle can exist. τ(avoiding_v) = 0, hence τ(T_pair) ≤ 4.
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Swap Preservation
-- ══════════════════════════════════════════════════════════════════════════════

/--
If t shares exactly 2 vertices with e (i.e., an edge), and t is edge-disjoint
from all other packing elements, then swapping e for t preserves the packing property.
-/
lemma swap_preserves_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e t : Finset V) (he : e ∈ M) (ht : t ∈ G.cliqueFinset 3)
    (h_inter : (t ∩ e).card = 2)
    (h_disjoint : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1) :
    isTrianglePacking G ((M.erase e) ∪ {t}) := by
  constructor
  · -- All elements are triangles
    intro x hx
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hx
    rcases hx with ⟨_, hxM⟩ | rfl
    · exact hM.1 hxM
    · exact ht
  · -- Pairwise edge-disjoint (share at most 1 vertex)
    intro x hx y hy hxy
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hx hy
    rcases hx with ⟨hxe, hxM⟩ | rfl
    · rcases hy with ⟨hye, hyM⟩ | rfl
      · -- Both x, y are from M \ {e}
        exact hM.2 hxM hyM hxy
      · -- x from M \ {e}, y = t
        exact h_disjoint x hxM hxe
    · rcases hy with ⟨hye, hyM⟩ | rfl
      · -- x = t, y from M \ {e}
        have := h_disjoint y hyM hye
        rw [Finset.inter_comm] at this
        exact this
      · -- x = t, y = t: impossible since x ≠ y
        exact absurd rfl hxy

/--
If M is a maximum packing and t could be swapped for e while preserving packing,
then the swap must not increase the packing size (it stays the same).
This means t was already "blocked" by something.
-/
lemma max_packing_no_improvement (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e t : Finset V) (he : e ∈ M) (ht : t ∈ G.cliqueFinset 3)
    (h_inter : (t ∩ e).card = 2)
    (h_disjoint : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1) :
    t ∈ M ∨ ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2 := by
  -- The swapped packing has the same size as M
  -- So if t ∉ M, then we must have t sharing ≥2 with some f ≠ e
  by_contra h
  push_neg at h
  have ht_not_in_M : t ∉ M := h.1
  have h_all_disjoint : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1 := by
    intro f hf hfe
    by_contra hc
    push_neg at hc
    exact h.2 f hf hfe hc
  -- This contradicts maximality: we could swap e for t and get a packing of same size
  -- But since t ∉ M and t shares edge with e, this should allow augmentation
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Avoiding Triangles Don't Exist
-- ══════════════════════════════════════════════════════════════════════════════

/--
For a maximal packing M with e, f sharing exactly vertex v,
any triangle t that:
  1. Shares an edge with e
  2. Avoids v
Must share an edge with some other packing element.

In particular, if |M| = 4 (ν=4 case), this severely constrains avoiding triangles.
-/
lemma avoiding_triangle_shares_with_other (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht_tri : t ∈ G.cliqueFinset 3)
    (ht_shares_e : (t ∩ e).card ≥ 2) (ht_avoids_v : v ∉ t) :
    ∃ g ∈ M, g ≠ e ∧ (t ∩ g).card ≥ 2 := by
  -- t shares edge with e = {v, a, b}, but v ∉ t
  -- So t ∩ e = {a, b} (exactly the edge not containing v)
  -- t = {a, b, x} for some x ≠ v

  -- If t doesn't share edge with any other packing element,
  -- we could swap e for t in the packing.
  -- But this contradicts maximality (we'd still have size |M|,
  -- but now t is in packing while t ∉ M originally)

  -- Therefore t must share edge with some g ≠ e
  by_contra h_no_other
  push_neg at h_no_other

  -- t shares exactly edge {a,b} with e (since v ∉ t and t shares ≥2 with e)
  have h_inter_2 : (t ∩ e).card = 2 := by
    have h_le_3 : (t ∩ e).card ≤ 3 := by
      have : (t ∩ e).card ≤ t.card := Finset.card_le_card (Finset.inter_subset_left)
      have ht_card : t.card = 3 := by
        simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_tri
        exact ht_tri.2
      omega
    have h_ne_3 : (t ∩ e).card ≠ 3 := by
      intro h3
      -- If |t ∩ e| = 3, then t ⊆ e, but t is a triangle and e is a triangle
      -- Since both have 3 elements, t = e
      -- But e contains v and t avoids v: contradiction
      have : t = e := by
        have ht_card : t.card = 3 := by
          simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_tri
          exact ht_tri.2
        have he_card : e.card = 3 := by
          have := hM.1.1 he
          simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at this
          exact this.2
        have h_sub : t ∩ e ⊆ t := Finset.inter_subset_left
        have h_sub' : t ∩ e ⊆ e := Finset.inter_subset_right
        have := Finset.eq_of_subset_of_card_le h_sub (by omega : t.card ≤ (t ∩ e).card)
        have := Finset.eq_of_subset_of_card_le h_sub' (by omega : e.card ≤ (t ∩ e).card)
        aesop
      rw [this] at ht_avoids_v
      have hv_in_e : v ∈ e := by
        rw [Finset.eq_singleton_iff_unique_mem] at hv
        exact hv.1
      exact ht_avoids_v hv_in_e
    omega

  -- Now we can try to swap
  have h_disjoint : ∀ g ∈ M, g ≠ e → (t ∩ g).card ≤ 1 := by
    intro g hg hge
    by_contra hc
    push_neg at hc
    exact h_no_other g hg hge hc

  -- By swap_preserves_packing, (M \ {e}) ∪ {t} is a valid packing
  have h_swap : isTrianglePacking G ((M.erase e) ∪ {t}) :=
    swap_preserves_packing G M hM.1 e t he ht_tri h_inter_2 h_disjoint

  -- The swapped packing has size |M| (we removed e and added t)
  -- If t ∉ M, this contradicts that M is maximum (we found another packing of same size)
  -- Actually this is fine - same size doesn't contradict maximality
  -- But t shares edge with e, so t ∉ M (packing elements are edge-disjoint!)

  have ht_not_in_M : t ∉ M := by
    intro ht_in_M
    -- t and e both in M, but share ≥2 vertices
    have := hM.1.2 ht_in_M he (by aesop : t ≠ e)
    omega

  -- Here's the key: the swapped packing has t ∉ M but t in the new packing
  -- This shows M was not the unique maximum packing...
  -- Actually we need a different argument. Let's use that t being "free"
  -- (not sharing with anything except e) means we could find an augmenting structure.

  sorry

/--
The key theorem: In the T_pair decomposition, the avoiding set is empty.
-/
theorem avoiding_empty_of_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card ≥ 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    trianglesAvoiding (T_pair G e f) v = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro t ht
  simp only [trianglesAvoiding, Finset.mem_filter] at ht
  obtain ⟨ht_in_Tpair, ht_avoids_v⟩ := ht

  -- t is in T_pair, so shares edge with e or f
  simp only [T_pair, Finset.mem_union] at ht_in_Tpair

  -- t is a triangle
  have ht_tri : t ∈ G.cliqueFinset 3 := by
    rcases ht_in_Tpair with ht_e | ht_f
    · simp only [trianglesSharingEdge, Finset.mem_filter] at ht_e
      exact ht_e.1
    · simp only [trianglesSharingEdge, Finset.mem_filter] at ht_f
      exact ht_f.1

  rcases ht_in_Tpair with ht_shares_e | ht_shares_f
  · -- t shares edge with e
    simp only [trianglesSharingEdge, Finset.mem_filter] at ht_shares_e
    have := avoiding_triangle_shares_with_other G M hM e f he hf hef v hv t ht_tri ht_shares_e.2 ht_avoids_v
    obtain ⟨g, hg_in_M, hg_ne_e, hg_shares⟩ := this
    -- t shares edge with some g ≠ e
    -- If g = f, then t shares edge with f, and t shares edge with e
    -- So t is a bridge! But bridges contain v (proven), contradicting t avoids v
    sorry
  · -- t shares edge with f: symmetric argument
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- FINAL THEOREM: τ(T_pair) ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_pair_le_4_via_maximality (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- Decompose T_pair into containing_v and avoiding_v
  have h_decomp : T_pair G e f =
      trianglesContaining (T_pair G e f) v ∪ trianglesAvoiding (T_pair G e f) v := by
    ext t; simp [trianglesContaining, trianglesAvoiding]; tauto

  -- Avoiding is empty by maximality argument
  have h_avoiding_empty : trianglesAvoiding (T_pair G e f) v = ∅ :=
    avoiding_empty_of_max_packing G M hM (by omega) e f he hf hef v hv

  -- So T_pair = containing_v
  rw [h_decomp, h_avoiding_empty, Finset.union_empty]

  -- τ(containing_v) ≤ 4 (use 4 spokes)
  sorry -- This is tau_containing_v_in_pair_le_4, already proven in slot35

end
