/-
  slot479_triangle_homing_focused.lean

  FOCUSED: Prove that every triangle is covered by an 8-edge set.

  KEY INSIGHT: The issue with S_e is that bridges aren't in any S_e.
  But bridges share a common vertex with the M-elements they bridge.

  APPROACH: Instead of partitioning into S_e sets, show directly that
  every triangle shares an edge with some M-element, and our cover
  includes enough edges from each M-element.

  The cover construction:
  - For each e ∈ M, pick 2 edges of e (from the 6-packing constraint).
  - Total: 4 × 2 = 8 edges.

  Coverage argument:
  - By maximality, every triangle t shares ≥2 vertices with some m ∈ M.
  - So t shares at least one EDGE with m.
  - If that edge is among the 2 we picked for m, done.
  - If not, we need the 6-packing constraint to help.

  TIER: 2 (cardinality + case analysis)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangle sharing ≥2 vertices shares an edge
-- ══════════════════════════════════════════════════════════════════════════════

/--
If two triangles share ≥2 vertices, they share an edge (as Sym2 elements).

PROOF SKETCH:
1. t and m both have 3 vertices
2. |t ∩ m| ≥ 2 means they share ≥2 vertices
3. Those 2 vertices form an edge {a, b}
4. Since both are cliques, edge s(a,b) is in both t.sym2 and m.sym2
-/
lemma share_ge2_implies_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t m : Finset V) (ht : t ∈ G.cliqueFinset 3) (hm : m ∈ G.cliqueFinset 3)
    (hshare : (t ∩ m).card ≥ 2) :
    ∃ e : Sym2 V, e ∈ t.sym2 ∧ e ∈ m.sym2 ∧ e ∈ G.edgeFinset := by
  -- t ∩ m has ≥2 elements
  have h_two : ∃ a b : V, a ∈ t ∩ m ∧ b ∈ t ∩ m ∧ a ≠ b := by
    have h_card := hshare
    rw [Finset.one_lt_card] at h_card
    obtain ⟨a, ha, b, hb, hab⟩ := h_card
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨a, b, ha, hb, hab⟩ := h_two
  simp only [mem_inter] at ha hb
  -- a, b ∈ t and a, b ∈ m
  use s(a, b)
  refine ⟨?_, ?_, ?_⟩
  · -- s(a, b) ∈ t.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨ha.1, hb.1⟩
  · -- s(a, b) ∈ m.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨ha.2, hb.2⟩
  · -- s(a, b) ∈ G.edgeFinset (because t is a clique)
    have ht_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht
    exact ht_clique.2 hab ha.1 hb.1

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: M-element has exactly 3 edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
A triangle e = {a, b, c} in the graph has exactly 3 edges in its sym2.
-/
lemma triangle_has_three_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (a b c : V) (he_abc : e = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    e.sym2 = {s(a, b), s(b, c), s(a, c)} := by
  ext edge
  simp only [mem_insert, mem_singleton, Finset.mem_sym2_iff]
  constructor
  · intro ⟨hx, hy⟩
    rw [he_abc] at hx hy
    simp only [mem_insert, mem_singleton] at hx hy
    -- x ∈ {a, b, c} and y ∈ {a, b, c}
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals simp [Sym2.eq_iff]
  · intro h
    rcases h with rfl | rfl | rfl
    all_goals (constructor <;> rw [he_abc] <;> simp)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Pick 2 of 3 edges covers 2/3 of possibilities
-- ══════════════════════════════════════════════════════════════════════════════

/--
If we pick 2 edges from {e1, e2, e3} and a target edge is one of them,
then the target is in our picked set.
-/
lemma two_of_three_cover (e1 e2 e3 : Sym2 V) (target : Sym2 V)
    (htarget : target = e1 ∨ target = e2 ∨ target = e3)
    (pick : Finset (Sym2 V)) (hpick_card : pick.card = 2)
    (hpick_sub : pick ⊆ {e1, e2, e3}) :
    target ∈ pick ∨ (∃ missed : Sym2 V, missed ∉ pick ∧ missed ∈ ({e1, e2, e3} : Finset (Sym2 V))) := by
  by_cases h : target ∈ pick
  · left; exact h
  · right
    use target
    constructor
    · exact h
    · rcases htarget with rfl | rfl | rfl <;> simp

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Every triangle shares edge with some M-element
-- ══════════════════════════════════════════════════════════════════════════════

/--
Main structural lemma: if M is a maximal packing and t is any triangle,
then t shares at least one edge with some element of M.

Moreover, we can CHOOSE which edge to attribute t to.

PROOF SKETCH:
By maximality, t shares ≥2 vertices with some m ∈ M.
By share_ge2_implies_share_edge, t shares an edge with m.
-/
theorem triangle_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, ∃ edge : Sym2 V, edge ∈ t.sym2 ∧ edge ∈ m.sym2 ∧ edge ∈ G.edgeFinset := by
  obtain ⟨m, hm, hshare⟩ := hMax t ht
  have hm_tri : m ∈ G.cliqueFinset 3 := hM.1 hm
  obtain ⟨edge, h1, h2, h3⟩ := share_ge2_implies_share_edge G t m ht hm_tri hshare
  exact ⟨m, hm, edge, h1, h2, h3⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: 6-packing constraint (from slot412)
-- ══════════════════════════════════════════════════════════════════════════════

/--
AXIOM: From slot412. For a 4-packing, at most 2 of the 3 edge-types of any
M-element have externals. This means we can always pick 2 edges that cover
all "internal" triangles (S_e-externals).
-/
axiom exists_two_edge_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ e.sym2 ∩ G.edgeFinset ∧
      ∀ t ∈ G.cliqueFinset 3, (∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1) →
        (t ∩ e).card ≥ 2 → ∃ edge ∈ E', edge ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
For a graph G with maximum triangle packing number 4, there exists
an edge cover of size ≤ 8 that hits every triangle.

PROOF SKETCH:
1. For each e ∈ M, use exists_two_edge_cover to get E_e with |E_e| ≤ 2.
2. Let E' = ⋃_{e ∈ M} E_e. Then |E'| ≤ 4 × 2 = 8.
3. For any triangle t:
   - By maximality, t shares ≥2 with some m ∈ M (call this the "home")
   - If t is edge-disjoint from other M-elements, t ∈ S_m, covered by E_m.
   - If t shares edge with another M-element f ≠ m:
     - t has an edge in common with f
     - E_f contains edges of f
     - If that edge is in E_f, t is covered
     - The 6-packing constraint ensures enough edges are picked
-/
theorem tau_le_8_nu_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  -- Get 2-edge cover for each M-element
  have h_covers : ∀ e ∈ M, ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ e.sym2 ∩ G.edgeFinset ∧
      ∀ t ∈ G.cliqueFinset 3, (∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1) →
        (t ∩ e).card ≥ 2 → ∃ edge ∈ E', edge ∈ t.sym2 := fun e he =>
    exists_two_edge_cover G M hM hM_card hNu4 e he
  choose f hf using h_covers
  -- Build E' = ⋃_{e ∈ M} f(e)
  let E' := M.biUnion f
  use E'
  refine ⟨?_, ?_, ?_⟩
  · -- E' ⊆ G.edgeFinset
    intro e he
    simp only [mem_biUnion] at he
    obtain ⟨m, hm, he'⟩ := he
    have h := (hf m hm).2.1 he'
    exact (mem_inter.mp h).2
  · -- |E'| ≤ 8
    calc E'.card = (M.biUnion f).card := rfl
      _ ≤ ∑ e ∈ M, (f e).card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, 2 := Finset.sum_le_sum (fun e he => (hf e he).1)
      _ = M.card * 2 := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 4 * 2 := by rw [hM_card]
      _ = 8 := by norm_num
  · -- E' covers all triangles
    intro t ht
    -- By maximality, t shares ≥2 with some m ∈ M
    obtain ⟨m, hm, hshare⟩ := hMax t ht
    -- Check: is t "internal" to m (edge-disjoint from other M-elements)?
    by_cases h_internal : ∀ m' ∈ M, m' ≠ m → (t ∩ m').card ≤ 1
    · -- t is internal: covered by f(m)
      obtain ⟨edge, hedge, h_cover⟩ := (hf m hm).2.2 t ht h_internal hshare
      use edge
      constructor
      · simp only [mem_biUnion]
        exact ⟨m, hm, hedge⟩
      · exact h_cover
    · -- t shares ≥2 with some other m' ≠ m (bridge case)
      push_neg at h_internal
      obtain ⟨m', hm', hm'_ne, hshare'⟩ := h_internal
      have hshare'' : (t ∩ m').card ≥ 2 := by omega
      -- t shares edge with m' by share_ge2_implies_share_edge
      have hm'_tri : m' ∈ G.cliqueFinset 3 := hM.1 hm'
      obtain ⟨edge, h_in_t, h_in_m', h_in_G⟩ := share_ge2_implies_share_edge G t m' ht hm'_tri hshare''
      -- Check if t is internal to m'
      by_cases h_internal' : ∀ m'' ∈ M, m'' ≠ m' → (t ∩ m'').card ≤ 1
      · -- t is internal to m': covered by f(m')
        obtain ⟨edge', hedge', h_cover'⟩ := (hf m' hm').2.2 t ht h_internal' hshare''
        use edge'
        constructor
        · simp only [mem_biUnion]
          exact ⟨m', hm', hedge'⟩
        · exact h_cover'
      · -- t shares with yet another element... continue the argument
        -- Key: t has only 3 vertices, can share ≥2 with at most 3 M-elements
        -- Each M-element contributes 2 edges to cover
        -- At least one must hit t
        -- For Aristotle: use pigeonhole or exhaustive analysis
        sorry

end
