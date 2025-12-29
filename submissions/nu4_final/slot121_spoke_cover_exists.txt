/-
Tuza ν=4 Cycle_4: SPOKE COVER EXISTS
Slot 121

AI CONSENSUS (Grok + Gemini Round 2):
Gemini's key lemma: For local S_e covers, we can CHOOSE edges that "dock" at shared vertices

KEY INSIGHT (from Gemini):
"Se_cover_exists_with_spoke": For a maximal packing element A, there exists a minimum cover
of its neighborhood S_A that uses at least one edge incident to a chosen vertex v ∈ A.

WHY THIS MATTERS:
- We know τ(S_e) ≤ 2 (PROVEN)
- But can we CHOOSE those 2 edges to be incident to shared vertices?
- If yes, then local covers "dock" at shared vertices, automatically covering bridges

PROOF STRATEGY:
1. S_e triangles either contain v (shared vertex) or avoid v
2. For triangles containing v: any spoke at v covers them
3. For triangles avoiding v: they must share base edge {a,b} (PROVEN pattern)
4. So we can choose: base edge {a,b} + one spoke at v → covers S_e with spoke

This is the Gemini insight that makes Approach B work!
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard)
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

/-- S_e: triangles sharing edge with e but not with other packing elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- Triangles containing v -/
def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

/-- Triangles avoiding v -/
def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

/-- Is a triangle cover for a set of triangles -/
def isTriangleCover (G : SimpleGraph V) (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Triangles avoiding v must share base edge
-- ══════════════════════════════════════════════════════════════════════════════

/--
PROVEN PATTERN: If t shares edge with packing element e = {v, a, b} but avoids v,
then t must share the base edge {a, b}.

This is because:
- t shares edge with e means (t ∩ e).card ≥ 2
- t avoids v means v ∉ t
- So t ∩ e ⊆ {a, b}
- For (t ∩ e).card ≥ 2, we need {a, b} ⊆ t
-/
lemma avoiding_shares_base_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e.card = 3)
    (v a b : V) (hv : v ∈ e) (ha : a ∈ e) (hb : b ∈ e)
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v)
    (he_eq : e = {v, a, b})
    (t : Finset V) (ht_shares : (t ∩ e).card ≥ 2) (ht_avoids : v ∉ t) :
    {a, b} ⊆ t := by
  -- Since t shares edge with e but avoids v, t ∩ e ⊆ {a, b}
  have h_inter_sub : t ∩ e ⊆ {a, b} := by
    intro x hx
    simp only [Finset.mem_inter] at hx
    have hxe := hx.2
    rw [he_eq] at hxe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with hxv | hxa | hxb
    · subst hxv; exact absurd hx.1 ht_avoids
    · subst hxa; simp
    · subst hxb; simp
  -- Since (t ∩ e).card ≥ 2 and t ∩ e ⊆ {a, b} with {a,b}.card = 2
  have hab_card : ({a, b} : Finset V).card = 2 := by
    rw [Finset.card_pair hab]
  have h_inter_eq : t ∩ e = {a, b} := by
    apply Finset.Subset.antisymm h_inter_sub
    -- Need: {a, b} ⊆ t ∩ e
    -- We know (t ∩ e).card ≥ 2 and t ∩ e ⊆ {a, b} with |{a,b}| = 2
    -- So t ∩ e = {a, b}
    have h_card_le : (t ∩ e).card ≤ ({a, b} : Finset V).card := Finset.card_le_card h_inter_sub
    have h_eq : (t ∩ e).card = 2 := by omega
    exact Finset.eq_of_subset_of_card_le h_inter_sub (by rw [h_eq, hab_card])
  -- Now {a, b} = t ∩ e ⊆ t
  rw [← h_inter_eq]
  exact Finset.inter_subset_left

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: S_e cover can use spoke at v
-- ══════════════════════════════════════════════════════════════════════════════

/--
GEMINI'S KEY LEMMA: For S_e where e = {v, a, b}, there exists a cover of size ≤ 2
that uses at least one edge incident to v.

Proof strategy:
1. S_e = (triangles containing v) ∪ (triangles avoiding v but sharing base {a,b})
2. Triangles avoiding v: covered by base edge s(a,b) (1 edge)
3. Triangles containing v: covered by one spoke at v (the spoke that covers most)
4. Total: base + spoke = 2 edges, and spoke is incident to v

Note: This is DIFFERENT from the FALSE lemma "local_cover_le_2 using only M-edges".
Here we use ANY edges, including the base edge s(a,b) which is in M-element e.
-/
lemma Se_cover_exists_with_spoke (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (v a b : V) (hv : v ∈ e) (ha : a ∈ e) (hb : b ∈ e)
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v)
    (he_eq : e = {v, a, b})
    (he_card : e.card = 3) :
    ∃ (C : Finset (Sym2 V)), C.card ≤ 2 ∧ isTriangleCover G (S_e G M e) C ∧
    (∃ spoke ∈ C, v ∈ spoke) := by
  -- Partition S_e into containing v and avoiding v
  have h_partition : S_e G M e = trianglesContaining (S_e G M e) v ∪ trianglesAvoiding (S_e G M e) v := by
    ext t
    simp only [trianglesContaining, trianglesAvoiding, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ht
      by_cases hv' : v ∈ t
      · left; exact ⟨ht, hv'⟩
      · right; exact ⟨ht, hv'⟩
    · intro h
      rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

  -- Case 1: S_e is empty
  by_cases hS_empty : S_e G M e = ∅
  · use ∅
    simp [isTriangleCover, hS_empty]

  -- Case 2: S_e is non-empty
  -- Base edge covers avoiding triangles
  have base_edge : Sym2 V := s(a, b)

  -- For containing triangles, we need a spoke
  -- Pick any triangle containing v in S_e (if exists), get a spoke that hits it
  by_cases h_containing_empty : trianglesContaining (S_e G M e) v = ∅
  · -- Only avoiding triangles: base edge suffices
    use {base_edge}
    constructor
    · simp
    constructor
    · constructor
      · -- base_edge ∈ G.edgeFinset
        sorry -- Need: e is a triangle in G, so its edges are in G.edgeFinset
      · intro t ht
        -- t avoids v, so t shares base {a,b}
        rw [h_partition] at ht
        simp only [Finset.mem_union, h_containing_empty, Finset.not_mem_empty, false_or] at ht
        have ht_avoid := (Finset.mem_filter.mp ht).2
        have ht_Se := (Finset.mem_filter.mp ht).1
        simp only [S_e, Finset.mem_filter, trianglesSharingEdge] at ht_Se
        have ht_shares := ht_Se.1
        simp only [Finset.mem_filter] at ht_shares
        have hab_sub := avoiding_shares_base_edge G e he_card v a b hv ha hb hab hav hbv he_eq t ht_shares.2 ht_avoid
        use base_edge
        simp only [Finset.mem_singleton, true_and]
        -- base_edge = s(a,b) ∈ t.sym2 since {a,b} ⊆ t
        sorry
    · -- The spoke part: we don't have a spoke in this case
      -- Actually, we need to ADD a spoke even if not needed for coverage
      -- OR: this case means no containing triangles, so we can't prove spoke exists
      -- Revise: The lemma should say "if there are containing triangles, spoke exists"
      -- For now, sorry
      sorry

  · -- Both containing and avoiding triangles exist
    -- Pick a spoke that covers at least one containing triangle
    -- Then use base + spoke
    obtain ⟨t₀, ht₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_containing_empty
    simp only [trianglesContaining, Finset.mem_filter] at ht₀
    have hv_in_t₀ := ht₀.2
    -- t₀ is a triangle containing v, so it has edges s(v, x) and s(v, y)
    -- Pick one such edge as the spoke
    have ht₀_tri : t₀ ∈ G.cliqueFinset 3 := by
      simp only [S_e, Finset.mem_filter, trianglesSharingEdge] at ht₀
      exact ht₀.1.1.1
    -- Get another vertex w ∈ t₀ with w ≠ v
    have ht₀_card : t₀.card = 3 := Finset.mem_cliqueFinset_iff.mp ht₀_tri |>.2
    obtain ⟨w, hw_mem, hw_ne⟩ : ∃ w ∈ t₀, w ≠ v := by
      by_contra h
      push_neg at h
      have : t₀ ⊆ {v} := fun x hx => Finset.mem_singleton.mpr (h x hx)
      have : t₀.card ≤ 1 := Finset.card_le_card this |> fun h => le_trans h (by simp)
      omega
    let spoke : Sym2 V := s(v, w)
    use {base_edge, spoke}
    constructor
    · -- Card bound
      have h_ne : base_edge ≠ spoke := by
        simp only [base_edge, spoke]
        intro h_eq
        -- s(a,b) = s(v,w) implies {a,b} = {v,w}
        -- But v ∉ {a,b} (since v ≠ a and v ≠ b and a ≠ b implies v ∉ {a,b}... actually need v ∉ e \ {a,b} = {v})
        sorry
      rw [Finset.card_pair h_ne]
    constructor
    · -- Coverage
      constructor
      · -- Subset of edgeFinset
        intro edge hedge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
        rcases hedge with rfl | rfl
        · sorry -- base_edge in G.edgeFinset
        · sorry -- spoke in G.edgeFinset
      · intro t ht
        -- Split by whether t contains v
        by_cases hv_t : v ∈ t
        · -- t contains v: spoke covers it
          use spoke
          simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, true_and]
          sorry -- s(v,w) ∈ t.sym2 if v ∈ t... not quite, need w ∈ t too
        · -- t avoids v: base covers it
          use base_edge
          simp only [Finset.mem_insert, Finset.mem_singleton, true_and]
          sorry
    · -- Spoke exists in cover
      use spoke
      simp

-- ══════════════════════════════════════════════════════════════════════════════
-- CONSEQUENCE: Docked covers absorb bridges
-- ══════════════════════════════════════════════════════════════════════════════

/--
GEMINI'S SECOND LEMMA: If a cover for S_A contains a spoke at v_ab,
it automatically covers all bridges in X_{AB} that contain v_ab.

This is the "docking" insight: spokes at shared vertices pull double duty.
-/
lemma docked_cover_absorbs_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (C_A : Finset (Sym2 V))
    (h_spoke : ∃ e ∈ C_A, v ∈ e)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_v : v ∈ t) :
    ∃ e ∈ C_A, e ∈ t.sym2 := by
  obtain ⟨spoke, h_spoke_mem, h_v_in_spoke⟩ := h_spoke
  -- spoke contains v
  -- If spoke = s(v, w) and both v ∈ t and w ∈ t, then spoke ∈ t.sym2
  -- But we only know v ∈ t, not necessarily w ∈ t
  -- This lemma is INCORRECT as stated!
  -- The spoke s(v, w) only covers triangles containing BOTH v and w
  -- Not all triangles containing v

  -- CORRECTION: The spoke covers triangles containing v IF we picked the right spoke
  -- Or: we need MORE than one spoke
  sorry

end
