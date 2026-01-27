/-
  slot398_lp_tau_8.lean

  Tuza ν=4 PATH_4: LP/Fractional Approach to τ ≤ 8

  KEY INSIGHT: Instead of constructing explicit 8-edge covers, use fractional
  relaxation and counting arguments.

  THEOREM: For any graph G with ν(G) = 4, τ(G) ≤ 8.

  APPROACH:
  1. Every triangle T in G shares an edge with some M-element (maximality)
  2. For each M-element e, count how many edges are needed to cover S_e
  3. Show that on average, each M-element needs ≤ 2 edges
  4. Total: 4 × 2 = 8 edges

  WHY 2 PER M-ELEMENT:
  - The 3 edges of M-element e partition S_e ∪ {e} into 3 groups
  - Each group has triangles sharing that specific edge
  - But some edges might not have any externals!
  - And some externals might be covered by edges from other M-elements!

  FRACTIONAL BOUND:
  - Assign weight 1/2 to each edge of each M-element (12 × 1/2 = 6 fractional)
  - Each M-element has total weight 3/2 ≥ 1 ✓
  - Each external T shares edge with some M-element, gets weight ≥ 1/2... not enough!

  BETTER FRACTIONAL BOUND:
  - Assign weight 2/3 to edges of endpoint elements (A, D)
  - Assign weight 1/3 to edges of interior elements (B, C)
  - Each M-element: 3 × weight = 2 (endpoints) or 1 (interior)... doesn't work

  DIRECT COUNTING (NEW APPROACH):
  - For PATH_4, the 4 M-elements share vertices along the spine
  - Use edges incident to spine vertices {v₁, v₂, v₃}
  - Count how many triangles each such edge covers

  TIER: 2-3 (structural argument)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isPath4Labeled (M : Finset (Finset V)) (A B C D : Finset V)
    (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V) : Prop :=
  M = {A, B, C, D} ∧
  A = {v₁, a₂, a₃} ∧ B = {v₁, v₂, b₃} ∧ C = {v₂, v₃, c₃} ∧ D = {v₃, d₂, d₃} ∧
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ v₁ ≠ b₃ ∧ v₁ ≠ c₃ ∧ v₁ ≠ d₂ ∧ v₁ ≠ d₃ ∧
  v₂ ≠ v₃ ∧ v₂ ≠ a₂ ∧ v₂ ≠ a₃ ∧ v₂ ≠ b₃ ∧ v₂ ≠ c₃ ∧ v₂ ≠ d₂ ∧ v₂ ≠ d₃ ∧
  v₃ ≠ a₂ ∧ v₃ ≠ a₃ ∧ v₃ ≠ b₃ ∧ v₃ ≠ c₃ ∧ v₃ ≠ d₂ ∧ v₃ ≠ d₃ ∧
  a₂ ≠ a₃ ∧ a₂ ≠ b₃ ∧ a₂ ≠ c₃ ∧ a₂ ≠ d₂ ∧ a₂ ≠ d₃ ∧
  a₃ ≠ b₃ ∧ a₃ ≠ c₃ ∧ a₃ ≠ d₂ ∧ a₃ ≠ d₃ ∧
  b₃ ≠ c₃ ∧ b₃ ≠ d₂ ∧ b₃ ≠ d₃ ∧
  c₃ ≠ d₂ ∧ c₃ ≠ d₃ ∧
  d₂ ≠ d₃

def isEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, ∃ u v : V, e = s(u, v) ∧ u ∈ T ∧ v ∈ T

-- ══════════════════════════════════════════════════════════════════════════════
-- SPINE-BASED COVER: All edges incident to spine vertices
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle contains at least one spine vertex or is edge-disjoint from M -/
theorem triangle_contains_spine_or_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    v₁ ∈ T ∨ v₂ ∈ T ∨ v₃ ∈ T ∨ T ∈ M := by
  by_cases hT_in_M : T ∈ M
  · right; right; right; exact hT_in_M
  · -- T ∉ M, so T shares edge with some M-element
    obtain ⟨E, hE_in_M, hT_share_E⟩ := hMaximal T hT hT_in_M
    have hM_eq : M = {A, B, C, D} := hpath.1
    rw [hM_eq] at hE_in_M
    simp only [mem_insert, mem_singleton] at hE_in_M
    rcases hE_in_M with rfl | rfl | rfl | rfl
    · -- T shares edge with A = {v₁, a₂, a₃}
      -- A-external contains ≥2 vertices of A, one must be v₁ or we need a₂,a₃
      have hA_eq : A = {v₁, a₂, a₃} := hpath.2.1
      rw [hA_eq] at hT_share_E
      have h2 : (T ∩ {v₁, a₂, a₃}).card ≥ 2 := hT_share_E
      by_cases hv1 : v₁ ∈ T
      · left; exact hv1
      · -- v₁ ∉ T, so T ∩ A = {a₂, a₃}
        -- This means T = {a₂, a₃, x} for some x
        -- T is a triangle, so might contain v₂ or v₃
        left -- Actually, we don't know v₁ is in T. Let's try differently
        sorry
    · -- T shares edge with B = {v₁, v₂, b₃}
      have hB_eq : B = {v₁, v₂, b₃} := hpath.2.2.1
      rw [hB_eq] at hT_share_E
      have h2 : (T ∩ {v₁, v₂, b₃}).card ≥ 2 := hT_share_E
      -- T contains at least 2 of {v₁, v₂, b₃}
      by_contra h
      push_neg at h
      -- If v₁ ∉ T and v₂ ∉ T and v₃ ∉ T, then T ∩ B ⊆ {b₃}
      have hsub : T ∩ {v₁, v₂, b₃} ⊆ {b₃} := by
        intro x hx
        simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 h.1
        · exact absurd hx.1 h.2.1
        · rfl
      have hcard : (T ∩ {v₁, v₂, b₃}).card ≤ 1 := by
        calc (T ∩ {v₁, v₂, b₃}).card ≤ ({b₃} : Finset V).card := card_le_card hsub
          _ = 1 := card_singleton b₃
      omega
    · -- T shares edge with C = {v₂, v₃, c₃}
      have hC_eq : C = {v₂, v₃, c₃} := hpath.2.2.2.1
      rw [hC_eq] at hT_share_E
      have h2 : (T ∩ {v₂, v₃, c₃}).card ≥ 2 := hT_share_E
      by_contra h
      push_neg at h
      have hsub : T ∩ {v₂, v₃, c₃} ⊆ {c₃} := by
        intro x hx
        simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 h.2.1
        · exact absurd hx.1 h.2.2
        · rfl
      have hcard : (T ∩ {v₂, v₃, c₃}).card ≤ 1 := by
        calc (T ∩ {v₂, v₃, c₃}).card ≤ ({c₃} : Finset V).card := card_le_card hsub
          _ = 1 := card_singleton c₃
      omega
    · -- T shares edge with D = {v₃, d₂, d₃}
      have hD_eq : D = {v₃, d₂, d₃} := hpath.2.2.2.2.1
      rw [hD_eq] at hT_share_E
      have h2 : (T ∩ {v₃, d₂, d₃}).card ≥ 2 := hT_share_E
      by_contra h
      push_neg at h
      have hsub : T ∩ {v₃, d₂, d₃} ⊆ {d₂, d₃} := by
        intro x hx
        simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 h.2.2
        · left; rfl
        · right; rfl
      -- T contains d₂ and d₃, but not v₃. This is OK for A-externals etc.
      -- But we wanted to show v₁ ∨ v₂ ∨ v₃ ∈ T...
      -- D-externals containing only d₂, d₃ (not v₃) exist!
      sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COUNTING ARGUMENT: Each M-element contributes ≤ 2 edges on average
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for average bound:
1. Consider the "load" on each M-element: how many external types it has
2. A and D have 3 external types each (3 edges × possibly externals)
3. B and C have 3 external types each, but some types might be empty
4. Key: If T ∈ S_e for M-element e, then T shares a SPECIFIC edge with e
5. The 3 edges of e partition S_e
6. To cover S_e ∪ {e}, we need at most 3 edges
7. But we can share! If T shares {v₁, v₂} with B AND contains v₃, maybe {v₂, v₃} also hits T?
   Wait, {v₂, v₃} hits T iff both v₂, v₃ ∈ T. Not necessarily.
8. For interior elements (B, C):
   - slot390: Every B-external contains v₁ or v₂
   - This means B-externals only appear in 2 of B's 3 edge-groups? No, all 3 groups have v₁ or v₂.
9. New insight: Interior B-externals are covered by at most 3 B-edges, but we've proven
   ALL B-externals contain v₁ or v₂. The third vertex is b₃. So:
   - {v₁, v₂}-externals: hit by {v₁, v₂}
   - {v₁, b₃}-externals: hit by {v₁, b₃}
   - {v₂, b₃}-externals: hit by {v₂, b₃}
   All 3 needed. No savings for interior.
10. For endpoint elements (A, D):
    - A-externals have |T ∩ A| ≥ 2, but A ∩ B = {v₁}
    - If T ∈ S_A and v₁ ∈ T, then T also intersects B at v₁
    - T doesn't share edge with B (A-external definition), so T ∩ B = {v₁} exactly
    - So A-externals containing v₁ are NOT hit by any B-edge or C-edge or D-edge
11. Conclusion: No cross-coverage savings. Total = 12 edges needed???

This contradicts Tuza. Where's the error?

ERROR: The conjecture is about ν = 4 graphs, not PATH_4 specifically.
For PATH_4, maybe τ < 12 because not all external types can coexist!

For example, if A has {a₂, a₃}-externals, these are triangles {a₂, a₃, x}.
If B has {v₂, b₃}-externals, these are triangles {v₂, b₃, y}.
Can these coexist with ν = 4?

{a₂, a₃, x} is edge-disjoint from B, C, D (by S_A definition).
{v₂, b₃, y} is edge-disjoint from A, C, D (by S_B definition).
So {A, {a₂,a₃,x}, C, D} and {A, B, {v₂,b₃,y}, D} are both 4-packings.

But wait, {A, {a₂,a₃,x}, {v₂,b₃,y}, D} might be a 4-packing if they're pairwise edge-disjoint!
- {a₂,a₃,x} ∩ {v₂,b₃,y} = ∅ or {x} or {y} depending on whether x,y share
- If x ≠ y and x,y ∉ {v₂,b₃,a₂,a₃}, then intersection is empty, so edge-disjoint!

So we could have ν ≥ 4 even with these externals. The constraint is ν = 4 exactly,
meaning NO 5-packing exists.

For ν = 4, adding any triangle to M must violate the packing property.
This means EVERY triangle in the graph shares an edge with some M-element.
That's exactly the maximality condition!

So the maximality condition enforces ν = 4 when M is a maximum packing.
But the maximality condition alone doesn't prevent externals from existing.

The τ ≤ 8 bound must come from a more subtle argument...
-/

-- Actually let me try a different tactic: prove the M-elements themselves
-- are covered by at most 4 edges (one per element), then prove externals
-- add at most 4 more edges.

/-- The 4 M-elements can be covered by 4 edges -/
theorem M_covered_by_4_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M) :
    ∃ (cover : Finset (Sym2 V)), cover.card = 4 ∧
      ∀ T ∈ M, ∃ e ∈ cover, ∃ u v : V, e = s(u, v) ∧ u ∈ T ∧ v ∈ T := by
  -- Use one edge from each: {a₂, a₃}, {v₁, v₂}, {v₂, v₃}, {d₂, d₃}
  let cover : Finset (Sym2 V) := {s(a₂, a₃), s(v₁, v₂), s(v₂, v₃), s(d₂, d₃)}
  use cover
  constructor
  · -- card = 4
    simp only [cover]
    -- All 4 edges are distinct
    have h1 : s(a₂, a₃) ≠ s(v₁, v₂) := by
      simp only [Sym2.eq, Sym2.rel_iff']; push_neg
      constructor
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.1]
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.2.1]
    have h2 : s(a₂, a₃) ≠ s(v₂, v₃) := by
      simp only [Sym2.eq, Sym2.rel_iff']; push_neg
      constructor
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.1]
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.2.2.1]
    have h3 : s(a₂, a₃) ≠ s(d₂, d₃) := by
      simp only [Sym2.eq, Sym2.rel_iff']; push_neg
      constructor
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    have h4 : s(v₁, v₂) ≠ s(v₂, v₃) := by
      simp only [Sym2.eq, Sym2.rel_iff']; push_neg
      constructor
      · intro h; simp_all [hpath.2.2.2.2.2.1]
      · intro h; simp_all [hpath.1]
    have h5 : s(v₁, v₂) ≠ s(d₂, d₃) := by
      simp only [Sym2.eq, Sym2.rel_iff']; push_neg
      constructor
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      · intro h; simp_all [hpath.2.2.2.2.2.2.1]
    have h6 : s(v₂, v₃) ≠ s(d₂, d₃) := by
      simp only [Sym2.eq, Sym2.rel_iff']; push_neg
      constructor
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      · intro h; simp_all [hpath.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    simp [cover, card_insert_of_not_mem, h1, h2, h3, h4, h5, h6]
  · -- Every M-element is covered
    intro T hT_in_M
    have hM_eq : M = {A, B, C, D} := hpath.1
    rw [hM_eq] at hT_in_M
    simp only [mem_insert, mem_singleton] at hT_in_M
    rcases hT_in_M with rfl | rfl | rfl | rfl
    · -- T = A = {v₁, a₂, a₃}
      use s(a₂, a₃)
      constructor
      · simp [cover]
      · use a₂, a₃
        constructor
        · rfl
        · have hA_eq : A = {v₁, a₂, a₃} := hpath.2.1
          simp [hA_eq]
    · -- T = B = {v₁, v₂, b₃}
      use s(v₁, v₂)
      constructor
      · simp [cover]
      · use v₁, v₂
        constructor
        · rfl
        · have hB_eq : B = {v₁, v₂, b₃} := hpath.2.2.1
          simp [hB_eq]
    · -- T = C = {v₂, v₃, c₃}
      use s(v₂, v₃)
      constructor
      · simp [cover]
      · use v₂, v₃
        constructor
        · rfl
        · have hC_eq : C = {v₂, v₃, c₃} := hpath.2.2.2.1
          simp [hC_eq]
    · -- T = D = {v₃, d₂, d₃}
      use s(d₂, d₃)
      constructor
      · simp [cover]
      · use d₂, d₃
        constructor
        · rfl
        · have hD_eq : D = {v₃, d₂, d₃} := hpath.2.2.2.2.1
          simp [hD_eq]

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Externals add at most 4 more edges
-- This is the crux of τ ≤ 8 for PATH_4!
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for external bound ≤ 4:
The 4-edge cover {{a₂,a₃}, {v₁,v₂}, {v₂,v₃}, {d₂,d₃}} covers M.
For externals, we need additional edges.

Key observation: Each external T shares an edge with exactly one M-element.
That edge is one of the 12 M-edges (3 per element).

The 4-edge cover uses only 4 of these 12 edges.
The remaining 8 M-edges are:
- From A: {v₁,a₂}, {v₁,a₃}
- From B: {v₁,b₃}, {v₂,b₃}
- From C: {v₂,c₃}, {v₃,c₃}
- From D: {v₃,d₂}, {v₃,d₃}

An external T ∈ S_e is NOT covered by the 4-edge cover iff T's edge with e is
one of the 8 remaining M-edges.

For each of the 8 remaining edges, adding it to the cover would handle all
externals sharing that edge.

But we only need 4 more edges to get τ ≤ 8!

Claim: At most 4 of the 8 remaining edges are "necessary" (have externals).

Why? Because ν = 4 constraint limits how many externals can exist!

Specifically:
- If {v₁,a₂}-externals exist, they're edge-disjoint from B,C,D
- If {v₁,b₃}-externals exist, they're edge-disjoint from A,C,D
- But both types contain v₁, so they might share edges!

Actually, {v₁,a₂,x} and {v₁,b₃,y} share at most {v₁} (single vertex).
So they're edge-disjoint if x ≠ b₃ and y ≠ a₂.

For ν = 4, there's no 5-packing. So:
{A, B, C, D} is maximal, meaning any external shares edge with M.

But multiple externals can exist! The ν = 4 constraint doesn't directly
limit the NUMBER of externals, just that they share edges with M.

I think the τ ≤ 8 bound is more subtle and might require LP or probabilistic methods.
-/

/-- CONJECTURE: External triangles can be covered by at most 4 additional edges -/
theorem externals_covered_by_4_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (baseCover : Finset (Sym2 V))
    (hBase : baseCover = {s(a₂, a₃), s(v₁, v₂), s(v₂, v₃), s(d₂, d₃)}) :
    ∃ (extraEdges : Finset (Sym2 V)), extraEdges.card ≤ 4 ∧
      ∀ T ∈ G.cliqueFinset 3, T ∉ M →
        (∃ e ∈ baseCover, ∃ u v : V, e = s(u, v) ∧ u ∈ T ∧ v ∈ T) ∨
        (∃ e ∈ extraEdges, ∃ u v : V, e = s(u, v) ∧ u ∈ T ∧ v ∈ T) := by
  -- The extra edges needed are: {v₁,a₂}, {v₁,a₃}, {v₃,d₂}, {v₃,d₃}
  -- Wait, that's 4 edges but only covers A-externals and D-externals not in base
  -- We also need B-externals and C-externals...
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM (combining M coverage + external coverage)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_path4_lp (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧ isEdgeCover G cover := by
  sorry

end
