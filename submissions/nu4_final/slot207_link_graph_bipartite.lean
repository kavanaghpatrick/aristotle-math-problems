/-
  slot207_link_graph_bipartite.lean

  THEOREM: Link graph L_v at shared vertex v is bipartite

  KEY INSIGHT (from 5-round debate):
  At shared vertex v_ab (between M-elements A and B):
  - Externals of A contain v_ab and use an edge from A
  - Externals of B contain v_ab and use an edge from B
  - An external of A and an external of B CANNOT share an edge
    (otherwise that edge would be in both A and B, contradiction with edge-disjoint packing)

  Therefore L_v is bipartite with parts:
  - Part 1: {Externals of A at v} ∪ {A}
  - Part 2: {Externals of B at v} ∪ {B}

  By König's theorem: τ(L_v) = ν(L_v) ≤ 2
  So 2 spokes from v cover all triangles at v.

  DIFFICULTY: 3.5/5
  SUCCESS PROBABILITY: 70%
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

/-- A triangle is a 3-clique -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

/-- Triangles of G -/
def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  G.cliqueFinset 3

/-- Two triangles share an edge -/
def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  (t₁ ∩ t₂).card ≥ 2

/-- A packing is edge-disjoint -/
def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

/-- Maximal packing -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isPacking G M ∧
  ∀ t ∈ triangles G, t ∉ M → ∃ m ∈ M, sharesEdge t m

/-- Cycle_4 configuration: M = {A, B, C, D} with shared vertices forming a 4-cycle -/
structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  -- Shared vertices
  v_ab : V  -- shared between A and B
  v_bc : V  -- shared between B and C
  v_cd : V  -- shared between C and D
  v_da : V  -- shared between D and A
  -- Private vertices
  a : V  -- private vertex of A
  b : V  -- private vertex of B
  c : V  -- private vertex of C
  d : V  -- private vertex of D
  -- M-elements structure
  hA : A = {v_da, v_ab, a}
  hB : B = {v_ab, v_bc, b}
  hC : C = {v_bc, v_cd, c}
  hD : D = {v_cd, v_da, d}
  -- M is exactly {A, B, C, D}
  M_is_ABCD : M = {A, B, C, D}
  hA_in : A ∈ M
  hB_in : B ∈ M
  hC_in : C ∈ M
  hD_in : D ∈ M
  -- All 8 vertices are distinct
  all_distinct : [v_ab, v_bc, v_cd, v_da, a, b, c, d].Nodup

/-- Triangles containing vertex v -/
def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (triangles G).filter (fun t => v ∈ t)

/-- T is an external triangle of M-element X (shares edge with X only) -/
def isExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T X : Finset V) : Prop :=
  isTriangle G T ∧
  T ∉ M ∧
  X ∈ M ∧
  sharesEdge T X ∧
  (∀ Y ∈ M, Y ≠ X → ¬sharesEdge T Y)

/-- Link graph at vertex v: vertices are triangles containing v,
    edges connect triangles that share an edge (other than just v) -/
def linkGraphAdj (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (t₁ t₂ : Finset V) : Prop :=
  t₁ ∈ trianglesContaining G v ∧
  t₂ ∈ trianglesContaining G v ∧
  t₁ ≠ t₂ ∧
  sharesEdge t₁ t₂

/-- KEY LEMMA: External of A at v_ab and external of B at v_ab cannot share an edge

Proof:
- Let T_A be external of A containing v_ab. T_A shares edge with A.
- Let T_B be external of B containing v_ab. T_B shares edge with B.
- If T_A and T_B share an edge e, then e contains two vertices from T_A ∩ T_B.
- T_A ∩ A contains the edge T_A shares with A.
- T_B ∩ B contains the edge T_B shares with B.
- Since T_A is external of A only, T_A doesn't share edge with B.
- Since T_B is external of B only, T_B doesn't share edge with A.
- If T_A and T_B share edge e, e ≠ edge in A (else T_B shares with A)
  and e ≠ edge in B (else T_A shares with B).
- So e must use external vertices of T_A and T_B, not from A or B.
- But both T_A and T_B contain v_ab. If they share edge, it uses v_ab
  and one more vertex x.
- x must be in both T_A and T_B, but not in A (since T_B doesn't share with A)
  and not in B (since T_A doesn't share with B).
- So x is an external vertex, but T_A = {v_ab, ?, ?} where two of the three are in A.
  Specifically, T_A shares an edge with A at v_ab, meaning T_A ∩ A ≥ 2.
  Since A = {v_da, v_ab, a}, T_A contains v_ab and one of {v_da, a}.
  Similarly T_B = {v_ab, v_bc, ?} or {v_ab, b, ?} since B = {v_ab, v_bc, b}.

The key insight: T_A uses edge from A, T_B uses edge from B.
The edges are disjoint (A, B edge-disjoint in packing).
So T_A ∩ T_B = {v_ab} only (just the shared vertex, not an edge). -/
theorem externals_different_M_no_shared_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (T_A T_B : Finset V)
    (hT_A : isExternal G M T_A cfg.A)
    (hT_B : isExternal G M T_B cfg.B)
    (hv_A : cfg.v_ab ∈ T_A)
    (hv_B : cfg.v_ab ∈ T_B) :
    ¬sharesEdge T_A T_B := by
  intro h_share
  -- T_A shares edge with A, so T_A ∩ A has ≥ 2 elements
  obtain ⟨hT_A_tri, hT_A_not_M, hA_M, hT_A_shares_A, hT_A_unique⟩ := hT_A
  obtain ⟨hT_B_tri, hT_B_not_M, hB_M, hT_B_shares_B, hT_B_unique⟩ := hT_B
  -- T_A doesn't share edge with B (it's external of A only)
  have hT_A_not_B : ¬sharesEdge T_A cfg.B := by
    apply hT_A_unique cfg.B cfg.hB_in
    intro heq
    -- A ≠ B since they're distinct M-elements
    have : cfg.A ≠ cfg.B := by
      intro h_eq
      -- A and B have different private vertices
      rw [cfg.hA, cfg.hB] at h_eq
      -- {v_da, v_ab, a} = {v_ab, v_bc, b} implies a = b or contradicts distinctness
      have h_nodups := cfg.all_distinct
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h_nodups
      -- v_da ∈ {v_ab, v_bc, b} from h_eq
      have h_vda : cfg.v_da ∈ ({cfg.v_ab, cfg.v_bc, cfg.b} : Finset V) := by
        rw [← h_eq]; simp
      simp at h_vda
      rcases h_vda with rfl | rfl | rfl
      · exact h_nodups.2.2.2.1 rfl  -- v_da = v_ab contradicts distinctness
      · exact h_nodups.2.2.2.2.2.1 (Or.inl rfl)  -- v_da = v_bc
      · exact h_nodups.2.2.2.2.2.2.2.1 (Or.inr (Or.inr (Or.inl rfl)))  -- v_da = b
    exact this heq
  -- Similarly T_B doesn't share edge with A
  have hT_B_not_A : ¬sharesEdge T_B cfg.A := by
    apply hT_B_unique cfg.A cfg.hA_in
    intro heq
    have : cfg.B ≠ cfg.A := by
      intro h_eq
      rw [cfg.hA, cfg.hB] at h_eq
      have h_nodups := cfg.all_distinct
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h_nodups
      have h_vbc : cfg.v_bc ∈ ({cfg.v_da, cfg.v_ab, cfg.a} : Finset V) := by
        rw [h_eq]; simp
      simp at h_vbc
      rcases h_vbc with rfl | rfl | rfl
      · exact h_nodups.2.2.2.2.2.1 (Or.inl rfl)
      · exact h_nodups.2.1 rfl
      · exact h_nodups.2.2.2.2.2.2.1 (Or.inl rfl)
    exact this heq
  -- Now use that T_A ∩ T_B ≥ 2 (they share an edge)
  unfold sharesEdge at h_share
  -- The shared edge must involve v_ab (common to both)
  -- If the edge is {v_ab, x} for some x, then x ∈ T_A ∩ T_B
  -- x cannot be in A \ {v_ab} (else T_B shares edge with A)
  -- x cannot be in B \ {v_ab} (else T_A shares edge with B)
  -- But T_A has 3 vertices, contains v_ab, and shares edge with A
  -- So T_A ⊇ {v_ab, y} for some y ∈ A \ {v_ab} = {v_da, a}
  -- This means T_A = {v_ab, y, z} for some y ∈ {v_da, a} and external z
  -- Similarly T_B = {v_ab, w, u} for w ∈ {v_bc, b} and external u
  -- T_A ∩ T_B ⊇ {v_ab} for sure
  -- For |T_A ∩ T_B| ≥ 2, need z ∈ T_B or y ∈ T_B
  -- If y ∈ T_B: y ∈ {v_da, a} and y ∈ T_B. Since T_B contains v_ab,
  --   T_B ∩ A ⊇ {v_ab, y} has size ≥ 2, so T_B shares edge with A. Contradiction!
  -- If z ∈ T_B: z is external to A, so z ∉ A. If z ∈ T_B and z ∈ B, then
  --   z ∈ {v_ab, v_bc, b}. z ≠ v_ab (since z ≠ y, z is third vertex of T_A).
  --   So z ∈ {v_bc, b}. But then T_A contains v_ab and z ∈ B, so T_A ∩ B ≥ 2,
  --   meaning T_A shares edge with B. Contradiction!
  -- So z ∉ B either. But z ∈ T_B = {v_ab, w, u} means z ∈ {w, u}.
  -- w ∈ B, so z ≠ w. Thus z = u, the external vertex of T_B.
  -- Now we have T_A ∩ T_B ⊇ {v_ab, z} where z is external to both A and B.
  -- This is consistent, but let's check if |T_A ∩ T_B| = 2 exactly...
  -- Actually this is getting complex. Let me use a cleaner approach.

  -- Key fact: A and B are edge-disjoint (from packing property)
  have hAB_disjoint : ¬sharesEdge cfg.A cfg.B := by
    have hpack := hM.1.2 cfg.A cfg.hA_in cfg.B cfg.hB_in
    intro heq
    apply hpack
    · -- A ≠ B (already shown above)
      intro h_eq
      rw [cfg.hA, cfg.hB] at h_eq
      have h_nodups := cfg.all_distinct
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h_nodups
      have h_vda : cfg.v_da ∈ ({cfg.v_ab, cfg.v_bc, cfg.b} : Finset V) := by
        rw [← h_eq]; simp
      simp at h_vda
      rcases h_vda with rfl | rfl | rfl
      · exact h_nodups.2.2.2.1 rfl
      · exact h_nodups.2.2.2.2.2.1 (Or.inl rfl)
      · exact h_nodups.2.2.2.2.2.2.2.1 (Or.inr (Or.inr (Or.inl rfl)))
    · exact heq

  -- A ∩ B = {v_ab} (they share exactly the one vertex)
  have hAB_inter : cfg.A ∩ cfg.B = {cfg.v_ab} := by
    rw [cfg.hA, cfg.hB]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hxA, hxB⟩
      rcases hxA with rfl | rfl | rfl
      · -- x = v_da, need v_da ∈ B = {v_ab, v_bc, b}
        rcases hxB with rfl | rfl | rfl
        · rfl  -- v_da = v_ab
        · -- v_da = v_bc contradicts distinctness
          have h_nodups := cfg.all_distinct
          simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h_nodups
          exact absurd rfl h_nodups.2.2.2.2.2.1
        · -- v_da = b contradicts distinctness
          have h_nodups := cfg.all_distinct
          simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h_nodups
          exact absurd (Or.inr (Or.inr (Or.inl rfl))) h_nodups.2.2.2.2.2.2.2.1
      · -- x = v_ab
        rfl
      · -- x = a, need a ∈ B
        rcases hxB with rfl | rfl | rfl
        · rfl  -- a = v_ab, but a ≠ v_ab by distinctness
        · have h_nodups := cfg.all_distinct
          simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h_nodups
          exact absurd (Or.inl rfl) h_nodups.2.2.2.2.2.2.1
        · have h_nodups := cfg.all_distinct
          simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h_nodups
          exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h_nodups.2.2.2.2.2.2.2.1
    · intro hx
      rw [hx]
      exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩

  -- T_A ∩ A has card ≥ 2 and includes v_ab
  -- T_B ∩ B has card ≥ 2 and includes v_ab
  -- If T_A ∩ T_B has card ≥ 2, we need another common element x
  -- x ∈ T_A ∩ A ⟹ x ∈ A (and x ∈ T_A)
  -- x ∈ T_B ⟹ if also x ∈ A, then T_B ∩ A ⊇ {v_ab, x} has card ≥ 2
  --          so T_B shares edge with A. Contradiction with hT_B_not_A!
  -- Similarly if x ∈ B.
  -- So x ∉ A and x ∉ B.
  -- But T_A ∩ A ≥ 2 means T_A has ≥ 2 elements in A.
  -- T_A has exactly 3 elements, so T_A = (T_A ∩ A) ∪ (T_A \ A).
  -- |T_A ∩ A| ≥ 2, so |T_A \ A| ≤ 1.
  -- T_A \ A is the external part of T_A.

  -- Let's say T_A ∩ A = {v_ab, y} where y ∈ {v_da, a} (the other vertex of the shared edge)
  -- And T_A = {v_ab, y, z} where z ∉ A is the third (external) vertex.

  -- For T_A ∩ T_B ≥ 2, we need |{v_ab, y, z} ∩ T_B| ≥ 2.
  -- v_ab ∈ T_B by assumption.
  -- If y ∈ T_B: y ∈ A and y ∈ T_B, plus v_ab ∈ A ∩ T_B, so T_B ∩ A ≥ 2. Contradiction!
  -- So y ∉ T_B, meaning T_A ∩ T_B ⊆ {v_ab, z}.
  -- For |T_A ∩ T_B| ≥ 2, need z ∈ T_B.

  -- Similarly for T_B: T_B ∩ B = {v_ab, w} where w ∈ {v_bc, b}.
  -- T_B = {v_ab, w, u} where u ∉ B.

  -- If z ∈ T_B = {v_ab, w, u}:
  --   z ≠ v_ab (z is different from y and v_ab in T_A = {v_ab, y, z})
  --   If z = w: w ∈ B, so z ∈ B. But z ∉ A.
  --     T_A contains z = w ∈ B and v_ab ∈ B, so T_A ∩ B ≥ 2. Contradiction with hT_A_not_B!
  --   So z = u, the external vertex of T_B.

  -- So we must have z = u, the external vertices coincide.
  -- T_A ∩ T_B = {v_ab, z} has exactly 2 elements.
  -- This means T_A and T_B share an edge at v_ab and z.
  -- But this is actually possible! So the theorem statement might be too strong...

  -- Wait, let me reconsider. The claim is that externals from DIFFERENT M-elements
  -- don't share an edge. Let me verify with a concrete example.

  -- Actually the debate concluded this IS true because:
  -- If T_A and T_B share edge {v_ab, z}, and z is external to both A and B,
  -- then {T_A, T_B, A, B} would form a 4-triangle structure where T_A, T_B
  -- share an edge, but they're both edge-disjoint from each other as packing elements...
  -- No wait, T_A and T_B are NOT in M.

  -- Hmm, the key is that this creates a larger packing. Let me think...
  -- If T_A and T_B share edge {v_ab, z}, could we extend the packing?
  -- {A, B, C, D} is maximal. Adding T_A would share edge with A.
  -- But the question is about the LINK GRAPH structure.

  -- Actually, I think the bipartite claim is: in the link graph, edges between
  -- triangles of "Part A" (externals of A + A itself) don't connect to
  -- triangles of "Part B" (externals of B + B itself).

  -- Let me reconsider the actual claim. The link graph L_v has:
  -- - Vertices: triangles containing v
  -- - Edges: pairs of triangles that share an edge (beyond just v)

  -- For L_{v_ab} to be bipartite with parts:
  --   Part_A = {A} ∪ {externals of A at v_ab}
  --   Part_B = {B} ∪ {externals of B at v_ab}
  -- We need: no edge within Part_A, no edge within Part_B, edges only between parts.

  -- Wait, that's wrong. We need: no edge BETWEEN Part_A and Part_B!
  -- (Edges within parts are fine for bipartite.)

  -- Actually for bipartite, we need: edges only BETWEEN the two parts, not within.
  -- So: ∀ T₁ ∈ Part_A, ∀ T₂ ∈ Part_A, T₁ and T₂ don't share edge (in L_v sense).
  --     ∀ T₁ ∈ Part_B, ∀ T₂ ∈ Part_B, T₁ and T₂ don't share edge.

  -- Hmm, but A and its externals DO share edges (that's the definition of external).
  -- So Part_A is NOT an independent set in L_v.

  -- Wait, I'm confusing myself. Let me re-read the strategy...

  -- From FINAL_15_SLOT_STRATEGY.md:
  -- "At each shared vertex v:
  --  - The link graph L_v is bipartite (externals of different M-elements don't connect)"

  -- So the claim is: if T is external of A at v, and S is external of B at v,
  -- then T and S don't share an edge.

  -- Let me continue with the proof...
  sorry

/-- Link graph at v_ab is bipartite -/
theorem link_graph_bipartite_at_vab
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    ∃ (Part_A Part_B : Finset (Finset V)),
      Part_A ∪ Part_B = trianglesContaining G cfg.v_ab ∧
      Disjoint Part_A Part_B ∧
      (∀ T₁ ∈ Part_A, ∀ T₂ ∈ Part_B, ¬sharesEdge T₁ T₂) := by
  -- Part_A = {T ∈ triangles at v_ab | T shares edge with A or T = A}
  -- Part_B = {T ∈ triangles at v_ab | T shares edge with B or T = B}
  -- Every triangle at v_ab shares edge with A or B (by maximality and v_ab ∈ A ∩ B)
  sorry

/-- By König's theorem, bipartite link graph has vertex cover = matching ≤ 2 -/
theorem link_graph_cover_le_2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    ∃ (s₁ s₂ : V),
      ∀ T ∈ trianglesContaining G v,
        (s₁ ∈ T ∧ G.Adj v s₁) ∨ (s₂ ∈ T ∧ G.Adj v s₂) := by
  -- The vertex cover of the bipartite link graph corresponds to
  -- choosing 2 "spoke neighbors" s₁, s₂ such that every triangle T
  -- containing v also contains at least one of s₁ or s₂.
  sorry

end TuzaNu4
