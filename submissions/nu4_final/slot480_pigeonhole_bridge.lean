/-
  slot480_pigeonhole_bridge.lean

  FOCUSED: Prove that a triangle can share ≥2 vertices with at most 2
  elements of a triangle packing.

  KEY INSIGHT (Pigeonhole):
  - t has 3 vertices
  - If t shares ≥2 with m1, m2, m3 (three distinct packing elements)
  - Then |t ∩ m1| + |t ∩ m2| + |t ∩ m3| ≥ 6
  - By pigeonhole on 3 vertices, some vertex v is in all three
  - So v ∈ m1 ∩ m2, v ∈ m1 ∩ m3, v ∈ m2 ∩ m3
  - The packing condition says |mi ∩ mj| ≤ 1
  - Let t ∩ m1 = {v, a}, t ∩ m2 = {v, b}, t ∩ m3 = {v, c} (each ≥2)
  - But t = {v, a, b} has only 3 vertices, so c ∈ {v, a, b}
  - If c = a: then a ∈ m1 ∩ m3, so m1 ∩ m3 contains both v and a → |m1 ∩ m3| ≥ 2
  - Contradiction with packing!

  TIER: 1-2 (pigeonhole + cardinality)
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

-- Set of M-elements that triangle t shares ≥2 vertices with
def shareTwoWith (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  M.filter (fun m => (t ∩ m).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: If t shares ≥2 with 3 elements, there's a common vertex
-- ══════════════════════════════════════════════════════════════════════════════

/--
If a set of 3 elements (triangle t) has ≥2 elements in common with each of
three sets m1, m2, m3, then there exists a vertex v in all four sets.

PROOF SKETCH:
- |t ∩ m1| ≥ 2, |t ∩ m2| ≥ 2, |t ∩ m3| ≥ 2
- Sum ≥ 6, but t has only 3 elements
- By pigeonhole, some element v is counted at least ⌈6/3⌉ = 2 times
- Actually stronger: v must be in t ∩ m1 ∩ m2 ∩ m3
-/
lemma common_vertex_of_three_shares (t m1 m2 m3 : Finset V)
    (ht_card : t.card = 3)
    (h1 : (t ∩ m1).card ≥ 2)
    (h2 : (t ∩ m2).card ≥ 2)
    (h3 : (t ∩ m3).card ≥ 2)
    (h12 : m1 ≠ m2) (h13 : m1 ≠ m3) (h23 : m2 ≠ m3) :
    ∃ v, v ∈ t ∧ v ∈ m1 ∧ v ∈ m2 ∧ v ∈ m3 := by
  -- t has 3 vertices, call them a, b, c
  have ⟨a, b, c, hab, hbc, hac, ht_eq⟩ : ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ t = {a, b, c} := by
    have h3 := ht_card
    rw [card_eq_three] at h3
    obtain ⟨a, b, c, hab, hac, hbc, heq⟩ := h3
    exact ⟨a, b, c, hab, hbc.symm, hac, heq⟩
  -- Each intersection has ≥2 of {a, b, c}
  -- t ∩ m1 ∈ {{a,b}, {a,c}, {b,c}, {a,b,c}}
  rw [ht_eq] at h1 h2 h3
  -- The only subsets of {a,b,c} with ≥2 elements are:
  -- {a,b}, {a,c}, {b,c}, {a,b,c}
  -- We need to show one of a,b,c is in all three of m1, m2, m3

  -- Count: how many times does each vertex appear across the three intersections?
  -- If a ∈ m1 ∩ m2 ∩ m3, we're done. Similarly for b, c.
  -- If no vertex is in all three, then each vertex is in at most 2 of {m1, m2, m3}
  -- But then total intersection size ≤ 3 × 2 = 6... wait that's not a contradiction directly

  -- Better approach: use that t ∩ mi ⊆ t, so t ∩ mi ⊆ {a,b,c}
  -- |t ∩ m1| ≥ 2 means at least 2 of {a,b,c} are in m1
  -- Same for m2, m3
  -- Total "hits" ≥ 2 + 2 + 2 = 6
  -- But only 3 vertices, so by pigeonhole, some vertex has ≥ 2 hits
  -- Actually we need ≥ 3 hits (in all of m1, m2, m3)

  -- Let's count: for vertex x ∈ {a,b,c}, let f(x) = |{i : x ∈ mi}|
  -- Sum over x: f(a) + f(b) + f(c) = |{(x,i) : x ∈ t ∩ mi}|
  --                                = |t ∩ m1| + |t ∩ m2| + |t ∩ m3|
  --                                ≥ 2 + 2 + 2 = 6
  -- Since f(x) ≤ 3 for each x (can be in at most 3 sets), and sum ≥ 6
  -- If all f(x) ≤ 2, then sum ≤ 3 × 2 = 6
  -- Equality means each f(x) = 2 exactly
  -- But we need sum ≥ 6, so either some f(x) = 3 (done!) or all f(x) = 2

  -- Case: all f(x) = 2
  -- Then a is in exactly 2 of {m1, m2, m3}, say {m1, m2}
  -- b is in exactly 2, and c is in exactly 2
  -- Total pairs: (a in m1), (a in m2), (b in ?), (b in ?), (c in ?), (c in ?)
  -- Each mi gets exactly 2 vertices (since |t ∩ mi| ≥ 2 and t ∩ mi ⊆ {a,b,c})
  -- Wait, but we assumed |t ∩ mi| ≥ 2, and t has 3 elements
  -- If a ∈ m1, a ∈ m2, a ∉ m3
  -- Then t ∩ m3 ⊆ {b, c}, so |t ∩ m3| ≤ 2
  -- For |t ∩ m3| ≥ 2, we need t ∩ m3 = {b, c}
  -- Similarly, b is in 2 of {m1,m2,m3}, say not in m1 (since a ∈ m1, b ∈ m3, need b in m2)
  -- c is in 2 of {m1,m2,m3}, say not in m2 (since a ∈ m2, c ∈ m3, need c in m1)
  -- Check: m1 gets {a, c}, m2 gets {a, b}, m3 gets {b, c} ✓
  -- So each mi gets exactly 2 vertices, and the sum is exactly 6.

  -- In the "all f(x) = 2" case, we need to find a contradiction or extract a vertex
  -- Actually no - the "all f(x) = 2" case is possible! Example:
  --   t = {a,b,c}, m1 = {a,c,d}, m2 = {a,b,e}, m3 = {b,c,f}
  --   t ∩ m1 = {a,c}, t ∩ m2 = {a,b}, t ∩ m3 = {b,c}
  --   No vertex is in all three mi.
  -- So the lemma as stated is FALSE!

  -- Let me re-examine the original claim...
  -- Actually, we don't need a vertex in all three mi.
  -- We need to show that |shareTwoWith t M| ≤ 2 for a packing M.
  -- The packing condition |mi ∩ mj| ≤ 1 is key!

  -- Let me restart with the packing constraint.
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Triangle shares ≥2 with at most 2 packing elements
-- ══════════════════════════════════════════════════════════════════════════════

/--
A triangle can share ≥2 vertices with at most 2 elements of a packing.

PROOF SKETCH (using packing condition):
Suppose t shares ≥2 with m1, m2, m3 (distinct packing elements).
- t ∩ m1 = {v, a} for some v, a ∈ t
- t ∩ m2 = {w, b} for some w, b ∈ t
- t ∩ m3 = {x, c} for some x, c ∈ t

t = {p, q, r} has 3 vertices.
{v, a}, {w, b}, {x, c} are all 2-subsets of {p, q, r}.
The 2-subsets of {p,q,r} are: {p,q}, {p,r}, {q,r} (exactly 3).

So each (t ∩ mi) is one of these three 2-subsets.
If m1, m2, m3 each take a different 2-subset:
- t ∩ m1 = {p, q}
- t ∩ m2 = {p, r}
- t ∩ m3 = {q, r}

Then p ∈ m1 ∩ m2, so |m1 ∩ m2| ≥ 1. Packing says ≤ 1. ✓
And q ∈ m1 ∩ m3, so |m1 ∩ m3| ≥ 1. ✓
And r ∈ m2 ∩ m3, so |m2 ∩ m3| ≥ 1. ✓

Hmm, this satisfies the packing condition...

Wait, the packing condition applies to the TRIANGLES mi, not their intersections with t.
Let me re-examine.

Packing: |m1 ∩ m2| ≤ 1 means m1 and m2 share at most 1 vertex.

From t ∩ m1 = {p, q} and t ∩ m2 = {p, r}:
- p ∈ m1, q ∈ m1, p ∈ m2, r ∈ m2
- m1 ∩ m2 ⊇ {p}

This is consistent with |m1 ∩ m2| ≤ 1 if m1 ∩ m2 = {p}.

Now from t ∩ m1 = {p, q} and t ∩ m3 = {q, r}:
- q ∈ m1, q ∈ m3
- m1 ∩ m3 ⊇ {q}

From t ∩ m2 = {p, r} and t ∩ m3 = {q, r}:
- r ∈ m2, r ∈ m3
- m2 ∩ m3 ⊇ {r}

So: m1 ∩ m2 = {p}, m1 ∩ m3 = {q}, m2 ∩ m3 = {r}

This IS consistent with a valid packing!
So a triangle CAN share ≥2 with THREE packing elements.

But wait - let's check if m1, m2, m3 can actually be triangles:
- m1 ⊇ {p, q} ⊆ t
- m2 ⊇ {p, r} ⊆ t
- m3 ⊇ {q, r} ⊆ t

If m1 = {p, q, s1}, m2 = {p, r, s2}, m3 = {q, r, s3} where s1, s2, s3 ∉ t:
- m1 ∩ m2 = {p} ✓ (since s1, s2 are distinct from each other and from t)
- m1 ∩ m3 = {q} ✓
- m2 ∩ m3 = {r} ✓

So yes, this is a valid packing with t sharing ≥2 with all three!

CONCLUSION: The original lemma is FALSE. Need different approach.
-/
lemma triangle_shares_with_at_most_two_WRONG (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (shareTwoWith t M).card ≤ 2 := by
  -- THIS LEMMA IS FALSE - see counterexample above
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CORRECT APPROACH: Don't need this lemma!
-- ══════════════════════════════════════════════════════════════════════════════

/--
The correct insight: we don't need to bound how many M-elements t shares with.

Instead: every triangle t shares an EDGE with at least one M-element
(by maximality). That edge is covered by the 2 edges we pick from that element.

The 6-packing constraint ensures that for each M-element, the 2 edges we pick
cover all triangles that are "internal" to that element (in S_e).

For bridges: they share edges with multiple M-elements. The edges we pick
from ANY of those elements will cover the bridge.

The key is that our cover has 4×2 = 8 edges, and every triangle shares at
least one edge with the cover (through whichever M-element it's closest to).
-/

-- The approach that DOES work:
-- 1. Every triangle t shares ≥2 with some m ∈ M (maximality)
-- 2. Therefore t shares at least one EDGE with m
-- 3. m contributes 2 edges to cover; one of them might cover t
-- 4. If not, t is a "missed external" for m
-- 5. The 6-packing constraint limits missed externals
-- 6. But bridges are not externals! They share with multiple M-elements.
-- 7. For bridges: they share edge with m AND with some other m'
-- 8. So they get "two chances" to be covered

-- The proof needs to show: if t is missed by the 2 edges from m,
-- then t shares edge with some other m' ∈ M, and that edge covers t.

theorem tau_le_8_correct_approach (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  -- The construction: pick ALL edges from ALL M-elements
  -- That's at most 4 × 3 = 12 edges, but many are shared
  -- Hmm, that doesn't give ≤ 8

  -- Better: use the 6-packing constraint to pick 2 edges per M-element
  -- Then use coverage argument

  sorry

end
