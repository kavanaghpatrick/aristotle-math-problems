/-
Tuza ν=4 Strategy - Slot 56: Close the Avoiding-Spokes Gap

EXACT GAP IDENTIFIED (from slot35, line 325):
`avoiding_covered_by_spokes` has a sorry. If proven, τ(T_pair) ≤ 4 follows.

THE CLAIM TO PROVE:
If t ∈ trianglesAvoiding(T_pair) and t has some vertex x ∈ (e ∪ f) \ {v},
then some spoke s(v,y) for y ∈ (e ∪ f) \ {v} is in t.sym2.

WHY THIS MIGHT BE FALSE (and why it needs careful analysis):
- t avoids v, so v ∉ t
- So s(v,y) ∈ t.sym2 means {v,y} is an edge of t
- But t doesn't contain v! So s(v,y) ∉ t.sym2 for any y

WAIT - the lemma as stated seems FALSE. Let me re-examine...

REREAD OF SLOT35:
The lemma `avoiding_covered_by_spokes` says:
"If t avoids v but has vertex x ∈ (e ∪ f) \ {v}, then some spoke is in t.sym2"

But a spoke is s(v,x) which requires v to be in the triangle!
This is a CONTRADICTION - t avoids v means v ∉ t, so no spoke s(v,*) can be in t.

RESOLUTION:
The real insight is that if t avoids v and shares edge with e = {v,a,b}:
- t ∩ e ≥ 2 (shares edge)
- v ∉ t (avoids v)
- So t ∩ e = {a,b} exactly
- t = {a,b,x} for some x

Now, where can x come from?
- If x ∈ f = {v,c,d}: Since x ≠ v (t avoids v), x ∈ {c,d}
  - Then t = {a,b,c} or {a,b,d}
  - Such t shares vertex with both e and f!
  - t ∩ e = {a,b} (2 vertices), t ∩ f = {c} or {d} (1 vertex)
  - Wait, that's still only 1 vertex with f, not an edge

- If x ∉ e ∪ f:
  - t = {a,b,x} with x "external"
  - Does such t exist? This is the MAXIMALITY question from slot55!

KEY INSIGHT: The gap is NOT about spokes covering avoiding triangles.
The gap is: DO avoiding triangles even exist?

APPROACHES TO PROVE avoiding = ∅:

1. MAXIMALITY (slot55 attempt):
   If t = {a,b,x} shares edge with e = {v,a,b} but x ∉ e ∪ f,
   then we could potentially swap e for t in the packing.
   But this doesn't contradict maximality - just gives another max packing.

2. STRUCTURE OF T_pair:
   T_pair = trianglesSharingEdge(e) ∪ trianglesSharingEdge(f)

   For t to be in T_pair and avoid v:
   - t shares edge with e AND avoids v: t ∩ e = {a,b}
   OR
   - t shares edge with f AND avoids v: t ∩ f = {c,d}

   Case A: t ∩ e = {a,b}, t = {a,b,x}
   - If t also shares edge with f = {v,c,d}: impossible since t ∩ f ⊆ {x} and x ≠ v
   - So t is in T_pair ONLY from the e side

   Case B: t ∩ f = {c,d}, t = {c,d,y}
   - Similarly, in T_pair ONLY from the f side

So avoiding triangles come in two disjoint classes:
- Class A: {a,b,x} triangles (share edge {a,b} with e)
- Class B: {c,d,y} triangles (share edge {c,d} with f)

Each class can be covered by ONE edge:
- Class A: covered by edge {a,b}
- Class B: covered by edge {c,d}

So τ(avoiding) ≤ 2, and with containing ≤ 4, we get τ(T_pair) ≤ 6.
But we need ≤ 4!

THE REAL INSIGHT: The containing triangles are covered by spokes.
Spokes are {v,a}, {v,b}, {v,c}, {v,d} - exactly 4 edges.
If we use {a,b}, {c,d} instead of two spokes, we ALSO cover avoiding!

REFINED COVER:
Use edges {v,a}, {v,b}, {a,b}, {c,d} - 4 edges total.
- {v,a} covers triangles with edge {v,a}
- {v,b} covers triangles with edge {v,b}
- {a,b} covers triangles with edge {a,b} (including Class A avoiding)
- {c,d} covers triangles with edge {c,d} (including Class B avoiding)

But wait - we also need to cover triangles containing {v,c} and {v,d}!
Our cover {v,a}, {v,b}, {a,b}, {c,d} misses triangles like {v,c,x}.

BETTER COVER:
{a,b}, {c,d}, {v,a}, {v,c} - 4 edges
Check coverage:
- {a,b}: covers {a,b,*} triangles ✓
- {c,d}: covers {c,d,*} triangles ✓
- {v,a}: covers {v,a,*} triangles ✓
- {v,c}: covers {v,c,*} triangles ✓

Remaining to check:
- {v,b,*} triangles: need {v,b} ∈ cover or {b,*} ∈ cover
  - If * = a: {v,b,a} covered by {v,a} or {a,b} ✓
  - If * = c: {v,b,c} covered by {v,c} ✓
  - If * = d: {v,b,d} needs {v,b} or {b,d} or {v,d}... NOT COVERED!

So {v,b,d} is not covered by {a,b}, {c,d}, {v,a}, {v,c}.

CONCLUSION: There's no 4-edge cover that works universally.
The 4-spoke cover {v,a}, {v,b}, {v,c}, {v,d} covers all CONTAINING but misses AVOIDING.
Alternative covers might cover some avoiding but miss some containing.

THIS IS THE HARD PART OF THE PROBLEM.

NEW STRATEGY: Prove avoiding is actually EMPTY via packing structure.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot35)
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

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY STRUCTURAL LEMMA: Avoiding triangles have specific form
-- ══════════════════════════════════════════════════════════════════════════════

/--
An avoiding triangle t that shares edge with e = {v,a,b} must have t ∩ e = {a,b}.
-/
lemma avoiding_shares_base_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (v a b : V) (he : e = {v, a, b})
    (hv_ne_a : v ≠ a) (hv_ne_b : v ≠ b) (ha_ne_b : a ≠ b)
    (t : Finset V) (ht_tri : t ∈ G.cliqueFinset 3)
    (ht_shares : (t ∩ e).card ≥ 2) (ht_avoids : v ∉ t) :
    t ∩ e = {a, b} := by
  have h_sub : t ∩ e ⊆ {a, b} := by
    intro x hx
    simp only [Finset.mem_inter] at hx
    rw [he] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 ht_avoids
    · exact Finset.mem_insert_self a {b}
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have h_card_ab : ({a, b} : Finset V).card = 2 := by
    simp [Finset.card_insert_of_not_mem, ha_ne_b]
  have h_card_le : (t ∩ e).card ≤ 2 := by
    calc (t ∩ e).card ≤ ({a, b} : Finset V).card := Finset.card_le_card h_sub
      _ = 2 := h_card_ab
  exact Finset.eq_of_subset_of_card_le h_sub (by omega)

/--
All avoiding triangles that share edge with e are covered by edge {a,b}.
-/
lemma avoiding_e_covered_by_ab (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (v a b : V) (he : e = {v, a, b})
    (hv_ne_a : v ≠ a) (hv_ne_b : v ≠ b) (ha_ne_b : a ≠ b)
    (hab_edge : G.Adj a b)
    (t : Finset V) (ht_tri : t ∈ G.cliqueFinset 3)
    (ht_shares : (t ∩ e).card ≥ 2) (ht_avoids : v ∉ t) :
    s(a, b) ∈ t.sym2 := by
  have h_inter : t ∩ e = {a, b} := avoiding_shares_base_edge G e v a b he hv_ne_a hv_ne_b ha_ne_b t ht_tri ht_shares ht_avoids
  have hab_sub_t : {a, b} ⊆ t := by
    rw [← h_inter]; exact Finset.inter_subset_left
  have ha_in_t : a ∈ t := hab_sub_t (Finset.mem_insert_self a {b})
  have hb_in_t : b ∈ t := hab_sub_t (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  exact Finset.mk_mem_sym2_iff.mpr ⟨ha_in_t, hb_in_t⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROOF ATTEMPT: τ(avoiding) ≤ 2 via base edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
The avoiding triangles in T_pair split into two disjoint classes:
1. Those sharing edge {a,b} with e (but not edge with f)
2. Those sharing edge {c,d} with f (but not edge with e)
Each class is covered by one edge, so τ(avoiding) ≤ 2.
-/
lemma tau_avoiding_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v a b c d : V)
    (he_eq : e = {v, a, b}) (hf_eq : f = {v, c, d})
    (hv : e ∩ f = {v})
    (hdistinct_e : v ≠ a ∧ v ≠ b ∧ a ≠ b)
    (hdistinct_f : v ≠ c ∧ v ≠ d ∧ c ≠ d)
    (hab : G.Adj a b) (hcd : G.Adj c d) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  -- Cover: {a,b} covers Class A, {c,d} covers Class B
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE: Prove avoiding = ∅ using the fact that
-- avoiding triangles can't share edge with BOTH e and f
-- ══════════════════════════════════════════════════════════════════════════════

/--
If t avoids v and shares edge with e, it cannot share edge with f.
Therefore avoiding triangles are "single-sided" in T_pair.
-/
lemma avoiding_single_sided (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v a b c d : V)
    (he_eq : e = {v, a, b}) (hf_eq : f = {v, c, d})
    (hv : e ∩ f = {v})
    (hdistinct_e : v ≠ a ∧ v ≠ b ∧ a ≠ b)
    (hdistinct_f : v ≠ c ∧ v ≠ d ∧ c ≠ d)
    (h_disjoint : ({a, b} : Finset V) ∩ {c, d} = ∅)  -- from e ∩ f = {v}
    (t : Finset V) (ht_tri : t ∈ G.cliqueFinset 3)
    (ht_avoids : v ∉ t)
    (ht_shares_e : (t ∩ e).card ≥ 2)
    (ht_shares_f : (t ∩ f).card ≥ 2) :
    False := by
  -- t ∩ e = {a,b} and t ∩ f = {c,d}, so {a,b,c,d} ⊆ t
  -- But t has only 3 vertices, and {a,b} ∩ {c,d} = ∅ means |{a,b,c,d}| = 4
  -- Contradiction!
  have he_inter : t ∩ e = {a, b} := avoiding_shares_base_edge G e v a b he_eq hdistinct_e.1 hdistinct_e.2.1 hdistinct_e.2.2 t ht_tri ht_shares_e ht_avoids
  have hf_inter : t ∩ f = {c, d} := avoiding_shares_base_edge G f v c d hf_eq hdistinct_f.1 hdistinct_f.2.1 hdistinct_f.2.2 t ht_tri ht_shares_f ht_avoids
  have hab_sub : {a, b} ⊆ t := by rw [← he_inter]; exact Finset.inter_subset_left
  have hcd_sub : {c, d} ⊆ t := by rw [← hf_inter]; exact Finset.inter_subset_left
  have habcd_sub : ({a, b} : Finset V) ∪ {c, d} ⊆ t := Finset.union_subset hab_sub hcd_sub
  have h_card_abcd : (({a, b} : Finset V) ∪ {c, d}).card = 4 := by
    rw [Finset.card_union_of_disjoint h_disjoint]
    simp [Finset.card_insert_of_not_mem, hdistinct_e.2.2, hdistinct_f.2.2]
  have h_t_card : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_tri
    exact ht_tri.2
  have h_le : (({a, b} : Finset V) ∪ {c, d}).card ≤ t.card := Finset.card_le_card habcd_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ(T_pair) ≤ 4 when e ∩ f = {v}.

Using the avoiding_single_sided lemma, we know avoiding triangles come from
only one side (e or f) and can be covered by base edges.
Combined with spokes for containing triangles, total ≤ 4.
-/
theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v a b c d : V)
    (he_eq : e = {v, a, b}) (hf_eq : f = {v, c, d})
    (hv : e ∩ f = {v})
    (hdistinct : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d ∧ a ≠ b ∧ c ≠ d)
    (h_abcd_disjoint : ({a, b} : Finset V) ∩ {c, d} = ∅) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- Decompose T_pair = containing ∪ avoiding
  have h_decomp : T_pair G e f =
      trianglesContaining (T_pair G e f) v ∪ trianglesAvoiding (T_pair G e f) v := by
    ext t; simp [trianglesContaining, trianglesAvoiding]; tauto

  -- τ(containing) ≤ 4 via spokes {v,a}, {v,b}, {v,c}, {v,d}
  -- τ(avoiding) ≤ 2 via base edges {a,b}, {c,d}
  -- But τ(T_pair) ≤ τ(containing) + τ(avoiding) ≤ 6... too loose!

  -- The key insight: the cover can SHARE edges between containing and avoiding
  -- Specifically: if we use {a,b} and {c,d} as part of the cover,
  -- they cover some containing triangles TOO (e and f themselves)

  -- Claim: {a,b}, {c,d}, {v,a}, {v,c} covers everything
  -- But this misses {v,b,d} as shown in the header analysis

  -- Alternative: prove that the avoiding set is actually empty
  -- because any avoiding triangle would share edge with ONLY one of e,f
  -- and such triangles either don't exist or are covered by the 4 spokes

  sorry

end
