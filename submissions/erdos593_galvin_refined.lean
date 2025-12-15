/-
Erdős Problem #593 - Hypergraphs with Uncountable Chromatic Number
$500 Prize - GALVIN-STYLE CHARACTERIZATION

PROBLEM: Characterize finite 3-uniform hypergraphs appearing in EVERY
3-uniform hypergraph with chromatic number > ℵ₀.

FROM ERDŐS: "For graphs the problem is completely solved: a graph of
chromatic number ≥ ℵ₁ must contain all finite bipartite graphs but
need not contain any fixed odd cycle."

EXPECTED ANSWER FOR HYPERGRAPHS:
H is unavoidable ↔ H has Property B (is 2-colorable)

PROOF STRATEGY:

DIRECTION 1 (Galvin): 2-colorable → unavoidable
- Define "Complete Bipartite 3-Hypergraph" K(A,B) with edges intersecting both parts
- Lemma: Any 2-colorable H embeds into some finite K(A,B)
- Generalized Galvin: Any G with χ > ℵ₀ contains K(n,n) for all finite n
- Transitivity: H ⊆ K(A,B) ⊆ G

DIRECTION 2 (Avoidance): NOT 2-colorable → avoidable
- If H lacks Property B, construct G with χ > ℵ₀ that avoids H
- Use "high girth" constructions (Erdős-Hajnal type)
- Such G exists by probabilistic method / explicit constructions
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Classical Cardinal
open Set Function Cardinal

set_option maxHeartbeats 400000

noncomputable section

/-! ## Core Definitions -/

/-- A 3-uniform hypergraph: edges are sets of exactly 3 vertices -/
structure Hypergraph3 (V : Type*) where
  edges : Set (Set V)
  uniform : ∀ e ∈ edges, e.ncard = 3

variable {V W U : Type*}

/-- Property B: Vertices can be 2-colored such that no edge is monochromatic.
    Equivalently: vertices partition into two parts, no edge contained in one part. -/
def HasPropertyB (H : Hypergraph3 V) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- Alternative: partition into two non-trivially intersecting each edge -/
def HasPropertyB' (H : Hypergraph3 V) : Prop :=
  ∃ (A : Set V), ∀ e ∈ H.edges, (e ∩ A).Nonempty ∧ (e ∩ Aᶜ).Nonempty

/-- These definitions are equivalent -/
lemma propertyB_iff_propertyB' (H : Hypergraph3 V) :
    HasPropertyB H ↔ HasPropertyB' H := by
  constructor
  · intro ⟨c, hc⟩
    use {v | c v = true}
    intro e he
    obtain ⟨x, hx, y, hy, hne⟩ := hc e he
    constructor
    · cases hcx : c x
      · use y; simp [hcx] at hne ⊢; exact ⟨hy, hne.symm⟩
      · use x; exact ⟨hx, hcx⟩
    · cases hcx : c x
      · use x; simp; exact ⟨hx, hcx⟩
      · use y; simp at hne ⊢; exact ⟨hy, fun h => hne (hcx.trans h.symm)⟩
  · intro ⟨A, hA⟩
    use fun v => if v ∈ A then true else false
    intro e he
    obtain ⟨⟨x, hxe, hxA⟩, ⟨y, hye, hyA⟩⟩ := hA e he
    use x, hxe, y, hye
    simp [hxA, hyA]

/-- A proper coloring: no edge is monochromatic -/
def IsProperColoring (H : Hypergraph3 V) (c : V → ℕ) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- Chromatic number > ℵ₀: no countable coloring is proper -/
def HasUncountableChromatic (H : Hypergraph3 V) : Prop :=
  ∀ (c : V → ℕ), ¬ IsProperColoring H c

/-- H embeds into G as a subhypergraph -/
def EmbedsInto (H : Hypergraph3 U) (G : Hypergraph3 W) : Prop :=
  ∃ f : U → W, Injective f ∧ ∀ e ∈ H.edges, (f '' e) ∈ G.edges

/-- H is unavoidable: appears in every hypergraph with χ > ℵ₀ -/
def IsUnavoidable (H : Hypergraph3 V) : Prop :=
  Finite V ∧ ∀ (W : Type*) (G : Hypergraph3 W), HasUncountableChromatic G → EmbedsInto H G

/-! ## Complete Bipartite 3-Hypergraph -/

/-- The complete bipartite 3-hypergraph K(A,B): all 3-element sets that
    intersect BOTH A and B (not contained entirely in either) -/
def CompleteBipartite3 (A B : Set W) : Set (Set W) :=
  {e | e.ncard = 3 ∧ e ⊆ A ∪ B ∧ (e ∩ A).Nonempty ∧ (e ∩ B).Nonempty}

/-- K(A,B) forms a valid 3-uniform hypergraph when A, B are disjoint -/
def CompleteBipartite3Hyper (A B : Set W) (h_disj : Disjoint A B) : Hypergraph3 W :=
  { edges := CompleteBipartite3 A B,
    uniform := fun e he => he.1 }

/-! ## Direction 1: 2-colorable → Unavoidable -/

/-- If H has Property B, it embeds into a complete bipartite hypergraph -/
lemma propertyB_embeds_complete_bipartite [Finite V] (H : Hypergraph3 V)
    (hB : HasPropertyB H) :
    ∃ (A B : Set V), Disjoint A B ∧ A ∪ B = Set.univ ∧
    ∀ e ∈ H.edges, e ∈ CompleteBipartite3 A B := by
  rw [propertyB_iff_propertyB'] at hB
  obtain ⟨A, hA⟩ := hB
  use A, Aᶜ
  refine ⟨disjoint_compl_right, union_compl_self A, ?_⟩
  intro e he
  obtain ⟨hinter_A, hinter_Ac⟩ := hA e he
  refine ⟨H.uniform e he, ?_, hinter_A, ?_⟩
  · intro x hx; exact Set.mem_union_left _ hx <|> exact Set.mem_union_right _ hx
  · simp only [Set.compl_eq_univ_diff] at hinter_Ac ⊢
    convert hinter_Ac using 1
    ext; simp [Set.mem_inter_iff, Set.mem_diff]

/-- KEY LEMMA (Generalized Galvin): Any hypergraph with χ > ℵ₀ contains
    arbitrarily large complete bipartite subhypergraphs.

    This is the deep Ramsey-theoretic content. -/
lemma uncountable_chromatic_contains_complete_bipartite (n : ℕ) (G : Hypergraph3 W)
    (hchi : HasUncountableChromatic G) :
    ∃ (A B : Set W), Disjoint A B ∧ A.ncard = n ∧ B.ncard = n ∧
    CompleteBipartite3 A B ⊆ G.edges := by
  sorry

/-- Embedding transitivity -/
lemma embedsInto_trans {H : Hypergraph3 U} {K : Hypergraph3 V} {G : Hypergraph3 W}
    (h1 : EmbedsInto H K) (h2 : EmbedsInto K G) : EmbedsInto H G := by
  obtain ⟨f, hf_inj, hf_edges⟩ := h1
  obtain ⟨g, hg_inj, hg_edges⟩ := h2
  use g ∘ f
  constructor
  · exact hg_inj.comp hf_inj
  · intro e he
    have hfe : f '' e ∈ K.edges := hf_edges e he
    have : g '' (f '' e) ∈ G.edges := hg_edges (f '' e) hfe
    convert this using 1
    ext w
    simp only [Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨f u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩

/-- DIRECTION 1: Property B implies unavoidable -/
theorem propertyB_implies_unavoidable [Finite V] (H : Hypergraph3 V)
    (hB : HasPropertyB H) : IsUnavoidable H := by
  constructor
  · exact ‹Finite V›
  · intro W G hchi
    -- H embeds into K(A,B) where A,B are color classes
    obtain ⟨A, B, h_disj, h_univ, h_edges⟩ := propertyB_embeds_complete_bipartite H hB
    -- G contains some K(A',B') of sufficient size
    have hn : ∃ n, Fintype.card V ≤ n := ⟨Fintype.card V, le_refl _⟩
    obtain ⟨n, hn⟩ := hn
    obtain ⟨A', B', h_disj', hA'_card, hB'_card, h_subset⟩ :=
      uncountable_chromatic_contains_complete_bipartite n G hchi
    -- Construct embedding
    sorry

/-! ## Direction 2: NOT Property B → Avoidable -/

/-- KEY LEMMA: There exist hypergraphs with χ > ℵ₀ that avoid any fixed
    non-2-colorable finite hypergraph.

    Construction: "High girth" hypergraphs via probabilistic method or
    explicit Erdős-Hajnal type constructions. -/
lemma exists_avoiding_high_chromatic [Finite V] (H : Hypergraph3 V)
    (hnotB : ¬ HasPropertyB H) :
    ∃ (W : Type*) (G : Hypergraph3 W), HasUncountableChromatic G ∧ ¬ EmbedsInto H G := by
  sorry

/-- DIRECTION 2: NOT Property B implies avoidable -/
theorem not_propertyB_implies_avoidable [Finite V] (H : Hypergraph3 V)
    (hnotB : ¬ HasPropertyB H) : ¬ IsUnavoidable H := by
  intro ⟨_, hforall⟩
  obtain ⟨W, G, hchi, hnotEmbed⟩ := exists_avoiding_high_chromatic H hnotB
  exact hnotEmbed (hforall W G hchi)

/-! ## Main Characterization -/

/-- THE ERDŐS #593 CHARACTERIZATION THEOREM:
    A finite 3-uniform hypergraph is unavoidable ↔ it has Property B -/
theorem erdos_593_characterization [Finite V] (H : Hypergraph3 V) :
    IsUnavoidable H ↔ HasPropertyB H := by
  constructor
  · -- Unavoidable → Property B (contrapositive of Direction 2)
    intro h_unavoid
    by_contra h_notB
    exact not_propertyB_implies_avoidable H h_notB h_unavoid
  · -- Property B → Unavoidable (Direction 1)
    exact propertyB_implies_unavoidable H

/-! ## Examples -/

/-- The single-edge hypergraph {a,b,c} has Property B -/
example : HasPropertyB ⟨{{(0 : Fin 3), 1, 2}}, by simp [Set.ncard]⟩ := by
  use fun v => v = 0
  intro e he
  simp at he
  subst he
  use 0, by simp
  use 1, by simp

/-- The Fano plane does NOT have Property B (classical result) -/
-- This would require explicit construction of Fano plane

end
