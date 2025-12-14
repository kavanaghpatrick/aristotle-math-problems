/-
Erdős Problem #593 - PIVOT to Galvin's Theorem Approach
$500 Prize - OPEN

PROBLEM: Characterize finite 3-uniform hypergraphs appearing in EVERY
3-uniform hypergraph with chromatic number > ℵ₀.

INSIGHT (from Gemini analysis):
- Previous approach (incidence graph bipartiteness) was WRONG - trivially true for all hypergraphs
- Correct approach: Generalize Galvin's Theorem from graphs to hypergraphs

GALVIN'S THEOREM (for graphs):
Every graph with χ > ℵ₀ contains every finite bipartite graph as subgraph.

HYPERGRAPH CONJECTURE:
Every 3-uniform hypergraph with χ > ℵ₀ contains every finite 2-colorable
3-uniform hypergraph as a subhypergraph.

EXPECTED CHARACTERIZATION:
H appears in all uncountable chromatic hypergraphs ↔ H is 2-colorable

KEY: 2-colorable means "has Property B" - vertices can be 2-colored so no edge is monochromatic.
This is DIFFERENT from incidence graph bipartiteness!
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Cardinal

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Set Function Cardinal

/-! ### Definitions -/

/-- A 3-uniform hypergraph: edges are sets of exactly 3 vertices -/
structure Hypergraph3 (V : Type*) where
  edges : Set (Set V)
  uniform : ∀ e ∈ edges, e.ncard = 3

/-- Property B: A hypergraph is 2-colorable if vertices can be colored with 2 colors
    such that NO edge is monochromatic (every edge has both colors) -/
def Has2Coloring {V : Type*} (H : Hypergraph3 V) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- A proper coloring: no edge is monochromatic -/
def IsProperColoring {V C : Type*} (H : Hypergraph3 V) (c : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- Chromatic number > ℵ₀: no countable coloring works -/
def HasUncountableChromatic {V : Type*} (H : Hypergraph3 V) : Prop :=
  ∀ (c : V → ℕ), ¬ IsProperColoring H c

/-- H embeds into G as a subhypergraph -/
def EmbedsInto {V W : Type*} (H : Hypergraph3 V) (G : Hypergraph3 W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ e ∈ H.edges, (f '' e) ∈ G.edges

/-- H appears in every hypergraph with uncountable chromatic number -/
def AppearsInAllUncountableChromatic {V : Type*} (H : Hypergraph3 V) : Prop :=
  Finite V ∧ ∀ (W : Type*) (G : Hypergraph3 W), HasUncountableChromatic G → EmbedsInto H G

/-! ### The Erdős #593 Characterization (Galvin-style)

Main theorem: A finite 3-uniform hypergraph appears in every uncountable
chromatic hypergraph ↔ it is 2-colorable.

Intuition: 2-colorable hypergraphs are "simple" (like bipartite graphs) and unavoidable.
Non-2-colorable hypergraphs are "complex" and can be avoided by suitable constructions.
-/

/-- Direction 1: 2-colorable → appears in all (the Galvin direction)
    This is the hard direction requiring Ramsey-theoretic arguments -/
theorem two_colorable_appears_in_all {V : Type*} [Finite V] (H : Hypergraph3 V)
    (h2col : Has2Coloring H) :
    ∀ (W : Type*) (G : Hypergraph3 W), HasUncountableChromatic G → EmbedsInto H G := by
  sorry

/-- Direction 2: Appears in all → 2-colorable (contrapositive construction)
    Construct a hypergraph with χ > ℵ₀ that avoids non-2-colorable H -/
theorem appears_in_all_implies_two_colorable {V : Type*} [Finite V] (H : Hypergraph3 V)
    (hAppears : ∀ (W : Type*) (G : Hypergraph3 W), HasUncountableChromatic G → EmbedsInto H G) :
    Has2Coloring H := by
  sorry

/-- THE MAIN CHARACTERIZATION: Erdős #593 -/
theorem erdos_593_characterization {V : Type*} [Finite V] (H : Hypergraph3 V) :
    AppearsInAllUncountableChromatic H ↔ Has2Coloring H := by
  constructor
  · intro ⟨_, hAppears⟩
    exact appears_in_all_implies_two_colorable H hAppears
  · intro h2col
    exact ⟨‹Finite V›, two_colorable_appears_in_all H h2col⟩

end
