/-
Erdős Problem #944 - Critical Vertices/Edges
BORIS PATTERN: Multiple SOLVED variants exist!

Target: Prove the SOLVED cases (Brown 1992, Jensen 2002, Lattanzio 2002)
These are KNOWN constructions - exactly what Aristotle excels at!
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

universe u
variable {V : Type u}

namespace Erdos944

open SimpleGraph

/-- A vertex v is critical if deleting it lowers the chromatic number -/
def SimpleGraph.IsCriticalVertex (G : SimpleGraph V) (v : V) : Prop :=
  G.chromaticNumber = (G.deleteVerts {v}).chromaticNumber + 1

/-- A graph is vertex-critical if every vertex is critical -/
def SimpleGraph.IsVertexCritical (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ v : V, G.IsCriticalVertex v

/-- An edge set is critical if deleting it lowers the chromatic number -/
def SimpleGraph.IsCriticalEdgeSet (G : SimpleGraph V) (edges : Set (Sym2 V)) : Prop :=
  edges ⊆ G.edgeSet ∧
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

/-- The Erdős-944 property: chromatic number k, all vertices critical,
    but every critical edge set has size > r -/
def SimpleGraph.IsErdos944 (G : SimpleGraph V) (k r : ℕ) : Prop :=
  G.IsVertexCritical k ∧
  ∀ (edges : Set (Sym2 V)), G.IsCriticalEdgeSet edges → r < edges.ncard

/-!
## SOLVED VARIANTS - These have known proofs!
-/

/--
Brown (1992) proved Dirac's conjecture for k=5:
There exists a 5-critical graph where every vertex is critical
but no single edge is critical.
-/

theorem dirac_k5_brown1992 :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 5 1 := by
  sorry

/--
Lattanzio (2002): k-critical graphs without critical edges exist
when k-1 is not prime.
-/

theorem lattanzio2002 (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry

/--
Jensen (2002): k-critical graphs without critical edges exist for all k ≥ 5.
-/

theorem jensen2002 (k : ℕ) (hk : 5 ≤ k) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  sorry

/--
The main open case: Does there exist a 4-critical graph with no critical edges?
This is the only remaining open case of Dirac's conjecture.
-/

theorem dirac_k4_open :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 4 1 := by
  sorry

end Erdos944
