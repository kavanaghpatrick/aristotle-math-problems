/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d1b0cad3-bbde-41bf-a8e7-917e1e957eb7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 57844105-2cf6-45e0-ae72-76f3e1591868

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot537: LP DUALITY INTERFACE

  This file prepares the interface for LP-based proof of τ ≤ 8.

  BACKGROUND: By LP duality, if we can find a dual feasible solution
  with objective value ≤ 8, then τ ≤ 8.

  The LP formulation:
  - Primal (covering): min Σ x_e s.t. Σ_{e∈T} x_e ≥ 1 for all triangles T
  - Dual (packing): max Σ y_T s.t. Σ_{T∋e} y_T ≤ 1 for all edges e

  For ν = 4, the maximum packing has value 4.
  Tuza's conjecture says τ ≤ 2ν = 8.

  This file establishes the INTERFACE for the LP argument,
  leaving the heavy formalization for later.
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token 'in'; expected ','
unexpected token 'in'; expected ','
unexpected token 'in'; expected ','
unexpected end of input; expected ','-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token 'in'; expected ','
unexpected token 'in'; expected ','
unexpected token 'in'; expected ','
unexpected end of input; expected ','-/
set_option maxHeartbeats 400000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- FRACTIONAL VERSIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A fractional packing assigns non-negative weights to triangles
    such that each edge is covered by total weight ≤ 1 -/
def isFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : Finset V → ℚ) : Prop :=
  (∀ T, T ∉ G.cliqueFinset 3 → y T = 0) ∧
  (∀ T, 0 ≤ y T) ∧
  (∀ e ∈ G.edgeFinset, ∑ T

in G.cliqueFinset 3, if e ∈ T.sym2 then y T else 0 ≤ 1)

/-- The value of a fractional packing -/
def fractionalPackingValue (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : Finset V → ℚ) : ℚ :=
  ∑ T

in G.cliqueFinset 3, y T

/-- A fractional cover assigns non-negative weights to edges
    such that each triangle is covered by total weight ≥ 1 -/
def isFractionalCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Sym2 V → ℚ) : Prop :=
  (∀ e, e ∉ G.edgeFinset → x e = 0) ∧
  (∀ e, 0 ≤ x e) ∧
  (∀ T ∈ G.cliqueFinset 3, ∑ e

in T.sym2, x e ≥ 1)

/-- The value of a fractional cover -/
def fractionalCoverValue (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Sym2 V → ℚ) : ℚ :=
  ∑ e

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected identifier; expected command
Function expected at
  isFractionalPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isFractionalCover
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalPackingValue
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalCoverValue
but this term has type
  ?m.5

Note: Expected a function because this term is being applied to the argument
  G-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected identifier; expected command
Function expected at
  isFractionalPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isFractionalCover
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalPackingValue
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalCoverValue
but this term has type
  ?m.5

Note: Expected a function because this term is being applied to the argument
  G-/
in G.edgeFinset, x e

-- ══════════════════════════════════════════════════════════════════════════════
-- LP DUALITY (WEAK VERSION)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Weak duality: Any fractional packing value ≤ any fractional cover value -/
theorem weak_duality (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : Finset V → ℚ) (hy : isFractionalPacking G y)
    (x : Sym2 V → ℚ) (hx : isFractionalCover G x) :
    fractionalPackingValue G y ≤ fractionalCoverValue G x := by
  -- Standard LP weak duality proof
  -- Σ_T y_T = Σ_T y_T · 1
  --         ≤ Σ_T y_T · (Σ_{e∈T} x_e)  [by cover constraint]
  --         = Σ_T Σ_{e∈T} y_T · x_e
  --         = Σ_e Σ_{T∋e} y_T · x_e
  --         ≤ Σ_e x_e · 1  [by packing constraint]
  --         = Σ_e x_e
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isFractionalPacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalPackingValue
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Tactic `constructor` failed: target is not an inductive datatype

case left
V : Type u_1
x✝² : Sort u_2
isTrianglePacking : x✝²
x✝¹ : Sort u_3
isFractionalPacking : x✝¹
x✝ : Sort u_4
fractionalPackingValue : x✝
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : sorry
⊢ sorry
Invalid argument: Variable `fractionalPackingValue` is not a proposition or let-declaration
`simp` made no progress-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isFractionalPacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalPackingValue
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Tactic `constructor` failed: target is not an inductive datatype

case left
V : Type u_1
x✝² : Sort u_2
isTrianglePacking : x✝²
x✝¹ : Sort u_3
isFractionalPacking : x✝¹
x✝ : Sort u_4
fractionalPackingValue : x✝
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : sorry
⊢ sorry
Invalid argument: Variable `fractionalPackingValue` is not a proposition or let-declaration
`simp` made no progress-/
-- ══════════════════════════════════════════════════════════════════════════════
-- INTEGER PACKING GIVES FRACTIONAL PACKING
-- ══════════════════════════════════════════════════════════════════════════════

/-- An integer packing induces a fractional packing with same value -/
lemma integer_to_fractional_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    isFractionalPacking G (fun T => if T ∈ M then 1 else 0) ∧
    fractionalPackingValue G (fun T => if T ∈ M then 1 else 0) = M.card := by
  constructor
  · constructor
    · intro T hT
      simp only [ite_eq_right_iff, one_ne_zero]
      intro hT_in
      exact hT (hM.1 hT_in)
    constructor
    · intro T
      split_ifs <;> linarith
    · intro e he
      -- Each edge appears in at most one packing element
      -- (by edge-disjointness)
      sorry
  · -- Value equals cardinality
    simp only [fractionalPackingValue]
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not (G.cliqueFinset 3) (· ∈ M)]
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isFractionalCover
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalCoverValue
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isFractionalCover
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalCoverValue
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LP INTERFACE THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- If ν = 4, then τ* ≤ 8 (fractional cover) -/
theorem fractional_tuza_nu_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hν : ∀ M : Finset (Finset V), isTrianglePacking G M → M.card ≤ 4) :
    ∃ x : Sym2 V → ℚ, isFractionalCover G x ∧ fractionalCoverValue G x ≤ 8 := by
  -- By strong LP duality, the fractional covering number equals
  -- the fractional packing number.
  -- For triangle packing with ν = 4, we have ν* ≤ ν = 4.
  -- By Tuza-like bound for fractional case: τ* ≤ 2ν* ≤ 8.
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isFractionalCover
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalCoverValue
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTriangleCover
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isFractionalCover
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  fractionalCoverValue
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTriangleCover
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G-/
/-- Rounding: If fractional cover ≤ 8, there exists integer cover ≤ 8 -/
theorem fractional_to_integer_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Sym2 V → ℚ) (hx : isFractionalCover G x)
    (hx_val : fractionalCoverValue G x ≤ 8) :
    ∃ E : Finset (Sym2 V), isTriangleCover G E ∧ E.card ≤ 8 := by
  -- This requires a rounding argument
  -- One approach: Greedy selection of high-weight edges
  -- Another: Randomized rounding with union bound
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTriangleCover
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTriangleCover
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
-- ══════════════════════════════════════════════════════════════════════════════
-- COMBINED THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- LP-based proof of τ ≤ 8 when ν = 4 -/
theorem tau_le_8_via_lp (G : SimpleGraph V) [DecidableRel G.Adj]
    (hν : ∀ M : Finset (Finset V), isTrianglePacking G M → M.card ≤ 4) :
    ∃ E : Finset (Sym2 V), isTriangleCover G E ∧ E.card ≤ 8 := by
  obtain ⟨x, hx, hx_val⟩ := fractional_tuza_nu_4 G hν
  exact fractional_to_integer_cover G x hx hx_val

end