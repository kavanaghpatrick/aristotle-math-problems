/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7e626f64-fa01-45b0-a9ec-94688ecd883f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype { H : Subgroup G // H.Normal }

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-!
# Leinster Groups: Cyclic groups of perfect order are Leinster

A finite group G is a Leinster group if the sum of the orders of all its normal
subgroups equals twice the group's order.

PROVIDED SOLUTION:
For a cyclic group G of order n:
1. Cyclic implies commutative (IsCyclic.commGroup), so every subgroup is normal.
2. Since every subgroup is normal, {H : Subgroup G // H.Normal} ≃ Subgroup G.
3. Subgroups of a cyclic group of order n are in bijection with divisors of n.
   For each divisor d | n, there is exactly one subgroup of order d.
4. Therefore, the sum of orders of normal subgroups = ∑ d ∈ n.divisors, d = σ₁(n).
5. If n is a perfect number, then σ₁(n) = 2n by definition.
6. So the sum = 2n = 2 * Fintype.card G, which is exactly the Leinster condition.

Key Mathlib lemmas:
- `IsCyclic.commGroup`: cyclic groups are commutative
- `Subgroup.Normal.mk`: construct normal subgroup proof
- `Nat.Perfect`: definition of perfect numbers
- `Nat.sum_divisors_eq_sum_properDivisors_add_self`: σ(n) = σ*(n) + n
- `Subgroup.card_subgroup_dvd_card`: Lagrange's theorem
- `IsCyclic.card_orderOf_eq_totient`: structure of cyclic groups

Reference: Leinster, Tom (2001). "Perfect numbers and groups". arXiv:math/0104012
-/

namespace LeinsterGroup

open Finset Subgroup

/-- A finite group G is a Leinster group if the sum of the orders of all its normal subgroups
equals twice the group's order. -/
def IsLeinster (G : Type*) [Group G] [Fintype G] : Prop :=
  ∑ H : {H : Subgroup G // H.Normal}, Nat.card H = 2 * Fintype.card G

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  IsLeinster
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G-/
/-- Cyclic groups of perfect number order are Leinster groups.

This follows because:
- In a cyclic group, all subgroups are normal (since cyclic → abelian).
- The subgroups of a cyclic group of order n correspond to divisors of n,
  with each divisor d giving a unique subgroup of order d.
- The sum of orders of all subgroups equals σ(n) = ∑ d|n, d.
- For perfect n, σ(n) = 2n = 2|G|. -/
theorem cyclic_of_perfect_is_leinster (G : Type*) [Group G] [Fintype G]
    [IsCyclic G] (h_perfect : Nat.Perfect (Fintype.card G)) :
    IsLeinster G := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `LeinsterGroup` after `end`: The current section is unnamed

Hint: Delete the name `LeinsterGroup` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵L̵e̵i̵n̵s̵t̵e̵r̵G̵r̵o̵u̵p̵-/
end LeinsterGroup