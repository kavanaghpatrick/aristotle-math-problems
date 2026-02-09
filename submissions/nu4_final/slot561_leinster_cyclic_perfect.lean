import Mathlib

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

end LeinsterGroup
