# Debate Context: Leinster Groups — Multiple Sub-problems

## The Problems

Leinster groups: A finite group G is Leinster if the sum of orders of all its normal subgroups equals twice the group's order. Several formalized sub-problems exist at different difficulty levels.

## Lean Formalizations (from formal-conjectures/Wikipedia/LeinsterGroup.lean)

```lean
-- Definition
def IsLeinster (G : Type*) [Group G] [Fintype G] : Prop :=
  ∑ H : {H : Subgroup G // H.Normal}, Nat.card H = 2 * Fintype.card G

-- PROBLEM 1: Cyclic groups of perfect number order are Leinster [category API]
theorem cyclic_of_perfect_is_leinster (G : Type*) [Group G] [Fintype G]
    [IsCyclic G] (h_perfect : Nat.Perfect (Fintype.card G)) :
    IsLeinster G := by sorry

-- PROBLEM 2: Abelian iff cyclic perfect [category research solved]
theorem abelian_is_leinster_iff_cyclic_perfect (G : Type*) [CommGroup G] [Fintype G] :
    IsLeinster G ↔ IsCyclic G ∧ Nat.Perfect (Fintype.card G) := by sorry

-- PROBLEM 3: Non-abelian Leinster groups exist [category research solved]
theorem exists_nonabelian_leinster_group :
    ∃ G : Type, ∃ (_ : Group G) (_ : Fintype G),
      IsLeinster G ∧ ¬ ∀ (a b : G), a * b = b * a := by sorry

-- PROBLEM 4: Dihedral iff odd perfect [category research solved]
theorem dihedral_is_leinster_iff_odd_perfect (n : ℕ) [NeZero n] :
    IsLeinster (DihedralGroup n) ↔ Nat.Perfect n ∧ Odd n := by sorry

-- PROBLEM 5: Infinitely many Leinster groups? [category research open]
theorem infinitely_many_leinster_groups : answer(sorry) ↔
    ¬∃ n : ℕ, ∀ G : Type, ∀ (_ : Group G) (_ : Fintype G),
      IsLeinster G → Fintype.card G < n := by sorry
```

## Analysis

- PROBLEM 1 (API): Should be provable — for cyclic groups, subgroups correspond to divisors, and perfect number = sigma(n) = 2n
- PROBLEM 2 (solved): Known theorem by Leinster (2001) — the abelian case reduces to divisor sums
- PROBLEM 3 (solved): S3 × C5 (order 30) is a known example
- PROBLEM 4 (solved): Known connection between dihedral Leinster groups and odd perfect numbers
- PROBLEM 5 (open): Genuinely open — connected to whether infinitely many perfect numbers exist

## Key Questions for Debate

1. Which of these 5 problems should we target first?
2. Is Problem 1 (cyclic+perfect → Leinster) tractable in Lean via mathlib's divisor sum API?
3. Problem 3 could be a falsification-style win — just verify S3 × C5 has the Leinster property. Is this doable?
4. Problem 4 connects to odd perfect numbers — is the conditional direction useful?
5. Should we submit multiple sub-problems or focus on one?
