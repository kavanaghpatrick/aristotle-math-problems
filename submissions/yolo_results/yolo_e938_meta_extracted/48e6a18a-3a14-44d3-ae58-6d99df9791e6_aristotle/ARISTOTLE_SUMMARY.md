# Summary of changes for run 48e6a18a-3a14-44d3-ae58-6d99df9791e6
# Erdős Problem 938 — Formalization

## Status: OPEN PROBLEM (sorry on the main conjecture is mathematically unavoidable)

I created `RequestProject/Erdos938.lean` containing:

### Definitions
- **`Nat.Powerful`**: A natural number n is powerful if n ≥ 1 and for every prime p dividing n, p² also divides n.
- **`Set.IsAPOfLength`**: A set S forms a k-term arithmetic progression if S = {a, a+d, a+2d, …, a+(k-1)d} for some a and d > 0.

### Proved results (all sorry-free, standard axioms only)
1. **`Nat.Powerful.one`**: 1 is powerful (vacuously).
2. **`Nat.Powerful.sq`**: Every perfect square m² with m ≥ 1 is powerful.
3. **`Nat.Powerful.infinite`**: The set of powerful numbers is infinite.
4. **`exists_sq_between`**: Between any two natural numbers sufficiently far apart (gap > 2√b + 2), there exists a perfect square strictly between them with m ≥ 1. This is the key unconditional ingredient for the square-gap bound: if three consecutive powerful numbers form an AP with common difference d, then d ≤ √(n_{k+2}) + 1.

### Main conjecture (sorry)
```lean
theorem erdos_938 :
    {P : Finset ℕ | Set.IsAPOfLength (P : Set ℕ) 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)}}.Finite := by sorry
```

This `sorry` represents genuine mathematical uncertainty — Erdős 938 is an **open problem**. Up to 10¹⁴, only 18 consecutive powerful 3-APs are known. Moreover, van Doorn (2026, arXiv:2605.06697) conjectures the opposite: that infinitely many consecutive powerful 3-APs exist, which would *falsify* this conjecture. The structural gap between:
- the unconditional square-gap bound (d ≤ √n + 1),
- abc-conditional lower bounds on gaps between powerful numbers (Chan 2022), and
- the per-kernel Mordell–Siegel finiteness argument

remains the open core of the problem. No known technique closes it unconditionally.