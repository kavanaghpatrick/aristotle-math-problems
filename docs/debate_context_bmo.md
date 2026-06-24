# Debate Context: Busy Beaver Math Olympiad — Turing Machine Halting as Pure NT

## The Open Problems

The Beaver Math Olympiad (BMO) reformulates Turing machine halting problems as pure number theory / recurrence relations. These come from studying small Busy Beaver values (6-state machines).

## BMO Problem 1 — Lean Formalization

```lean
@[category research open, AMS 5 11 68]
theorem busy_beaver_math_olympiad_problem_1 :
    answer(sorry) ↔ ∀ᵉ (a : ℕ → ℕ) (b : ℕ → ℕ)
    (a_ini : a 0 = 1)
    (a_rec : ∀ n, a (n + 1) = if b n ≤ a n then a n - b n else 2 * a n + 1)
    (b_ini : b 0 = 2)
    (b_rec : ∀ n, b (n + 1) = if b n ≤ a n then 4 * b n + 2 else b n - a n),
    ∃ i, a i = b i := by
  sorry
```

## What This Is

Starting from (a₀, b₀) = (1, 2), iterate:
- If a_n ≥ b_n: (a_{n+1}, b_{n+1}) = (a_n - b_n, 4b_n + 2)
- If a_n < b_n: (a_{n+1}, b_{n+1}) = (2a_n + 1, b_n - a_n)

Question: Does there exist i with a_i = b_i?

## Key Properties

- answer(sorry) — can prove True (converges) or False (diverges forever)
- Pure ℕ arithmetic recurrence — no analysis, no topology
- The recurrence is COMPLETELY CONCRETE — Aristotle can compute values
- This is equivalent to a 6-state Turing machine halting problem
- "No consensus on whether the machine halts or not"
- The first 10 values are given: (1,2), (3,1), (2,6), (5,4), (1,18), (3,17), (7,14), (15,7), (8,30), (17,22)

## Why This Might Be Tractable

1. The recurrence is simple — just if/else with basic arithmetic
2. If the answer is True (halts), a finite computation witnesses it
3. If the answer is False (doesn't halt), Aristotle needs to find an invariant
4. Collatz-like problems have been studied extensively — Aristotle may find patterns
5. The problem is FULLY DECIDABLE for any finite number of steps

## Why This Might Be Hard

1. It's equivalent to a Turing machine halting problem — potentially undecidable in practice
2. Collatz-like recurrences are notoriously hard
3. If it diverges, proving non-termination requires finding a suitable invariant or monovariant

## Other BMO Problems

The file contains multiple BMO problems — some may be more tractable than others. The "Antihydra" problem (BMO#2) is another famous one.
