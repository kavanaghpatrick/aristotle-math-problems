# Debate Context: Erdos 850 — Three Consecutive Pairs with Same Prime Factors

## The Open Problem

Erdos Problem 850: Do there exist two distinct integers x and y such that x,y have the same prime factors, x+1,y+1 have the same prime factors, AND x+2,y+2 also have the same prime factors?

## Lean Formalization

```lean
@[category research open, AMS 11]
theorem erdos_850 :
    answer(sorry) ↔ ∃ x y : ℕ, x ≠ y ∧ x.primeFactors = y.primeFactors
      ∧ (x + 1).primeFactors = (y + 1).primeFactors
      ∧ (x + 2).primeFactors = (y + 2).primeFactors := by
    sorry
```

## Key Properties

- `answer(sorry)` — Aristotle can prove True (construct a witness pair) OR False (prove no such pair exists)
- Uses only `ℕ`, `primeFactors`, equality — basic Mathlib
- Pure existential over ℕ: a concrete numerical witness would resolve it
- The 2-consecutive version (x,y and x+1,y+1 same prime factors) is known to have solutions
- Question: does extending to 3 consecutive pairs make it impossible?

## What We Know

- For k=1 (just x,y same prime factors): trivially yes (e.g., 2 and 4)
- For k=2 (pairs x,x+1 and y,y+1): yes, known solutions exist
- For k=3 (triples x,x+1,x+2 and y,y+1,y+2): THIS IS THE OPEN QUESTION
- Numbers sharing prime factors are called "ABC-equivalent" or have the same radical

## Our Project Context

- We submit bare gap conjectures to Aristotle (Lean theorem prover)
- answer(sorry) problems are highest value — prover can resolve either direction
- Our one success was a FALSIFICATION (ArithmeticSumS)
- We need to determine: is this gap tractable? Which direction is more likely?
