# Debate Context: Lehmer's Totient Problem

## The Problem

Lehmer's totient problem (1932): Does there exist a composite number n > 1 such that Euler's totient function phi(n) divides n - 1?

Equivalently: Is every totient "cototient-free" in the sense that phi(n) | (n-1) implies n is prime?

## Lean Formalization (from formal-conjectures)

```lean
-- From FormalConjectures/Wikipedia/LehmerTotient.lean
namespace LehmerTotient

/--
Does there exist a composite number n > 1 such that Euler's totient function
phi(n) divides n - 1?
-/
@[category research open, AMS 11]
theorem lehmer_totient :
    answer(sorry) ↔ ∃ n > 1, ¬Prime n ∧ Nat.totient n ∣ n - 1 := by
  sorry

end LehmerTotient
```

KEY: The `answer(sorry)` format means the answer could be True OR False. Aristotle can resolve this by:
- Proving `True ↔ ∃ n > 1, ¬Prime n ∧ Nat.totient n ∣ n - 1` (counterexample EXISTS)
- Proving `False ↔ ∃ n > 1, ¬Prime n ∧ Nat.totient n ∣ n - 1` (no such composite exists, i.e., phi(n) | (n-1) implies n is prime)

## Known Results

1. Any counterexample n (Lehmer number) must be:
   - Odd
   - Squarefree
   - A product of distinct primes (Carmichael number-like structure)
   - Have at least 14 distinct prime factors (Cohen & Hagis, 1980)
   - Exceed 10^30
   - Be a Carmichael number (phi(n) | n-1 implies lambda(n) | n-1 for squarefree n)
   - Satisfy: for each prime p | n, (p-1) | (n-1) and p ∤ (n/p - 1)

2. Connected to Carmichael numbers: Every Lehmer number would be a Carmichael number, but not every Carmichael number is a Lehmer number.

3. The conjecture (that no counterexample exists) has been verified computationally up to very large bounds.

## Our Project Context

- We submit bare gap conjectures to Aristotle (a Lean theorem prover)
- Our one success so far was a FALSIFICATION (ArithmeticSumS: proved the conjecture false)
- answer(sorry) problems are high-value because Aristotle can prove either direction
- We need to determine: What is the exact open gap? Is it tractable?

## Debate Goal

Identify the exact open gap for submission to Aristotle. Key questions:
1. Is the falsification direction (finding a counterexample) or the proof direction (showing none exists) more tractable?
2. Are there known partial results that Aristotle could formalize?
3. Is this problem too hard for current methods, or is there a tractable sub-gap?
4. Should we submit the full open problem, or a specific partial result?
