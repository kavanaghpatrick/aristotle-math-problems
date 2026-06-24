import Mathlib

/-!
# Erdős Problem 1003: Infinitely many n with φ(n) = φ(n+1)

## Status: OPEN PROBLEM

This is an **open problem** in number theory. Erdős conjectured (1985) that there
are infinitely many positive integers n such that φ(n) = φ(n+1), where φ is
Euler's totient function.

## Known results

- Many solutions are known computationally: n = 1, 3, 15, 104, 164, 194, 255,
  495, 584, 975, ... extending to roughly 10¹¹.
- Erdős-Pomerance-Sárközy (1987) proved the count of n ≤ x is at most
  x / exp((log x)^{1/3}), so the set has natural density zero.
- Graham-Holt-Pomerance (1998) showed standard prime-tuple constructions that
  work for φ(n) = φ(n+k) with k ≥ 2 fail at k = 1.
- The only known structured family is n = 2^(2^r) − 1 (requiring F₀,...,F_{r-1}
  to all be Fermat primes), which terminates at r = 5 since F₅ is composite.

## Why standard approaches fail

1. **Fermat prime tower**: n = 2^(2^k) − 1 = F₀·F₁·...·F_{k-1} satisfies
   φ(n) = φ(n+1) when all Fermat numbers F₀,...,F_{k-1} are prime. This gives
   solutions for k = 1,...,5 but F₅ = 2³²+1 = 641 × 6700417 is composite.

2. **Prime tuple approach**: For k ≥ 2, one can construct n with φ(n) = φ(n+k)
   using simultaneous prime conditions (e.g., find primes p,q with p|n, q|n+k
   and appropriate multiplicity). Graham-Holt-Pomerance showed this fails for
   k = 1 due to a parity obstruction.

3. **S-unit equations**: For fixed prime support, the equation n + 1 = n implies
   a unit equation with finitely many solutions (by Evertse-Schlickewei-Schmidt).
   Any infinite family must use unbounded prime support.

## What we prove here

We computationally verify several small solutions, confirming the set is nonempty.
The full infinitude statement remains as a sorry — it is an open conjecture.
-/

open Nat in
/-- Computational verification: φ(1) = φ(2) = 1 -/
example : Nat.totient 1 = Nat.totient 2 := by native_decide

open Nat in
/-- Computational verification: φ(3) = φ(4) = 2 -/
example : Nat.totient 3 = Nat.totient 4 := by native_decide

open Nat in
/-- Computational verification: φ(15) = φ(16) = 8 -/
example : Nat.totient 15 = Nat.totient 16 := by native_decide

open Nat in
/-- Computational verification: φ(104) = φ(105) = 48 -/
example : Nat.totient 104 = Nat.totient 105 := by native_decide

open Nat in
/-- Computational verification: φ(164) = φ(165) = 80 -/
example : Nat.totient 164 = Nat.totient 165 := by native_decide

open Nat in
/-- Computational verification: φ(194) = φ(195) = 96 -/
example : Nat.totient 194 = Nat.totient 195 := by native_decide

open Nat in
/-- Computational verification: φ(255) = φ(256) = 128 -/
example : Nat.totient 255 = Nat.totient 256 := by native_decide

/-- The set {n : ℕ | φ(n) = φ(n+1)} is nonempty (witnessed by n = 1). -/
theorem erdos_1003_nonempty :
    {n : ℕ | Nat.totient n = Nat.totient (n + 1)}.Nonempty := by
  exact ⟨1, by native_decide⟩

/--
**Erdős Problem 1003** (Open Conjecture):
There are infinitely many positive integers n such that φ(n) = φ(n+1).

This is an open problem in number theory. No proof is currently known (as of 2026).
The `sorry` below reflects the open status of this conjecture.
-/
theorem erdos_1003 :
    {n : ℕ | Nat.totient n = Nat.totient (n + 1)}.Infinite := by sorry
