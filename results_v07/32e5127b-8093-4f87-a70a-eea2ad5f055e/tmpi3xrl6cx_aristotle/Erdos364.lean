import Mathlib

/-!
# Erdős Problem 364 — No Three Consecutive Powerful Numbers

A positive integer `n` is **powerful** (also called *squarefull*) if every
prime factor of `n` appears with exponent ≥ 2 in its factorization.

**Conjecture (Erdős, 1976)**: There do not exist three consecutive positive
integers `n, n+1, n+2` that are all powerful.

Golomb proved that consecutive powerful *pairs* exist (e.g., `(8, 9)`).
No consecutive powerful *triple* has ever been found computationally.

## Status

This is an **open problem**. The ABC conjecture would imply at most finitely
many such triples, but an unconditional proof remains unknown.

## What we prove

We formalize a **partial result**: For 3 out of 4 residue classes mod 4,
the conjecture follows from a simple argument.

**Key lemma**: Among any three consecutive integers, if `n ≢ 3 (mod 4)`,
then one of `n, n+1, n+2` is `≡ 2 (mod 4)`, hence divisible by 2 but not 4,
and therefore not powerful.

The remaining case `n ≡ 3 (mod 4)` — where `n` and `n+2` are both odd
and `n+1 ≡ 0 (mod 4)` — is the core difficulty. One can extend the modular
sieve to primes 3, 5, 7, … (eliminating cases where some `p ∣ (n+k)` but
`p² ∤ (n+k)`), but the sieve never terminates: for any finite set of primes,
there exist residue classes that survive all checks.
-/

/-- A number `m` is **powerful** if every prime divisor `p` satisfies `p² ∣ m`. -/
def IsPowerful (m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m

/-- If `m ≡ 2 (mod 4)`, then `m` is not powerful: the prime 2 divides `m`
but `2² = 4` does not. -/
lemma not_powerful_of_two_mod_four (m : ℕ) (h : m % 4 = 2) : ¬ IsPowerful m := by
  exact fun H => absurd (H 2 Nat.prime_two (Nat.dvd_of_mod_eq_zero (by omega))) (by omega)

/-- **Proved**: If `n ≢ 3 (mod 4)`, then `n, n+1, n+2` cannot all be powerful.

When `n % 4 ∈ {0, 1, 2}`, one of the three consecutive numbers is `≡ 2 (mod 4)`:
- `n ≡ 0`: then `n + 2 ≡ 2 (mod 4)`
- `n ≡ 1`: then `n + 1 ≡ 2 (mod 4)`
- `n ≡ 2`: then `n ≡ 2 (mod 4)`

That number is divisible by 2 but not 4, hence not powerful. -/
lemma erdos364_easy_cases (n : ℕ) (hn : n % 4 ≠ 3)
    (h1 : IsPowerful n) (h2 : IsPowerful (n + 1)) (h3 : IsPowerful (n + 2)) : False := by
  have h_cases : (n % 4 = 0 ∧ (n + 2) % 4 = 2) ∨ (n % 4 = 1 ∧ (n + 1) % 4 = 2) ∨
      (n % 4 = 2 ∧ n % 4 = 2) := by grind
  rcases h_cases with (⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5⟩) <;>
    have := not_powerful_of_two_mod_four _ h5 <;> simp_all +decide

/-- **OPEN**: The case `n ≡ 3 (mod 4)` of Erdős Problem 364.

When `n ≡ 3 (mod 4)`, both `n` and `n + 2` are odd and `4 ∣ (n + 1)`.
Simple modular arithmetic modulo 4 does not eliminate this case. Further
analysis modulo 3 restricts to `n ≡ 7, 27, 35 (mod 36)`, but no finite
modular sieve closes the argument.

This remains an open problem in number theory. -/
theorem erdos364_mod4 (n : ℕ) (hn : n ≥ 1) (hmod : n % 4 = 3)
    (h1 : ∀ p, Nat.Prime p → p ∣ n → p ^ 2 ∣ n)
    (h2 : ∀ p, Nat.Prime p → p ∣ (n + 1) → p ^ 2 ∣ (n + 1))
    (h3 : ∀ p, Nat.Prime p → p ∣ (n + 2) → p ^ 2 ∣ (n + 2)) :
    False := by
  sorry

/-- **Erdős Problem 364** (OPEN): There do not exist three consecutive positive
integers that are all powerful.

**Status**: This conjecture remains open. The case `n ≢ 3 (mod 4)` is proved
by `erdos364_easy_cases` above. The case `n ≡ 3 (mod 4)` — where both `n` and
`n + 2` are odd and `4 ∣ (n + 1)` — requires methods beyond simple modular
arithmetic and remains unresolved. The theorem `erdos364_mod4` captures this
open case.

The ABC conjecture implies that there are at most finitely many counterexamples.
No counterexample has been found computationally for `n < 10²²`. -/
theorem erdos364 : ¬ ∃ n : ℕ, n ≥ 1 ∧
    (∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n) ∧
    (∀ p : ℕ, Nat.Prime p → p ∣ (n + 1) → p ^ 2 ∣ (n + 1)) ∧
    (∀ p : ℕ, Nat.Prime p → p ∣ (n + 2) → p ^ 2 ∣ (n + 2)) := by
  intro ⟨n, hn, h1, h2, h3⟩
  by_cases hmod : n % 4 = 3
  · exact erdos364_mod4 n hn hmod h1 h2 h3
  · exact erdos364_easy_cases n hmod h1 h2 h3
